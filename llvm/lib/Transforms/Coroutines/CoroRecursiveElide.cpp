//===- CoroRecursiveElide.cpp - Elide recursive coroutine frames ---------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// \file
// CoroAnnotationElide requires the callee's final frame size (known only
// after the callee is split) and a still-presplit caller. On an acyclic call
// graph the CGSCC pipeline provides both by visiting callees first, but a
// recursive coroutine is a call graph cycle: every function on it is split
// during the same SCC visit, so no call site on the cycle ever observes a
// presplit caller and recursion never benefits from elision.
//
// These two passes lift that restriction by walking the recursion's
// *activation tree* instead of its call graph, nesting activations into a
// single block allocation until the elision frame-size limit is reached:
//
// - CoroRecursionStashPass runs before the CGSCC pipeline. For every SCC of
//   presplit coroutines connected by direct coro_elide_safe call sites, it
//   clones each member into a "template": an internal function that the
//   normal pipeline simplifies like any presplit coroutine but that
//   CoroSplit is taught to skip, preserving cloneable presplit IR past the
//   point where real frame sizes exist.
//
// - CoroRecursiveElidePass runs after the CGSCC pipeline. Starting from the
//   ordinary split of each cycle member (generation 0), it repeatedly clones
//   the template into generation k+1, eliding each cycle call site into the
//   generation-k callee -- exactly like CoroAnnotationElide, alloca plus
//   `.noalloc` call plus inlining -- whenever generation k's now-known frame
//   size fits under the elision limits, and then splits the new clone. Frame
//   sizes grow strictly per generation and are bounded by the limits, so the
//   iteration reaches a fixed point: the generation whose children no longer
//   fit. That top generation is republished under the original symbol.
//
// Every caller of the original -- including the "escape" call sites inside
// the blocks themselves, which still name the original symbol -- thereby
// enters a full-sized block, and the recursion proceeds block by block, each
// block one allocation. No call graph trickery is needed: by the time the
// republished symbol re-forms the cycle, every function involved is already
// split, and the elision decisions are already made. If the recursion
// terminates before reaching the bottom of a block, the remaining elided
// frames are never started; as with any speculatively elided frame on an
// untaken path, the space is wasted but no lifetime begins.
//
// Besides direct coro_elide_safe call sites, these passes support *bulk
// range* sites: coroutines created in a statically bounded loop and joined
// through a bulk awaitable whose type carries
// [[clang::coro_await_elidable_range]]. The frontend tags the awaitable's
// llvm.coro.await.suspend.* call with the "coro-elide-range" attribute; the
// creation calls themselves carry no attribute (they are reached through
// iterators and are invisible to the syntactic elide-safe marking). They are
// recovered from the IR instead: a call whose returned coroutine handle
// receives a store of a pointer into the marked awaiter object is one of the
// coroutines that awaitable joins, and the attribute asserts that all of
// them complete before the await resumes. Each such call executing at most N
// times per activation (N = the containing loop's constant trip bound, or 1
// in straight-line code) is given an N-slot frame array in the caller,
// indexed by a synthesized per-activation counter, so concurrently live
// children occupy distinct slots. Since the cycle these sites form passes
// through non-coroutine glue (iterator adaptors, lambdas), the stash accepts
// SCCs with such glue members and pins the glue's cycle call sites noinline
// in place, so the sites survive, still outlined, once the glue is inlined
// into the templates.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Coroutines/CoroRecursiveElide.h"

#include "CoroInternal.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/Coroutines/CoroInstr.h"
#include "llvm/Transforms/IPO/AlwaysInliner.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

using namespace llvm;

#define DEBUG_TYPE "coro-recursive-elide"

// Defined in CoroAnnotationElide.cpp; the same limits size the blocks here.
extern cl::opt<uint64_t> CoroElideMaxFrameSize;
extern cl::opt<uint64_t> CoroElideMaxAccumulatedFrameSize;

static cl::opt<unsigned> CoroRecursiveElideMaxGenerations(
    "coro-recursive-elide-max-generations", cl::init(32), cl::Hidden,
    cl::desc("Maximum number of specialization generations built while "
             "nesting a recursive coroutine into block allocations; each "
             "generation nests one more level of the recursion. 0 disables "
             "recursive elision."));

static cl::opt<uint64_t> CoroBulkDefaultSlots(
    "coro-elide-bulk-default-slots", cl::init(8), cl::Hidden,
    cl::desc("Maximum frame slots reserved for one bulk range creation "
             "site; executions beyond the reserved slots allocate "
             "normally. Bounds the speculative block size on sites with "
             "large or unknown execution counts."));

// Prints the bulk range site discovery decisions; usable in builds without
// assertions, unlike -debug-only.
static cl::opt<bool> CoroBulkDebug("coro-elide-bulk-debug", cl::init(false),
                                   cl::Hidden);

static constexpr const char *TemplateAttr = "coro.recursive.template";
static constexpr const char *GroupAttr = "coro.recursive.group";
// Call-site attribute the frontend places on the llvm.coro.await.suspend.*
// call of a directly awaited [[clang::coro_await_elidable_range]] awaitable.
static constexpr const char *RangeMarkAttr = "coro-elide-range";

//===----------------------------------------------------------------------===//
// Shared helpers (mirroring CoroAnnotationElide's elision mechanics)
//===----------------------------------------------------------------------===//

static Instruction *getFirstNonAllocaInEntry(Function *F) {
  for (Instruction &I : F->getEntryBlock())
    if (!isa<AllocaInst>(&I))
      return &I;
  llvm_unreachable("no terminator in the entry block");
}

static uint64_t accumulatedElidedFrameSize(Function *Caller) {
  uint64_t Sum = 0;
  const DataLayout &DL = Caller->getDataLayout();
  for (Instruction &I : Caller->getEntryBlock())
    if (auto *AI = dyn_cast<AllocaInst>(&I))
      if (AI->hasMetadata("coro.elided.frame"))
        if (auto Size = AI->getAllocationSize(DL))
          Sum += Size->getFixedValue();
  return Sum;
}

// Rewrite one call site to the `.noalloc` variant taking FramePtr as its
// frame storage, and inline that variant.
static void rewriteToNoAlloc(CallBase *CB, Function *NoAllocCallee,
                             Value *FramePtr) {
  SmallVector<Value *, 4> NewArgs(CB->args());
  NewArgs.push_back(FramePtr);
  CallBase *NewCB = nullptr;
  if (auto *CI = dyn_cast<CallInst>(CB)) {
    auto *NewCI = CallInst::Create(NoAllocCallee->getFunctionType(),
                                   NoAllocCallee, NewArgs, "",
                                   CB->getIterator());
    NewCI->setTailCallKind(CI->getTailCallKind());
    NewCB = NewCI;
  } else if (auto *II = dyn_cast<InvokeInst>(CB)) {
    NewCB = InvokeInst::Create(NoAllocCallee->getFunctionType(), NoAllocCallee,
                               II->getNormalDest(), II->getUnwindDest(),
                               NewArgs, {}, "", CB->getIterator());
  } else {
    llvm_unreachable("CallBase should either be Call or Invoke");
  }
  NewCB->setCallingConv(CB->getCallingConv());
  NewCB->setAttributes(CB->getAttributes());
  NewCB->setDebugLoc(CB->getDebugLoc());
  NewCB->removeFnAttr(llvm::Attribute::CoroElideSafe);
  NewCB->removeFnAttr(llvm::Attribute::NoInline);
  CB->replaceAllUsesWith(NewCB);

  InlineFunctionInfo IFI;
  if (InlineFunction(*NewCB, IFI).isSuccess()) {
    CB->eraseFromParent();
  } else {
    NewCB->replaceAllUsesWith(CB);
    NewCB->eraseFromParent();
  }
}

// Allocate frame storage of Size bytes in the caller's entry block, tagged
// so later elision decisions can total up the bytes already elided here.
static AllocaInst *createElidedFrameStorage(Function *Caller, uint64_t Size,
                                            Align FrameAlign) {
  LLVMContext &C = Caller->getContext();
  const DataLayout &DL = Caller->getDataLayout();
  auto *FrameTy = ArrayType::get(Type::getInt8Ty(C), Size);
  auto *Frame =
      new AllocaInst(FrameTy, DL.getAllocaAddrSpace(), "",
                     getFirstNonAllocaInEntry(Caller)->getIterator());
  Frame->setAlignment(FrameAlign);
  Frame->setMetadata("coro.elided.frame", MDNode::get(C, {}));
  return Frame;
}

// Elide one call site: allocate the callee frame in the caller, call the
// `.noalloc` variant with it, and inline that variant.
static void elideSite(CallBase *CB, Function *Caller, Function *NoAllocCallee,
                      uint64_t FrameSize, Align FrameAlign) {
  auto *Frame = createElidedFrameStorage(Caller, FrameSize, FrameAlign);
  rewriteToNoAlloc(CB, NoAllocCallee, Frame);
}

//===----------------------------------------------------------------------===//
// Bulk range sites
//===----------------------------------------------------------------------===//

bool coro::isRangeMarkedAwaitSuspend(const CallBase &CB) {
  return isa<CoroAwaitSuspendInst>(&CB) && CB.hasFnAttr(RangeMarkAttr);
}

static bool isRangeMarkedSuspend(const CallBase &CB) {
  return coro::isRangeMarkedAwaitSuspend(CB);
}

namespace {
// A coroutine-creating call site joined by a range-marked bulk await.
struct BulkRangeSite {
  CallBase *CreationCall = nullptr;
  // Loop containing the creation call, or null in straight-line code.
  Loop *L = nullptr;
  // Constant bound on the executions of the creation call per caller
  // activation, if one is known (loop trip bound), else 0. Purely a sizing
  // hint: an execution beyond the reserved slots falls back to the
  // original, allocating callee at runtime.
  uint64_t KnownBound = 1;
  // Number of frame slots to reserve; decided by the cost model.
  uint64_t NSlots = 1;
};
} // namespace

// Find the creation calls joined by range-marked bulk awaits in F. A
// creation call is a direct call returning a coroutine handle through which
// a pointer into a marked awaiter object is stored -- the linking the bulk
// awaitable performs (continuation, done-count, result pointers) on each
// coroutine it will run and join. The range attribute asserts that every
// coroutine so linked completes before the await resumes, which contains the
// child frame's lifetime within the caller's activation. Candidates must
// execute a statically bounded number of times per activation: at most once
// (straight-line code, e.g. after full unrolling), or bounded by the
// constant maximum trip count of the containing loop, which must be in
// simplified form and the outermost one so a slot counter can be
// synthesized (see elideBulkSite).
static void findBulkRangeSites(Function &F, LoopInfo &LI, ScalarEvolution &SE,
                               DominatorTree &DT,
                               function_ref<bool(Function *)> IsCandidateCallee,
                               SmallVectorImpl<BulkRangeSite> &Out) {
  SmallPtrSet<Value *, 32> IntoAwaiter;
  SmallVector<Value *, 16> Worklist;
  for (Instruction &I : instructions(F)) {
    auto *CB = dyn_cast<CallBase>(&I);
    if (!CB || !isRangeMarkedSuspend(*CB))
      continue;
    Value *Awaiter = cast<CoroAwaitSuspendInst>(CB)->getAwaiter()
                         ->stripPointerCasts();
    if (IntoAwaiter.insert(Awaiter).second)
      Worklist.push_back(Awaiter);
  }
  if (Worklist.empty())
    return;

  // Close over derived pointers into the awaiter objects.
  while (!Worklist.empty()) {
    Value *V = Worklist.pop_back_val();
    for (User *U : V->users())
      if (isa<GetElementPtrInst>(U) || isa<BitCastInst>(U) ||
          isa<AddrSpaceCastInst>(U))
        if (IntoAwaiter.insert(cast<Value>(U)).second)
          Worklist.push_back(cast<Value>(U));
  }

  SmallPtrSet<CallBase *, 8> Creations;
  SmallVector<CallBase *, 8> CreationOrder;
  for (Instruction &I : instructions(F)) {
    auto *SI = dyn_cast<StoreInst>(&I);
    if (!SI || !IntoAwaiter.count(SI->getValueOperand()))
      continue;
    auto *CB =
        dyn_cast<CallBase>(getUnderlyingObject(SI->getPointerOperand()));
    if (!CB || !CB->getType()->isPointerTy() || !CB->getCalledFunction() ||
        !IsCandidateCallee(CB->getCalledFunction()))
      continue;
    if (Creations.insert(CB).second)
      CreationOrder.push_back(CB);
  }
  if (CoroBulkDebug)
    errs() << "[bulk] " << F.getName() << ": " << IntoAwaiter.size()
           << " awaiter-derived values, " << CreationOrder.size()
           << " creation calls\n";

  SmallPtrSet<Loop *, 4> ClaimedLoops;
  for (CallBase *C : CreationOrder) {
    BulkRangeSite Site;
    Site.CreationCall = C;
    if (Loop *L = LI.getLoopFor(C->getParent())) {
      // The synthesized counter (a header phi incremented at the call)
      // requires the call directly in the loop (not in an inner loop, so it
      // executes at most once per iteration) with its block dominating the
      // single latch (so the incremented value reaches the phi on every
      // backedge). One site per loop: the elision inlining splits blocks,
      // after which a second site could no longer wire its counter to the
      // loop's (stale) structure.
      BasicBlock *Latch = L->getLoopLatch();
      if (!Latch || !DT.dominates(C->getParent(), Latch) ||
          !ClaimedLoops.insert(L).second) {
        if (CoroBulkDebug)
          errs() << "[bulk]   reject (loop shape) latch=" << !!Latch
                 << " in block " << C->getParent()->getName() << "\n";
        continue;
      }
      Site.L = L;
      Site.KnownBound = SE.getSmallConstantMaxTripCount(L);
    }
    if (CoroBulkDebug)
      errs() << "[bulk]   site in " << C->getParent()->getName()
             << " bound=" << Site.KnownBound << "\n";
    Out.push_back(Site);
  }
}

// Elide one bulk range site: allocate an array of NSlots callee frames in
// the caller and synthesize a counter selecting the next slot on each
// execution of the creation call. Within one activation every concurrently
// live child gets a distinct slot; a re-entry of the loop can only follow
// the bulk await's completion (the direct-await contract), by which point
// all previously linked children have finished.
//
// When the executions are not proven to fit the reserved slots, the site is
// rewritten to a small always-inlined dispatch helper instead of directly
// to `.noalloc`: executions past the last slot keep calling the original,
// runtime-allocating symbol. The helper (and its `.noalloc` arm) is inlined
// immediately; building the dispatch as a function lets InlineFunction do
// the control-flow surgery, which keeps invoke sites and their landing
// pads intact.
static void elideBulkSite(const BulkRangeSite &Site, Function *Caller,
                          Function *NoAllocCallee, uint64_t FrameSize,
                          Align FrameAlign) {
  LLVMContext &Ctx = Caller->getContext();
  uint64_t Padded = alignTo(FrameSize, FrameAlign);
  auto *Arr =
      createElidedFrameStorage(Caller, Padded * Site.NSlots, FrameAlign);

  CallBase *C = Site.CreationCall;
  if (!Site.L) {
    rewriteToNoAlloc(C, NoAllocCallee, Arr);
    return;
  }

  auto *I64 = Type::getInt64Ty(Ctx);
  BasicBlock *Header = Site.L->getHeader();
  auto *Idx = PHINode::Create(I64, pred_size(Header), "", Header->begin());
  // The increment sits before the call (counting started executions), so
  // it dominates the latch whenever the call's block does, whether the
  // call is a CallInst or an InvokeInst terminator.
  auto *Inc = BinaryOperator::CreateNUWAdd(Idx, ConstantInt::get(I64, 1), "",
                                           C->getIterator());
  // Predecessor edges from outside the loop enter it (count restarts at
  // zero); the ones inside are latches, where the incremented count flows
  // back around.
  for (BasicBlock *Pred : predecessors(Header))
    Idx->addIncoming(Site.L->contains(Pred)
                         ? static_cast<Value *>(Inc)
                         : static_cast<Value *>(ConstantInt::get(I64, 0)),
                     Pred);
  auto *Off = BinaryOperator::CreateNUWMul(Idx, ConstantInt::get(I64, Padded),
                                           "", C->getIterator());
  Value *Slot = GetElementPtrInst::Create(Type::getInt8Ty(Ctx), Arr, {Off},
                                          "", C->getIterator());

  if (Site.KnownBound != 0 && Site.KnownBound <= Site.NSlots) {
    // Every execution is proven to have a slot; call `.noalloc` directly.
    rewriteToNoAlloc(C, NoAllocCallee, Slot);
    return;
  }

  // Guarded dispatch: pass a null slot past the last reserved one.
  auto *Cmp = new ICmpInst(C->getIterator(), ICmpInst::ICMP_ULT, Idx,
                           ConstantInt::get(I64, Site.NSlots));
  Value *SlotOrNull = SelectInst::Create(
      Cmp, Slot, ConstantPointerNull::get(PointerType::get(Ctx, 0)), "",
      C->getIterator());

  // The dispatch helper: (args..., slot) -> slot ? noalloc(args..., slot)
  //                                             : original(args...)
  Function *Original = C->getCalledFunction();
  Module *M = Caller->getParent();
  auto *HelperTy = NoAllocCallee->getFunctionType();
  Function *Helper =
      Function::Create(HelperTy, GlobalValue::InternalLinkage,
                       Original->getName() + ".bulk.dispatch", M);
  Argument *SlotArg = Helper->getArg(Helper->arg_size() - 1);
  SmallVector<Value *, 8> FwdArgs;
  for (unsigned ArgI = 0, E = Helper->arg_size() - 1; ArgI != E; ++ArgI)
    FwdArgs.push_back(Helper->getArg(ArgI));

  auto *EntryBB = BasicBlock::Create(Ctx, "entry", Helper);
  auto *ElideBB = BasicBlock::Create(Ctx, "elide", Helper);
  auto *HeapBB = BasicBlock::Create(Ctx, "heap", Helper);
  auto *IsNull =
      new ICmpInst(EntryBB, ICmpInst::ICMP_EQ, SlotArg,
                   ConstantPointerNull::get(PointerType::get(Ctx, 0)));
  CondBrInst::Create(IsNull, HeapBB, ElideBB, EntryBB);

  SmallVector<Value *, 8> ElideArgs(FwdArgs);
  ElideArgs.push_back(SlotArg);
  auto *ElideCall =
      CallInst::Create(NoAllocCallee->getFunctionType(), NoAllocCallee,
                       ElideArgs, "", ElideBB);
  ReturnInst::Create(Ctx, ElideCall, ElideBB);

  auto *HeapCall = CallInst::Create(Original->getFunctionType(), Original,
                                    FwdArgs, "", HeapBB);
  // The escape leg must stay an outlined call to the published symbol.
  HeapCall->addFnAttr(llvm::Attribute::NoInline);
  ReturnInst::Create(Ctx, HeapCall, HeapBB);

  // Rewrite the creation call to the helper and fold everything in place:
  // first the helper into the caller, then the `.noalloc` arm it carried.
  SmallVector<Value *, 8> NewArgs(C->args());
  NewArgs.push_back(SlotOrNull);
  CallBase *NewCB = nullptr;
  if (isa<CallInst>(C)) {
    NewCB = CallInst::Create(HelperTy, Helper, NewArgs, "", C->getIterator());
  } else {
    auto *II = cast<InvokeInst>(C);
    NewCB = InvokeInst::Create(HelperTy, Helper, II->getNormalDest(),
                               II->getUnwindDest(), NewArgs, {}, "",
                               C->getIterator());
  }
  NewCB->setCallingConv(C->getCallingConv());
  NewCB->setDebugLoc(C->getDebugLoc());
  C->replaceAllUsesWith(NewCB);
  C->eraseFromParent();

  InlineFunctionInfo IFI;
  if (!InlineFunction(*NewCB, IFI).isSuccess()) {
    // Leave the outlined helper behind; it is correct, merely not folded.
    return;
  }
  Helper->eraseFromParent();
  for (CallBase *Inlined : IFI.InlinedCallSites) {
    if (Inlined->getCalledFunction() == NoAllocCallee) {
      InlineFunctionInfo NestedIFI;
      InlineFunction(*Inlined, NestedIFI);
      break;
    }
  }
}

// Point the coroutine id of a freshly cloned coroutine at the clone itself.
static void retargetCoroId(Function *Clone, Function *PreviousSelf) {
  for (Instruction &I : instructions(*Clone))
    if (auto *II = dyn_cast<IntrinsicInst>(&I))
      if (II->getIntrinsicID() == Intrinsic::coro_id &&
          II->getArgOperand(2) == PreviousSelf)
        II->setArgOperand(2, Clone);
}

//===----------------------------------------------------------------------===//
// CoroRecursionStashPass
//===----------------------------------------------------------------------===//

PreservedAnalyses CoroRecursionStashPass::run(Module &M,
                                              ModuleAnalysisManager &MAM) {
  if (CoroRecursiveElideMaxGenerations == 0)
    return PreservedAnalyses::all();

  // Cheap gate: some direct coro_elide_safe call site to a presplit
  // coroutine, or some range-marked bulk await inside one, must exist
  // before it is worth building a call graph.
  bool AnyCandidateSite = false;
  for (Function &F : M) {
    if (F.isDeclaration())
      continue;
    for (Instruction &I : instructions(F)) {
      auto *CB = dyn_cast<CallBase>(&I);
      if (!CB)
        continue;
      if ((CB->hasFnAttr(llvm::Attribute::CoroElideSafe) &&
           CB->getCalledFunction() &&
           CB->getCalledFunction()->isPresplitCoroutine()) ||
          (F.isPresplitCoroutine() && isRangeMarkedSuspend(*CB))) {
        AnyCandidateSite = true;
        break;
      }
    }
    if (AnyCandidateSite)
      break;
  }
  if (!AnyCandidateSite)
    return PreservedAnalyses::all();

  FunctionAnalysisManager &FAM =
      MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();

  // Collect call graph cycles containing at least one presplit coroutine
  // definition, connected by a direct, elide-safe, loop-free cycle call
  // site or carrying a range-marked bulk await in a coroutine member. The
  // cycle may pass through non-coroutine "glue" definitions (iterator
  // adaptors, lambdas, awaitable machinery): those are not stashed, but
  // their cycle call sites are pinned noinline in place so the sites
  // survive, still outlined, once the glue is inlined into the templates.
  struct StashGroup {
    SmallVector<Function *, 2> Coros;
    SmallVector<Function *, 4> Glue;
  };
  CallGraph CG(M);
  SmallVector<StashGroup, 4> Groups;
  for (scc_iterator<CallGraph *> I = scc_begin(&CG); !I.isAtEnd(); ++I) {
    if (!I.hasCycle())
      continue;
    StashGroup Group;
    bool AllDefined = true;
    for (CallGraphNode *N : *I) {
      Function *F = N->getFunction();
      if (!F || F->isDeclaration()) {
        AllDefined = false;
        break;
      }
      if (F->isPresplitCoroutine())
        Group.Coros.push_back(F);
      else
        Group.Glue.push_back(F);
    }
    if (!AllDefined || Group.Coros.empty())
      continue;

    SmallPtrSet<Function *, 4> InSCC(Group.Coros.begin(), Group.Coros.end());
    bool HasSite = false;
    for (Function *F : Group.Coros) {
      LoopInfo &LI = FAM.getResult<LoopAnalysis>(*F);
      for (Instruction &I : instructions(*F)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB)
          continue;
        if ((CB->hasFnAttr(llvm::Attribute::CoroElideSafe) &&
             CB->getCalledFunction() &&
             InSCC.count(CB->getCalledFunction()) &&
             !LI.getLoopFor(CB->getParent())) ||
            isRangeMarkedSuspend(*CB)) {
          HasSite = true;
          break;
        }
      }
      if (HasSite)
        break;
    }
    if (HasSite)
      Groups.push_back(std::move(Group));
  }
  if (Groups.empty())
    return PreservedAnalyses::all();

  SmallVector<GlobalValue *, 4> KeepAlive;
  unsigned GroupId = 0;
  for (StashGroup &Group : Groups) {
    SmallPtrSet<Function *, 4> InSCC(Group.Coros.begin(), Group.Coros.end());
    for (Function *F : Group.Coros) {
      LoopInfo &LI = FAM.getResult<LoopAnalysis>(*F);
      ValueToValueMapTy VMap;
      Function *T = CloneFunction(F, VMap);
      T->setName(F->getName() + ".recursive.template");
      T->setLinkage(GlobalValue::InternalLinkage);
      T->addFnAttr(TemplateAttr, F->getName());
      T->addFnAttr(GroupAttr, std::to_string(GroupId));
      retargetCoroId(T, F);

      // In the template: a cycle call site inside a loop must never be
      // elided as a direct site (its block slot would be reused while a
      // previous iteration's coroutine may still be live), so strip its
      // marking; statically bounded loop sites are recovered as bulk range
      // sites with one slot per iteration instead. Mark every cycle call
      // site noinline so that nothing folds away these symbol references
      // before the generations are built from them.
      for (Instruction &I : instructions(*F)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (!CB || !CB->getCalledFunction() ||
            !InSCC.count(CB->getCalledFunction()))
          continue;
        auto *TCB = cast<CallBase>(VMap[CB]);
        if (LI.getLoopFor(CB->getParent()))
          TCB->removeFnAttr(llvm::Attribute::CoroElideSafe);
        TCB->addFnAttr(llvm::Attribute::NoInline);
      }
      KeepAlive.push_back(T);
      LLVM_DEBUG(dbgs() << "CoroRecursionStash: stashed template for '"
                        << F->getName() << "' (group " << GroupId << ")\n");
    }

    // Pin the glue's cycle call sites in place; inlined copies inherit the
    // attribute, preserving direct creation calls inside the templates.
    // The glue functions themselves must fold completely into the template
    // for the bulk range analysis to see the creation pattern. The originals
    // get them inlined during their own SCC's bottom-up visit while each
    // piece is still small; the templates are visited later, when the fully
    // expanded machinery can exceed the inliner's cost thresholds, so the
    // inlining must be made mandatory.
    for (Function *F : Group.Glue) {
      for (Instruction &I : instructions(*F)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (CB && CB->getCalledFunction() &&
            InSCC.count(CB->getCalledFunction()))
          CB->addFnAttr(llvm::Attribute::NoInline);
      }
      if (!F->hasFnAttribute(llvm::Attribute::NoInline) &&
          !F->hasFnAttribute(llvm::Attribute::OptimizeNone) &&
          !F->hasFnAttribute(llvm::Attribute::AlwaysInline))
        F->addFnAttr(llvm::Attribute::AlwaysInline);
    }
    ++GroupId;
  }
  appendToCompilerUsed(M, KeepAlive);
  return PreservedAnalyses::none();
}

//===----------------------------------------------------------------------===//
// CoroRecursiveElidePass
//===----------------------------------------------------------------------===//

namespace {
struct GenState {
  Function *Fn = nullptr;
  Function *NoAlloc = nullptr;
  uint64_t FrameSize = 0;
  Align FrameAlign;
};
} // namespace

static bool readGenState(Module &M, Function *Fn, GenState &Out) {
  Function *NA = M.getFunction((Fn->getName() + ".noalloc").str());
  if (!NA)
    return false;
  unsigned FrameArg = NA->arg_size() - 1;
  Out.Fn = Fn;
  Out.NoAlloc = NA;
  Out.FrameSize = NA->getParamDereferenceableBytes(FrameArg);
  Out.FrameAlign = NA->getParamAlign(FrameArg).valueOrOne();
  return Out.FrameSize != 0;
}

static bool
processGroup(Module &M, ArrayRef<std::pair<Function *, Function *>> Group,
             FunctionAnalysisManager &FAM) {
  unsigned N = Group.size();
  SmallDenseMap<Function *, unsigned, 4> OrigIndex;
  for (unsigned I = 0; I != N; ++I)
    OrigIndex[Group[I].second] = I;

  // Generation 0 is the ordinary split of each original.
  SmallVector<GenState, 2> Cur(N);
  for (unsigned I = 0; I != N; ++I)
    if (!readGenState(M, Group[I].second, Cur[I]))
      return false;

  SmallVector<bool, 2> Saturated(N, false);
  bool AnyGenerationBuilt = false;

  for (unsigned Gen = 1; Gen <= CoroRecursiveElideMaxGenerations; ++Gen) {
    // Build this generation's candidate clone for each unsaturated member
    // and elide every cycle call site whose callee generation fits.
    SmallVector<Function *, 2> Next(N, nullptr);
    SmallVector<bool, 2> Elided(N, false);
    for (unsigned I = 0; I != N; ++I) {
      if (Saturated[I])
        continue;
      Function *T = Group[I].first;
      ValueToValueMapTy VMap;
      Function *G = CloneFunction(T, VMap);
      G->setName(Group[I].second->getName() + ".block." + Twine(Gen));
      G->setLinkage(GlobalValue::InternalLinkage);
      G->removeFnAttr(TemplateAttr);
      G->removeFnAttr(GroupAttr);
      retargetCoroId(G, T);
      Next[I] = G;

      // Analyses on the fresh clone; sites are collected before any elision
      // mutates it (the elision inlining invalidates the analyses, but not
      // the loop header/latch blocks the bulk transform revisits).
      auto &LI = FAM.getResult<LoopAnalysis>(*G);
      auto &SE = FAM.getResult<ScalarEvolutionAnalysis>(*G);
      auto &DT = FAM.getResult<DominatorTreeAnalysis>(*G);

      SmallVector<CallBase *, 4> Sites;
      for (Instruction &Inst : instructions(*G)) {
        auto *CB = dyn_cast<CallBase>(&Inst);
        // A direct site inside a loop must not be elided: its single slot
        // would be reused while a previous iteration's coroutine may still
        // be live. (Stash-time stripping already handles the sites cloned
        // from the original; this also covers sites carried in by glue
        // inlined into the template afterwards.)
        if (CB && CB->hasFnAttr(llvm::Attribute::CoroElideSafe) &&
            CB->getCalledFunction() &&
            OrigIndex.contains(CB->getCalledFunction()) &&
            !LI.getLoopFor(CB->getParent()))
          Sites.push_back(CB);
      }
      SmallVector<BulkRangeSite, 4> BulkSites;
      findBulkRangeSites(
          *G, LI, SE, DT,
          [&](Function *Callee) { return OrigIndex.contains(Callee); },
          BulkSites);

      // A generation that elides only part of the sites that structurally
      // fit (unit cap passed, accumulated cap exceeded) is abandoned: the
      // mix of nested children and full-block escapes measures worse than
      // stopping at the previous, fully nested generation.
      bool Partial = false;
      for (CallBase *CB : Sites) {
        const GenState &Callee = Cur[OrigIndex[CB->getCalledFunction()]];
        if (Callee.FrameSize > CoroElideMaxFrameSize)
          continue;
        if (accumulatedElidedFrameSize(G) + Callee.FrameSize >
            CoroElideMaxAccumulatedFrameSize) {
          Partial = true;
          continue;
        }
        elideSite(CB, G, Callee.NoAlloc, Callee.FrameSize, Callee.FrameAlign);
        Elided[I] = true;
      }
      for (BulkRangeSite &BS : BulkSites) {
        const GenState &Callee =
            Cur[OrigIndex[BS.CreationCall->getCalledFunction()]];
        if (Callee.FrameSize > CoroElideMaxFrameSize)
          continue;
        uint64_t Padded = alignTo(Callee.FrameSize, Callee.FrameAlign);
        // Slot target: the known execution bound, capped by the default
        // (executions past the reserved slots take the runtime fallback,
        // so the cap trades block size against fallback allocations; on
        // jagged trees most activations use far fewer slots than the
        // worst-case bound). A site whose target does not fit the
        // remaining accumulated budget makes the generation partial.
        uint64_t Target = !BS.L ? 1
                                : std::min(BS.KnownBound ? BS.KnownBound
                                                         : UINT64_MAX,
                                           CoroBulkDefaultSlots.getValue());
        uint64_t Accum = accumulatedElidedFrameSize(G);
        // Division form; immune to overflow on absurd trip bounds.
        if (Accum >= CoroElideMaxAccumulatedFrameSize ||
            Target > (CoroElideMaxAccumulatedFrameSize - Accum) / Padded) {
          Partial = true;
          continue;
        }
        BS.NSlots = Target;
        elideBulkSite(BS, G, Callee.NoAlloc, Callee.FrameSize,
                      Callee.FrameAlign);
        Elided[I] = true;
      }

      if (Partial) {
        LLVM_DEBUG(dbgs() << "CoroRecursiveElide: abandoning partial '"
                          << G->getName() << "'\n");
        G->eraseFromParent();
        Next[I] = nullptr;
        Elided[I] = false;
        Saturated[I] = true;
      }
    }

    // Split the clones that elided something and check for progress; a
    // member whose frame stops growing is saturated. Clones that made no
    // progress are simply abandoned (internal and uncalled, so they and
    // their split artifacts are cleaned up by GlobalDCE).
    bool Progress = false;
    for (unsigned I = 0; I != N; ++I) {
      if (!Next[I])
        continue;
      if (!Elided[I]) {
        Next[I]->eraseFromParent();
        Saturated[I] = true;
        continue;
      }
      auto &TTI = FAM.getResult<TargetIRAnalysis>(*Next[I]);
      SmallVector<Function *, 4> Clones;
      coro::splitStandaloneCoroutine(*Next[I], TTI, Clones,
                                     /*OptimizeFrame=*/true,
                                     /*ForceNoAllocVariant=*/true);
      GenState NewState;
      if (!readGenState(M, Next[I], NewState) ||
          NewState.FrameSize <= Cur[I].FrameSize) {
        Saturated[I] = true;
        continue;
      }
      LLVM_DEBUG(dbgs() << "CoroRecursiveElide: '" << Next[I]->getName()
                        << "' frame " << NewState.FrameSize << " bytes\n");
      Cur[I] = NewState;
      Progress = true;
      AnyGenerationBuilt = true;
    }
    if (!Progress)
      break;
  }

  if (!AnyGenerationBuilt)
    return false;

  // Republish: the top generation takes over the original's identity. Every
  // caller of the original -- external ones and the escape sites inside the
  // blocks -- now enters a full-sized block.
  for (unsigned I = 0; I != N; ++I) {
    Function *O = Group[I].second;
    Function *Top = Cur[I].Fn;
    if (Top == O)
      continue;
    std::string Name = O->getName().str();
    O->setName(Name + ".block.0");
    Top->setLinkage(O->getLinkage());
    Top->setVisibility(O->getVisibility());
    Top->setDSOLocal(O->isDSOLocal());
    if (Comdat *C = O->getComdat()) {
      Top->setComdat(C);
      O->setComdat(nullptr);
    }
    O->replaceAllUsesWith(Top);
    O->setLinkage(GlobalValue::InternalLinkage);
    Top->setName(Name);
    LLVM_DEBUG(dbgs() << "CoroRecursiveElide: republished '" << Name
                      << "' as a " << Cur[I].FrameSize << "-byte block\n");
  }

  // The noinline markers added at stash time have served their purpose;
  // remaining escape call sites may be inlined normally from here on.
  for (unsigned I = 0; I != N; ++I) {
    for (Function *Fn : {Cur[I].Fn, Group[I].second}) {
      for (Instruction &Inst : instructions(*Fn))
        if (auto *CB = dyn_cast<CallBase>(&Inst))
          if (CB->getCalledFunction() &&
              OrigIndex.contains(CB->getCalledFunction()))
            CB->removeFnAttr(llvm::Attribute::NoInline);
    }
  }
  return true;
}

PreservedAnalyses CoroRecursiveElidePass::run(Module &M,
                                              ModuleAnalysisManager &MAM) {
  // Collect stashed templates, grouped by recursion cycle.
  SmallVector<Function *, 4> Templates;
  DenseMap<unsigned, SmallVector<std::pair<Function *, Function *>, 2>> Groups;
  for (Function &F : M) {
    if (!F.hasFnAttribute(TemplateAttr))
      continue;
    Templates.push_back(&F);
    StringRef OrigName = F.getFnAttribute(TemplateAttr).getValueAsString();
    unsigned GroupId = 0;
    if (F.getFnAttribute(GroupAttr)
            .getValueAsString()
            .getAsInteger(10, GroupId))
      continue;
    Function *Orig = M.getFunction(OrigName);
    if (Orig && !Orig->isDeclaration())
      Groups[GroupId].push_back({&F, Orig});
  }
  if (Templates.empty())
    return PreservedAnalyses::all();

  FunctionAnalysisManager &FAM =
      MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();

  bool Changed = false;
  if (CoroRecursiveElideMaxGenerations != 0)
    for (auto &[Id, Group] : Groups)
      Changed |= processGroup(M, Group, FAM);

  // The templates are cloning material only; remove them.
  SmallPtrSet<GlobalValue *, 4> TemplateSet(Templates.begin(),
                                            Templates.end());
  removeFromUsedLists(M, [&](Constant *C) {
    auto *GV = dyn_cast<GlobalValue>(C->stripPointerCasts());
    return GV && TemplateSet.count(GV);
  });
  for (Function *T : Templates)
    T->eraseFromParent();

  // The split artifacts created here never revisit the inliner, so the
  // always-inline await-suspend wrappers (inlined into ordinary resume
  // functions during the post-split CGSCC revisit) would otherwise remain
  // outlined in the generations' resume functions.
  if (Changed)
    AlwaysInlinerPass().run(M, MAM);

  return Changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
}
