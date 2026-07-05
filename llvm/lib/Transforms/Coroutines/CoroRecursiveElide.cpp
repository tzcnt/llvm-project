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
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/Coroutines/CoroInstr.h"
#include "llvm/Transforms/IPO/AlwaysInliner.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"
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

static cl::opt<bool> CoroRecursiveElideInlineRamp(
    "coro-recursive-elide-inline-ramp", cl::init(true), cl::Hidden,
    cl::desc("After republishing, inline the block ramp into the cycle "
             "re-entry call sites in the originals' split clones. The "
             "stash-time noinline pins only exist to keep those sites "
             "outlined symbol references until the republish has "
             "retargeted them; past that point the ramp is an ordinary "
             "small function and staying outlined is pure call overhead."));

static cl::opt<uint64_t> CoroBulkDefaultSlots(
    "coro-elide-bulk-default-slots", cl::init(8), cl::Hidden,
    cl::desc("Maximum frame slots reserved for one bulk range creation "
             "site; executions beyond the reserved slots allocate "
             "normally. Bounds the speculative block size on sites with "
             "large or unknown execution counts."));

static cl::opt<uint64_t> CoroBulkMaxArenaSlots(
    "coro-elide-bulk-max-arena-slots", cl::init(1024), cl::Hidden,
    cl::desc("Maximum frame slots one per-activation arena may hold for a "
             "self-recursive bulk range site; executions beyond it "
             "allocate normally."));

static cl::opt<bool> CoroBulkArenaLineAlign(
    "coro-elide-bulk-arena-line-align", cl::init(false), cl::Hidden,
    cl::desc("Pack per-activation arena slots at whole cache lines "
             "(aligned_alloc + line-rounded slot pitch) so concurrently "
             "running sibling frames never share a line, at the cost of "
             "padding bytes and the allocator's aligned path."));

static cl::opt<uint64_t> CoroBulkArenaMaxFrameSize(
    "coro-elide-bulk-arena-max-frame-size", cl::init(256), cl::Hidden,
    cl::desc("Only arena-elide self-recursive bulk range sites whose "
             "child frame is at most this size. Larger frames recycle "
             "better individually through a caching allocator than "
             "batched into multi-KB arenas (measured: 176-byte frames "
             "win, 360+ lose), so oversized sites are left unelided."));

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
  // Self-recursive loop site: child frames come from a lazily allocated,
  // runtime-sized heap arena instead of in-frame slots, and the children
  // call this very generation's `.noalloc` variant (see elideArenaSite).
  bool SelfArena = false;
  // Self-recursive loop site that must not be elided at all: the arena
  // trade was rejected (frame too large), and in-frame slots for such
  // sites charge every activation for the worst case.
  bool Skipped = false;
  // The site's execution count per loop entry as an i64 materialized in the
  // loop preheader, when SCEV can both compute and safely expand it there;
  // null otherwise. Used to size the arena exactly.
  Value *TripCount = nullptr;
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

// Rewrite one creation call to a small dispatch helper taking the selected
// slot: a null slot keeps calling the original, runtime-allocating symbol;
// a non-null one calls the `.noalloc` variant with the slot as its frame.
// The helper is inlined immediately (building the dispatch as a function
// lets InlineFunction do the control-flow surgery, which keeps invoke
// sites and their landing pads intact), and its `.noalloc` arm after it,
// unless that arm is a self-referential declaration whose body only exists
// once this very caller is split -- that call is a plain recursive call
// and stays outlined.
static void rewriteToGuardedDispatch(CallBase *C, Value *SlotOrNull,
                                     Function *NoAllocCallee) {
  Function *Original = C->getCalledFunction();
  LLVMContext &Ctx = C->getContext();
  Module *M = C->getModule();
  auto *HelperTy = NoAllocCallee->getFunctionType();
  Function *Helper =
      Function::Create(HelperTy, GlobalValue::InternalLinkage,
                       Original->getName() + ".bulk.dispatch", M);
  Helper->setCallingConv(C->getCallingConv());
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
  ElideCall->setCallingConv(NoAllocCallee->getCallingConv());
  ReturnInst::Create(Ctx, ElideCall, ElideBB);

  auto *HeapCall = CallInst::Create(Original->getFunctionType(), Original,
                                    FwdArgs, "", HeapBB);
  HeapCall->setCallingConv(C->getCallingConv());
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
  NewCB->setCallingConv(Helper->getCallingConv());
  NewCB->setDebugLoc(C->getDebugLoc());
  C->replaceAllUsesWith(NewCB);
  C->eraseFromParent();

  InlineFunctionInfo IFI;
  if (!InlineFunction(*NewCB, IFI).isSuccess()) {
    // Leave the outlined helper behind; it is correct, merely not folded.
    return;
  }
  Helper->eraseFromParent();
  if (NoAllocCallee->isDeclaration())
    return;
  for (CallBase *Inlined : IFI.InlinedCallSites) {
    if (Inlined->getCalledFunction() == NoAllocCallee) {
      InlineFunctionInfo NestedIFI;
      InlineFunction(*Inlined, NestedIFI);
      break;
    }
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
  rewriteToGuardedDispatch(C, SlotOrNull, NoAllocCallee);
}

//===----------------------------------------------------------------------===//
// Self-recursive bulk range sites: per-activation frame arenas
//
// In-frame slot arrays charge every activation of the block for the site's
// worst-case fan-out. On jagged trees most activations are leaves that use
// no slots at all, and nesting a second generation multiplies the dead
// space again: measured on UTS (geometric tree, ~80% leaves), the blocks
// grew to 58x the plain frame while the allocation count barely halved,
// because slot children run generation-0 code whose own children re-enter
// the published block symbol (only alternating levels elide).
//
// When the creation call targets the recursion member itself, both
// problems disappear at once by moving the slots out of the frame into a
// per-activation heap arena, and pointing the children at this very
// generation's `.noalloc` variant:
//
//  - The frame carries only an arena pointer (plus a capacity when the
//    size is dynamic); activations that never create a child never
//    allocate an arena. The arena is sized exactly when SCEV can
//    materialize the creation loop's trip count in the preheader, and is
//    freed at frame teardown -- re-entries of the loop (batched joins)
//    reuse it.
//
//  - Because the children run the same generation, every level of the
//    recursion elides: each activation lives in its parent's arena and
//    allocates exactly one arena for all of its own children. One
//    generation therefore covers the whole recursion, replacing the
//    N-frames-per-block geometric growth (and the generation ladder) with
//    one exact-sized allocation per internal node.
//
// The slot size is the generation's own final frame size, which does not
// exist while the generation is still presplit; llvm.coro.size/align stand
// in for it and are folded by CoroSplit when the generation is split. For
// the same reason the children call a placeholder declaration
// `<gen>.noalloc.self` that is RAUW'd to the real `.noalloc` right after
// the split.
//===----------------------------------------------------------------------===//

// Materialize the number of executions of a bulk site's creation call per
// loop entry as an i64 in the loop preheader, if SCEV can compute and
// safely expand it there. The value may overestimate by one on loops that
// exit before the creation block in their final iteration; the in-bounds
// guard makes any estimate safe, so precision only affects arena sizing.
static Value *materializeArenaTripCount(Loop *L, ScalarEvolution &SE) {
  BasicBlock *Preheader = L->getLoopPreheader();
  if (!Preheader) {
    if (CoroBulkDebug)
      errs() << "[bulk]     count: no preheader\n";
    return nullptr;
  }
  const SCEV *BTC = SE.getBackedgeTakenCount(L);
  if (isa<SCEVCouldNotCompute>(BTC)) {
    // Exceptional exits (invoke unwind edges) make the exact count
    // formally uncomputable even when every normal exit is counted; the
    // symbolic maximum is still a tight bound on the creations performed,
    // since an exception only cuts the loop short. An uncounted *normal*
    // exit (e.g. a filtering iterator's != end) instead means the real
    // count typically runs far below any structural bound: give up, so
    // the site takes the clamped default reservation.
    SmallVector<BasicBlock *, 4> Exiting;
    L->getExitingBlocks(Exiting);
    for (BasicBlock *EB : Exiting) {
      if (!isa<SCEVCouldNotCompute>(SE.getExitCount(L, EB)))
        continue;
      auto *II = dyn_cast<InvokeInst>(EB->getTerminator());
      bool Exceptional = II && !L->contains(II->getUnwindDest()) &&
                         L->contains(II->getNormalDest());
      if (!Exceptional) {
        if (CoroBulkDebug)
          errs() << "[bulk]     count: normal exit without a count\n";
        return nullptr;
      }
    }
    BTC = SE.getSymbolicMaxBackedgeTakenCount(L);
    if (isa<SCEVCouldNotCompute>(BTC)) {
      if (CoroBulkDebug)
        errs() << "[bulk]     count: backedge count not computable\n";
      return nullptr;
    }
  }
  Type *I64 = Type::getInt64Ty(L->getHeader()->getContext());
  if (SE.getTypeSizeInBits(BTC->getType()) > 64)
    return nullptr;
  const SCEV *Count =
      SE.getAddExpr(SE.getNoopOrZeroExtend(BTC, I64), SE.getOne(I64));
  SCEVExpander Expander(SE, "coro.arena");
  if (!Expander.isSafeToExpandAt(Count, Preheader->getTerminator())) {
    if (CoroBulkDebug)
      errs() << "[bulk]     count: not expandable at preheader: " << *Count
             << "\n";
    return nullptr;
  }
  return Expander.expandCodeFor(Count, I64, Preheader->getTerminator());
}

// The placeholder declaration for a generation's own `.noalloc` variant,
// which cannot exist before the generation is split. Signature and calling
// convention mirror what CoroSplit's createNoAllocVariant will build.
static Function *getOrCreateSelfNoAllocDecl(Function *G) {
  Module *M = G->getParent();
  std::string Name = (G->getName() + ".noalloc.self").str();
  if (Function *Existing = M->getFunction(Name))
    return Existing;
  SmallVector<Type *, 8> Params(G->getFunctionType()->params());
  Params.push_back(PointerType::getUnqual(G->getContext()));
  auto *FnTy = FunctionType::get(G->getReturnType(), Params,
                                 G->getFunctionType()->isVarArg());
  Function *Decl = Function::Create(FnTy, GlobalValue::ExternalLinkage,
                                    G->getAddressSpace(), Name, M);
  Decl->setCallingConv(G->getCallingConv());
  return Decl;
}

// Elide one self-recursive bulk range site with a per-activation arena
// (see the file section comment above). Returns false, leaving the site
// untouched, if the caller has no llvm.coro.free to anchor the arena's
// teardown on.
static bool elideArenaSite(const BulkRangeSite &Site, Function *Caller,
                           Function *SelfNoAlloc) {
  SmallVector<Instruction *, 2> CoroFrees;
  for (Instruction &I : instructions(*Caller))
    if (isa<CoroFreeInst>(&I))
      CoroFrees.push_back(&I);
  if (CoroFrees.empty())
    return false;

  LLVMContext &Ctx = Caller->getContext();
  Module *M = Caller->getParent();
  const DataLayout &DL = Caller->getDataLayout();
  auto *I64 = Type::getInt64Ty(Ctx);
  auto *PtrTy = PointerType::getUnqual(Ctx);
  auto *NullPtr = ConstantPointerNull::get(PtrTy);
  FunctionCallee AlignedAlloc =
      M->getOrInsertFunction("aligned_alloc", PtrTy, I64, I64);
  FunctionCallee Malloc = M->getOrInsertFunction("malloc", PtrTy, I64);
  FunctionCallee Free =
      M->getOrInsertFunction("free", Type::getVoidTy(Ctx), PtrTy);
  CallBase *C = Site.CreationCall;
  BasicBlock *Header = Site.L->getHeader();

  // Hidden per-activation state; lives across suspends and spills into the
  // frame. The capacity is only tracked for dynamically sized arenas,
  // whose needed size can differ between entries of the loop.
  Instruction *InitPt = getFirstNonAllocaInEntry(Caller);
  auto *ArenaA = new AllocaInst(PtrTy, DL.getAllocaAddrSpace(), "coro.arena",
                                InitPt->getIterator());
  AllocaInst *CapA = nullptr;
  if (Site.TripCount)
    CapA = new AllocaInst(I64, DL.getAllocaAddrSpace(), "coro.arena.cap",
                          InitPt->getIterator());
  IRBuilder<> B(InitPt);
  B.CreateStore(NullPtr, ArenaA);
  if (CapA)
    B.CreateStore(ConstantInt::get(I64, 0), CapA);

  // The padded slot size, this generation's own frame size rounded up to
  // its alignment; the intrinsics fold to constants when it is split. For
  // exactly sized arenas the computation must sit in the preheader (the
  // needed size takes part in the per-entry shrink check; the trip count
  // was expanded there, or folded to a constant); otherwise it sits with
  // the creation call.
  if (Site.TripCount)
    B.SetInsertPoint(Site.L->getLoopPreheader()->getTerminator());
  else
    B.SetInsertPoint(C);
  Value *FrameSize = B.CreateIntrinsic(I64, Intrinsic::coro_size, {});
  Value *FrameAlign = B.CreateIntrinsic(I64, Intrinsic::coro_align, {});
  // Optionally pack the slots at whole cache lines (the runtime's own
  // frame allocations are line-rounded) so concurrently running sibling
  // frames never share one; costs padding bytes and the allocator's
  // aligned path.
  Value *PadAlign =
      CoroBulkArenaLineAlign
          ? B.CreateBinaryIntrinsic(Intrinsic::umax, FrameAlign,
                                    ConstantInt::get(I64, 64))
          : FrameAlign;
  Value *AlignM1 = B.CreateSub(PadAlign, ConstantInt::get(I64, 1));
  Value *Padded = B.CreateAnd(B.CreateAdd(FrameSize, AlignM1),
                              B.CreateNot(AlignM1), "coro.arena.slotsize");
  // Exactly counted arenas are still rounded up to the default slot
  // target: the tail slots are never touched (children allocate lazily
  // into their slot), but the constant size below the floor keeps the
  // arena in a single hot allocator size class, which recycles far better
  // than one class per fan-out.
  Value *NSlots = ConstantInt::get(I64, Site.NSlots);
  if (Site.TripCount) {
    NSlots = B.CreateBinaryIntrinsic(
        Intrinsic::umin, Site.TripCount,
        ConstantInt::get(I64, CoroBulkMaxArenaSlots.getValue()));
    NSlots = B.CreateBinaryIntrinsic(
        Intrinsic::umax, NSlots,
        ConstantInt::get(I64, CoroBulkDefaultSlots.getValue()));
  }
  Value *Need = B.CreateMul(NSlots, Padded, "coro.arena.need");

  // Exactly counted arenas are ensured eagerly in the preheader -- a
  // nonzero count proves a creation follows, so this allocates no earlier
  // than the lazy form would -- which keeps the in-loop path branchless.
  // Re-entries with a larger need than the retained capacity release the
  // old arena first. The ensured arena and its usability are then loop
  // invariants.
  Value *ArenaLive = nullptr;
  Value *ArenaUsable = nullptr;
  if (Site.TripCount) {
    Instruction *PHTerm = &*B.GetInsertPoint();
    Value *Arena0 = B.CreateLoad(PtrTy, ArenaA);
    Value *MustAlloc = B.CreateAnd(
        B.CreateICmpNE(Site.TripCount, ConstantInt::get(I64, 0)),
        B.CreateOr(B.CreateICmpEQ(Arena0, NullPtr),
                   B.CreateICmpULT(B.CreateLoad(I64, CapA), Need)));
    Instruction *ThenTerm = SplitBlockAndInsertIfThen(
        MustAlloc, B.GetInsertPoint(), /*Unreachable=*/false);
    B.SetInsertPoint(ThenTerm);
    Instruction *FreeTerm = SplitBlockAndInsertIfThen(
        B.CreateICmpNE(Arena0, NullPtr), B.GetInsertPoint(),
        /*Unreachable=*/false);
    IRBuilder<> FB(FreeTerm);
    FB.CreateCall(Free, Arena0);
    B.SetInsertPoint(ThenTerm);
    Value *Fresh = CoroBulkArenaLineAlign
                       ? B.CreateCall(AlignedAlloc, {PadAlign, Need})
                       : B.CreateCall(Malloc, Need);
    B.CreateStore(Fresh, ArenaA);
    B.CreateStore(Need, CapA);
    // Back on the main path (PHTerm followed the splits into the tail
    // block), reload the ensured arena once per entry.
    B.SetInsertPoint(PHTerm);
    ArenaLive = B.CreateLoad(PtrTy, ArenaA, "coro.arena.live");
    ArenaUsable = B.CreateICmpNE(ArenaLive, NullPtr);
  }

  // The per-entry execution counter, as for in-frame slots: entering the
  // loop restarts it, each started execution increments it before the
  // call.
  auto *Idx = PHINode::Create(I64, pred_size(Header), "coro.arena.idx",
                              Header->begin());
  auto *Inc = BinaryOperator::CreateNUWAdd(
      Idx, ConstantInt::get(I64, 1), "", C->getIterator());
  for (BasicBlock *Pred : predecessors(Header))
    Idx->addIncoming(Site.L->contains(Pred)
                         ? static_cast<Value *>(Inc)
                         : static_cast<Value *>(ConstantInt::get(I64, 0)),
                     Pred);

  // In front of the creation call: executions within the slot target take
  // their slot; the rest -- beyond the target, or with the allocation
  // failed -- pass a null slot and fall back to the published symbol in
  // the dispatch below.
  Value *SlotOrNull;
  if (Site.TripCount) {
    // The arena was ensured in the preheader: the in-loop path is a
    // branchless select on loop-invariant operands.
    B.SetInsertPoint(C);
    Value *RawSlot = B.CreateGEP(Type::getInt8Ty(Ctx), ArenaLive,
                                 B.CreateNUWMul(Idx, Padded));
    Value *Ok = B.CreateAnd(B.CreateICmpULT(Idx, NSlots), ArenaUsable);
    SlotOrNull = B.CreateSelect(Ok, RawSlot, NullPtr, "coro.arena.slotsel");
  } else {
    // No usable count: the arena is allocated lazily at the first
    // creation, so activations without children never pay.
    BasicBlock *BB = C->getParent();
    auto *InBounds =
        new ICmpInst(C->getIterator(), ICmpInst::ICMP_ULT, Idx, NSlots);
    BasicBlock *ContBB = SplitBlock(BB, C->getIterator());
    ContBB->setName(BB->getName() + ".arena.cont");
    auto *EnsureBB = BasicBlock::Create(
        Ctx, BB->getName() + ".arena.ensure", Caller, ContBB);
    auto *AllocBB = BasicBlock::Create(Ctx, BB->getName() + ".arena.alloc",
                                       Caller, ContBB);
    auto *SlotBB = BasicBlock::Create(Ctx, BB->getName() + ".arena.slot",
                                      Caller, ContBB);
    BB->getTerminator()->eraseFromParent();
    CondBrInst::Create(InBounds, EnsureBB, ContBB, BB);

    B.SetInsertPoint(EnsureBB);
    Value *Arena0 = B.CreateLoad(PtrTy, ArenaA);
    B.CreateCondBr(B.CreateICmpEQ(Arena0, NullPtr), AllocBB, SlotBB);

    B.SetInsertPoint(AllocBB);
    Value *Arena1 = CoroBulkArenaLineAlign
                        ? B.CreateCall(AlignedAlloc, {PadAlign, Need})
                        : B.CreateCall(Malloc, Need);
    B.CreateStore(Arena1, ArenaA);
    B.CreateBr(SlotBB);

    B.SetInsertPoint(SlotBB);
    auto *ArenaPhi = B.CreatePHI(PtrTy, 2);
    ArenaPhi->addIncoming(Arena0, EnsureBB);
    ArenaPhi->addIncoming(Arena1, AllocBB);
    Value *RawSlot = B.CreateGEP(Type::getInt8Ty(Ctx), ArenaPhi,
                                 B.CreateNUWMul(Idx, Padded));
    Value *Slot = B.CreateSelect(B.CreateICmpNE(ArenaPhi, NullPtr), RawSlot,
                                 NullPtr);
    B.CreateBr(ContBB);

    B.SetInsertPoint(ContBB, ContBB->begin());
    auto *SlotPhi = B.CreatePHI(PtrTy, 2, "coro.arena.slotsel");
    SlotPhi->addIncoming(NullPtr, BB);
    SlotPhi->addIncoming(Slot, SlotBB);
    SlotOrNull = SlotPhi;
  }

  rewriteToGuardedDispatch(C, SlotOrNull, SelfNoAlloc);

  // Release the arena wherever this activation's frame dies: children have
  // completed before the joining await resumes (the range attribute's
  // contract), so teardown strictly follows the last slot's use. Most
  // activations are leaves that never allocated one, so the free hides
  // behind a null check.
  for (Instruction *CF : CoroFrees) {
    B.SetInsertPoint(CF);
    Value *A = B.CreateLoad(PtrTy, ArenaA);
    Instruction *ThenTerm = SplitBlockAndInsertIfThen(
        B.CreateICmpNE(A, NullPtr), B.GetInsertPoint(), /*Unreachable=*/false);
    B.SetInsertPoint(ThenTerm);
    B.CreateCall(Free, A);
  }
  return true;
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
    SmallVector<bool, 2> ArenaSaturated(N, false);
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

      // Loop sites whose creation call targets this member itself take the
      // per-activation arena (see elideArenaSite): frames stay small, the
      // arena is lazily allocated and exactly sized where possible, and one
      // generation covers every level of the recursion. Trip counts must be
      // materialized before any elision mutates G (SCEV validity).
      for (BulkRangeSite &BS : BulkSites) {
        if (!BS.L || BS.CreationCall->getCalledFunction() != Group[I].second)
          continue;
        const GenState &Callee =
            Cur[OrigIndex[BS.CreationCall->getCalledFunction()]];
        // The final generation frame is generation 0's plus a few pointer
        // fields, so gate the arena trade and the malloc'd arena's
        // alignment guarantee on generation 0 as a proxy. A site over the
        // size threshold is skipped outright: in-frame slots would charge
        // every activation for the worst case (the original uts
        // regression), and large frames recycle better individually.
        if (Callee.FrameSize > CoroBulkArenaMaxFrameSize ||
            Callee.FrameAlign.value() > 16) {
          BS.Skipped = true;
          if (CoroBulkDebug)
            errs() << "[bulk]   skip self loop site (frame "
                   << Callee.FrameSize << " over arena threshold)\n";
          continue;
        }
        BS.SelfArena = true;
        // Exact sizing anchors the count (and the arena's shrink check) in
        // the preheader; give the loop one if it lacks it.
        if (!BS.L->getLoopPreheader())
          InsertPreheaderForLoop(BS.L, &DT, &LI, /*MSSAU=*/nullptr,
                                 /*PreserveLCSSA=*/false);
        BS.TripCount = materializeArenaTripCount(BS.L, SE);
        // Without an exact count, a known bound sizes the arena only up to
        // the default slot target: filtered creation loops typically run
        // far below their structural bound, and every activation would pay
        // the full reservation.
        if (!BS.TripCount)
          BS.NSlots = std::min(BS.KnownBound ? BS.KnownBound : UINT64_MAX,
                               CoroBulkDefaultSlots.getValue());
        if (CoroBulkDebug) {
          errs() << "[bulk]   arena site in "
                 << BS.CreationCall->getParent()->getName() << " count=";
          if (BS.TripCount)
            errs() << "dynamic";
          else
            errs() << BS.NSlots;
          errs() << "\n";
        }
      }

      // A generation that elides only part of the sites that structurally
      // fit (unit cap passed, accumulated cap exceeded) is abandoned: the
      // mix of nested children and full-block escapes measures worse than
      // stopping at the previous, fully nested generation.
      bool Partial = false;
      bool NonArenaElision = false;
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
        NonArenaElision = true;
      }
      for (BulkRangeSite &BS : BulkSites) {
        if (BS.Skipped)
          continue;
        if (BS.SelfArena) {
          if (elideArenaSite(BS, G, getOrCreateSelfNoAllocDecl(G))) {
            Elided[I] = true;
            continue;
          }
          // No teardown anchor; the in-frame worst-case reservation is
          // not an acceptable substitute -- leave the site unelided.
          continue;
        }
        const GenState &Callee =
            Cur[OrigIndex[BS.CreationCall->getCalledFunction()]];
        if (Callee.FrameSize > CoroElideMaxFrameSize)
          continue;
        uint64_t Padded = alignTo(Callee.FrameSize, Callee.FrameAlign);
        uint64_t Accum = accumulatedElidedFrameSize(G);
        // Division form; immune to overflow on absurd trip bounds.
        uint64_t BudgetSlots =
            Accum >= CoroElideMaxAccumulatedFrameSize
                ? 0
                : (CoroElideMaxAccumulatedFrameSize - Accum) / Padded;
        // Slot target: a site with a known execution bound that fits the
        // remaining accumulated budget is sized exactly to it and needs no
        // runtime guard. Sites with unknown (or over-budget) bounds get
        // the guarded default: executions past the reserved slots allocate
        // through the published symbol instead. A site that cannot even
        // fit that makes the generation partial.
        uint64_t Target;
        if (!BS.L)
          Target = 1;
        else if (BS.KnownBound && BS.KnownBound <= BudgetSlots)
          Target = BS.KnownBound;
        else
          Target = CoroBulkDefaultSlots;
        if (Target > BudgetSlots) {
          Partial = true;
          continue;
        }
        BS.NSlots = Target;
        elideBulkSite(BS, G, Callee.NoAlloc, Callee.FrameSize,
                      Callee.FrameAlign);
        Elided[I] = true;
        NonArenaElision = true;
      }
      // An arena needs no deeper generations: its children already run this
      // very generation. Members whose only elisions are arenas are done
      // after this one.
      if (Elided[I] && !NonArenaElision)
        ArenaSaturated[I] = true;

      if (Partial) {
        LLVM_DEBUG(dbgs() << "CoroRecursiveElide: abandoning partial '"
                          << G->getName() << "'\n");
        std::string PreDeclName = (G->getName() + ".noalloc.self").str();
        G->eraseFromParent();
        if (Function *PreDecl = M.getFunction(PreDeclName))
          if (PreDecl->use_empty())
            PreDecl->eraseFromParent();
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
        std::string PreDeclName =
            (Next[I]->getName() + ".noalloc.self").str();
        Next[I]->eraseFromParent();
        if (Function *PreDecl = M.getFunction(PreDeclName))
          if (PreDecl->use_empty())
            PreDecl->eraseFromParent();
        Saturated[I] = true;
        continue;
      }
      auto &TTI = FAM.getResult<TargetIRAnalysis>(*Next[I]);
      SmallVector<Function *, 4> Clones;
      coro::splitStandaloneCoroutine(*Next[I], TTI, Clones,
                                     /*OptimizeFrame=*/true,
                                     /*ForceNoAllocVariant=*/true);
      // Bind self-referential arena children to the freshly split
      // `.noalloc`.
      if (Function *PreDecl =
              M.getFunction((Next[I]->getName() + ".noalloc.self").str())) {
        if (Function *Real =
                M.getFunction((Next[I]->getName() + ".noalloc").str()))
          PreDecl->replaceAllUsesWith(Real);
        if (PreDecl->use_empty())
          PreDecl->eraseFromParent();
      }
      // Frame growth is the ladder's progress signal, but an arena
      // generation is useful even when the added bookkeeping hides in
      // frame padding; it is accepted unconditionally and, being
      // self-covering, ends its member's ladder.
      GenState NewState;
      if (!readGenState(M, Next[I], NewState) ||
          (NewState.FrameSize <= Cur[I].FrameSize && !ArenaSaturated[I])) {
        Saturated[I] = true;
        continue;
      }
      LLVM_DEBUG(dbgs() << "CoroRecursiveElide: '" << Next[I]->getName()
                        << "' frame " << NewState.FrameSize << " bytes\n");
      Cur[I] = NewState;
      AnyGenerationBuilt = true;
      if (ArenaSaturated[I])
        Saturated[I] = true;
      else
        Progress = true;
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

  // The stash-time pins kept every cycle re-entry an outlined reference to
  // the original symbol so the RAUW above could retarget it into the block
  // ramp; a glue-inlined copy of the allocating ramp would have pinned its
  // branch of the recursion to unelided frames forever. Republished, the
  // block ramp is an ordinary small function, and the re-entry sites live
  // in the originals' split clones, which no inliner visits again -- so
  // fold the ramp into them here, as the CGSCC inliner does for ordinary
  // split ramps. The guarded-dispatch escape legs inside the generations
  // keep their own noinline and stay outlined.
  if (CoroRecursiveElideInlineRamp) {
    SmallPtrSet<Function *, 4> Tops;
    for (unsigned I = 0; I != N; ++I)
      if (Cur[I].Fn != Group[I].second)
        Tops.insert(Cur[I].Fn);
    for (unsigned I = 0; I != N; ++I) {
      if (Cur[I].Fn == Group[I].second)
        continue;
      // The republished name is the prefix the original's clones were
      // split under during the CGSCC pipeline.
      StringRef Name = Cur[I].Fn->getName();
      for (StringRef Suffix : {".resume", ".destroy", ".cleanup"}) {
        Function *Clone = M.getFunction((Name + Suffix).str());
        if (!Clone || Clone->isDeclaration())
          continue;
        SmallVector<CallBase *, 16> ReentrySites;
        for (Instruction &Inst : instructions(*Clone))
          if (auto *CB = dyn_cast<CallBase>(&Inst))
            if (CB->getCalledFunction() &&
                Tops.contains(CB->getCalledFunction()))
              ReentrySites.push_back(CB);
        for (CallBase *CB : ReentrySites) {
          CB->removeFnAttr(llvm::Attribute::NoInline);
          InlineFunctionInfo IFI;
          if (InlineFunction(*CB, IFI).isSuccess())
            LLVM_DEBUG(dbgs() << "CoroRecursiveElide: inlined block ramp "
                                 "re-entry in '"
                              << Clone->getName() << "'\n");
        }
      }
    }
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
