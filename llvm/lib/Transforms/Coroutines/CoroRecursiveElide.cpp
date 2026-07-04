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
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Coroutines/CoroRecursiveElide.h"

#include "CoroInternal.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
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

static constexpr const char *TemplateAttr = "coro.recursive.template";
static constexpr const char *GroupAttr = "coro.recursive.group";

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

// Elide one call site: allocate the callee frame in the caller, call the
// `.noalloc` variant with it, and inline that variant.
static void elideSite(CallBase *CB, Function *Caller, Function *NoAllocCallee,
                      uint64_t FrameSize, Align FrameAlign) {
  LLVMContext &C = Caller->getContext();
  const DataLayout &DL = Caller->getDataLayout();
  auto *FrameTy = ArrayType::get(Type::getInt8Ty(C), FrameSize);
  auto *Frame =
      new AllocaInst(FrameTy, DL.getAllocaAddrSpace(), "",
                     getFirstNonAllocaInEntry(Caller)->getIterator());
  Frame->setAlignment(FrameAlign);
  Frame->setMetadata("coro.elided.frame", MDNode::get(C, {}));

  SmallVector<Value *, 4> NewArgs(CB->args());
  NewArgs.push_back(Frame);
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
  // coroutine must exist before it is worth building a call graph.
  bool AnyCandidateSite = false;
  for (Function &F : M) {
    if (F.isDeclaration())
      continue;
    for (Instruction &I : instructions(F)) {
      auto *CB = dyn_cast<CallBase>(&I);
      if (CB && CB->hasFnAttr(llvm::Attribute::CoroElideSafe) &&
          CB->getCalledFunction() &&
          CB->getCalledFunction()->isPresplitCoroutine()) {
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

  // Collect call graph cycles made entirely of presplit coroutine
  // definitions and connected by at least one direct, elide-safe,
  // loop-free cycle call site.
  CallGraph CG(M);
  SmallVector<SmallVector<Function *, 2>, 4> Groups;
  for (scc_iterator<CallGraph *> I = scc_begin(&CG); !I.isAtEnd(); ++I) {
    if (!I.hasCycle())
      continue;
    SmallVector<Function *, 2> Members;
    bool AllPresplit = true;
    for (CallGraphNode *N : *I) {
      Function *F = N->getFunction();
      if (!F || F->isDeclaration() || !F->isPresplitCoroutine()) {
        AllPresplit = false;
        break;
      }
      Members.push_back(F);
    }
    if (!AllPresplit || Members.empty())
      continue;

    SmallPtrSet<Function *, 4> InSCC(Members.begin(), Members.end());
    bool HasSite = false;
    for (Function *F : Members) {
      LoopInfo &LI = FAM.getResult<LoopAnalysis>(*F);
      for (Instruction &I : instructions(*F)) {
        auto *CB = dyn_cast<CallBase>(&I);
        if (CB && CB->hasFnAttr(llvm::Attribute::CoroElideSafe) &&
            CB->getCalledFunction() && InSCC.count(CB->getCalledFunction()) &&
            !LI.getLoopFor(CB->getParent())) {
          HasSite = true;
          break;
        }
      }
      if (HasSite)
        break;
    }
    if (HasSite)
      Groups.push_back(std::move(Members));
  }
  if (Groups.empty())
    return PreservedAnalyses::all();

  SmallVector<GlobalValue *, 4> KeepAlive;
  unsigned GroupId = 0;
  for (SmallVector<Function *, 2> &Members : Groups) {
    SmallPtrSet<Function *, 4> InSCC(Members.begin(), Members.end());
    for (Function *F : Members) {
      LoopInfo &LI = FAM.getResult<LoopAnalysis>(*F);
      ValueToValueMapTy VMap;
      Function *T = CloneFunction(F, VMap);
      T->setName(F->getName() + ".recursive.template");
      T->setLinkage(GlobalValue::InternalLinkage);
      T->addFnAttr(TemplateAttr, F->getName());
      T->addFnAttr(GroupAttr, std::to_string(GroupId));
      retargetCoroId(T, F);

      // In the template: a cycle call site inside a loop must never be
      // elided (its block slot would be reused while a previous iteration's
      // coroutine may still be live), so strip its marking. Mark every cycle
      // call site noinline so that nothing folds away these symbol
      // references before the generations are built from them.
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

      SmallVector<CallBase *, 4> Sites;
      for (Instruction &Inst : instructions(*G)) {
        auto *CB = dyn_cast<CallBase>(&Inst);
        if (CB && CB->hasFnAttr(llvm::Attribute::CoroElideSafe) &&
            CB->getCalledFunction() &&
            OrigIndex.contains(CB->getCalledFunction()))
          Sites.push_back(CB);
      }
      for (CallBase *CB : Sites) {
        const GenState &Callee = Cur[OrigIndex[CB->getCalledFunction()]];
        if (Callee.FrameSize > CoroElideMaxFrameSize)
          continue;
        if (accumulatedElidedFrameSize(G) + Callee.FrameSize >
            CoroElideMaxAccumulatedFrameSize)
          continue;
        elideSite(CB, G, Callee.NoAlloc, Callee.FrameSize, Callee.FrameAlign);
        Elided[I] = true;
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
