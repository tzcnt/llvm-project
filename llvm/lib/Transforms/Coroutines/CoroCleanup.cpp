//===- CoroCleanup.cpp - Coroutine Cleanup Pass ---------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Coroutines/CoroCleanup.h"
#include "CoroInternal.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/Analysis/PtrUseVisitor.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

using namespace llvm;

#define DEBUG_TYPE "coro-cleanup"

namespace {
// Created on demand if CoroCleanup pass has work to do.
struct Lowerer : coro::LowererBase {
  IRBuilder<> Builder;
  Constant *NoopCoro = nullptr;
  bool CFGChanged = false;

  Lowerer(Module &M) : LowererBase(M), Builder(Context) {}
  bool lower(Function &F);

private:
  void lowerCoroNoop(IntrinsicInst *II);
};

// Recursively walk and eliminate resume/destroy call on noop coro
class NoopCoroElider : public PtrUseVisitor<NoopCoroElider> {
  using Base = PtrUseVisitor<NoopCoroElider>;

  IRBuilder<> Builder;

public:
  NoopCoroElider(const DataLayout &DL, LLVMContext &C) : Base(DL), Builder(C) {}

  void run(IntrinsicInst *II);

  void visitLoadInst(LoadInst &I) { enqueueUsers(I); }
  void visitCallBase(CallBase &CB);
  void visitIntrinsicInst(IntrinsicInst &II);

private:
  bool tryEraseCallInvoke(Instruction *I);
  void eraseFromWorklist(Instruction *I);
};
} // namespace

static void lowerSubFn(IRBuilder<> &Builder, CoroSubFnInst *SubFn) {
  Builder.SetInsertPoint(SubFn);
  Value *FramePtr = SubFn->getFrame();
  int Index = SubFn->getIndex();

  auto *FrameTy = StructType::get(SubFn->getContext(),
                                  {Builder.getPtrTy(), Builder.getPtrTy()});

  Builder.SetInsertPoint(SubFn);
  auto *Gep = Builder.CreateConstInBoundsGEP2_32(FrameTy, FramePtr, 0, Index);
  auto *Load = Builder.CreateLoad(FrameTy->getElementType(Index), Gep);

  SubFn->replaceAllUsesWith(Load);
}

static void buildDebugInfoForNoopResumeDestroyFunc(Function *NoopFn) {
  Module &M = *NoopFn->getParent();
  if (M.debug_compile_units().empty())
    return;

  DICompileUnit *CU = *M.debug_compile_units_begin();
  DIBuilder DB(M, /*AllowUnresolved*/ false, CU);
  std::array<Metadata *, 2> Params{nullptr, nullptr};
  auto *SubroutineType =
      DB.createSubroutineType(DB.getOrCreateTypeArray(Params));
  StringRef Name = NoopFn->getName();
  auto *SP = DB.createFunction(
      CU, /*Name=*/Name, /*LinkageName=*/Name, /*File=*/CU->getFile(),
      /*LineNo=*/0, SubroutineType, /*ScopeLine=*/0, DINode::FlagArtificial,
      DISubprogram::SPFlagDefinition);
  NoopFn->setSubprogram(SP);
  DB.finalize();
}

// Return true if \p V feeds, within block \p BB, a call whose callee is taken
// from the coroutine frame \p V points to. This is the resume/destroy pattern
// that NoopCoroElider erases once the frame is known to be the noop coroutine.
// Recognizes both the pre-lowering form (llvm.coro.subfn.addr + call) and the
// lowered form ((gep +) load + indirect call).
static bool feedsElidableCall(Value *V, BasicBlock *BB) {
  for (User *U : V->users()) {
    if (auto *SubFn = dyn_cast<CoroSubFnInst>(U)) {
      if (SubFn->getFrame() == V && SubFn->getParent() == BB)
        return true;
    } else if (auto *GEP = dyn_cast<GetElementPtrInst>(U)) {
      if (GEP->getPointerOperand() == V && GEP->getParent() == BB &&
          feedsElidableCall(GEP, BB))
        return true;
    } else if (auto *Load = dyn_cast<LoadInst>(U)) {
      if (Load->getPointerOperand() != V || Load->getParent() != BB ||
          !Load->getType()->isPointerTy())
        continue;
      for (User *LU : Load->users()) {
        auto *CB = dyn_cast<CallBase>(LU);
        if (CB && CB->getParent() == BB && CB->getCalledOperand() == Load)
          return true;
      }
    }
  }
  return false;
}

// Specialize away phi-merged noop coroutine handles.
//
// A common pattern after inlining is a symmetric transfer where await_suspend
// either returns a real continuation or std::noop_coroutine():
//
//   %handle = phi ptr [ %continuation, %bb1 ], [ %noop, %bb2 ]
//   %fn = call ptr @llvm.coro.subfn.addr(ptr %handle, i8 0)
//   musttail call void %fn(ptr %handle)
//   ret void
//
// The phi hides the noop handle from NoopCoroElider, so the noop paths lower
// to an indirect jump to __NoopCoro_ResumeDestroy, a function that consists of
// a single ret. Redirect the noop-carrying edges to a specialized clone of the
// block in which the handle is the noop coroutine directly; the regular
// elision then deletes the call in the clone, so those paths simply return.
static bool threadNoopPhiEdges(IntrinsicInst *NoopCoro) {
  // Modest limit on the number of instructions duplicated per specialized
  // predecessor.
  constexpr unsigned MaxBlockSize = 16;

  SmallSetVector<PHINode *, 4> Phis;
  for (User *U : NoopCoro->users())
    if (auto *PN = dyn_cast<PHINode>(U))
      Phis.insert(PN);

  bool Changed = false;
  for (PHINode *PN : Phis) {
    BasicBlock *BB = PN->getParent();
    if (BB->isEHPad() || !isa<ReturnInst>(BB->getTerminator()) ||
        BB->size() > MaxBlockSize)
      continue;
    if (!feedsElidableCall(PN, BB))
      continue;

    // Collect predecessors whose every edge into BB carries the noop handle.
    // All phis in BB must be uniform across the edges of such a predecessor so
    // that the block can be specialized per predecessor.
    SmallSetVector<BasicBlock *, 4> Candidates;
    for (unsigned I = 0, E = PN->getNumIncomingValues(); I != E; ++I)
      if (PN->getIncomingValue(I) == NoopCoro)
        Candidates.insert(PN->getIncomingBlock(I));

    SmallVector<BasicBlock *, 4> NoopPreds;
    for (BasicBlock *Pred : Candidates) {
      bool Uniform = true;
      for (PHINode &P : BB->phis()) {
        Value *V = nullptr;
        for (unsigned I = 0, E = P.getNumIncomingValues(); I != E; ++I) {
          if (P.getIncomingBlock(I) != Pred)
            continue;
          if (!V)
            V = P.getIncomingValue(I);
          else if (V != P.getIncomingValue(I)) {
            Uniform = false;
            break;
          }
        }
        if (!Uniform || (&P == PN && V != NoopCoro)) {
          Uniform = false;
          break;
        }
      }
      if (Uniform)
        NoopPreds.push_back(Pred);
    }
    if (NoopPreds.empty())
      continue;

    // Keep BB reachable. If every edge carries the noop handle the phi would
    // have been folded already; don't leave BB behind without predecessors.
    SmallPtrSet<BasicBlock *, 8> AllPreds(pred_begin(BB), pred_end(BB));
    if (NoopPreds.size() == AllPreds.size())
      continue;

    for (BasicBlock *Pred : NoopPreds) {
      ValueToValueMapTy VMap;
      // Insert the clone at the end of the function so that the instruction
      // walk in lower() still visits (and lowers) any coroutine intrinsics
      // cloned into it.
      BasicBlock *Clone = BasicBlock::Create(
          BB->getContext(), BB->getName() + ".noop", BB->getParent());
      for (PHINode &P : BB->phis())
        VMap[&P] = P.getIncomingValueForBlock(Pred);
      for (Instruction &I : *BB) {
        if (isa<PHINode>(I))
          continue;
        // llvm.coro.subfn.addr calls that lower() already lowered linger
        // use-empty until the deferred DeadInsts sweep; don't clone them.
        if (I.use_empty() && isa<CoroSubFnInst>(I))
          continue;
        Instruction *C = I.clone();
        C->setName(I.getName());
        C->insertInto(Clone, Clone->end());
        RemapInstruction(C, VMap,
                         RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
        VMap[&I] = C;
      }
      Pred->getTerminator()->replaceSuccessorWith(BB, Clone);
      for (PHINode &P : make_early_inc_range(BB->phis()))
        P.removeIncomingValueIf(
            [&](unsigned Idx) { return P.getIncomingBlock(Idx) == Pred; },
            /*DeletePHIIfEmpty=*/false);
      Changed = true;
    }
  }
  return Changed;
}

bool Lowerer::lower(Function &F) {
  bool IsPrivateAndUnprocessed = F.isPresplitCoroutine() && F.hasLocalLinkage();
  bool Changed = false;

  NoopCoroElider NCE(F.getDataLayout(), F.getContext());
  SmallPtrSet<Instruction *, 8> DeadInsts{};
  for (Instruction &I : instructions(F)) {
    if (auto *II = dyn_cast<IntrinsicInst>(&I)) {
      switch (II->getIntrinsicID()) {
      default:
        continue;
      case Intrinsic::coro_begin:
      case Intrinsic::coro_begin_custom_abi:
        II->replaceAllUsesWith(II->getArgOperand(1));
        break;
      case Intrinsic::coro_free:
        II->replaceAllUsesWith(II->getArgOperand(1));
        break;
      case Intrinsic::coro_dead:
        break;
      case Intrinsic::coro_alloc:
        II->replaceAllUsesWith(ConstantInt::getTrue(Context));
        break;
      case Intrinsic::coro_async_resume:
        II->replaceAllUsesWith(
            ConstantPointerNull::get(cast<PointerType>(I.getType())));
        break;
      case Intrinsic::coro_id:
      case Intrinsic::coro_id_retcon:
      case Intrinsic::coro_id_retcon_once:
      case Intrinsic::coro_id_async:
        II->replaceAllUsesWith(ConstantTokenNone::get(Context));
        break;
      case Intrinsic::coro_noop:
        CFGChanged |= threadNoopPhiEdges(II);
        NCE.run(II);
        if (!II->user_empty())
          lowerCoroNoop(II);
        break;
      case Intrinsic::coro_subfn_addr:
        lowerSubFn(Builder, cast<CoroSubFnInst>(II));
        break;
      case Intrinsic::coro_suspend_retcon:
      case Intrinsic::coro_is_in_ramp:
        if (IsPrivateAndUnprocessed) {
          II->replaceAllUsesWith(PoisonValue::get(II->getType()));
        } else
          continue;
        break;
      case Intrinsic::coro_async_size_replace:
        auto *Target = cast<ConstantStruct>(
            cast<GlobalVariable>(
                II->getArgOperand(0)->stripPointerCastsAndAliases())
                ->getInitializer());
        auto *Source = cast<ConstantStruct>(
            cast<GlobalVariable>(
                II->getArgOperand(1)->stripPointerCastsAndAliases())
                ->getInitializer());
        auto *TargetSize = Target->getOperand(1);
        auto *SourceSize = Source->getOperand(1);
        if (TargetSize->isElementWiseEqual(SourceSize)) {
          break;
        }
        auto *TargetRelativeFunOffset = Target->getOperand(0);
        auto *NewFuncPtrStruct = ConstantStruct::get(
            Target->getType(), TargetRelativeFunOffset, SourceSize);
        Target->replaceAllUsesWith(NewFuncPtrStruct);
        break;
      }
      DeadInsts.insert(II);
      Changed = true;
    }
  }

  for (auto *I : DeadInsts)
    I->eraseFromParent();
  return Changed;
}

void Lowerer::lowerCoroNoop(IntrinsicInst *II) {
  if (!NoopCoro) {
    LLVMContext &C = Builder.getContext();
    Module &M = *II->getModule();

    // Create a noop.frame struct type.
    auto *FnTy = FunctionType::get(Type::getVoidTy(C), Builder.getPtrTy(0),
                                   /*isVarArg=*/false);
    auto *FnPtrTy = Builder.getPtrTy(0);
    StructType *FrameTy =
        StructType::create({FnPtrTy, FnPtrTy}, "NoopCoro.Frame");

    // Create a Noop function that does nothing.
    Function *NoopFn = Function::createWithDefaultAttr(
        FnTy, GlobalValue::LinkageTypes::InternalLinkage,
        M.getDataLayout().getProgramAddressSpace(), "__NoopCoro_ResumeDestroy",
        &M);
    buildDebugInfoForNoopResumeDestroyFunc(NoopFn);
    auto *Entry = BasicBlock::Create(C, "entry", NoopFn);
    ReturnInst::Create(C, Entry);

    // Create a constant struct for the frame.
    Constant *Values[] = {NoopFn, NoopFn};
    Constant *NoopCoroConst = ConstantStruct::get(FrameTy, Values);
    NoopCoro = new GlobalVariable(
        M, NoopCoroConst->getType(), /*isConstant=*/true,
        GlobalVariable::PrivateLinkage, NoopCoroConst, "NoopCoro.Frame.Const");
    cast<GlobalVariable>(NoopCoro)->setNoSanitizeMetadata();
  }

  Builder.SetInsertPoint(II);
  auto *NoopCoroVoidPtr = Builder.CreateBitCast(NoopCoro, Int8Ptr);
  II->replaceAllUsesWith(NoopCoroVoidPtr);
}

void NoopCoroElider::run(IntrinsicInst *II) {
  visitPtr(*II);

  Worklist.clear();
  VisitedUses.clear();
}

void NoopCoroElider::visitCallBase(CallBase &CB) {
  auto *V = U->get();
  bool ResumeOrDestroy = V == CB.getCalledOperand();
  if (ResumeOrDestroy) {
    [[maybe_unused]] bool Success = tryEraseCallInvoke(&CB);
    assert(Success && "Unexpected CallBase");

    auto AboutToDeleteCallback = [this](Value *V) {
      eraseFromWorklist(cast<Instruction>(V));
    };
    RecursivelyDeleteTriviallyDeadInstructions(V, nullptr, nullptr,
                                               AboutToDeleteCallback);
  }
}

void NoopCoroElider::visitIntrinsicInst(IntrinsicInst &II) {
  if (auto *SubFn = dyn_cast<CoroSubFnInst>(&II)) {
    auto *User = SubFn->getUniqueUndroppableUser();
    assert(User && "Broken module");
    if (!tryEraseCallInvoke(cast<Instruction>(User)))
      return;
    SubFn->eraseFromParent();
  }
}

bool NoopCoroElider::tryEraseCallInvoke(Instruction *I) {
  if (auto *Call = dyn_cast<CallInst>(I)) {
    eraseFromWorklist(Call);
    Call->eraseFromParent();
    return true;
  }

  if (auto *II = dyn_cast<InvokeInst>(I)) {
    Builder.SetInsertPoint(II);
    Builder.CreateBr(II->getNormalDest());
    eraseFromWorklist(II);
    II->getUnwindDest()->removePredecessor(II->getParent());
    II->eraseFromParent();
    return true;
  }
  return false;
}

void NoopCoroElider::eraseFromWorklist(Instruction *I) {
  erase_if(Worklist, [I](UseToVisit &U) {
    return I == U.UseAndIsOffsetKnown.getPointer()->getUser();
  });
}

static bool declaresCoroCleanupIntrinsics(const Module &M) {
  return coro::declaresIntrinsics(
      M, {Intrinsic::coro_alloc, Intrinsic::coro_begin,
          Intrinsic::coro_subfn_addr, Intrinsic::coro_free,
          Intrinsic::coro_dead, Intrinsic::coro_id, Intrinsic::coro_id_retcon,
          Intrinsic::coro_id_async, Intrinsic::coro_id_retcon_once,
          Intrinsic::coro_noop, Intrinsic::coro_async_size_replace,
          Intrinsic::coro_async_resume, Intrinsic::coro_begin_custom_abi});
}

PreservedAnalyses CoroCleanupPass::run(Module &M,
                                       ModuleAnalysisManager &MAM) {
  if (!declaresCoroCleanupIntrinsics(M))
    return PreservedAnalyses::all();

  FunctionAnalysisManager &FAM =
      MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();

  FunctionPassManager FPM;
  FPM.addPass(SimplifyCFGPass());

  PreservedAnalyses FuncPA;
  FuncPA.preserveSet<CFGAnalyses>();

  Lowerer L(M);
  for (auto &F : M) {
    L.CFGChanged = false;
    if (L.lower(F)) {
      FAM.invalidate(F, L.CFGChanged ? PreservedAnalyses::none() : FuncPA);
      FPM.run(F, FAM);
    }
  }

  return PreservedAnalyses::none();
}
