//===- CoroAnnotationElide.cpp - Elide attributed safe coroutine calls ----===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// \file
// This pass transforms all Call or Invoke instructions that are annotated
// "coro_elide_safe" to call the `.noalloc` variant of coroutine instead.
// The frame of the callee coroutine is allocated inside the caller. A pointer
// to the allocated frame will be passed into the `.noalloc` ramp function.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Coroutines/CoroAnnotationElide.h"

#include "llvm/Analysis/CGSCCPassManager.h"
#include "llvm/Analysis/LazyCallGraph.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/IR/Analysis.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/BranchProbability.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Transforms/Utils/CallGraphUpdater.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include <cassert>

using namespace llvm;

#define DEBUG_TYPE "coro-annotation-elide"

// BranchProbabilityInfo models the resume path of suspend points in the
// (presplit) caller as overwhelmingly likely, so a directly awaited call
// site in straight-line code is estimated at ~100% of the caller's entry
// frequency regardless of how many suspend points precede it, and dilution
// below the threshold reflects genuine branch conditions: profile data, an
// explicit [[unlikely]] / __builtin_expect annotation (~0.05% of entry), or
// statically cold paths. The default of 0 disables the frequency gate;
// pass a positive ratio to reject call sites less likely to execute than
// that fraction of the caller's entry frequency.
static cl::opt<float> CoroElideBranchRatio(
    "coro-elide-branch-ratio", cl::init(0.0), cl::Hidden,
    cl::desc("Minimum ratio between the frequency of a coro_elide_safe call "
             "site and the entry frequency of its caller for the callee "
             "coroutine to be elided."));

// An elided callee's frame becomes part of the caller's frame, so elision
// compounds through nested awaits: the callee's frame size at decision time
// already includes every frame previously elided into it. Without a limit,
// recursive task trees accrete into a single enormous root frame whose
// working set far exceeds what heap allocation (with allocator block reuse)
// would touch. Callee frames larger than this limit stay heap-allocated.
// The default was chosen empirically on fork-join task tree benchmarks,
// both statically instantiated and runtime-recursive: performance peaks in
// the 4-8 KiB range (4 KiB is markedly better when the tree's depth varies
// at runtime, because a rejected subtree frame is the block actually
// allocated, and oversized blocks go mostly unused near the leaves),
// degrades past 32 KiB, and falls below no-elision-at-all past 128 KiB.
// Bounding the callee frame size (a complete, temporally compact unit of
// work) measures better than bounding the caller's accumulated total, which
// preferentially rejects the later visited (larger, in postorder) children
// and fragments the task tree into long-lived chains touched at widely
// separated fork and join times.
cl::opt<uint64_t> CoroElideMaxFrameSize(
    "coro-elide-max-frame-size", cl::init(4096), cl::Hidden,
    cl::desc("Maximum callee coroutine frame size, in bytes, that may be "
             "elided into a caller's frame. Larger callee frames remain "
             "dynamically allocated."));

// The per-callee limit alone still allows a caller with many elidable call
// sites to accrete (sites x limit) bytes, since each callee is admitted
// individually. This bounds the total: once the frames already elided into
// a caller plus the candidate exceed it, further callees stay
// heap-allocated. It is a backstop for wide fan-out bodies (e.g. a variadic
// join of dozens of tasks); at 4x the per-callee limit it never binds for
// fan-outs of four or fewer maximum-size children.
cl::opt<uint64_t> CoroElideMaxAccumulatedFrameSize(
    "coro-elide-max-accumulated-frame-size", cl::init(16384), cl::Hidden,
    cl::desc("Maximum total size, in bytes, of callee coroutine frames "
             "elided into any one caller's frame. Callee frames that do not "
             "fit under this limit remain dynamically allocated."));
extern cl::opt<unsigned> MinBlockCounterExecution;

static Instruction *getFirstNonAllocaInTheEntryBlock(Function *F) {
  for (Instruction &I : F->getEntryBlock())
    if (!isa<AllocaInst>(&I))
      return &I;
  llvm_unreachable("no terminator in the entry block");
}

// Create an alloca in the caller, using FrameSize and FrameAlign as the callee
// coroutine's activation frame. The alloca is tagged with metadata so later
// elision decisions can total up the frame bytes already elided into the
// caller.
static Value *allocateFrameInCaller(Function *Caller, uint64_t FrameSize,
                                    Align FrameAlign) {
  LLVMContext &C = Caller->getContext();
  BasicBlock::iterator InsertPt =
      getFirstNonAllocaInTheEntryBlock(Caller)->getIterator();
  const DataLayout &DL = Caller->getDataLayout();
  auto FrameTy = ArrayType::get(Type::getInt8Ty(C), FrameSize);
  auto *Frame = new AllocaInst(FrameTy, DL.getAllocaAddrSpace(), "", InsertPt);
  Frame->setAlignment(FrameAlign);
  Frame->setMetadata("coro.elided.frame", MDNode::get(C, {}));
  return Frame;
}

// Total size in bytes of callee coroutine frames already elided into this
// function. Elided-frame allocas always land in the entry block (both when
// created here and after InlineFunction hoists them from an inlined callee).
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

// Given a call or invoke instruction to the elide safe coroutine, this function
// does the following:
//  - Allocate a frame for the callee coroutine in the caller using alloca.
//  - Replace the old CB with a new Call or Invoke to `NewCallee`, with the
//    pointer to the frame as an additional argument to NewCallee.
static void processCall(CallBase *CB, Function *Caller, Function *NewCallee,
                        uint64_t FrameSize, Align FrameAlign) {
  // TODO: generate the lifetime intrinsics for the new frame. This will require
  // introduction of two pesudo lifetime intrinsics in the frontend around the
  // `co_await` expression and convert them to real lifetime intrinsics here.
  auto *FramePtr = allocateFrameInCaller(Caller, FrameSize, FrameAlign);
  auto NewCBInsertPt = CB->getIterator();
  llvm::CallBase *NewCB = nullptr;
  SmallVector<Value *, 4> NewArgs;
  NewArgs.append(CB->arg_begin(), CB->arg_end());
  NewArgs.push_back(FramePtr);

  if (auto *CI = dyn_cast<CallInst>(CB)) {
    auto *NewCI = CallInst::Create(NewCallee->getFunctionType(), NewCallee,
                                   NewArgs, "", NewCBInsertPt);
    NewCI->setTailCallKind(CI->getTailCallKind());
    NewCB = NewCI;
  } else if (auto *II = dyn_cast<InvokeInst>(CB)) {
    NewCB = InvokeInst::Create(NewCallee->getFunctionType(), NewCallee,
                               II->getNormalDest(), II->getUnwindDest(),
                               NewArgs, {}, "", NewCBInsertPt);
  } else {
    llvm_unreachable("CallBase should either be Call or Invoke!");
  }

  NewCB->setCalledFunction(NewCallee->getFunctionType(), NewCallee);
  NewCB->setCallingConv(CB->getCallingConv());
  NewCB->setAttributes(CB->getAttributes());
  NewCB->setDebugLoc(CB->getDebugLoc());
  std::copy(CB->bundle_op_info_begin(), CB->bundle_op_info_end(),
            NewCB->bundle_op_info_begin());

  NewCB->removeFnAttr(llvm::Attribute::CoroElideSafe);
  CB->replaceAllUsesWith(NewCB);

  InlineFunctionInfo IFI;
  InlineResult IR = InlineFunction(*NewCB, IFI);
  if (IR.isSuccess()) {
    CB->eraseFromParent();
  } else {
    NewCB->replaceAllUsesWith(CB);
    NewCB->eraseFromParent();
  }
}

PreservedAnalyses CoroAnnotationElidePass::run(LazyCallGraph::SCC &C,
                                               CGSCCAnalysisManager &AM,
                                               LazyCallGraph &CG,
                                               CGSCCUpdateResult &UR) {
  bool Changed = false;
  CallGraphUpdater CGUpdater;
  CGUpdater.initialize(CG, C, AM, UR);

  auto &FAM =
      AM.getResult<FunctionAnalysisManagerCGSCCProxy>(C, CG).getManager();

  for (LazyCallGraph::Node &N : C) {
    Function *Callee = &N.getFunction();
    Function *NewCallee = Callee->getParent()->getFunction(
        (Callee->getName() + ".noalloc").str());
    if (!NewCallee)
      continue;

    SmallVector<CallBase *, 4> Users;
    for (auto *U : Callee->users()) {
      if (auto *CB = dyn_cast<CallBase>(U)) {
        if (CB->getCalledFunction() == Callee)
          Users.push_back(CB);
      }
    }
    auto FramePtrArgPosition = NewCallee->arg_size() - 1;
    auto FrameSize =
        NewCallee->getParamDereferenceableBytes(FramePtrArgPosition);
    auto FrameAlign =
        NewCallee->getParamAlign(FramePtrArgPosition).valueOrOne();

    auto &ORE = FAM.getResult<OptimizationRemarkEmitterAnalysis>(*Callee);

    for (auto *CB : Users) {
      auto *Caller = CB->getFunction();
      if (!Caller)
        continue;

      // Recursion templates are stashed presplit copies kept only as cloning
      // material for CoroRecursiveElide; eliding into them would duplicate
      // the elision when generations are cloned from them later.
      if (Caller->hasFnAttribute("coro.recursive.template"))
        continue;

      bool IsCallerPresplitCoroutine = Caller->isPresplitCoroutine();
      bool HasAttr = CB->hasFnAttr(llvm::Attribute::CoroElideSafe);
      if (IsCallerPresplitCoroutine && HasAttr) {
        if (FrameSize > CoroElideMaxFrameSize) {
          ORE.emit([&]() {
            return OptimizationRemarkMissed(
                       DEBUG_TYPE, "CoroAnnotationElideTooLarge", Caller)
                   << "'" << ore::NV("callee", Callee->getName())
                   << "' not elided in '"
                   << ore::NV("caller", Caller->getName())
                   << "' because its frame is too large: "
                   << ore::NV("frame_size", FrameSize) << " (max: "
                   << ore::NV("max_frame_size",
                              CoroElideMaxFrameSize.getValue())
                   << ")";
          });
          continue;
        }

        uint64_t AccumFrameSize =
            accumulatedElidedFrameSize(Caller) + FrameSize;
        if (AccumFrameSize > CoroElideMaxAccumulatedFrameSize) {
          ORE.emit([&]() {
            return OptimizationRemarkMissed(
                       DEBUG_TYPE, "CoroAnnotationElideTooManyFrames", Caller)
                   << "'" << ore::NV("callee", Callee->getName())
                   << "' not elided in '"
                   << ore::NV("caller", Caller->getName())
                   << "' because the caller's accumulated elided frame size "
                      "would be too large: "
                   << ore::NV("accumulated_frame_size", AccumFrameSize)
                   << " (max: "
                   << ore::NV("max_accumulated_frame_size",
                              CoroElideMaxAccumulatedFrameSize.getValue())
                   << ")";
          });
          continue;
        }

        auto &BFI = FAM.getResult<BlockFrequencyAnalysis>(*Caller);

        auto BlockFreq = BFI.getBlockFreq(CB->getParent()).getFrequency();
        auto EntryFreq = BFI.getEntryFreq().getFrequency();
        uint64_t MinFreq =
            static_cast<uint64_t>(EntryFreq * CoroElideBranchRatio);

        if (BlockFreq < MinFreq) {
          ORE.emit([&]() {
            return OptimizationRemarkMissed(
                       DEBUG_TYPE, "CoroAnnotationElideUnlikely", Caller)
                   << "'" << ore::NV("callee", Callee->getName())
                   << "' not elided in '"
                   << ore::NV("caller", Caller->getName())
                   << "' because of low frequency: "
                   << ore::NV("block_freq", BlockFreq)
                   << " (threshold: " << ore::NV("min_freq", MinFreq) << ")";
          });
          continue;
        }

        auto *CallerN = CG.lookup(*Caller);
        auto *CallerC = CallerN ? CG.lookupSCC(*CallerN) : nullptr;
        // If CallerC is nullptr, it means LazyCallGraph hasn't visited Caller
        // yet. Skip the call graph update.
        auto ShouldUpdateCallGraph = !!CallerC;
        processCall(CB, Caller, NewCallee, FrameSize, FrameAlign);

        ORE.emit([&]() {
          return OptimizationRemark(DEBUG_TYPE, "CoroAnnotationElide", Caller)
                 << "'" << ore::NV("callee", Callee->getName())
                 << "' elided in '" << ore::NV("caller", Caller->getName())
                 << "' (block_freq: " << ore::NV("block_freq", BlockFreq)
                 << ")";
        });

        FAM.invalidate(*Caller, PreservedAnalyses::none());
        Changed = true;
        if (ShouldUpdateCallGraph)
          updateCGAndAnalysisManagerForCGSCCPass(CG, *CallerC, *CallerN, AM, UR,
                                                 FAM);

      } else {
        ORE.emit([&]() {
          return OptimizationRemarkMissed(DEBUG_TYPE, "CoroAnnotationElide",
                                          Caller)
                 << "'" << ore::NV("callee", Callee->getName())
                 << "' not elided in '" << ore::NV("caller", Caller->getName())
                 << "' (caller_presplit="
                 << ore::NV("caller_presplit", IsCallerPresplitCoroutine)
                 << ", elide_safe_attr=" << ore::NV("elide_safe_attr", HasAttr)
                 << ")";
        });
      }
    }
  }

  return Changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
}
