//===- CoroRecursionPeel.cpp - Peel recursive coroutines for elision ------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// \file
// CoroAnnotationElide can only elide a coro_elide_safe call site while the
// caller is still a presplit coroutine, and it needs the callee's frame size,
// which exists only after the callee has been split. The CGSCC pipeline
// satisfies both requirements for acyclic call graphs by visiting callees
// before callers, but a recursive coroutine is a call graph cycle: every
// function on the cycle is split during the same SCC visit, so no call site
// on the cycle ever observes a presplit caller and recursion never benefits
// from elision.
//
// This pass restores the acyclic shape by peeling. The body of a
// self-recursive coroutine F with coro_elide_safe self-call sites is cloned
// into a chain F -> F.peel.1 -> ... -> F.peel.N, rewriting the elide-safe
// self-call sites of each copy to call the next copy. The bottom copy calls
// F again -- the recursion is real, so the cycle must exist somewhere -- but
// through a pointer laundered by llvm.coro.recursion.anchor, which the call
// graph does not treat as a call edge. The chain is therefore processed
// leaf-first, and CoroAnnotationElide packs it into caller frames bottom-up
// until its frame size limits stop it, carving the recursion tree into
// bounded blocks: within a block, awaits resume coroutines whose frames were
// elided into the block's allocation; the leaves of a block start the next
// block by calling F through the anchored pointer. CoroCleanup folds the
// anchor away after all split and elide decisions are complete, so the block
// boundary is an ordinary direct call in the final code.
//
// If the recursion terminates before reaching the bottom of a block, the
// remaining elided frames are never started; as with any speculatively
// elided frame on an untaken path, the space is wasted but no lifetime
// begins.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Coroutines/CoroRecursionPeel.h"

#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Twine.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

using namespace llvm;

#define DEBUG_TYPE "coro-recursion-peel"

static cl::opt<unsigned> CoroRecursionPeelDepth(
    "coro-recursion-peel-depth", cl::init(8), cl::Hidden,
    cl::desc("Number of copies a self-recursive coroutine with "
             "coro_elide_safe self-call sites is peeled into, bounding the "
             "depth of recursion that can be elided into one allocation. "
             "0 disables peeling."));

// Find the direct, coro_elide_safe self-call sites of F outside of loops. A
// frame slot elided for a call site inside a loop would be reused on every
// iteration while a coroutine from a prior iteration may still be live, so
// such sites are not peeled.
static SmallVector<CallBase *, 4> collectPeelSites(Function &F, LoopInfo &LI) {
  SmallVector<CallBase *, 4> Sites;
  for (Instruction &I : instructions(F)) {
    auto *CB = dyn_cast<CallBase>(&I);
    if (!CB || CB->getCalledFunction() != &F)
      continue;
    if (!CB->hasFnAttr(llvm::Attribute::CoroElideSafe))
      continue;
    if (LI.getLoopFor(CB->getParent()))
      continue;
    Sites.push_back(CB);
  }
  return Sites;
}

// Redirect a direct call to Root so that it goes through
// llvm.coro.recursion.anchor, hiding the call graph edge until CoroCleanup
// lowers the anchor back to a direct call.
static void anchorCallToRoot(CallBase *CB, Function *Root) {
  IRBuilder<> Builder(CB);
  CallInst *Anchor = Builder.CreateIntrinsicWithoutFolding(
      Intrinsic::coro_recursion_anchor, {Root});
  CB->setCalledOperand(Anchor);
  CB->removeFnAttr(llvm::Attribute::CoroElideSafe);
}

static void peelRecursiveCoroutine(Function &F, ArrayRef<CallBase *> Sites,
                                   unsigned Depth) {
  // Clone the chain F.peel.1 .. F.peel.Depth, using the value maps to locate
  // each copy's peel sites without rescanning.
  SmallVector<Function *, 8> Copies;
  SmallVector<SmallVector<CallBase *, 4>, 8> CopySites;
  for (unsigned I = 0; I != Depth; ++I) {
    ValueToValueMapTy VMap;
    Function *Copy = CloneFunction(&F, VMap);
    Copy->setName(F.getName() + ".peel." + Twine(I + 1));
    Copy->setLinkage(GlobalValue::InternalLinkage);
    SmallVector<CallBase *, 4> Mapped;
    for (CallBase *CB : Sites)
      Mapped.push_back(cast<CallBase>(VMap[CB]));
    Copies.push_back(Copy);
    CopySites.push_back(std::move(Mapped));
  }

  // Each copy's coroutine id must identify the copy itself, not F.
  for (Function *Copy : Copies)
    for (Instruction &I : instructions(*Copy))
      if (auto *II = dyn_cast<IntrinsicInst>(&I))
        if (II->getIntrinsicID() == Intrinsic::coro_id &&
            II->getArgOperand(2) == &F)
          II->setArgOperand(2, Copy);

  // Rewire the chain: F's peel sites call the first copy, each copy's peel
  // sites call the next copy, and the last copy's peel sites return to F
  // through the anchor.
  for (CallBase *CB : Sites)
    CB->setCalledFunction(Copies.front());
  for (unsigned I = 0; I + 1 != Depth; ++I)
    for (CallBase *CB : CopySites[I])
      CB->setCalledFunction(Copies[I + 1]);
  for (CallBase *CB : CopySites.back())
    anchorCallToRoot(CB, &F);

  // Self-call sites that were not eligible for peeling (inside loops, or not
  // elide-safe) still call F directly in every copy. Anchor them too: a
  // direct call back to F would merge the whole chain into F's SCC and
  // defeat the leaf-first processing the peel exists to create.
  for (Function *Copy : Copies)
    for (Instruction &I : instructions(*Copy))
      if (auto *CB = dyn_cast<CallBase>(&I))
        if (CB->getCalledFunction() == &F)
          anchorCallToRoot(CB, &F);
}

PreservedAnalyses CoroRecursionPeelPass::run(Module &M,
                                             ModuleAnalysisManager &MAM) {
  unsigned Depth = CoroRecursionPeelDepth;
  if (Depth == 0)
    return PreservedAnalyses::all();

  // Collect candidates before cloning mutates the function list.
  SmallVector<Function *, 4> Candidates;
  for (Function &F : M)
    if (!F.isDeclaration() && F.isPresplitCoroutine())
      Candidates.push_back(&F);
  if (Candidates.empty())
    return PreservedAnalyses::all();

  FunctionAnalysisManager &FAM =
      MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();

  bool Changed = false;
  for (Function *F : Candidates) {
    SmallVector<CallBase *, 4> Sites =
        collectPeelSites(*F, FAM.getResult<LoopAnalysis>(*F));
    if (Sites.empty())
      continue;
    peelRecursiveCoroutine(*F, Sites, Depth);
    Changed = true;
  }
  return Changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
}
