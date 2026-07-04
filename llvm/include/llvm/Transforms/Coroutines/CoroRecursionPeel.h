//===- CoroRecursionPeel.h - Peel recursive coroutines for elision -------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
// \file
// This file declares a module pass that peels self-recursive coroutines with
// coro_elide_safe self-call sites into an acyclic chain of clones, so that
// CoroAnnotationElide can elide a bounded depth of the recursion into a
// single block allocation.
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_COROUTINES_CORORECURSIONPEEL_H
#define LLVM_TRANSFORMS_COROUTINES_CORORECURSIONPEEL_H

#include "llvm/IR/PassManager.h"

namespace llvm {

struct CoroRecursionPeelPass : PassInfoMixin<CoroRecursionPeelPass> {
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM);
  static bool isRequired() { return false; }
};

} // end namespace llvm

#endif // LLVM_TRANSFORMS_COROUTINES_CORORECURSIONPEEL_H
