//===- CoroRecursiveElide.h - Elide recursive coroutine frames -----------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
// \file
// Two cooperating module passes that let coro_elide_safe elision apply to
// recursive coroutines by specializing bounded blocks of the recursion tree,
// sized by the elision frame-size limits.
//
// CoroRecursionStashPass runs early (before the CGSCC pipeline) and stashes a
// presplit template clone of every coroutine on a recursive cycle whose
// cycle call sites are elide-safe. CoroRecursiveElidePass runs after the
// CGSCC pipeline, when real frame sizes exist, and grows specialized
// "generations" from the templates until the frame-size limit stops further
// nesting, then republishes the top generation under the original symbol.
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_COROUTINES_CORORECURSIVEELIDE_H
#define LLVM_TRANSFORMS_COROUTINES_CORORECURSIVEELIDE_H

#include "llvm/IR/PassManager.h"

namespace llvm {

struct CoroRecursionStashPass : PassInfoMixin<CoroRecursionStashPass> {
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM);
  static bool isRequired() { return false; }
};

struct CoroRecursiveElidePass : PassInfoMixin<CoroRecursiveElidePass> {
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM);
  static bool isRequired() { return false; }
};

} // end namespace llvm

#endif // LLVM_TRANSFORMS_COROUTINES_CORORECURSIVEELIDE_H
