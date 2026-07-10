//===- Linearity.h ----------------------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// An intra-procedural analysis that enforces linear (use-exactly-once)
// semantics for values of class types marked with the [[clang::linear]]
// attribute. Every tracked local variable and temporary must be consumed
// exactly once on every control-flow path; consuming operations are moves,
// binding to rvalue-reference or by-value parameters, calls to member
// functions marked [[clang::linear_consumer]], and returning the value.
// Because argument binding consumes in the caller, by-value and
// rvalue-reference parameters of linear type carry the consumption
// obligation into the callee and are tracked from function entry.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_ANALYSIS_ANALYSES_LINEARITY_H
#define LLVM_CLANG_ANALYSIS_ANALYSES_LINEARITY_H

#include "clang/AST/Type.h"
#include "clang/Basic/SourceLocation.h"
#include "llvm/ADT/StringRef.h"

namespace clang {

class AnalysisDeclContext;
class Decl;

namespace linearity {

/// Receives the diagnostics produced by the linearity analysis.
/// In all callbacks an empty \p Name identifies a temporary object rather
/// than a named variable.
class LinearityWarningsHandlerBase {
public:
  virtual ~LinearityWarningsHandlerBase();

  /// Called once at the end of the analysis so the handler can emit the
  /// diagnostics it has collected, sorted by source location.
  virtual void emitDiagnostics() {}

  /// A linear object is destroyed (or reaches the end of the function)
  /// without ever having been consumed. \p IsParam is true when the object
  /// is a function parameter whose consumption obligation was received from
  /// the caller. \p IsDrain is true when the type is consumed by draining
  /// (it has a sentinel-mode linear_consumer member), which selects
  /// drain-specific diagnostic wording.
  virtual void warnNeverConsumed(SourceLocation Loc, StringRef Name,
                                 QualType Ty, SourceLocation CreatedLoc,
                                 bool IsParam, bool IsDrain) {}

  /// A linear object is destroyed but was only consumed on some of the
  /// control-flow paths that reach the destruction point.
  virtual void warnMaybeNotConsumed(SourceLocation Loc, StringRef Name,
                                    QualType Ty, SourceLocation ConsumedLoc,
                                    bool IsParam, bool IsDrain) {}

  /// A linear object is consumed (or otherwise used as a consumable value)
  /// after it has (\p Maybe: may have) already been consumed. This covers
  /// both double-consumption and use-after-move.
  virtual void warnUseAfterConsume(SourceLocation Loc, StringRef Name,
                                   QualType Ty, bool Maybe,
                                   SourceLocation ConsumedLoc) {}

  /// An assignment overwrites a linear value that has not been consumed.
  virtual void warnAssignDiscards(SourceLocation Loc, StringRef Name,
                                  QualType Ty, SourceLocation CreatedLoc) {}

  /// The consumption state of a variable differs between loop iterations.
  virtual void warnLoopStateMismatch(SourceLocation Loc, StringRef Name) {}

  /// A non-linear local object (e.g. a std::vector of tasks) into which a
  /// linear value was moved is destroyed without the value having been
  /// consumed.
  virtual void warnContainerNeverConsumed(SourceLocation Loc, StringRef Name,
                                          QualType ElemTy,
                                          SourceLocation TaintLoc) {}

  /// As warnContainerNeverConsumed, but the contents are consumed on only
  /// some of the control-flow paths reaching the destruction point.
  virtual void warnContainerMaybeNotConsumed(SourceLocation Loc,
                                             StringRef Name, QualType ElemTy,
                                             SourceLocation ConsumedLoc) {}

  /// A container's linear contents are handed to a consuming operation
  /// after they have (\p Maybe: may have) already been consumed.
  virtual void warnContainerUseAfterConsume(SourceLocation Loc, StringRef Name,
                                            bool Maybe,
                                            SourceLocation ConsumedLoc) {}
};

/// Quickly scans a function body for any mention of a type carrying the
/// [[clang::linear]] attribute. Used to gate both the CFG build options and
/// the analysis itself so that functions not using linear types pay no cost.
bool functionUsesLinearTypes(const Decl *D);

/// Check a function's CFG for violations of linear type semantics.
void runLinearityAnalysis(AnalysisDeclContext &AC,
                          LinearityWarningsHandlerBase &Handler);

} // namespace linearity
} // namespace clang

#endif // LLVM_CLANG_ANALYSIS_ANALYSES_LINEARITY_H
