//===- Linearity.cpp ------------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// An intra-procedural analysis enforcing linear (use-exactly-once) semantics
// for values of class types marked [[clang::linear]].
//
// The analysis tracks local variables and temporaries of linear type through
// the CFG. Each tracked object is in one of three states: Unconsumed,
// Consumed, or MaybeConsumed (consumed on some but not all incoming paths).
//
// An object is *consumed* by:
//   - binding it to an rvalue-reference parameter of any function call,
//   - passing it by value (which invokes its move/copy constructor),
//   - move/copy-constructing or move-assigning another object from it,
//   - calling a member function marked [[clang::linear_consumer]] with a
//     matching tag on it (this is how consuming operations that do not
//     syntactically move the object, e.g. `.detach()`, are modeled),
//   - returning it from the function.
//
// Because binding an argument to a by-value or rvalue-reference parameter
// consumes it in the caller, the callee inherits the consumption obligation:
// such parameters start the function in the Unconsumed state and must
// themselves be consumed on every path. Deliberate (lenient) exceptions:
// unnamed parameters (an explicit drop), const-qualified parameters (cannot
// be consumed at all), and member functions of the linear class itself
// (whose special members manipulate raw fields of other instances).
//
// std::move / std::forward and fluent member functions that return a
// reference to the same linear class are treated as transparent
// pass-throughs.
//
// Diagnostics:
//   - never consumed: reported at the object's destruction (dtor CFG
//     elements) or, for trivially-destructible linear types, at the CFG exit
//     block,
//   - consumed on only some paths,
//   - used after being consumed (double-consume / use-after-move),
//   - assignment overwriting an unconsumed value,
//   - consumption state mismatch between loop iterations.
//
//===----------------------------------------------------------------------===//

#include "clang/Analysis/Analyses/Linearity.h"
#include "clang/AST/Attr.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/ParentMap.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/Type.h"
#include "clang/Analysis/Analyses/PostOrderCFGView.h"
#include "clang/Analysis/AnalysisDeclContext.h"
#include "clang/Analysis/CFG.h"
#include "clang/Basic/Builtins.h"
#include "clang/Basic/LLVM.h"
#include "clang/Basic/OperatorKinds.h"
#include "clang/Basic/SourceLocation.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include <cassert>
#include <memory>
#include <optional>

using namespace clang;
using namespace linearity;

// Key method definition.
LinearityWarningsHandlerBase::~LinearityWarningsHandlerBase() = default;

//===----------------------------------------------------------------------===//
// Helpers
//===----------------------------------------------------------------------===//

/// Returns the LinearAttr of the class type \p QT, or null. Does not look
/// through references; callers strip those explicitly where appropriate.
static const LinearAttr *getLinearAttr(QualType QT) {
  if (QT.isNull())
    return nullptr;
  const CXXRecordDecl *RD = QT->getAsCXXRecordDecl();
  if (!RD)
    return nullptr;
  if (const LinearAttr *LA = RD->getAttr<LinearAttr>())
    return LA;
  // A class template specialization only receives the pattern's attributes
  // when it is instantiated, but a specialization can be named without ever
  // being completed (e.g. a do-nothing function taking Spec&&: neither the
  // reference parameter nor the empty body requires a complete type). Read
  // the attribute from the primary template's pattern so such parameters
  // are still armed.
  if (const auto *Spec = dyn_cast<ClassTemplateSpecializationDecl>(RD))
    if (!Spec->hasDefinition() &&
        Spec->getSpecializationKind() == TSK_Undeclared)
      if (const ClassTemplateDecl *CTD = Spec->getSpecializedTemplate())
        return CTD->getTemplatedDecl()->getAttr<LinearAttr>();
  return nullptr;
}

static bool isLinearType(QualType QT) { return getLinearAttr(QT) != nullptr; }

/// Does the consumer/producer attribute's tag match the linear tag of \p QT?
static bool linearTagMatches(StringRef Tag, QualType QT) {
  const LinearAttr *LA = getLinearAttr(QT.getNonReferenceType());
  return LA && LA->getTag() == Tag;
}

/// Strips parentheses and ExprWithCleanups wrappers; the canonical key for
/// the propagation map.
static const Expr *canonicalExpr(const Expr *E) {
  while (true) {
    E = E->IgnoreParens();
    if (const auto *EWC = dyn_cast<ExprWithCleanups>(E)) {
      E = EWC->getSubExpr();
      continue;
    }
    return E;
  }
}

static StringRef varName(const VarDecl *VD) {
  if (VD->getIdentifier())
    return VD->getName();
  return StringRef();
}

/// Is this call a transparent identity function (std::move and friends)?
static bool isPassThroughCall(const CallExpr *Call) {
  const FunctionDecl *FD = Call->getDirectCallee();
  if (!FD || Call->getNumArgs() != 1)
    return false;
  switch (FD->getBuiltinID()) {
  case Builtin::BImove:
  case Builtin::BImove_if_noexcept:
  case Builtin::BIforward:
  case Builtin::BIforward_like:
  case Builtin::BIas_const:
    return true;
  default:
    return false;
  }
}

/// Does \p Param transfer a consumption obligation into \p FD's body?
/// True for named, non-const parameters of linear type taken by value or by
/// rvalue reference: the caller-side rules treat binding an argument to such
/// a parameter as consumption, so the callee inherits the obligation.
/// Deliberate escape hatches (all lenient): an unnamed parameter is an
/// explicit drop, a const-qualified parameter cannot be consumed at all, and
/// member functions of the linear class itself (move constructor, move
/// assignment, ...) manipulate raw fields of other instances rather than
/// consuming them.
static bool paramRequiresConsumption(const FunctionDecl *FD,
                                     const ParmVarDecl *Param) {
  QualType Ty = Param->getType();
  if (Ty->isRValueReferenceType())
    Ty = Ty->getPointeeType();
  else if (Ty->isReferenceType())
    return false;
  if (Ty.isConstQualified() || !isLinearType(Ty))
    return false;
  // A parameter annotated [[clang::linear_consumer]] declares that the
  // obligation is discharged at this call boundary: the caller consumes the
  // argument at the call site, and the callee is trusted, not tracked. The
  // value's onward path (e.g. binding into a reference member of a wrapper
  // under construction) need not be provable to the analysis.
  if (const auto *CA = Param->getAttr<LinearConsumerAttr>())
    if (linearTagMatches(CA->getTag(), Ty))
      return false;
  if (!Param->getIdentifier())
    return false;
  if (const auto *MD = dyn_cast<CXXMethodDecl>(FD))
    if (const CXXRecordDecl *RD = Ty->getAsCXXRecordDecl())
      if (MD->getParent()->getCanonicalDecl() == RD->getCanonicalDecl())
        return false;
  return true;
}

static SourceLocation getLastStmtLoc(const CFGBlock *Block) {
  if (const Stmt *StmtNode = Block->getTerminatorStmt())
    return StmtNode->getBeginLoc();
  for (CFGBlock::const_reverse_iterator BI = Block->rbegin(), BE = Block->rend();
       BI != BE; ++BI)
    if (std::optional<CFGStmt> CS = BI->getAs<CFGStmt>())
      return CS->getStmt()->getBeginLoc();
  if (Block->pred_size() == 1 && *Block->pred_begin())
    return getLastStmtLoc(*Block->pred_begin());
  return {};
}

//===----------------------------------------------------------------------===//
// State tracking
//===----------------------------------------------------------------------===//

namespace {

struct LinearInfo {
  enum State : uint8_t {
    LS_Unconsumed,
    LS_Consumed,
    LS_MaybeConsumed,
  };

  State St = LS_Unconsumed;
  /// For LS_Unconsumed: where the value was created. For LS_Consumed and
  /// LS_MaybeConsumed: where it was consumed.
  SourceLocation Loc;

  LinearInfo() = default;
  LinearInfo(State St, SourceLocation Loc) : St(St), Loc(Loc) {}

  bool operator==(const LinearInfo &Other) const { return St == Other.St; }
};

/// The per-CFG-block map from tracked objects to their linear state.
class LinearStateMap {
public:
  using VarMapType = llvm::DenseMap<const VarDecl *, LinearInfo>;
  using TmpMapType = llvm::DenseMap<const CXXBindTemporaryExpr *, LinearInfo>;

  VarMapType VarMap;
  TmpMapType TmpMap;

  std::optional<LinearInfo> getState(const VarDecl *Var) const {
    auto It = VarMap.find(Var);
    if (It == VarMap.end())
      return std::nullopt;
    return It->second;
  }

  std::optional<LinearInfo> getState(const CXXBindTemporaryExpr *Tmp) const {
    auto It = TmpMap.find(Tmp);
    if (It == TmpMap.end())
      return std::nullopt;
    return It->second;
  }

  void setState(const VarDecl *Var, LinearInfo Info) { VarMap[Var] = Info; }
  void setState(const CXXBindTemporaryExpr *Tmp, LinearInfo Info) {
    TmpMap[Tmp] = Info;
  }

  void remove(const VarDecl *Var) { VarMap.erase(Var); }
  void remove(const CXXBindTemporaryExpr *Tmp) { TmpMap.erase(Tmp); }

  /// Merge with the state along another incoming edge. Objects consumed on
  /// one path but not the other become MaybeConsumed; objects tracked on only
  /// one path keep that path's state.
  void intersect(const LinearStateMap &Other) {
    mergeMap(VarMap, Other.VarMap);
    mergeMap(TmpMap, Other.TmpMap);
  }

  /// Merge the state flowing around a loop back-edge into the loop head's
  /// entry state, reporting variables whose state differs between iterations.
  void intersectAtLoopHead(const CFGBlock *LoopBack,
                           const LinearStateMap *LoopBackStates,
                           LinearityWarningsHandlerBase &Handler) {
    SourceLocation BlameLoc = getLastStmtLoc(LoopBack);
    for (const auto &Entry : LoopBackStates->VarMap) {
      auto It = VarMap.find(Entry.first);
      if (It == VarMap.end())
        continue;
      if (It->second.St != Entry.second.St) {
        Handler.warnLoopStateMismatch(BlameLoc, varName(Entry.first));
        It->second =
            LinearInfo(LinearInfo::LS_MaybeConsumed,
                       It->second.St == LinearInfo::LS_Unconsumed
                           ? Entry.second.Loc
                           : It->second.Loc);
      }
    }
  }

private:
  template <typename MapT> static void mergeMap(MapT &Dst, const MapT &Src) {
    for (const auto &Entry : Src) {
      auto It = Dst.find(Entry.first);
      if (It == Dst.end()) {
        Dst.insert(Entry);
        continue;
      }
      LinearInfo &L = It->second;
      const LinearInfo &R = Entry.second;
      if (L.St == R.St)
        continue;
      // States differ: the object is consumed on some paths only.
      SourceLocation ConsumeLoc =
          L.St == LinearInfo::LS_Unconsumed ? R.Loc : L.Loc;
      L = LinearInfo(LinearInfo::LS_MaybeConsumed, ConsumeLoc);
    }
  }
};

/// Worklist bookkeeping for the single reverse-post-order pass, mirroring
/// consumed::ConsumedBlockInfo.
class LinearBlockInfo {
  std::vector<std::unique_ptr<LinearStateMap>> StateMapsArray;
  std::vector<unsigned> VisitOrder;

public:
  LinearBlockInfo() = default;

  LinearBlockInfo(unsigned NumBlocks, PostOrderCFGView *SortedGraph)
      : StateMapsArray(NumBlocks), VisitOrder(NumBlocks, 0) {
    unsigned VisitOrderCounter = 0;
    for (const auto BI : *SortedGraph)
      VisitOrder[BI->getBlockID()] = VisitOrderCounter++;
  }

  bool allBackEdgesVisited(const CFGBlock *CurrBlock,
                           const CFGBlock *TargetBlock) const {
    unsigned CurrBlockOrder = VisitOrder[CurrBlock->getBlockID()];
    for (const CFGBlock *Pred : TargetBlock->preds())
      if (Pred && CurrBlockOrder < VisitOrder[Pred->getBlockID()])
        return false;
    return true;
  }

  void addInfo(const CFGBlock *Block, LinearStateMap *StateMap,
               std::unique_ptr<LinearStateMap> &OwnedStateMap) {
    assert(Block && "Block pointer must not be NULL");
    auto &Entry = StateMapsArray[Block->getBlockID()];
    if (Entry)
      Entry->intersect(*StateMap);
    else if (OwnedStateMap)
      Entry = std::move(OwnedStateMap);
    else
      Entry = std::make_unique<LinearStateMap>(*StateMap);
  }

  LinearStateMap *borrowInfo(const CFGBlock *Block) {
    assert(Block && "Block pointer must not be NULL");
    return StateMapsArray[Block->getBlockID()].get();
  }

  void discardInfo(const CFGBlock *Block) {
    StateMapsArray[Block->getBlockID()] = nullptr;
  }

  std::unique_ptr<LinearStateMap> getInfo(const CFGBlock *Block) {
    assert(Block && "Block pointer must not be NULL");
    auto &Entry = StateMapsArray[Block->getBlockID()];
    if (!Entry)
      return nullptr;
    return isBackEdgeTarget(Block) ? std::make_unique<LinearStateMap>(*Entry)
                                   : std::move(Entry);
  }

  bool isBackEdge(const CFGBlock *From, const CFGBlock *To) const {
    return VisitOrder[From->getBlockID()] > VisitOrder[To->getBlockID()];
  }

  bool isBackEdgeTarget(const CFGBlock *Block) const {
    if (Block->pred_size() < 2)
      return false;
    unsigned BlockVisitOrder = VisitOrder[Block->getBlockID()];
    for (const CFGBlock *Pred : Block->preds())
      if (Pred && BlockVisitOrder < VisitOrder[Pred->getBlockID()])
        return true;
    return false;
  }
};

//===----------------------------------------------------------------------===//
// Statement visitor
//===----------------------------------------------------------------------===//

/// What an already-visited expression evaluates to, for the purposes of
/// linear tracking.
class PropagationInfo {
public:
  enum Kind : uint8_t {
    PI_None,
    /// Refers to a tracked local variable.
    PI_Var,
    /// Refers to a tracked temporary.
    PI_Tmp,
    /// A freshly created linear prvalue not yet bound to a variable or
    /// temporary.
    PI_Fresh,
  };

private:
  Kind K = PI_None;
  /// For PI_Fresh: the value is known to be empty (default-constructed) and
  /// therefore does not require consumption.
  bool FreshEmpty = false;
  union {
    const VarDecl *Var;
    const CXXBindTemporaryExpr *Tmp;
  };

public:
  PropagationInfo() : Var(nullptr) {}
  static PropagationInfo makeVar(const VarDecl *VD) {
    PropagationInfo PI;
    PI.K = PI_Var;
    PI.Var = VD;
    return PI;
  }
  static PropagationInfo makeTmp(const CXXBindTemporaryExpr *BTE) {
    PropagationInfo PI;
    PI.K = PI_Tmp;
    PI.Tmp = BTE;
    return PI;
  }
  static PropagationInfo makeFresh(bool Empty) {
    PropagationInfo PI;
    PI.K = PI_Fresh;
    PI.FreshEmpty = Empty;
    return PI;
  }

  Kind getKind() const { return K; }
  bool isValid() const { return K != PI_None; }
  bool isVar() const { return K == PI_Var; }
  bool isTmp() const { return K == PI_Tmp; }
  bool isFresh() const { return K == PI_Fresh; }
  bool isTracked() const { return K == PI_Var || K == PI_Tmp; }
  bool isFreshEmpty() const { return K == PI_Fresh && FreshEmpty; }

  const VarDecl *getVar() const {
    assert(K == PI_Var);
    return Var;
  }
  const CXXBindTemporaryExpr *getTmp() const {
    assert(K == PI_Tmp);
    return Tmp;
  }
};

class LinearityStmtVisitor : public ConstStmtVisitor<LinearityStmtVisitor> {
  using MapType = llvm::DenseMap<const Stmt *, PropagationInfo>;

  LinearityWarningsHandlerBase &Handler;
  ParentMap &PM;
  LinearStateMap *StateMap;
  MapType PropagationMap;

public:
  LinearityStmtVisitor(LinearityWarningsHandlerBase &Handler, ParentMap &PM,
                       LinearStateMap *StateMap)
      : Handler(Handler), PM(PM), StateMap(StateMap) {}

  void reset(LinearStateMap *NewStateMap) { StateMap = NewStateMap; }

  //===--------------------------------------------------------------------===//
  // Propagation map plumbing
  //===--------------------------------------------------------------------===//

  PropagationInfo findInfo(const Expr *E) const {
    auto It = PropagationMap.find(canonicalExpr(E));
    if (It == PropagationMap.end())
      return {};
    return It->second;
  }

  void insertInfo(const Expr *E, PropagationInfo PI) {
    PropagationMap.insert({canonicalExpr(E), PI});
  }

  void forwardInfo(const Expr *From, const Expr *To) {
    PropagationInfo PI = findInfo(From);
    if (PI.isValid())
      insertInfo(To, PI);
  }

  //===--------------------------------------------------------------------===//
  // Consumption
  //===--------------------------------------------------------------------===//

  QualType trackedType(const PropagationInfo &PI) const {
    if (PI.isVar())
      return PI.getVar()->getType().getNonReferenceType();
    return PI.getTmp()->getType();
  }

  StringRef trackedName(const PropagationInfo &PI) const {
    if (PI.isVar())
      return varName(PI.getVar());
    return StringRef();
  }

  std::optional<LinearInfo> trackedState(const PropagationInfo &PI) const {
    if (PI.isVar())
      return StateMap->getState(PI.getVar());
    if (PI.isTmp())
      return StateMap->getState(PI.getTmp());
    return std::nullopt;
  }

  void setTrackedState(const PropagationInfo &PI, LinearInfo Info) {
    if (PI.isVar())
      StateMap->setState(PI.getVar(), Info);
    else if (PI.isTmp())
      StateMap->setState(PI.getTmp(), Info);
  }

  /// Consume a tracked object at \p Loc, diagnosing double-consumption.
  void consumeObject(const PropagationInfo &PI, SourceLocation Loc) {
    if (!PI.isTracked())
      return;
    std::optional<LinearInfo> Info = trackedState(PI);
    if (!Info)
      return;
    switch (Info->St) {
    case LinearInfo::LS_Unconsumed:
      setTrackedState(PI, LinearInfo(LinearInfo::LS_Consumed, Loc));
      break;
    case LinearInfo::LS_Consumed:
      Handler.warnUseAfterConsume(Loc, trackedName(PI), trackedType(PI),
                                  /*Maybe=*/false, Info->Loc);
      break;
    case LinearInfo::LS_MaybeConsumed:
      Handler.warnUseAfterConsume(Loc, trackedName(PI), trackedType(PI),
                                  /*Maybe=*/true, Info->Loc);
      // Definitely consumed from here on; avoids cascading reports.
      setTrackedState(PI, LinearInfo(LinearInfo::LS_Consumed, Loc));
      break;
    }
  }

  /// Consume the tracked object silently (ownership handed off in a way
  /// that is always correct, e.g. returning from the function).
  void consumeSilently(const PropagationInfo &PI, SourceLocation Loc) {
    if (!PI.isTracked())
      return;
    if (trackedState(PI))
      setTrackedState(PI, LinearInfo(LinearInfo::LS_Consumed, Loc));
  }

  /// If \p E refers to a local (non-reference) variable of linear type,
  /// return it as a trackable target, even if it is not currently tracked.
  /// Used to start tracking a variable when a value is stored into it
  /// (assignment, producer methods). By-value parameters qualify: they are
  /// tracked from function entry, and re-arming after consumption follows
  /// the same rules as for ordinary locals.
  PropagationInfo localVarTarget(const Expr *E) const {
    const auto *DRE = dyn_cast<DeclRefExpr>(canonicalExpr(E)->IgnoreImplicit());
    if (!DRE)
      return {};
    const auto *VD = dyn_cast<VarDecl>(DRE->getDecl());
    if (!VD || !VD->hasLocalStorage() ||
        VD->getType()->isReferenceType() || !isLinearType(VD->getType()))
      return {};
    return PropagationInfo::makeVar(VD);
  }

  /// Does binding an argument to \p Param consume it?
  bool paramConsumes(const ParmVarDecl *Param, const PropagationInfo &ArgPI) {
    if (const auto *CA = Param->getAttr<LinearConsumerAttr>())
      if (linearTagMatches(CA->getTag(), trackedType(ArgPI)))
        return true;
    QualType ParamTy = Param->getType();
    if (ParamTy->isRValueReferenceType())
      return true;
    // By-value of a linear type. (In practice the argument is wrapped in a
    // CXXConstructExpr which consumes it first; this is a fallback.)
    if (!ParamTy->isReferenceType() && isLinearType(ParamTy))
      return true;
    return false;
  }

  /// Common handling of function, method and operator calls: consume
  /// arguments per parameter rules, then handle the implicit object argument
  /// (consumer methods and fluent pass-throughs).
  void handleCall(const CallExpr *Call, const Expr *ObjArg,
                  const FunctionDecl *FunD) {
    unsigned Offset = 0;
    if (isa<CXXOperatorCallExpr>(Call) && isa<CXXMethodDecl>(FunD))
      Offset = 1; // first argument is 'this'

    for (unsigned Index = Offset; Index < Call->getNumArgs(); ++Index) {
      if (Index - Offset >= FunD->getNumParams())
        break;
      const Expr *Arg = Call->getArg(Index);
      PropagationInfo ArgPI = findInfo(Arg);
      if (!ArgPI.isTracked())
        continue;
      const ParmVarDecl *Param = FunD->getParamDecl(Index - Offset);
      if (paramConsumes(Param, ArgPI))
        consumeObject(ArgPI, Arg->getExprLoc());
    }

    if (!ObjArg)
      return;

    // A producer method re-arms the object: it now (again) holds a value
    // that must be consumed. Starts tracking untracked local variables.
    if (const auto *PA = FunD->getAttr<LinearProducerAttr>()) {
      PropagationInfo ObjPI = findInfo(ObjArg);
      if (!ObjPI.isTracked())
        ObjPI = localVarTarget(ObjArg);
      if (ObjPI.isTracked() &&
          linearTagMatches(PA->getTag(), trackedType(ObjPI))) {
        setTrackedState(ObjPI, LinearInfo(LinearInfo::LS_Unconsumed,
                                          Call->getExprLoc()));
        return;
      }
    }

    PropagationInfo ObjPI = findInfo(ObjArg);
    if (!ObjPI.isTracked())
      return;

    if (const auto *CA = FunD->getAttr<LinearConsumerAttr>()) {
      if (linearTagMatches(CA->getTag(), trackedType(ObjPI))) {
        consumeObject(ObjPI, Call->getExprLoc());
        return;
      }
    }

    // Fluent pass-through: a member function returning a reference to a
    // linear class (e.g. `spawn(...).run_on(ex)` returning `aw_spawn&&`)
    // propagates the tracked object to the call result.
    QualType RetTy = FunD->getReturnType();
    if (RetTy->isReferenceType() &&
        isLinearType(RetTy.getNonReferenceType()))
      insertInfo(Call, ObjPI);
  }

  /// Track the value produced by a call returning a linear type by value.
  void propagateReturnedValue(const Expr *Call, const FunctionDecl *FunD) {
    QualType RetTy = FunD->getReturnType();
    if (!RetTy->isReferenceType() && isLinearType(RetTy)) {
      insertInfo(Call, PropagationInfo::makeFresh(/*Empty=*/false));
      checkDiscardedFresh(Call);
    }
  }

  /// Report a fresh linear value produced in a discarded-value position.
  /// This catches dropped temporaries of trivially-destructible linear types,
  /// for which no CXXBindTemporaryExpr / temporary-dtor CFG elements exist.
  /// The walk deliberately stops at CXXBindTemporaryExpr: temporaries with
  /// destructors are diagnosed by the dtor-element path instead.
  void checkDiscardedFresh(const Expr *E) {
    const Stmt *S = E;
    while (true) {
      const Stmt *P = PM.getParent(S);
      if (!P)
        return;
      if (isa<ParenExpr>(P) || isa<ExprWithCleanups>(P)) {
        S = P;
        continue;
      }
      if (const auto *CE = dyn_cast<CastExpr>(P)) {
        if (CE->getCastKind() == CK_ToVoid) {
          S = P;
          continue;
        }
        return;
      }
      if (const auto *BO = dyn_cast<BinaryOperator>(P)) {
        if (BO->getOpcode() == BO_Comma && BO->getLHS() == S)
          break;
        return;
      }
      if (isa<CompoundStmt>(P))
        break;
      if (const auto *FS = dyn_cast<ForStmt>(P)) {
        if (FS->getInc() == S)
          break;
        return;
      }
      return;
    }
    Handler.warnNeverConsumed(E->getExprLoc(), StringRef(), E->getType(),
                              E->getExprLoc(), /*IsParam=*/false);
  }

  //===--------------------------------------------------------------------===//
  // Visitors
  //===--------------------------------------------------------------------===//

  void VisitCastExpr(const CastExpr *Cast) {
    forwardInfo(Cast->getSubExpr(), Cast);
  }

  void VisitMaterializeTemporaryExpr(const MaterializeTemporaryExpr *Temp) {
    forwardInfo(Temp->getSubExpr(), Temp);
  }

  void VisitOpaqueValueExpr(const OpaqueValueExpr *OVE) {
    if (const Expr *Src = OVE->getSourceExpr())
      forwardInfo(Src, OVE);
  }

  /// Stop tracking an object whose ownership escapes the analysis (its
  /// address is taken, or it is moved into an untracked aggregate).
  void escapeObject(const PropagationInfo &PI) {
    if (PI.isVar())
      StateMap->remove(PI.getVar());
    else if (PI.isTmp())
      StateMap->remove(PI.getTmp());
  }

  void VisitInitListExpr(const InitListExpr *ILE) {
    if (ILE->getNumInits() == 1 && isLinearType(ILE->getType())) {
      forwardInfo(ILE->getInit(0), ILE);
      return;
    }
    // Linear values initializing the elements of an aggregate (e.g. an array
    // of tasks) escape: ownership now lives in the untracked aggregate.
    for (const Expr *Init : ILE->inits())
      if (Init)
        escapeObject(findInfo(Init));
  }

  void VisitUnaryOperator(const UnaryOperator *UO) {
    // Taking the address of a linear object escapes it: it may be consumed
    // through the pointer (e.g. an iterator passed to a spawn_many() group).
    if (UO->getOpcode() == UO_AddrOf)
      escapeObject(findInfo(UO->getSubExpr()));
  }

  void VisitDeclRefExpr(const DeclRefExpr *DeclRef) {
    if (const auto *Var = dyn_cast_or_null<VarDecl>(DeclRef->getDecl()))
      if (StateMap->getState(Var))
        insertInfo(DeclRef, PropagationInfo::makeVar(Var));
  }

  void VisitCXXBindTemporaryExpr(const CXXBindTemporaryExpr *Temp) {
    PropagationInfo SubPI = findInfo(Temp->getSubExpr());
    if (SubPI.isFresh()) {
      StateMap->setState(Temp, LinearInfo(SubPI.isFreshEmpty()
                                              ? LinearInfo::LS_Consumed
                                              : LinearInfo::LS_Unconsumed,
                                          Temp->getExprLoc()));
      insertInfo(Temp, PropagationInfo::makeTmp(Temp));
    } else if (SubPI.isTracked()) {
      insertInfo(Temp, SubPI);
    } else if (isLinearType(Temp->getType())) {
      // A linear temporary produced by an expression we could not see
      // through. Conservatively treat it as a fresh unconsumed value.
      StateMap->setState(
          Temp, LinearInfo(LinearInfo::LS_Unconsumed, Temp->getExprLoc()));
      insertInfo(Temp, PropagationInfo::makeTmp(Temp));
    }
  }

  void VisitCallExpr(const CallExpr *Call) {
    if (isPassThroughCall(Call)) {
      forwardInfo(Call->getArg(0), Call);
      return;
    }
    const FunctionDecl *FunD = Call->getDirectCallee();
    if (!FunD)
      return;
    handleCall(Call, nullptr, FunD);
    propagateReturnedValue(Call, FunD);
  }

  void VisitCXXMemberCallExpr(const CXXMemberCallExpr *Call) {
    const CXXMethodDecl *MD = Call->getMethodDecl();
    if (!MD)
      return;
    handleCall(Call, Call->getImplicitObjectArgument(), MD);
    propagateReturnedValue(Call, MD);
  }

  void VisitCXXOperatorCallExpr(const CXXOperatorCallExpr *Call) {
    const auto *FunD = dyn_cast_or_null<FunctionDecl>(Call->getDirectCallee());
    if (!FunD)
      return;

    if (Call->getOperator() == OO_Equal && isa<CXXMethodDecl>(FunD) &&
        Call->getNumArgs() == 2) {
      handleAssignment(Call, FunD);
      return;
    }

    const Expr *ObjArg = nullptr;
    if (isa<CXXMethodDecl>(FunD) &&
        cast<CXXMethodDecl>(FunD)->isInstance() && Call->getNumArgs() >= 1)
      ObjArg = Call->getArg(0);
    handleCall(Call, ObjArg, FunD);
    propagateReturnedValue(Call, FunD);
  }

  void handleAssignment(const CXXOperatorCallExpr *Call,
                        const FunctionDecl *FunD) {
    const Expr *LHS = Call->getArg(0);
    const Expr *RHS = Call->getArg(1);

    // Consume the RHS if the assignment takes it by rvalue reference or by
    // value (move-assignment and friends).
    PropagationInfo RHSPI = findInfo(RHS);
    if (RHSPI.isTracked() && FunD->getNumParams() >= 1 &&
        paramConsumes(FunD->getParamDecl(0), RHSPI))
      consumeObject(RHSPI, RHS->getExprLoc());

    // The LHS now holds whatever the RHS held. A default-constructed (empty)
    // RHS leaves the LHS not requiring consumption.
    LinearInfo::State NewSt = RHSPI.isFreshEmpty() ? LinearInfo::LS_Consumed
                                                   : LinearInfo::LS_Unconsumed;

    PropagationInfo LHSPI = findInfo(LHS);
    if (!LHSPI.isTracked()) {
      // Assigning a real value into an untracked local linear variable (e.g.
      // one that was default-constructed) starts tracking it.
      LHSPI = localVarTarget(LHS);
      if (!LHSPI.isTracked())
        return;
    } else {
      std::optional<LinearInfo> Cur = trackedState(LHSPI);
      if (Cur && Cur->St == LinearInfo::LS_Unconsumed)
        Handler.warnAssignDiscards(Call->getExprLoc(), trackedName(LHSPI),
                                   trackedType(LHSPI), Cur->Loc);
    }

    setTrackedState(LHSPI, LinearInfo(NewSt, Call->getExprLoc()));
    // The result of the assignment expression refers to the LHS.
    insertInfo(Call, LHSPI);
  }

  void VisitCXXConstructExpr(const CXXConstructExpr *Call) {
    const CXXConstructorDecl *Constructor = Call->getConstructor();
    QualType ThisType = Constructor->getFunctionObjectParameterType();
    bool Linear = isLinearType(ThisType);

    if (Linear && Constructor->isDefaultConstructor()) {
      insertInfo(Call, PropagationInfo::makeFresh(/*Empty=*/true));
      return;
    }

    if (Linear && Call->getNumArgs() >= 1 &&
        (Constructor->isMoveConstructor() ||
         Constructor->isCopyConstructor())) {
      // Initializing a new linear object from an existing one consumes the
      // source; for a copyable linear type a copy still transfers the
      // consumption obligation (both copies awaiting would double-run).
      PropagationInfo ArgPI = findInfo(Call->getArg(0));
      consumeObject(ArgPI, Call->getExprLoc());
      insertInfo(Call, PropagationInfo::makeFresh(/*Empty=*/false));
      return;
    }

    // Any other constructor: consume linear arguments per parameter rules
    // (e.g. a wrapper constructed from `task&&`).
    for (unsigned Index = 0; Index < Call->getNumArgs(); ++Index) {
      if (Index >= Constructor->getNumParams())
        break;
      const Expr *Arg = Call->getArg(Index);
      PropagationInfo ArgPI = findInfo(Arg);
      if (!ArgPI.isTracked())
        continue;
      if (paramConsumes(Constructor->getParamDecl(Index), ArgPI))
        consumeObject(ArgPI, Arg->getExprLoc());
    }
    if (Linear)
      insertInfo(Call, PropagationInfo::makeFresh(/*Empty=*/false));
  }

  void VisitDeclStmt(const DeclStmt *DeclS) {
    for (const auto *DI : DeclS->decls())
      if (const auto *Var = dyn_cast<VarDecl>(DI))
        handleVarDecl(Var);
  }

  void handleVarDecl(const VarDecl *Var) {
    QualType VarTy = Var->getType();

    if (VarTy->isReferenceType()) {
      // A reference bound to a tracked temporary takes over ownership (e.g.
      // `auto&& f = spawn(t); ... co_await std::move(f);`). References to
      // tracked variables do not transfer ownership.
      if (!Var->hasInit())
        return;
      PropagationInfo InitPI = findInfo(Var->getInit());
      if (InitPI.isTmp() && isLinearType(VarTy.getNonReferenceType())) {
        std::optional<LinearInfo> TmpInfo = StateMap->getState(InitPI.getTmp());
        if (TmpInfo) {
          StateMap->remove(InitPI.getTmp());
          if (TmpInfo->St == LinearInfo::LS_Unconsumed)
            TmpInfo->Loc = Var->getLocation();
          StateMap->setState(Var, *TmpInfo);
        }
      }
      return;
    }

    if (!isLinearType(VarTy))
      return;

    LinearInfo Info(LinearInfo::LS_Unconsumed, Var->getLocation());
    if (Var->hasInit()) {
      PropagationInfo InitPI = findInfo(Var->getInit());
      if (InitPI.isFreshEmpty()) {
        // A default-constructed linear object is empty: it carries no
        // consumption obligation, and the analysis cannot see it being
        // re-armed through direct member writes (e.g. factory functions that
        // assign into a handle field), so do not track it at all. Tracking
        // starts if a real value is later assigned into it.
        return;
      } else if (InitPI.isTmp()) {
        // Copy elision: the temporary *is* the variable now.
        if (std::optional<LinearInfo> TmpInfo =
                StateMap->getState(InitPI.getTmp())) {
          Info = *TmpInfo;
          if (Info.St == LinearInfo::LS_Unconsumed)
            Info.Loc = Var->getLocation();
          StateMap->remove(InitPI.getTmp());
        }
      }
      // PI_Fresh (non-empty) and untraceable initializers are treated as a
      // fresh unconsumed value.
    }
    StateMap->setState(Var, Info);
  }

  void VisitReturnStmt(const ReturnStmt *Ret) {
    // Returning a linear value transfers the consumption obligation to the
    // caller.
    if (const Expr *RetVal = Ret->getRetValue())
      consumeSilently(findInfo(RetVal), Ret->getReturnLoc());
  }

  void VisitCoroutineSuspendExpr(const CoroutineSuspendExpr *E) {
    // The operand is consumed via the await_transform / operator co_await
    // calls that are linearized separately in the CFG. The co_await
    // expression's own value is whatever await_resume() returned; forward it
    // so that a linear value produced by co_await is tracked.
    if (const Expr *Resume = E->getResumeExpr()) {
      PropagationInfo PI = findInfo(Resume);
      if (PI.isValid()) {
        insertInfo(E, PI);
        if (PI.isFresh() && !PI.isFreshEmpty())
          checkDiscardedFresh(E);
      }
    }
  }

  void VisitCoawaitExpr(const CoawaitExpr *E) { VisitCoroutineSuspendExpr(E); }
  void VisitCoyieldExpr(const CoyieldExpr *E) { VisitCoroutineSuspendExpr(E); }

  /// A constructor initializing a reference member from a tracked object
  /// escapes it: ownership is handed to whoever later consumes through the
  /// reference. (E.g. wrapper awaitables whose type parameter is deduced as
  /// an rvalue reference store the reference in a member and consume through
  /// it in await_suspend.) Non-reference members need no handling here: the
  /// member's constructor is linearized as its own CFG element and consumes
  /// per the usual rules.
  void handleCtorInitializer(const CXXCtorInitializer *CI) {
    if (!CI->isAnyMemberInitializer())
      return;
    if (!CI->getAnyMember()->getType()->isReferenceType())
      return;
    if (const Expr *Init = CI->getInit())
      escapeObject(findInfo(Init));
  }

  //===--------------------------------------------------------------------===//
  // Object death
  //===--------------------------------------------------------------------===//

  void checkAtDeath(const PropagationInfo &PI, SourceLocation Loc) {
    std::optional<LinearInfo> Info = trackedState(PI);
    if (!Info)
      return;
    bool IsParam = PI.isVar() && isa<ParmVarDecl>(PI.getVar());
    switch (Info->St) {
    case LinearInfo::LS_Unconsumed:
      Handler.warnNeverConsumed(Loc, trackedName(PI), trackedType(PI),
                                Info->Loc, IsParam);
      break;
    case LinearInfo::LS_MaybeConsumed:
      Handler.warnMaybeNotConsumed(Loc, trackedName(PI), trackedType(PI),
                                   Info->Loc, IsParam);
      break;
    case LinearInfo::LS_Consumed:
      break;
    }
    if (PI.isVar())
      StateMap->remove(PI.getVar());
    else
      StateMap->remove(PI.getTmp());
  }
};

//===----------------------------------------------------------------------===//
// Analyzer
//===----------------------------------------------------------------------===//

class LinearityAnalyzer {
  LinearityWarningsHandlerBase &Handler;
  LinearBlockInfo BlockInfo;
  std::unique_ptr<LinearStateMap> CurrStates;

public:
  LinearityAnalyzer(LinearityWarningsHandlerBase &Handler)
      : Handler(Handler) {}

  void run(AnalysisDeclContext &AC) {
    const auto *D = dyn_cast_or_null<FunctionDecl>(AC.getDecl());
    if (!D)
      return;
    CFG *CFGraph = AC.getCFG();
    if (!CFGraph)
      return;

    PostOrderCFGView *SortedGraph = AC.getAnalysis<PostOrderCFGView>();
    if (!SortedGraph)
      return;

    BlockInfo = LinearBlockInfo(CFGraph->getNumBlockIDs(), SortedGraph);
    CurrStates = std::make_unique<LinearStateMap>();

    // Parameters received by value or by rvalue reference were consumed in
    // the caller by the call expression itself; the consumption obligation
    // transfers to this function. Arm them at entry.
    for (const ParmVarDecl *Param : D->parameters())
      if (paramRequiresConsumption(D, Param))
        CurrStates->setState(
            Param, LinearInfo(LinearInfo::LS_Unconsumed, Param->getLocation()));

    LinearityStmtVisitor Visitor(Handler, AC.getParentMap(),
                                 CurrStates.get());

    for (const CFGBlock *CurrBlock : *SortedGraph) {
      if (!CurrStates)
        CurrStates = BlockInfo.getInfo(CurrBlock);
      if (!CurrStates)
        continue;

      Visitor.reset(CurrStates.get());

      for (const auto &B : *CurrBlock) {
        switch (B.getKind()) {
        case CFGElement::Statement:
        case CFGElement::Constructor:
        case CFGElement::CXXRecordTypedCall:
          Visitor.Visit(B.castAs<CFGStmt>().getStmt());
          break;

        case CFGElement::Initializer:
          Visitor.handleCtorInitializer(
              B.castAs<CFGInitializer>().getInitializer());
          break;

        case CFGElement::TemporaryDtor: {
          const CFGTemporaryDtor &DTor = B.castAs<CFGTemporaryDtor>();
          const CXXBindTemporaryExpr *BTE = DTor.getBindTemporaryExpr();
          Visitor.checkAtDeath(PropagationInfo::makeTmp(BTE),
                               BTE->getExprLoc());
          break;
        }

        case CFGElement::AutomaticObjectDtor: {
          const CFGAutomaticObjDtor &DTor = B.castAs<CFGAutomaticObjDtor>();
          const VarDecl *Var = DTor.getVarDecl();
          SourceLocation Loc;
          if (const Stmt *Trigger = DTor.getTriggerStmt())
            Loc = Trigger->getEndLoc();
          if (Loc.isInvalid())
            Loc = Var->getLocation();
          Visitor.checkAtDeath(PropagationInfo::makeVar(Var), Loc);
          break;
        }

        default:
          break;
        }
      }

      // A block containing a no-return call (assert failure handler,
      // std::abort, ...) jumps straight to the exit block in the CFG, but
      // the program terminates on that path: tracked objects are not leaked
      // there. Do not let its state flow into the exit merge, where it would
      // demote values consumed on all returning paths to MaybeConsumed.
      if (CurrBlock->hasNoReturnElement()) {
        CurrStates = nullptr;
        continue;
      }

      // At the exit block, report any tracked object that is still (maybe)
      // unconsumed. This catches linear types with trivial destructors, for
      // which no dtor CFG elements exist.
      if (CurrBlock == &CFGraph->getExit())
        sweepAtExit();

      // Propagate state to successors.
      if (CurrBlock->succ_size() > 1 ||
          (CurrBlock->succ_size() == 1 &&
           (*CurrBlock->succ_begin())->pred_size() > 1)) {
        LinearStateMap *RawState = CurrStates.get();
        for (CFGBlock::const_succ_iterator SI = CurrBlock->succ_begin(),
                                           SE = CurrBlock->succ_end();
             SI != SE; ++SI) {
          if (*SI == nullptr)
            continue;
          if (BlockInfo.isBackEdge(CurrBlock, *SI)) {
            if (LinearStateMap *HeadState = BlockInfo.borrowInfo(*SI)) {
              HeadState->intersectAtLoopHead(CurrBlock, RawState, Handler);
              if (BlockInfo.allBackEdgesVisited(CurrBlock, *SI))
                BlockInfo.discardInfo(*SI);
            }
          } else {
            BlockInfo.addInfo(*SI, RawState, CurrStates);
          }
        }
        CurrStates = nullptr;
      }
      // Otherwise: single successor that has a single predecessor. Reverse
      // post-order visits it next, so keep CurrStates for it.
    }

    CurrStates = nullptr;
    Handler.emitDiagnostics();
  }

private:
  void sweepAtExit() {
    for (const auto &Entry : CurrStates->VarMap) {
      const VarDecl *Var = Entry.first;
      const LinearInfo &Info = Entry.second;
      bool IsParam = isa<ParmVarDecl>(Var);
      QualType Ty = Var->getType().getNonReferenceType();
      if (Info.St == LinearInfo::LS_Unconsumed)
        Handler.warnNeverConsumed(Var->getLocation(), varName(Var), Ty,
                                  Info.Loc, IsParam);
      else if (Info.St == LinearInfo::LS_MaybeConsumed)
        Handler.warnMaybeNotConsumed(Var->getLocation(), varName(Var), Ty,
                                     Info.Loc, IsParam);
    }
    for (const auto &Entry : CurrStates->TmpMap) {
      const CXXBindTemporaryExpr *Tmp = Entry.first;
      const LinearInfo &Info = Entry.second;
      if (Info.St == LinearInfo::LS_Unconsumed)
        Handler.warnNeverConsumed(Tmp->getExprLoc(), StringRef(),
                                  Tmp->getType(), Info.Loc, /*IsParam=*/false);
      else if (Info.St == LinearInfo::LS_MaybeConsumed)
        Handler.warnMaybeNotConsumed(Tmp->getExprLoc(), StringRef(),
                                     Tmp->getType(), Info.Loc,
                                     /*IsParam=*/false);
    }
  }
};

} // anonymous namespace

//===----------------------------------------------------------------------===//
// Entry points
//===----------------------------------------------------------------------===//

bool clang::linearity::functionUsesLinearTypes(const Decl *D) {
  const Stmt *Body = D->getBody();
  if (!Body)
    return false;

  // A parameter carrying a consumption obligation makes the function worth
  // analyzing even if the body never mentions a linear type (e.g. an empty
  // body that leaks the parameter).
  if (const auto *FD = dyn_cast<FunctionDecl>(D))
    for (const ParmVarDecl *Param : FD->parameters())
      if (paramRequiresConsumption(FD, Param))
        return true;

  SmallVector<const Stmt *, 32> Worklist;
  Worklist.push_back(Body);
  while (!Worklist.empty()) {
    const Stmt *S = Worklist.pop_back_val();
    if (!S)
      continue;
    if (const auto *E = dyn_cast<Expr>(S)) {
      // Note: some expressions (e.g. syntactic InitListExpr forms) legally
      // have a null type.
      QualType T = E->getType();
      if (!T.isNull() && isLinearType(T.getNonReferenceType()))
        return true;
    } else if (const auto *DS = dyn_cast<DeclStmt>(S)) {
      for (const auto *DI : DS->decls()) {
        if (const auto *VD = dyn_cast<VarDecl>(DI)) {
          QualType T = VD->getType();
          if (!T.isNull() && isLinearType(T.getNonReferenceType()))
            return true;
        }
      }
    }
    for (const Stmt *Child : S->children())
      Worklist.push_back(Child);
  }
  return false;
}

void clang::linearity::runLinearityAnalysis(
    AnalysisDeclContext &AC, LinearityWarningsHandlerBase &Handler) {
  LinearityAnalyzer Analyzer(Handler);
  Analyzer.run(AC);
}
