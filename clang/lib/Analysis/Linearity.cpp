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
// Conditional consumption: a consumer annotated
// [[clang::linear_consumer("tag", conditional)]] consumes only if the call
// returns true (e.g. posting to a channel that may already be closed). The
// bound arguments are parked MaybeConsumed at the call; when the call's
// boolean result reaches a branch terminator — directly, through logical
// negations, comparisons against bool constants (`== false`, `!= true`),
// or through a local bool variable initialized with it — the
// state is split per edge: Consumed where the call returned true, the
// original Unconsumed state where it returned false. A result that is never
// tested leaves the value MaybeConsumed, so dropping it is diagnosed at its
// death; the caller must branch on the result (or otherwise consume the
// value) to prove the failure path handled.
//
// Container taint: moving a linear value into a non-linear local object
// through an *unannotated* rvalue-reference or by-value parameter of a
// member call (vec.push_back(std::move(t))) consumes the value but leaves
// the obligation inside the object. Such objects are tracked as "tainted":
// they must be consumed by passing them (or an iterator/pointer obtained
// from them) to a parameter marked [[clang::linear_consumer]] with the
// element's tag. Any use the analysis does not recognize (an unannotated
// function taking the container by reference, a range-for drain, an unknown
// member call such as clear() or size()) leniently ends the tracking with
// no diagnostic. Parameters annotated linear_consumer never taint: the
// annotation declares the obligation fully discharged at the boundary.
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

/// Returns the LinearAttr governing the elements of a "container of linear
/// values": a non-linear class type with a template argument that is (or
/// recursively contains, up to depth 2) a linear type. This is deliberately
/// structural rather than name-based; it covers std::vector<task>,
/// std::array<task, N>, std::optional<task>, containers of containers, ...
static const LinearAttr *getLinearElementAttr(QualType QT, unsigned Depth = 0) {
  if (QT.isNull() || Depth > 2)
    return nullptr;
  const CXXRecordDecl *RD = QT->getAsCXXRecordDecl();
  if (!RD || RD->hasAttr<LinearAttr>())
    return nullptr;
  const auto *Spec = dyn_cast<ClassTemplateSpecializationDecl>(RD);
  if (!Spec)
    return nullptr;
  auto CheckTypeArg = [Depth](QualType ArgTy) -> const LinearAttr * {
    ArgTy = ArgTy.getNonReferenceType();
    // Look through pointers so that detection does not depend on how a
    // standard library spells its handle types: libc++'s vector iterator is
    // __wrap_iter<task*> (only a pointer argument), while libstdc++'s is
    // __normal_iterator<task*, vector<task>>.
    while (ArgTy->isPointerType())
      ArgTy = ArgTy->getPointeeType();
    if (const LinearAttr *LA = getLinearAttr(ArgTy))
      return LA;
    return getLinearElementAttr(ArgTy, Depth + 1);
  };
  for (const TemplateArgument &Arg : Spec->getTemplateArgs().asArray()) {
    if (Arg.getKind() == TemplateArgument::Type) {
      if (const LinearAttr *LA = CheckTypeArg(Arg.getAsType()))
        return LA;
    } else if (Arg.getKind() == TemplateArgument::Pack) {
      // Pack-templated containers: std::tuple<task>, std::variant<task, E>.
      for (const TemplateArgument &Elem : Arg.pack_elements())
        if (Elem.getKind() == TemplateArgument::Type)
          if (const LinearAttr *LA = CheckTypeArg(Elem.getAsType()))
            return LA;
    }
  }
  return nullptr;
}

/// Is this class type iterator-like, i.e. does it declare an operator*?
/// Used to decide whether a member call returning a class object hands out
/// access to a tainted container's elements (begin()) or is unrelated.
static bool typeHasStarOperator(QualType QT) {
  const CXXRecordDecl *RD = QT->getAsCXXRecordDecl();
  if (!RD || !RD->hasDefinition())
    return false;
  DeclarationName Name =
      RD->getASTContext().DeclarationNames.getCXXOperatorName(OO_Star);
  if (!RD->lookup(Name).empty())
    return true;
  for (const CXXBaseSpecifier &Base : RD->bases())
    if (const CXXRecordDecl *BRD = Base.getType()->getAsCXXRecordDecl())
      if (BRD->hasDefinition() && !BRD->lookup(Name).empty())
        return true;
  return false;
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

/// Strips everything a boolean value passes through unchanged on its way
/// from a call to a branch condition: parentheses, implicit casts, and
/// ExprWithCleanups. (Negations are handled by the caller, which must count
/// them.)
static const Expr *stripCondWrappers(const Expr *E) {
  while (true) {
    const Expr *Prev = E;
    E = E->IgnoreParenImpCasts();
    if (const auto *EWC = dyn_cast<ExprWithCleanups>(E))
      E = EWC->getSubExpr();
    if (E == Prev)
      return E;
  }
}

/// Is this terminator a two-successor branch whose first successor is taken
/// when the condition is true? (Not the case for e.g. a switch on a bool,
/// whose successors are case blocks in case order.)
static bool isBoolBranchTerminator(const Stmt *Term) {
  if (!Term)
    return false;
  switch (Term->getStmtClass()) {
  case Stmt::IfStmtClass:
  case Stmt::WhileStmtClass:
  case Stmt::DoStmtClass:
  case Stmt::ForStmtClass:
  case Stmt::ConditionalOperatorClass:
  case Stmt::BinaryConditionalOperatorClass:
  case Stmt::BinaryOperatorClass: // && and ||
    return true;
  default:
    return false;
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

/// How binding an argument of type \p ArgTy to \p Param consumes it, if it
/// does. Annotated consumption is a trusted boundary (the obligation is
/// fully discharged there); structural consumption (an unannotated
/// rvalue-reference or by-value binding) moves the obligation onward — into
/// the callee, or into the object a member call was invoked on.
/// AnnotatedConditional is the trusted boundary of a consumer marked
/// `conditional`: the argument is consumed only if the call returns true.
enum class ConsumeKind : uint8_t {
  None,
  Annotated,
  AnnotatedConditional,
  Structural
};

static ConsumeKind paramConsumeKind(const ParmVarDecl *Param, QualType ArgTy) {
  if (const auto *CA = Param->getAttr<LinearConsumerAttr>())
    if (linearTagMatches(CA->getTag(), ArgTy))
      return CA->getMode() == LinearConsumerAttr::Conditional
                 ? ConsumeKind::AnnotatedConditional
                 : ConsumeKind::Annotated;
  QualType ParamTy = Param->getType();
  if (ParamTy->isRValueReferenceType())
    return ConsumeKind::Structural;
  // By-value of a linear type. (In practice the argument is wrapped in a
  // CXXConstructExpr which consumes it first; this is a fallback.)
  if (!ParamTy->isReferenceType() && isLinearType(ParamTy))
    return ConsumeKind::Structural;
  return ConsumeKind::None;
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

/// State of a non-linear local object holding linear content ("tainted
/// container"). The state field has the same meaning as for linear objects:
/// Unconsumed = holds content that must still be consumed.
struct ContainerInfo {
  LinearInfo::State St = LinearInfo::LS_Unconsumed;
  /// For LS_Unconsumed: where content was first moved in. Otherwise: where
  /// the content was consumed.
  SourceLocation Loc;
  /// The linear tag of the contained element type; consumer-annotated
  /// parameters must match it.
  StringRef Tag;
  /// The contained linear type, for diagnostics.
  QualType ElemTy;
};

/// A tracked object parked by a conditional-consumer call, together with the
/// state it had before the call so the returns-false edge can restore it.
struct CondParkedObject {
  /// PI_Var or PI_Tmp; stored as the raw pointers to avoid a dependency on
  /// PropagationInfo's declaration order.
  const VarDecl *Var = nullptr;
  const CXXBindTemporaryExpr *Tmp = nullptr;
  LinearInfo Orig;
};

/// The effect of one conditional-consumer call: its arguments are consumed
/// iff the call returned true. Recorded when the call is visited and applied
/// when its boolean result reaches a branch terminator.
struct CondConsumeInfo {
  SmallVector<CondParkedObject, 1> Objects;
  /// Fresh temporaries of trivially-destructible linear types bound to the
  /// call's conditional-consumer parameters. They have no tracked identity
  /// (no CXXBindTemporaryExpr exists), and no handle a failure branch could
  /// recover, so they are reported at the end of the analysis unless the
  /// call's result is explicitly discharged — mirroring the maybe-unconsumed
  /// report their non-trivial counterparts get at the temporary's dtor.
  SmallVector<std::pair<SourceLocation, QualType>, 1> FreshTemps;
  SourceLocation CallLoc;
};

/// The per-CFG-block map from tracked objects to their linear state.
class LinearStateMap {
public:
  using VarMapType = llvm::DenseMap<const VarDecl *, LinearInfo>;
  using TmpMapType = llvm::DenseMap<const CXXBindTemporaryExpr *, LinearInfo>;
  using ContainerMapType = llvm::DenseMap<const VarDecl *, ContainerInfo>;

  VarMapType VarMap;
  TmpMapType TmpMap;
  ContainerMapType ContainerMap;

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

  const ContainerInfo *getContainerState(const VarDecl *Var) const {
    auto It = ContainerMap.find(Var);
    return It == ContainerMap.end() ? nullptr : &It->second;
  }

  /// Merge with the state along another incoming edge. Objects consumed on
  /// one path but not the other become MaybeConsumed; objects tracked on only
  /// one path keep that path's state.
  void intersect(const LinearStateMap &Other) {
    mergeMap(VarMap, Other.VarMap);
    mergeMap(TmpMap, Other.TmpMap);
    for (const auto &Entry : Other.ContainerMap) {
      auto It = ContainerMap.find(Entry.first);
      if (It == ContainerMap.end()) {
        ContainerMap.insert(Entry);
        continue;
      }
      ContainerInfo &L = It->second;
      const ContainerInfo &R = Entry.second;
      if (L.St == R.St)
        continue;
      SourceLocation ConsumeLoc =
          L.St == LinearInfo::LS_Unconsumed ? R.Loc : L.Loc;
      L.St = LinearInfo::LS_MaybeConsumed;
      L.Loc = ConsumeLoc;
    }
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
    for (const auto &Entry : LoopBackStates->ContainerMap) {
      auto It = ContainerMap.find(Entry.first);
      if (It == ContainerMap.end())
        continue;
      if (It->second.St != Entry.second.St) {
        Handler.warnLoopStateMismatch(BlameLoc, varName(Entry.first));
        It->second.St = LinearInfo::LS_MaybeConsumed;
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

/// Refine \p Map along one edge of a branch that tested a
/// conditional-consumer call's result: on the returned-true edge the parked
/// objects are consumed; on the returned-false edge the caller still owns
/// them, so their pre-call state is restored. An object whose state was
/// touched between the call and the branch (a second consume already
/// diagnosed, an assignment) is left alone.
static void applyCondSplit(LinearStateMap &Map, const CondConsumeInfo &Info,
                           bool CallReturnedTrue) {
  for (const CondParkedObject &P : Info.Objects) {
    std::optional<LinearInfo> Cur =
        P.Var ? Map.getState(P.Var) : Map.getState(P.Tmp);
    if (!Cur || Cur->St != LinearInfo::LS_MaybeConsumed ||
        Cur->Loc != Info.CallLoc)
      continue;
    LinearInfo NewInfo = CallReturnedTrue
                             ? LinearInfo(LinearInfo::LS_Consumed, Info.CallLoc)
                             : P.Orig;
    if (P.Var)
      Map.setState(P.Var, NewInfo);
    else
      Map.setState(P.Tmp, NewInfo);
  }
}

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
    /// Refers to a local container object (tainted or taintable); Var is
    /// the container variable.
    PI_Container,
    /// An iterator or pointer obtained from a container (begin(), data());
    /// Var is the underlying container variable.
    PI_ContainerIter,
    /// An lvalue denoting one of a container's linear elements (front(),
    /// operator[], *iterator); Var is the underlying container variable.
    PI_ContainerElem,
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
  static PropagationInfo makeContainer(Kind CK, const VarDecl *VD) {
    assert(CK == PI_Container || CK == PI_ContainerIter ||
           CK == PI_ContainerElem);
    PropagationInfo PI;
    PI.K = CK;
    PI.Var = VD;
    return PI;
  }

  Kind getKind() const { return K; }
  bool isValid() const { return K != PI_None; }
  bool isVar() const { return K == PI_Var; }
  bool isTmp() const { return K == PI_Tmp; }
  bool isFresh() const { return K == PI_Fresh; }
  bool isTracked() const { return K == PI_Var || K == PI_Tmp; }
  bool isFreshEmpty() const { return K == PI_Fresh && FreshEmpty; }
  bool isContainer() const { return K == PI_Container; }
  bool isContainerIter() const { return K == PI_ContainerIter; }
  bool isContainerElem() const { return K == PI_ContainerElem; }
  bool isContainerRelated() const {
    return K == PI_Container || K == PI_ContainerIter || K == PI_ContainerElem;
  }

  const VarDecl *getVar() const {
    assert(K == PI_Var);
    return Var;
  }
  const CXXBindTemporaryExpr *getTmp() const {
    assert(K == PI_Tmp);
    return Tmp;
  }
  /// The container variable a container-related value refers to.
  const VarDecl *getContainer() const {
    assert(isContainerRelated());
    return Var;
  }
};

class LinearityStmtVisitor : public ConstStmtVisitor<LinearityStmtVisitor> {
  using MapType = llvm::DenseMap<const Stmt *, PropagationInfo>;

  LinearityWarningsHandlerBase &Handler;
  ParentMap &PM;
  /// The function being analyzed. Variables captured from an enclosing
  /// function are not armed or tainted here: the enclosing function owns
  /// their obligations.
  const DeclContext *FnCtx;
  LinearStateMap *StateMap;
  MapType PropagationMap;
  /// Iterator-typed (or pointer-typed) local variables known to have been
  /// obtained from a container, e.g. `auto it = vec.begin();`. Deliberately
  /// not flow-sensitive: an iterator variable is a short-lived handle.
  llvm::DenseMap<const VarDecl *, const VarDecl *> IterVarMap;
  /// Taint carried by a container constructed from another tainted container
  /// (move construction), keyed by the canonical CXXConstructExpr. Applied
  /// when the constructed object is bound to a variable.
  llvm::DenseMap<const Stmt *, ContainerInfo> PendingCtorTaint;
  /// Conditional-consumer calls whose parked arguments await a branch on the
  /// call's boolean result, keyed by the canonical call expression.
  llvm::DenseMap<const Stmt *, CondConsumeInfo> CondConsumeMap;
  /// Local bool variables initialized with a conditional-consumer call's
  /// result (`bool ok = token.post(std::move(t));`), mapping to the call's
  /// CondConsumeMap key. Invalidated on reassignment.
  llvm::DenseMap<const VarDecl *, const Stmt *> CondBoolVarMap;
  /// Container variables for which a diagnostic has been emitted; consulted
  /// by the whole-function backstop to avoid double reports.
  llvm::SmallPtrSetImpl<const VarDecl *> &ReportedContainers;

public:
  LinearityStmtVisitor(LinearityWarningsHandlerBase &Handler, ParentMap &PM,
                       const DeclContext *FnCtx, LinearStateMap *StateMap,
                       llvm::SmallPtrSetImpl<const VarDecl *> &Reported)
      : Handler(Handler), PM(PM), FnCtx(FnCtx), StateMap(StateMap),
        ReportedContainers(Reported) {}

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

  /// Park the tracked objects bound to \p Call's conditional-consumer
  /// parameters: consumed iff the call returns true. Until (unless) a branch
  /// on the result is found they are MaybeConsumed, which is also the
  /// correct final state when the result is discarded — the value then
  /// really is consumed on only some runtime paths, and its death is
  /// diagnosed. An object that is not (any longer) Unconsumed is consumed
  /// the ordinary way, which diagnoses the double-consume at the call.
  void registerCondConsume(
      const CallExpr *Call, ArrayRef<PropagationInfo> Objects,
      ArrayRef<std::pair<SourceLocation, QualType>> FreshTemps = {}) {
    CondConsumeInfo Info;
    Info.CallLoc = Call->getExprLoc();
    for (const PropagationInfo &PI : Objects) {
      std::optional<LinearInfo> Cur = trackedState(PI);
      if (!Cur)
        continue;
      if (Cur->St != LinearInfo::LS_Unconsumed) {
        consumeObject(PI, Call->getExprLoc());
        continue;
      }
      CondParkedObject Parked;
      if (PI.isVar())
        Parked.Var = PI.getVar();
      else
        Parked.Tmp = PI.getTmp();
      Parked.Orig = *Cur;
      Info.Objects.push_back(Parked);
      setTrackedState(
          PI, LinearInfo(LinearInfo::LS_MaybeConsumed, Call->getExprLoc()));
    }
    Info.FreshTemps.append(FreshTemps.begin(), FreshTemps.end());
    if (!Info.Objects.empty() || !Info.FreshTemps.empty())
      CondConsumeMap[canonicalExpr(Call)] = std::move(Info);
  }

  /// Consuming the *result* of a conditional-consumer call (or the bool
  /// variable holding it) with a matching-tag annotated consumer discharges
  /// the pending obligation: `tmc::consume(q.post(std::move(t)))` declares
  /// the failure path deliberately unhandled. The parked values are marked
  /// consumed and no branch split will occur. Returns true if a pending
  /// obligation was discharged.
  bool dischargeCondConsume(const Expr *Arg, StringRef Tag,
                            SourceLocation Loc) {
    const Stmt *Key = stripCondWrappers(Arg);
    if (const auto *DRE = dyn_cast<DeclRefExpr>(Key)) {
      const auto *VD = dyn_cast<VarDecl>(DRE->getDecl());
      if (!VD)
        return false;
      auto VIt = CondBoolVarMap.find(VD);
      if (VIt == CondBoolVarMap.end())
        return false;
      Key = VIt->second;
    }
    auto It = CondConsumeMap.find(Key);
    if (It == CondConsumeMap.end())
      return false;
    CondConsumeInfo &Info = It->second;
    // The consumer's tag must match the parked values' linear tag.
    QualType FirstTy = !Info.Objects.empty()
                           ? (Info.Objects.front().Var
                                  ? Info.Objects.front()
                                        .Var->getType()
                                        .getNonReferenceType()
                                  : Info.Objects.front().Tmp->getType())
                           : Info.FreshTemps.front().second;
    if (!linearTagMatches(Tag, FirstTy))
      return false;
    for (const CondParkedObject &P : Info.Objects) {
      PropagationInfo PI = P.Var ? PropagationInfo::makeVar(P.Var)
                                 : PropagationInfo::makeTmp(P.Tmp);
      std::optional<LinearInfo> Cur = trackedState(PI);
      if (Cur && Cur->St == LinearInfo::LS_MaybeConsumed &&
          Cur->Loc == Info.CallLoc)
        setTrackedState(PI, LinearInfo(LinearInfo::LS_Consumed, Loc));
    }
    CondConsumeMap.erase(It);
    return true;
  }

  /// Report fresh temporaries whose conditional-consumer call was never
  /// discharged; called once after the CFG walk.
  void reportUndischargedFreshTemps() {
    for (const auto &Entry : CondConsumeMap) {
      const CondConsumeInfo &Info = Entry.second;
      for (const auto &FT : Info.FreshTemps)
        Handler.warnMaybeNotConsumed(FT.first, StringRef(), FT.second,
                                     Info.CallLoc, /*IsParam=*/false);
    }
  }

  /// If \p Cond (a branch terminator's condition) tests the result of a
  /// conditional-consumer call — directly, through any number of logical
  /// negations, comparisons against bool constants (`== false`, `!= true`,
  /// `== 0`), or through a local bool variable initialized with it — return
  /// the call's parked-consumption record. \p Negated reports whether the
  /// condition is true when the call returned *false*.
  const CondConsumeInfo *resolveConditionalConsume(const Expr *Cond,
                                                   bool &Negated) const {
    // A bool constant in a comparison: true/false literals, or the integer
    // literals 0/1 (`ok == 0`). Other integers never equal a bool truthfully
    // enough to resolve.
    auto AsBoolConst = [](const Expr *E, bool &Val) {
      if (const auto *BL = dyn_cast<CXXBoolLiteralExpr>(E)) {
        Val = BL->getValue();
        return true;
      }
      if (const auto *IL = dyn_cast<IntegerLiteral>(E)) {
        if (IL->getValue() == 0) {
          Val = false;
          return true;
        }
        if (IL->getValue() == 1) {
          Val = true;
          return true;
        }
      }
      return false;
    };

    Negated = false;
    const Expr *E = stripCondWrappers(Cond);
    while (true) {
      if (const auto *UO = dyn_cast<UnaryOperator>(E)) {
        if (UO->getOpcode() != UO_LNot)
          return nullptr;
        Negated = !Negated;
        E = stripCondWrappers(UO->getSubExpr());
        continue;
      }
      if (const auto *BO = dyn_cast<BinaryOperator>(E)) {
        if (BO->getOpcode() != BO_EQ && BO->getOpcode() != BO_NE)
          return nullptr;
        const Expr *LHS = stripCondWrappers(BO->getLHS());
        const Expr *RHS = stripCondWrappers(BO->getRHS());
        bool LitVal;
        const Expr *Other = RHS;
        if (!AsBoolConst(LHS, LitVal)) {
          Other = LHS;
          if (!AsBoolConst(RHS, LitVal))
            return nullptr;
        }
        // `x == false` and `x != true` negate; `x == true` and `x != false`
        // are the identity.
        if (LitVal == (BO->getOpcode() == BO_NE))
          Negated = !Negated;
        E = Other;
        continue;
      }
      break;
    }
    const Stmt *Key = E;
    if (const auto *DRE = dyn_cast<DeclRefExpr>(E)) {
      const auto *VD = dyn_cast<VarDecl>(DRE->getDecl());
      if (!VD)
        return nullptr;
      auto VIt = CondBoolVarMap.find(VD);
      if (VIt == CondBoolVarMap.end())
        return nullptr;
      Key = VIt->second;
    }
    auto It = CondConsumeMap.find(Key);
    if (It == CondConsumeMap.end())
      return nullptr;
    return &It->second;
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
        VD->getType()->isReferenceType() || !isLinearType(VD->getType()) ||
        VD->getDeclContext() != FnCtx)
      return {};
    return PropagationInfo::makeVar(VD);
  }

  /// Does binding an argument to \p Param consume it?
  bool paramConsumes(const ParmVarDecl *Param, const PropagationInfo &ArgPI) {
    return paramConsumeKind(Param, trackedType(ArgPI)) != ConsumeKind::None;
  }

  //===--------------------------------------------------------------------===//
  // Container taint
  //===--------------------------------------------------------------------===//

  /// If \p E refers to a local, non-reference variable whose type can hold
  /// linear content (a non-linear class with a linear template argument),
  /// return it. Reference parameters are excluded: their container belongs
  /// to the caller.
  const VarDecl *containerVarTarget(const Expr *E) const {
    const auto *DRE = dyn_cast<DeclRefExpr>(canonicalExpr(E)->IgnoreImplicit());
    if (!DRE)
      return nullptr;
    const auto *VD = dyn_cast<VarDecl>(DRE->getDecl());
    // Compiler-generated variables are excluded: most importantly the
    // coroutine promise object, whose return_value(T&&) would otherwise
    // count as moving the co_returned value "into" the promise.
    if (!VD || VD->isImplicit() || !VD->hasLocalStorage() ||
        VD->getType()->isReferenceType() || VD->getDeclContext() != FnCtx)
      return nullptr;
    if (!getLinearElementAttr(VD->getType()))
      return nullptr;
    return VD;
  }

  /// Mark \p VD as holding unconsumed linear content. A container that is
  /// already tainted keeps its original taint location for the diagnostic
  /// note; a consumed container becomes tainted again (refill after reuse).
  void setContainerTaint(const VarDecl *VD, SourceLocation Loc, StringRef Tag,
                         QualType ElemTy) {
    if (const ContainerInfo *Cur = StateMap->getContainerState(VD))
      if (Cur->St == LinearInfo::LS_Unconsumed)
        return;
    ContainerInfo CI;
    CI.St = LinearInfo::LS_Unconsumed;
    CI.Loc = Loc;
    CI.Tag = Tag;
    CI.ElemTy = ElemTy;
    StateMap->ContainerMap[VD] = CI;
  }

  /// Leniently stop tracking a container: some use the analysis does not
  /// model may consume (or may have discarded) the contents.
  void untaintContainer(const VarDecl *VD) { StateMap->ContainerMap.erase(VD); }

  /// The container's contents are handed to a consuming operation.
  void consumeContainer(const VarDecl *VD, SourceLocation Loc) {
    auto It = StateMap->ContainerMap.find(VD);
    if (It == StateMap->ContainerMap.end())
      return;
    ContainerInfo &CI = It->second;
    switch (CI.St) {
    case LinearInfo::LS_Unconsumed:
      CI.St = LinearInfo::LS_Consumed;
      CI.Loc = Loc;
      break;
    case LinearInfo::LS_Consumed:
      Handler.warnContainerUseAfterConsume(Loc, varName(VD), /*Maybe=*/false,
                                           CI.Loc);
      break;
    case LinearInfo::LS_MaybeConsumed:
      Handler.warnContainerUseAfterConsume(Loc, varName(VD), /*Maybe=*/true,
                                           CI.Loc);
      CI.St = LinearInfo::LS_Consumed;
      CI.Loc = Loc;
      break;
    }
  }

  /// Effects of binding one call argument. Tracked linear values are
  /// consumed per parameter rules. Containers (and iterators/pointers
  /// derived from them) are consumed by consumer-annotated parameters whose
  /// tag matches the taint, and leniently escape when bound to anything the
  /// analysis does not recognize. Containers consumed by annotated
  /// parameters are collected into \p ConsumedContainers so a call receiving
  /// two handles to the same container (begin/end) consumes it once.
  /// A structural consumption of a tracked linear value is reported through
  /// \p StructuralElemAttr / \p StructuralElemTy so member calls can taint
  /// their object. Values bound to conditional-consumer parameters are
  /// collected into \p CondParked (when the caller provides it) instead of
  /// being consumed; contexts without a testable result (constructors) pass
  /// null and consume unconditionally.
  void handleArgumentBinding(
      const ParmVarDecl *Param, const Expr *Arg,
      llvm::SmallPtrSetImpl<const VarDecl *> &ConsumedContainers,
      const LinearAttr *&StructuralElemAttr, QualType &StructuralElemTy,
      SmallVectorImpl<PropagationInfo> *CondParked = nullptr,
      SmallVectorImpl<std::pair<SourceLocation, QualType>> *CondFresh =
          nullptr) {
    // An annotated consumer receiving the result of a pending
    // conditional-consumer call discharges that obligation.
    if (const auto *CA = Param->getAttr<LinearConsumerAttr>())
      if (dischargeCondConsume(Arg, CA->getTag(), Arg->getExprLoc()))
        return;
    PropagationInfo ArgPI = findInfo(Arg);
    if (ArgPI.isTracked()) {
      QualType ArgTy = trackedType(ArgPI);
      ConsumeKind CK = paramConsumeKind(Param, ArgTy);
      if (CK == ConsumeKind::None)
        return;
      if (CK == ConsumeKind::AnnotatedConditional && CondParked) {
        CondParked->push_back(ArgPI);
        return;
      }
      consumeObject(ArgPI, Arg->getExprLoc());
      if (CK == ConsumeKind::Structural)
        if (const LinearAttr *LA = getLinearAttr(ArgTy)) {
          StructuralElemAttr = LA;
          StructuralElemTy = ArgTy;
        }
      return;
    }
    // A fresh value of a trivially-destructible linear type has no tracked
    // identity (no CXXBindTemporaryExpr). Bound to a conditional consumer it
    // is unrecoverable on the failure path; record it on the call's pending
    // entry so it is reported unless the result is explicitly discharged.
    if (ArgPI.isFresh() && !ArgPI.isFreshEmpty() && CondFresh) {
      QualType ArgTy = Arg->getType().getNonReferenceType();
      if (paramConsumeKind(Param, ArgTy) == ConsumeKind::AnnotatedConditional)
        CondFresh->push_back({Arg->getExprLoc(), ArgTy});
      return;
    }
    if (ArgPI.isContainer() || ArgPI.isContainerIter()) {
      const VarDecl *Root = ArgPI.getContainer();
      if (const ContainerInfo *CI = StateMap->getContainerState(Root)) {
        if (const auto *CA = Param->getAttr<LinearConsumerAttr>();
            CA && CA->getTag() == CI->Tag) {
          ConsumedContainers.insert(Root);
          return;
        }
        // Bound to something unrecognized: it may consume through the
        // reference/iterator. Leniently stop tracking.
        untaintContainer(Root);
      }
      return;
    }
    if (ArgPI.isContainerElem()) {
      // A single element handed onward. If the binding consumes it, the
      // container has been partially drained; the analysis cannot count
      // elements, so leniently stop tracking.
      QualType ElemTy = Arg->getType().getNonReferenceType();
      if (paramConsumeKind(Param, ElemTy) != ConsumeKind::None)
        untaintContainer(ArgPI.getContainer());
      return;
    }
  }

  /// Taint bookkeeping for a call on a container object or on a value
  /// derived from one. Returns true if the call was fully handled as a
  /// container operation.
  bool handleContainerObject(const CallExpr *Call, const Expr *ObjArg,
                             const PropagationInfo &ObjPI,
                             const FunctionDecl *FunD,
                             const LinearAttr *StructuralElemAttr,
                             QualType StructuralElemTy) {
    const VarDecl *Root = nullptr;
    PropagationInfo::Kind ObjKind;
    if (ObjPI.isContainerRelated()) {
      Root = ObjPI.getContainer();
      ObjKind = ObjPI.getKind();
    } else if (!ObjPI.isValid()) {
      Root = containerVarTarget(ObjArg);
      if (!Root)
        return false;
      ObjKind = PropagationInfo::PI_Container;
    } else {
      return false; // a tracked linear object; not a container
    }

    // A member call that structurally consumed a linear argument moved that
    // value into the object: the object now carries the obligation
    // (vec.push_back(std::move(t))). Consumer-annotated parameters do not
    // reach here: the annotation declares the obligation discharged.
    if (StructuralElemAttr) {
      setContainerTaint(Root, Call->getExprLoc(), StructuralElemAttr->getTag(),
                        StructuralElemTy);
      return true;
    }

    QualType RetTy = FunD->getReturnType();
    QualType RetNonRef = RetTy.getNonReferenceType();
    if (ObjKind == PropagationInfo::PI_Container) {
      // Element accessors: front(), at(), operator[].
      if (RetTy->isReferenceType() && isLinearType(RetNonRef)) {
        insertInfo(Call, PropagationInfo::makeContainer(
                             PropagationInfo::PI_ContainerElem, Root));
        return true;
      }
      // Iterator/pointer providers: begin(), end(), data().
      if (RetTy->isPointerType() ||
          (RetNonRef->isRecordType() && typeHasStarOperator(RetNonRef))) {
        insertInfo(Call, PropagationInfo::makeContainer(
                             PropagationInfo::PI_ContainerIter, Root));
        return true;
      }
      // Anything else (reserve, clear, size, unknown mutators): leniently
      // stop tracking.
      untaintContainer(Root);
      return true;
    }
    if (ObjKind == PropagationInfo::PI_ContainerIter) {
      // Iterator operations: dereference yields an element, increment /
      // arithmetic yield iterators, comparisons are benign.
      if (isLinearType(RetNonRef))
        insertInfo(Call, PropagationInfo::makeContainer(
                             PropagationInfo::PI_ContainerElem, Root));
      else if (RetTy->isPointerType() || RetNonRef->isRecordType())
        insertInfo(Call, PropagationInfo::makeContainer(
                             PropagationInfo::PI_ContainerIter, Root));
      return true;
    }
    // ObjKind == PI_ContainerElem: a member call on one of the elements.
    if (const auto *CA = FunD->getAttr<LinearConsumerAttr>()) {
      if (const ContainerInfo *CI = StateMap->getContainerState(Root))
        if (CA->getTag() == CI->Tag)
          untaintContainer(Root); // partial drain through a consumer method
      return true;
    }
    // Fluent members returning a reference to the element keep the element
    // visible (std::move(vec[0]).run_on(ex)).
    if (RetTy->isReferenceType() && isLinearType(RetNonRef))
      insertInfo(Call, PropagationInfo::makeContainer(
                           PropagationInfo::PI_ContainerElem, Root));
    return true;
  }

  /// Common handling of function, method and operator calls: consume
  /// arguments per parameter rules, then handle the implicit object argument
  /// (consumer methods, fluent pass-throughs, and container taint).
  void handleCall(const CallExpr *Call, const Expr *ObjArg,
                  const FunctionDecl *FunD) {
    unsigned Offset = 0;
    if (isa<CXXOperatorCallExpr>(Call) && isa<CXXMethodDecl>(FunD))
      Offset = 1; // first argument is 'this'

    llvm::SmallPtrSet<const VarDecl *, 2> ConsumedContainers;
    const LinearAttr *StructuralElemAttr = nullptr;
    QualType StructuralElemTy;
    SmallVector<PropagationInfo, 1> CondParked;
    SmallVector<std::pair<SourceLocation, QualType>, 1> CondFresh;
    // A conditional consumer with a non-bool result cannot be tested;
    // fall back to unconditional consumption at the binding.
    bool ResultTestable = Call->getType()->isBooleanType();

    for (unsigned Index = Offset; Index < Call->getNumArgs(); ++Index) {
      if (Index - Offset >= FunD->getNumParams())
        break;
      handleArgumentBinding(FunD->getParamDecl(Index - Offset),
                            Call->getArg(Index), ConsumedContainers,
                            StructuralElemAttr, StructuralElemTy,
                            ResultTestable ? &CondParked : nullptr,
                            ResultTestable ? &CondFresh : nullptr);
    }
    for (const VarDecl *Root : ConsumedContainers)
      consumeContainer(Root, Call->getExprLoc());
    if (!CondParked.empty() || !CondFresh.empty())
      registerCondConsume(Call, CondParked, CondFresh);

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

    if (handleContainerObject(Call, ObjArg, ObjPI, FunD, StructuralElemAttr,
                              StructuralElemTy))
      return;

    if (!ObjPI.isTracked())
      return;

    if (const auto *CA = FunD->getAttr<LinearConsumerAttr>()) {
      if (linearTagMatches(CA->getTag(), trackedType(ObjPI))) {
        if (CA->getMode() == LinearConsumerAttr::Conditional &&
            Call->getType()->isBooleanType())
          registerCondConsume(Call, ObjPI);
        else
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
    else if (PI.isContainerRelated())
      untaintContainer(PI.getContainer());
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
    if (UO->getOpcode() == UO_AddrOf) {
      escapeObject(findInfo(UO->getSubExpr()));
      return;
    }
    // Dereferencing a pointer obtained from a container yields an element.
    if (UO->getOpcode() == UO_Deref) {
      PropagationInfo PI = findInfo(UO->getSubExpr());
      if (PI.isContainerIter())
        insertInfo(UO, PropagationInfo::makeContainer(
                           PropagationInfo::PI_ContainerElem,
                           PI.getContainer()));
    }
  }

  void VisitArraySubscriptExpr(const ArraySubscriptExpr *ASE) {
    PropagationInfo PI = findInfo(ASE->getBase());
    if (PI.isContainerIter())
      insertInfo(ASE, PropagationInfo::makeContainer(
                          PropagationInfo::PI_ContainerElem,
                          PI.getContainer()));
  }

  void VisitBinaryOperator(const BinaryOperator *BO) {
    switch (BO->getOpcode()) {
    case BO_Add:
    case BO_Sub: {
      // Pointer arithmetic on a pointer obtained from a container
      // (spawn_many(vec.data(), vec.data() + n)).
      PropagationInfo PI = findInfo(BO->getLHS());
      if (!PI.isContainerIter())
        PI = findInfo(BO->getRHS());
      if (PI.isContainerIter())
        insertInfo(BO, PI);
      break;
    }
    case BO_Assign: {
      const auto *DRE =
          dyn_cast<DeclRefExpr>(canonicalExpr(BO->getLHS())->IgnoreImplicit());
      const auto *VD = DRE ? dyn_cast<VarDecl>(DRE->getDecl()) : nullptr;
      // Assigning a conditional-consumer call's result into a bool variable
      // (re)binds the variable to that call (`ok = tok.post(...)`, reusing a
      // flag declared earlier); assigning anything else ends any prior
      // association.
      if (VD) {
        CondBoolVarMap.erase(VD);
        if (VD->getType()->isBooleanType()) {
          const Stmt *Key = stripCondWrappers(BO->getRHS());
          if (CondConsumeMap.count(Key))
            CondBoolVarMap[VD] = Key;
        }
      }
      // Storing a derived pointer into a local pointer variable keeps the
      // handle visible; storing it anywhere else escapes the container.
      PropagationInfo RHSPI = findInfo(BO->getRHS());
      if (!RHSPI.isContainerIter())
        break;
      if (VD && VD->hasLocalStorage())
        IterVarMap[VD] = RHSPI.getContainer();
      else
        untaintContainer(RHSPI.getContainer());
      break;
    }
    default:
      break;
    }
  }

  void VisitDeclRefExpr(const DeclRefExpr *DeclRef) {
    if (const auto *Var = dyn_cast_or_null<VarDecl>(DeclRef->getDecl())) {
      if (StateMap->getState(Var)) {
        insertInfo(DeclRef, PropagationInfo::makeVar(Var));
        return;
      }
      if (StateMap->getContainerState(Var)) {
        insertInfo(DeclRef, PropagationInfo::makeContainer(
                                PropagationInfo::PI_Container, Var));
        return;
      }
      auto It = IterVarMap.find(Var);
      if (It != IterVarMap.end())
        insertInfo(DeclRef, PropagationInfo::makeContainer(
                                PropagationInfo::PI_ContainerIter,
                                It->second));
    }
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

    PropagationInfo RHSPI = findInfo(RHS);
    PropagationInfo LHSPI = findInfo(LHS);

    // Assignment through a container element lvalue (vec[i] = std::move(t),
    // *it = std::move(t)) moves the value into the container.
    if (LHSPI.isContainerElem()) {
      if (RHSPI.isTracked() && FunD->getNumParams() >= 1) {
        QualType ArgTy = trackedType(RHSPI);
        ConsumeKind CK = paramConsumeKind(FunD->getParamDecl(0), ArgTy);
        if (CK != ConsumeKind::None) {
          consumeObject(RHSPI, RHS->getExprLoc());
          if (CK == ConsumeKind::Structural)
            if (const LinearAttr *LA = getLinearAttr(ArgTy))
              setContainerTaint(LHSPI.getContainer(), Call->getExprLoc(),
                                LA->getTag(), ArgTy);
        }
      }
      return;
    }

    // Container-to-container assignment: a move transfers the taint (and
    // ends tracking of the source); a copy duplicates it.
    if (RHSPI.isContainer()) {
      const VarDecl *Src = RHSPI.getContainer();
      if (const ContainerInfo *CI = StateMap->getContainerState(Src)) {
        ContainerInfo Taint = *CI;
        if (FunD->getNumParams() >= 1 &&
            FunD->getParamDecl(0)->getType()->isRValueReferenceType())
          untaintContainer(Src);
        if (const VarDecl *Dst = containerVarTarget(LHS))
          StateMap->ContainerMap[Dst] = Taint;
      }
      return;
    }

    // Overwriting a tainted container with something the analysis does not
    // recognize (opt = std::nullopt) leniently ends tracking.
    if (LHSPI.isContainer()) {
      untaintContainer(LHSPI.getContainer());
      return;
    }

    // Consume the RHS if the assignment takes it by rvalue reference or by
    // value (move-assignment and friends).
    if (RHSPI.isTracked() && FunD->getNumParams() >= 1 &&
        paramConsumes(FunD->getParamDecl(0), RHSPI))
      consumeObject(RHSPI, RHS->getExprLoc());

    // The LHS now holds whatever the RHS held. A default-constructed (empty)
    // RHS leaves the LHS not requiring consumption.
    LinearInfo::State NewSt = RHSPI.isFreshEmpty() ? LinearInfo::LS_Consumed
                                                   : LinearInfo::LS_Unconsumed;

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

    // Moving from a tainted container transfers the taint to the new
    // object; it is applied when the constructed object is bound to a
    // variable. (A copy leaves the source tainted and the copy untracked.)
    if (!Linear && Call->getNumArgs() >= 1 &&
        Constructor->isMoveConstructor()) {
      PropagationInfo ArgPI = findInfo(Call->getArg(0));
      if (ArgPI.isContainer()) {
        const VarDecl *Src = ArgPI.getContainer();
        if (const ContainerInfo *CI = StateMap->getContainerState(Src)) {
          PendingCtorTaint[canonicalExpr(Call)] = *CI;
          untaintContainer(Src);
        }
        return;
      }
    }

    // Any other constructor: consume linear arguments per parameter rules
    // (e.g. a wrapper constructed from `task&&`, or a mux constructed from
    // consumer-annotated iterator parameters).
    llvm::SmallPtrSet<const VarDecl *, 2> ConsumedContainers;
    const LinearAttr *StructuralElemAttr = nullptr;
    QualType StructuralElemTy;
    for (unsigned Index = 0; Index < Call->getNumArgs(); ++Index) {
      if (Index >= Constructor->getNumParams())
        break;
      handleArgumentBinding(Constructor->getParamDecl(Index),
                            Call->getArg(Index), ConsumedContainers,
                            StructuralElemAttr, StructuralElemTy);
    }
    for (const VarDecl *Root : ConsumedContainers)
      consumeContainer(Root, Call->getExprLoc());

    if (Linear) {
      insertInfo(Call, PropagationInfo::makeFresh(/*Empty=*/false));
      return;
    }

    // A non-linear object constructed by structurally consuming a linear
    // value (std::optional<task<int>> opt(std::move(t))) starts life
    // tainted.
    if (StructuralElemAttr && getLinearElementAttr(ThisType)) {
      ContainerInfo CI;
      CI.St = LinearInfo::LS_Unconsumed;
      CI.Loc = Call->getExprLoc();
      CI.Tag = StructuralElemAttr->getTag();
      CI.ElemTy = StructuralElemTy;
      PendingCtorTaint[canonicalExpr(Call)] = CI;
    }
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
      if (InitPI.isContainer() || InitPI.isContainerElem()) {
        // A reference to a tainted container or one of its elements (a
        // range-for's implicit __range, a manual drain) can consume through
        // the reference; leniently stop tracking.
        untaintContainer(InitPI.getContainer());
        return;
      }
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

    if (!isLinearType(VarTy)) {
      if (!Var->hasInit())
        return;
      // A bool variable capturing a conditional-consumer call's result:
      // bool ok = token.post(std::move(t)); a later branch on it splits the
      // parked state.
      if (VarTy->isBooleanType()) {
        const Stmt *Key = stripCondWrappers(Var->getInit());
        if (CondConsumeMap.count(Key))
          CondBoolVarMap[Var] = Key;
        return;
      }
      PropagationInfo InitPI = findInfo(Var->getInit());
      // An iterator variable obtained from a container: auto it =
      // vec.begin();
      if (InitPI.isContainerIter()) {
        IterVarMap[Var] = InitPI.getContainer();
        return;
      }
      // A container constructed by moving from a tainted container, or by
      // consuming a linear value, takes over the taint.
      auto It = PendingCtorTaint.find(canonicalExpr(Var->getInit()));
      if (It != PendingCtorTaint.end()) {
        StateMap->ContainerMap[Var] = It->second;
        PendingCtorTaint.erase(It);
      }
      return;
    }

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
    if (const Expr *RetVal = Ret->getRetValue()) {
      PropagationInfo PI = findInfo(RetVal);
      if (PI.isContainerRelated())
        untaintContainer(PI.getContainer());
      else
        consumeSilently(PI, Ret->getReturnLoc());
    }
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

  /// Report a container that dies while (maybe) holding unconsumed linear
  /// content.
  void checkContainerAtDeath(const VarDecl *Var, SourceLocation Loc) {
    auto It = StateMap->ContainerMap.find(Var);
    if (It == StateMap->ContainerMap.end())
      return;
    const ContainerInfo &CI = It->second;
    if (CI.St == LinearInfo::LS_Unconsumed) {
      Handler.warnContainerNeverConsumed(Loc, varName(Var), CI.ElemTy, CI.Loc);
      ReportedContainers.insert(Var);
    } else if (CI.St == LinearInfo::LS_MaybeConsumed) {
      Handler.warnContainerMaybeNotConsumed(Loc, varName(Var), CI.ElemTy,
                                            CI.Loc);
      ReportedContainers.insert(Var);
    }
    StateMap->ContainerMap.erase(It);
  }

  void checkAtDeath(const PropagationInfo &PI, SourceLocation Loc) {
    if (PI.isVar())
      checkContainerAtDeath(PI.getVar(), Loc);
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
// Write-only-container backstop
//===----------------------------------------------------------------------===//

/// The single-pass dataflow cannot carry state created inside a loop body to
/// the loop exit (the exit block's state is propagated from the condition
/// block before the body is visited), so the canonical fill loop
///   for (...) vec.push_back(make_task(i));
/// never taints `vec` at its destruction point. This backstop catches the
/// case path-insensitively: a local container that is only ever *filled*
/// with linear values is reported at its declaration. Any other appearance
/// of the variable — passing it or an iterator anywhere, a value-returning
/// member call, a capture — disqualifies it, so any use that could consume
/// keeps it silent.
class WriteOnlyContainerScanner {
  struct CandidateInfo {
    bool HasTaintingUse = false;
    bool Disqualified = false;
    SourceLocation FirstTaintLoc;
    QualType ElemTy;
  };

  const DeclContext *FnCtx;
  llvm::DenseMap<const VarDecl *, CandidateInfo> Candidates;
  llvm::SmallPtrSet<const DeclRefExpr *, 16> ClassifiedUses;

public:
  WriteOnlyContainerScanner(const DeclContext *FnCtx) : FnCtx(FnCtx) {}

  void scan(const Stmt *Body, LinearityWarningsHandlerBase &Handler,
            const llvm::SmallPtrSetImpl<const VarDecl *> &AlreadyReported) {
    collectCandidates(Body);
    if (Candidates.empty())
      return;
    classifyUses(Body);
    for (const auto &Entry : Candidates) {
      const VarDecl *VD = Entry.first;
      const CandidateInfo &CI = Entry.second;
      if (CI.HasTaintingUse && !CI.Disqualified && !AlreadyReported.count(VD))
        Handler.warnContainerNeverConsumed(VD->getLocation(), varName(VD),
                                           CI.ElemTy, CI.FirstTaintLoc);
    }
  }

private:
  void collectCandidates(const Stmt *Body) {
    SmallVector<const Stmt *, 32> Worklist{Body};
    while (!Worklist.empty()) {
      const Stmt *S = Worklist.pop_back_val();
      if (!S)
        continue;
      if (const auto *DS = dyn_cast<DeclStmt>(S))
        for (const auto *DI : DS->decls())
          if (const auto *VD = dyn_cast<VarDecl>(DI))
            if (!VD->isImplicit() && VD->hasLocalStorage() &&
                !VD->getType()->isReferenceType() &&
                VD->getDeclContext() == FnCtx &&
                getLinearElementAttr(VD->getType()))
              Candidates.try_emplace(VD);
      for (const Stmt *Child : S->children())
        Worklist.push_back(Child);
    }
  }

  CandidateInfo *candidateForExpr(const Expr *E, const DeclRefExpr **DREOut) {
    const auto *DRE = dyn_cast<DeclRefExpr>(E->IgnoreParenImpCasts());
    if (!DRE)
      return nullptr;
    const auto *VD = dyn_cast<VarDecl>(DRE->getDecl());
    if (!VD)
      return nullptr;
    auto It = Candidates.find(VD);
    if (It == Candidates.end())
      return nullptr;
    if (DREOut)
      *DREOut = DRE;
    return &It->second;
  }

  /// A structurally-consumed linear argument of this call, if any: the call
  /// moves a linear value into whatever it was invoked on.
  const Expr *findStructuralLinearArg(const FunctionDecl *FD,
                                      const CallExpr *Call, unsigned Offset) {
    for (unsigned Index = Offset; Index < Call->getNumArgs(); ++Index) {
      if (Index - Offset >= FD->getNumParams())
        break;
      const Expr *Arg = Call->getArg(Index);
      QualType ArgTy = Arg->getType().getNonReferenceType();
      if (!isLinearType(ArgTy))
        continue;
      if (paramConsumeKind(FD->getParamDecl(Index - Offset), ArgTy) ==
          ConsumeKind::Structural)
        return Arg;
    }
    return nullptr;
  }

  static bool allArgsScalar(const CallExpr *Call, unsigned Offset) {
    for (unsigned Index = Offset; Index < Call->getNumArgs(); ++Index)
      if (!Call->getArg(Index)->getType()->isScalarType())
        return false;
    return true;
  }

  void markTainting(CandidateInfo &CI, const DeclRefExpr *DRE,
                    const Expr *TaintArg) {
    ClassifiedUses.insert(DRE);
    if (!CI.HasTaintingUse) {
      CI.HasTaintingUse = true;
      CI.FirstTaintLoc = TaintArg->getExprLoc();
      CI.ElemTy = TaintArg->getType().getNonReferenceType();
    }
  }

  /// vec.push_back(std::move(t)) / vec.emplace_back(std::move(t)): a member
  /// call on the candidate that structurally consumes a linear argument.
  void classifyMemberCall(const CXXMemberCallExpr *MCE) {
    const CXXMethodDecl *MD = MCE->getMethodDecl();
    if (!MD)
      return;
    const DeclRefExpr *DRE = nullptr;
    CandidateInfo *CI =
        candidateForExpr(MCE->getImplicitObjectArgument(), &DRE);
    if (!CI)
      return;
    if (const Expr *TaintArg = findStructuralLinearArg(MD, MCE, 0)) {
      markTainting(*CI, DRE, TaintArg);
      return;
    }
    // A void-returning member call with scalar-only arguments cannot hand
    // out access to the contents (reserve, clear, pop_back).
    if (MD->getReturnType()->isVoidType() && allArgsScalar(MCE, 0))
      ClassifiedUses.insert(DRE);
  }

  /// vec[i] = std::move(t): an element-assignment through the candidate's
  /// subscript operator.
  void classifyOperatorCall(const CXXOperatorCallExpr *OCE) {
    if (OCE->getOperator() != OO_Equal || OCE->getNumArgs() != 2)
      return;
    const auto *FD = dyn_cast_or_null<FunctionDecl>(OCE->getDirectCallee());
    if (!FD || FD->getNumParams() < 1)
      return;
    const Expr *RHS = OCE->getArg(1);
    QualType RHSTy = RHS->getType().getNonReferenceType();
    if (!isLinearType(RHSTy) ||
        paramConsumeKind(FD->getParamDecl(0), RHSTy) !=
            ConsumeKind::Structural)
      return;
    // The LHS must be an element access on a candidate: vec[i] or vec.at(i)
    // returning a reference to the linear element type.
    const Expr *LHS = OCE->getArg(0)->IgnoreParenImpCasts();
    const Expr *Base = nullptr;
    const FunctionDecl *AccessFn = nullptr;
    if (const auto *SubOCE = dyn_cast<CXXOperatorCallExpr>(LHS)) {
      if (SubOCE->getOperator() == OO_Subscript && SubOCE->getNumArgs() >= 1) {
        Base = SubOCE->getArg(0);
        AccessFn = dyn_cast_or_null<FunctionDecl>(SubOCE->getDirectCallee());
      }
    } else if (const auto *SubMCE = dyn_cast<CXXMemberCallExpr>(LHS)) {
      Base = SubMCE->getImplicitObjectArgument();
      AccessFn = SubMCE->getMethodDecl();
    }
    if (!Base || !AccessFn)
      return;
    QualType AccessRet = AccessFn->getReturnType();
    if (!AccessRet->isReferenceType() ||
        !isLinearType(AccessRet.getNonReferenceType()))
      return;
    const DeclRefExpr *DRE = nullptr;
    if (CandidateInfo *CI = candidateForExpr(Base, &DRE))
      markTainting(*CI, DRE, RHS);
  }

  void classifyUses(const Stmt *Body) {
    // Parents are processed before their children, so a call node classifies
    // its object DeclRefExpr before the leaf itself is examined.
    SmallVector<std::pair<const Stmt *, bool>, 32> Worklist{{Body, false}};
    while (!Worklist.empty()) {
      auto [S, InLambda] = Worklist.pop_back_val();
      if (!S)
        continue;
      bool ChildInLambda = InLambda || isa<LambdaExpr>(S);
      if (const auto *DRE = dyn_cast<DeclRefExpr>(S)) {
        if (const auto *VD = dyn_cast<VarDecl>(DRE->getDecl())) {
          auto It = Candidates.find(VD);
          if (It != Candidates.end() &&
              (InLambda || !ClassifiedUses.count(DRE)))
            It->second.Disqualified = true;
        }
      } else if (!InLambda) {
        if (const auto *MCE = dyn_cast<CXXMemberCallExpr>(S))
          classifyMemberCall(MCE);
        else if (const auto *OCE = dyn_cast<CXXOperatorCallExpr>(S))
          classifyOperatorCall(OCE);
      }
      for (const Stmt *Child : S->children())
        Worklist.push_back({Child, ChildInLambda});
    }
  }
};

//===----------------------------------------------------------------------===//
// Analyzer
//===----------------------------------------------------------------------===//

class LinearityAnalyzer {
  LinearityWarningsHandlerBase &Handler;
  LinearBlockInfo BlockInfo;
  std::unique_ptr<LinearStateMap> CurrStates;
  /// Containers reported by the flow-sensitive pass; the whole-function
  /// backstop skips these.
  llvm::SmallPtrSet<const VarDecl *, 4> ReportedContainers;

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
                                 cast<DeclContext>(D), CurrStates.get(),
                                 ReportedContainers);

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

      // Branch-sensitive refinement for conditional consumers: if this
      // block's terminator tests the result of a conditional-consumer call,
      // the parked arguments are consumed on the returned-true edge and
      // still owned on the returned-false edge.
      if (CurrBlock->succ_size() == 2 &&
          isBoolBranchTerminator(CurrBlock->getTerminatorStmt())) {
        if (const auto *Cond = dyn_cast_or_null<Expr>(
                CurrBlock->getTerminatorCondition())) {
          bool Negated = false;
          const CondConsumeInfo *Split =
              Visitor.resolveConditionalConsume(Cond, Negated);
          const CFGBlock *TrueSucc = *CurrBlock->succ_begin();
          const CFGBlock *FalseSucc = *(CurrBlock->succ_begin() + 1);
          // Back-edge successors go through the loop-head merge instead of
          // addInfo; skip the refinement for those (rare) shapes.
          if (Split && TrueSucc && FalseSucc &&
              !BlockInfo.isBackEdge(CurrBlock, TrueSucc) &&
              !BlockInfo.isBackEdge(CurrBlock, FalseSucc)) {
            auto FalseStates = std::make_unique<LinearStateMap>(*CurrStates);
            // On the condition-true edge the call returned true unless the
            // condition negates the result an odd number of times.
            applyCondSplit(*CurrStates, *Split, /*CallReturnedTrue=*/!Negated);
            applyCondSplit(*FalseStates, *Split, /*CallReturnedTrue=*/Negated);
            BlockInfo.addInfo(TrueSucc, CurrStates.get(), CurrStates);
            BlockInfo.addInfo(FalseSucc, FalseStates.get(), FalseStates);
            CurrStates = nullptr;
            continue;
          }
        }
      }

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

    // Fresh temporaries of trivially-destructible linear types bound to
    // conditional consumers whose result was never explicitly discharged.
    Visitor.reportUndischargedFreshTemps();

    // Path-insensitive backstop for containers filled inside loops, which
    // the single-pass dataflow cannot see at the loop exit.
    WriteOnlyContainerScanner Scanner(cast<DeclContext>(D));
    Scanner.scan(AC.getBody(), Handler, ReportedContainers);

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
    // Tainted containers that reach the exit without a dtor CFG element
    // (trivially-destructible element types under NDEBUG).
    for (const auto &Entry : CurrStates->ContainerMap) {
      const VarDecl *Var = Entry.first;
      const ContainerInfo &CI = Entry.second;
      if (CI.St == LinearInfo::LS_Unconsumed) {
        Handler.warnContainerNeverConsumed(Var->getLocation(), varName(Var),
                                           CI.ElemTy, CI.Loc);
        ReportedContainers.insert(Var);
      } else if (CI.St == LinearInfo::LS_MaybeConsumed) {
        Handler.warnContainerMaybeNotConsumed(Var->getLocation(), varName(Var),
                                              CI.ElemTy, CI.Loc);
        ReportedContainers.insert(Var);
      }
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
