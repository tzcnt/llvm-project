// RUN: %clang_cc1 -std=c++20 -fsyntax-only -verify %s

namespace std {
template <typename T> struct remove_reference { using type = T; };
template <typename T> struct remove_reference<T &> { using type = T; };
template <typename T> struct remove_reference<T &&> { using type = T; };
template <typename T>
constexpr typename remove_reference<T>::type &&move(T &&t) noexcept {
  return static_cast<typename remove_reference<T>::type &&>(t);
}
} // namespace std

struct [[clang::linear("tok")]] Tok {
  Tok() = default;
  explicit Tok(int);
  Tok(Tok &&);
  Tok &operator=(Tok &&);
  ~Tok();
  void peek() const;
  [[clang::linear_consumer("tok")]] void finish();
};

Tok make();
void sink(Tok t);
void sink_rref(Tok &&t);
void observe(const Tok &t);

// Attribute checking.
struct NotLinear {
  [[clang::linear_consumer("tok")]] void finish(); // expected-warning {{'clang::linear_consumer' attribute on 'finish' has no effect: class 'NotLinear' has no 'linear' attribute}}
};
struct [[clang::linear("other")]] WrongTag {
  [[clang::linear_consumer("tok")]] void finish(); // expected-warning {{'clang::linear_consumer' attribute on 'finish' has no effect: its tag does not match the 'linear' attribute tag on class 'WrongTag'}}
};

// Clean usage: no diagnostics.
void ok_sink() {
  Tok t = make();
  sink(std::move(t));
}
void ok_sink_rref() {
  Tok t = make();
  sink_rref(std::move(t));
}
void ok_finish() {
  Tok t = make();
  t.finish();
}
void ok_finish_temp() { make().finish(); }
void ok_default() { Tok t; }
void ok_observe() {
  Tok t = make();
  observe(t);
  t.finish();
}
Tok ok_return() {
  Tok t = make();
  return t;
}
Tok ok_return_direct() { return make(); }
void ok_branch_both(bool c) {
  Tok t = make();
  if (c)
    t.finish();
  else
    sink(std::move(t));
}
void ok_loop_local(int n) {
  for (int i = 0; i < n; ++i) {
    Tok t = make();
    t.finish();
  }
}
void ok_reassign_after_consume() {
  Tok t = make();
  t.finish();
  t = make();
  t.finish();
}
void ok_default_then_assign() {
  Tok t;
  t = make();
  t.finish();
}

// Violations.
void err_leak() {
  Tok t = make(); // expected-note {{value created here}}
} // expected-error {{linear variable 't' of type 'Tok' is never consumed}}

void err_leak_temp() {
  make(); // expected-error {{temporary of linear type 'Tok' is never consumed}}
}

void err_double_finish() {
  Tok t = make();
  t.finish(); // expected-note {{consumed here}}
  t.finish(); // expected-error {{linear variable 't' of type 'Tok' is used after being consumed}}
}

void err_use_after_move() {
  Tok t = make();
  sink(std::move(t)); // expected-note {{consumed here}}
  t.finish();         // expected-error {{linear variable 't' of type 'Tok' is used after being consumed}}
}

void err_branch(bool c) {
  Tok t = make();
  if (c)
    t.finish(); // expected-note {{consumed here}}
} // expected-error {{linear variable 't' of type 'Tok' is not consumed on every control-flow path}}

void err_assign_discard() {
  Tok t = make(); // expected-note {{value created here}}
  t = make();     // expected-error {{assignment to linear variable 't' of type 'Tok' discards a value that has not been consumed}}
  t.finish();
}

void err_maybe_use(bool c) {
  Tok t = make();
  if (c)
    sink(std::move(t)); // expected-note {{consumed here}}
  t.finish(); // expected-error {{linear variable 't' of type 'Tok' is potentially used after being consumed}}
}

void err_default_then_assign_leak() {
  Tok t;
  t = make(); // expected-note {{value created here}}
} // expected-error {{linear variable 't' of type 'Tok' is never consumed}}

// Producer methods re-arm an object for another consumption cycle.
struct [[clang::linear("group")]] Group {
  Group();
  Group(Group &&);
  ~Group();
  [[clang::linear_producer("group")]] void add(Tok &&t);
  [[clang::linear_consumer("group")]] void run();
};

void ok_group_reuse() {
  Group g;
  g.add(make());
  g.run();
  g.add(make());
  g.run();
}

void err_group_rearmed_leak() {
  Group g;
  g.add(make());
  g.run();
  g.add(make()); // expected-note {{value created here}}
} // expected-error {{linear variable 'g' of type 'Group' is never consumed}}

// Trivially-destructible linear types have no destructor CFG elements;
// leaks are caught at the function exit or in discarded-value positions.
struct [[clang::linear("trivial")]] Triv {
  int x;
  [[clang::linear_consumer("trivial")]] void finish();
};
Triv make_triv();

void ok_triv() {
  Triv t = make_triv();
  t.finish();
}
void err_triv_leak() {
  Triv t = make_triv(); // expected-error {{linear variable 't' of type 'Triv' is never consumed}}
}
void err_triv_discard() {
  make_triv(); // expected-error {{temporary of linear type 'Triv' is never consumed}}
}
void err_triv_discard_void_cast() {
  (void)make_triv(); // expected-error {{temporary of linear type 'Triv' is never consumed}}
}

// Parameters: binding an argument to a by-value or rvalue-reference
// parameter consumes it in the caller, so the callee inherits the
// consumption obligation and must consume (or return) the parameter on
// every path. Lenient exceptions: unnamed parameters (an explicit drop),
// const-qualified parameters (cannot be consumed), lvalue-reference
// parameters (the caller retains ownership), and member functions of the
// linear class itself (whose special members manipulate raw fields of
// other instances).
void ok_param_sink(Tok t) { sink(std::move(t)); }
void ok_param_finish(Tok t) { t.finish(); }
Tok ok_param_return(Tok t) { return t; }
void ok_param_rref(Tok &&t) { sink_rref(std::move(t)); }
Tok ok_param_rref_return(Tok &&t) { return std::move(t); }
void ok_param_lref(Tok &t) {}
void ok_param_cref(const Tok &t) {}
void ok_param_unnamed(Tok) {}
void ok_param_const_val(const Tok t) {}
void ok_param_reassign(Tok t) {
  t.finish();
  t = make();
  t.finish();
}

// A path that provably does not return (assert failure handlers, abort)
// terminates the program rather than leaking the value; it must not demote
// values consumed on all returning paths.
[[noreturn]] void die();
void ok_param_noreturn_path(Tok t, bool c) {
  if (c)
    die();
  t.finish();
}
void ok_local_noreturn_path(bool c) {
  Tok t = make();
  if (c)
    die();
  sink(std::move(t));
}

// A constructor consuming its parameter in a member initializer.
struct ParamWrapper {
  Tok inner;
  ParamWrapper(Tok &&t) : inner(std::move(t)) {}
};

// Initializing a reference member from a linear value escapes it: ownership
// is handed to whoever later consumes through the reference (e.g. wrapper
// awaitables whose type parameter is deduced as an rvalue reference).
struct RefWrapper {
  Tok &&inner;
  RefWrapper(Tok &&t) : inner(static_cast<Tok &&>(t)) {}
};
void ok_ref_member_escape() {
  Tok t = make();
  RefWrapper w(std::move(t));
  w.inner.finish();
}

// Member functions of the linear class itself are exempt.
struct [[clang::linear("tok2")]] Tok2 {
  int h;
  Tok2(Tok2 &&o) : h(o.h) { o.h = 0; }
  Tok2 &operator=(Tok2 &&o) {
    h = o.h;
    o.h = 0;
    return *this;
  }
  [[clang::linear_consumer("tok2")]] void finish();
};

void err_param_leak(Tok t) {} // expected-error {{linear parameter 't' of type 'Tok' is never consumed}}
void err_param_rref_leak(Tok &&t) {} // expected-error {{linear parameter 't' of type 'Tok' is never consumed}}

void err_param_branch(Tok t, bool c) { // expected-error {{linear parameter 't' of type 'Tok' is not consumed on every control-flow path}}
  if (c)
    t.finish(); // expected-note {{consumed here}}
}

void err_param_double_consume(Tok t) {
  t.finish(); // expected-note {{consumed here}}
  t.finish(); // expected-error {{linear variable 't' of type 'Tok' is used after being consumed}}
}

struct BadParamWrapper {
  int x;
  BadParamWrapper(Tok &&t) : x(0) {} // expected-error {{linear parameter 't' of type 'Tok' is never consumed}}
};

void err_triv_param_leak(Triv t) {} // expected-error {{linear parameter 't' of type 'Triv' is never consumed}}

// linear_consumer in parameter position: the obligation is discharged at
// the call boundary. The caller consumes the argument at the call site; the
// callee is trusted, not tracked — even a body that visibly drops or only
// conditionally forwards the value is accepted.
void boundary_sink([[clang::linear_consumer("tok")]] Tok &&t) {}
void boundary_cond([[clang::linear_consumer("tok")]] Tok &&t, bool c) {
  if (c)
    sink(std::move(t));
}
void ok_boundary_caller(bool c) {
  Tok t = make();
  boundary_cond(std::move(t), c);
}
void err_boundary_double() {
  Tok t = make();
  boundary_sink(std::move(t)); // expected-note {{consumed here}}
  boundary_sink(std::move(t)); // expected-error {{linear variable 't' of type 'Tok' is used after being consumed}}
}

// An annotated lvalue-reference parameter also consumes at the call site (a
// capability the structural rvalue-reference rule does not provide).
void lref_consume([[clang::linear_consumer("tok")]] Tok &t);
void ok_lref_consumer() {
  Tok t = make();
  lref_consume(t);
}
void err_lref_consumer_double() {
  Tok t = make();
  lref_consume(t); // expected-note {{consumed here}}
  lref_consume(t); // expected-error {{linear variable 't' of type 'Tok' is used after being consumed}}
}

// A parameter whose type is a class template specialization that is never
// instantiated (a reference parameter and an empty body require no complete
// type) must still be armed: the linear attribute is read from the primary
// template's pattern.
template <typename T> struct [[clang::linear("tpl")]] TplTok {
  T x;
  [[clang::linear_consumer("tpl")]] void finish();
};
void err_uninstantiated_spec_param(TplTok<int> &&t) {} // expected-error {{linear parameter 't' of type 'TplTok<int>' is never consumed}}

// Container taint: moving a linear value into a non-linear local object
// through an unannotated rvalue-reference parameter of a member call leaves
// the obligation inside the object. The container must be consumed by
// passing it — or an iterator/pointer obtained from it — to a
// consumer-annotated parameter; unrecognized uses leniently end tracking.
template <typename T> struct Vec {
  T *p;
  unsigned n;
  Vec();
  ~Vec();
  Vec(Vec &&);
  Vec &operator=(Vec &&);
  void push_back(T &&);
  T &operator[](unsigned);
  T *begin();
  T *end();
  T *data();
  unsigned size() const;
  bool empty() const;
  void clear();
  void reserve(unsigned);
};

template <typename I>
void spawn_iters([[clang::linear_consumer("tok")]] I &&b,
                 [[clang::linear_consumer("tok")]] I &&e);
template <typename I>
void spawn_n([[clang::linear_consumer("tok")]] I &&b, unsigned n);
template <typename R>
void spawn_range([[clang::linear_consumer("tok")]] R &&r);
void take_vec_ref(Vec<Tok> &v);

void ok_container_spawn_range() {
  Vec<Tok> v;
  v.push_back(make());
  spawn_range(v);
}
void ok_container_spawn_iters() {
  Vec<Tok> v;
  v.push_back(make());
  spawn_iters(v.begin(), v.end());
}
void ok_container_spawn_data_count() {
  Vec<Tok> v;
  v.push_back(make());
  spawn_n(v.data(), v.size());
}
void ok_container_ptr_arith() {
  Vec<Tok> v;
  v.push_back(make());
  spawn_iters(v.data(), v.data() + 1);
}
void ok_container_iter_vars() {
  Vec<Tok> v;
  v.push_back(make());
  auto b = v.begin();
  auto e = v.end();
  spawn_iters(b, e);
}
void ok_container_loop_fill(int n) {
  Vec<Tok> v;
  v.reserve(4);
  for (int i = 0; i < n; ++i)
    v.push_back(make());
  spawn_range(v);
}
void ok_container_empty_guard(int n) {
  Vec<Tok> v;
  for (int i = 0; i < n; ++i)
    v.push_back(make());
  if (!v.empty())
    spawn_range(v);
}
void ok_container_helper_escape() {
  Vec<Tok> v;
  v.push_back(make());
  take_vec_ref(v); // unannotated reference: lenient escape
}
void ok_container_manual_drain() {
  Vec<Tok> v;
  v.push_back(make());
  for (auto &t : v)
    t.finish();
}
void ok_container_elem_drain() {
  Vec<Tok> v;
  v.push_back(make());
  v[0].finish();
}
void ok_container_conditional_fill(bool c) {
  Vec<Tok> v;
  if (c)
    v.push_back(make());
  spawn_range(v);
}
void ok_container_reuse() {
  Vec<Tok> v;
  v.push_back(make());
  spawn_range(v);
  v.clear();
  v.push_back(make());
  spawn_range(v);
}
void ok_container_move_transfer() {
  Vec<Tok> v;
  v.push_back(make());
  Vec<Tok> v2 = std::move(v);
  spawn_range(v2);
}
Vec<Tok> ok_container_return() {
  Vec<Tok> v;
  v.push_back(make());
  return v; // the obligation moves to the caller
}
void ok_container_lambda_fill() {
  // The lambda's own analysis must not arm the captured container; the
  // enclosing function owns it.
  Vec<Tok> v;
  auto fill = [&v] { v.push_back(make()); };
  fill();
  spawn_range(v);
}

void err_container_fill_drop() {
  Vec<Tok> v;
  v.push_back(make()); // expected-note {{linear value moved into the container here}}
} // expected-error {{'v' holds at least one value of linear type 'Tok' that is never consumed}}

void err_container_loop_fill_drop(int n) {
  Vec<Tok> v; // expected-error {{'v' holds at least one value of linear type 'Tok' that is never consumed}}
  for (int i = 0; i < n; ++i)
    v.push_back(make()); // expected-note {{linear value moved into the container here}}
}

void err_container_conditional_spawn(bool c) {
  Vec<Tok> v;
  v.push_back(make());
  if (c)
    spawn_range(v); // expected-note {{consumed here}}
} // expected-error {{'v' holds at least one value of linear type 'Tok' that is not consumed on every control-flow path}}

void err_container_double_spawn() {
  Vec<Tok> v;
  v.push_back(make());
  spawn_range(v); // expected-note {{consumed here}}
  spawn_range(v); // expected-error {{the linear contents of 'v' are consumed a second time}}
}

void err_container_elem_assign_drop() {
  Vec<Tok> v;
  v[0] = make(); // expected-note {{linear value moved into the container here}}
} // expected-error {{'v' holds at least one value of linear type 'Tok' that is never consumed}}

void err_container_move_drop() {
  Vec<Tok> v;
  v.push_back(make()); // expected-note {{linear value moved into the container here}}
  Vec<Tok> v2 = std::move(v);
} // expected-error {{'v2' holds at least one value of linear type 'Tok' that is never consumed}}

// A non-linear object constructed directly from a linear value.
template <typename T> struct Opt {
  Opt(T &&);
  ~Opt();
  T take(); // value-returning member: leniently ends tracking
};
void ok_opt_take() {
  Opt<Tok> o(make());
  o.take().finish();
}
void err_opt_drop() {
  Opt<Tok> o(make()); // expected-note {{linear value moved into the container here}}
} // expected-error {{'o' holds at least one value of linear type 'Tok' that is never consumed}}

// A container with no destructor produces no dtor CFG elements; taint is
// reported by the exit sweep at the variable's declaration.
template <typename T> struct TrivBox {
  T v;
  void put(T &&);
};
void err_trivbox_drop() {
  TrivBox<Triv> b; // expected-error {{'b' holds at least one value of linear type 'Triv' that is never consumed}}
  b.put(make_triv()); // expected-note {{linear value moved into the container here}}
}

// Detection looks through pointer type arguments, so a handle type whose
// only linear connection is a pointer argument (libc++'s vector iterator:
// __wrap_iter<task*>) behaves the same as one that names the container
// (libstdc++: __normal_iterator<task*, vector<task>>). Writing a linear
// value through such a view taints it; a consumer-annotated call (e.g.
// tmc::consume()) discharges it.
template <typename P> struct PtrIter {
  P p;
  PtrIter &operator++();
  Tok &operator*();
};
void err_ptr_view_write(PtrIter<Tok *> it) { // expected-error {{'it' holds at least one value of linear type 'Tok' that is never consumed}}
  *it = make(); // expected-note {{linear value moved into the container here}}
}
void ok_ptr_view_write_consumed(PtrIter<Tok *> it) {
  *it = make();
  spawn_n(it, 1); // annotated consumer discharges the view's taint
}

// A class-type iterator (operator*) works like a pointer iterator.
template <typename T> struct ClsIter {
  T *p;
  T &operator*();
  ClsIter &operator++();
  bool operator!=(const ClsIter &) const;
};
template <typename T> struct VecCls {
  VecCls();
  ~VecCls();
  void push_back(T &&);
  ClsIter<T> begin();
  ClsIter<T> end();
};
void ok_container_class_iter() {
  VecCls<Tok> v;
  v.push_back(make());
  spawn_iters(v.begin(), v.end());
}
void err_container_class_iter_drop() {
  VecCls<Tok> v;
  v.push_back(make()); // expected-note {{linear value moved into the container here}}
} // expected-error {{'v' holds at least one value of linear type 'Tok' that is never consumed}}

// Conditional consumption: [[clang::linear_consumer("tag", conditional)]]
// consumes the argument only if the call returns true (modeling e.g. a
// channel post that fails and leaves the value untouched when the channel
// is closed). The tracking state is split on a branch that tests the call's
// result; the returns-false edge still owns the value.
struct Chan {
  bool post([[clang::linear_consumer("tok", conditional)]] Tok &&t);
  void close();
};
struct ChanInt {
  // A conditional consumer without a testable (boolean) result consumes
  // unconditionally, as if the mode were absent.
  int post([[clang::linear_consumer("tok", conditional)]] Tok &&t);
};

// Attribute argument checking.
struct BadMode {
  bool post([[clang::linear_consumer("tok", sometimes)]] Tok &&t); // expected-warning {{attribute argument not supported: 'sometimes'}}
  bool post2([[clang::linear_consumer("tok", 42)]] Tok &&t); // expected-error {{attribute requires parameter 2 to be an identifier}}
};

void ok_cond_fallback(Chan &c) {
  Tok t = make();
  if (!c.post(std::move(t)))
    t.finish(); // post failed: still owned here
}
void ok_cond_fallback_else(Chan &c) {
  Tok t = make();
  if (c.post(std::move(t))) {
  } else {
    sink(std::move(t));
  }
}
void ok_cond_double_negation(Chan &c) {
  Tok t = make();
  if (!!c.post(std::move(t))) {
  } else {
    t.finish();
  }
}
void ok_cond_bool_var(Chan &c) {
  Tok t = make();
  bool ok = c.post(std::move(t));
  if (!ok)
    t.finish();
}
void ok_cond_ternary(Chan &c) {
  Tok t = make();
  c.post(std::move(t)) ? (void)0 : sink(std::move(t));
}
void ok_cond_retry_loop(Chan &c) {
  Tok t = make();
  while (!c.post(std::move(t))) {
  }
}
void ok_cond_retry_nested(Chan &c) {
  Tok t = make();
  if (!c.post(std::move(t))) {
    if (!c.post(std::move(t)))
      t.finish();
  }
}
void ok_cond_nonbool_result(ChanInt &c) {
  Tok t = make();
  c.post(std::move(t));
}

void err_cond_drop_on_false(Chan &c) {
  Tok t = make();
  if (!c.post(std::move(t))) { // expected-note {{consumed here}}
    // t is still owned here and then dropped.
  }
} // expected-error {{linear variable 't' of type 'Tok' is not consumed on every control-flow path}}

void err_cond_result_discarded(Chan &c) {
  Tok t = make();
  c.post(std::move(t)); // expected-note {{consumed here}}
} // expected-error {{linear variable 't' of type 'Tok' is not consumed on every control-flow path}}

void err_cond_use_after_success(Chan &c) {
  Tok t = make();
  if (c.post(std::move(t))) // expected-note {{consumed here}}
    t.finish(); // expected-error {{linear variable 't' of type 'Tok' is used after being consumed}}
  else
    sink(std::move(t));
}

void err_cond_repost_unbranched(Chan &c) {
  Tok t = make();
  c.post(std::move(t)); // expected-note {{consumed here}}
  c.post(std::move(t)); // expected-error {{linear variable 't' of type 'Tok' is potentially used after being consumed}}
}

// A temporary argument cannot be recovered on the failure path: it dies at
// the end of the condition's full-expression, where it is only maybe
// consumed. Use a named variable to write the fallback.
void err_cond_temp_arg(Chan &c) {
  if (!c.post(make())) { // expected-error {{temporary of linear type 'Tok' is not consumed on every control-flow path}} expected-note {{consumed here}}
  }
}

// Reassigning the bool that captured the result ends the association: the
// analysis conservatively keeps the value maybe-consumed on both branches.
void err_cond_bool_var_reassigned(Chan &c, bool other) {
  Tok t = make();
  bool ok = c.post(std::move(t)); // expected-note 2 {{consumed here}}
  ok = other;
  if (!ok)
    t.finish(); // expected-error {{linear variable 't' of type 'Tok' is potentially used after being consumed}}
  else
    sink(std::move(t)); // expected-error {{linear variable 't' of type 'Tok' is potentially used after being consumed}}
}

// A conditional consumer *method* consumes the object it is invoked on only
// if it returns true.
struct [[clang::linear("tok2")]] TryTok {
  TryTok();
  TryTok(TryTok &&);
  ~TryTok();
  [[clang::linear_consumer("tok2", conditional)]] bool try_commit();
  [[clang::linear_consumer("tok2")]] void abort();
};
TryTok make_try();
void ok_cond_method() {
  TryTok t = make_try();
  if (!t.try_commit())
    t.abort();
}
void err_cond_method_drop() {
  TryTok t = make_try();
  if (t.try_commit()) { // expected-note {{consumed here}}
  }
} // expected-error {{linear variable 't' of type 'TryTok' is not consumed on every control-flow path}}

// Comparisons against bool constants are equivalent to the negation forms.
void ok_cond_eq_false(Chan &c) {
  Tok t = make();
  bool ok = c.post(std::move(t));
  if (ok == false)
    t.finish();
}
void ok_cond_ne_true_direct(Chan &c) {
  Tok t = make();
  if (c.post(std::move(t)) != true)
    sink(std::move(t));
}
void ok_cond_literal_first(Chan &c) {
  Tok t = make();
  if (false == c.post(std::move(t)))
    t.finish();
}
void ok_cond_eq_zero(Chan &c) {
  Tok t = make();
  bool ok = c.post(std::move(t));
  if (ok == 0)
    t.finish();
}
void ok_cond_not_eq_true(Chan &c) {
  Tok t = make();
  if (!(c.post(std::move(t)) == true))
    t.finish();
}
void err_cond_eq_true_drop(Chan &c) {
  Tok t = make();
  if (c.post(std::move(t)) == true) { // expected-note {{consumed here}}
  }
} // expected-error {{linear variable 't' of type 'Tok' is not consumed on every control-flow path}}

// A flag variable may be reused: assigning a new conditional-consumer call
// result into it rebinds the association.
void ok_cond_bool_var_rebound(Chan &c) {
  Tok t1 = make();
  bool ok = c.post(std::move(t1));
  if (!ok)
    t1.finish();
  Tok t2 = make();
  ok = c.post(std::move(t2));
  if (ok == false)
    t2.finish();
}

// Escape hatch: consuming the *result* of a conditional-consumer call (or
// the bool variable holding it) with a matching-tag annotated consumer
// discharges the pending obligation — for callers that know the failure
// path is unreachable and deliberately ignore the result.
template <typename... A> void discharge([[clang::linear_consumer("tok")]] A &&...);
template <typename... A> void discharge_triv([[clang::linear_consumer("trivial")]] A &&...);
template <typename... A> void discharge_other([[clang::linear_consumer("other")]] A &&...);

void ok_cond_discharge_named(Chan &c) {
  Tok t = make();
  discharge(c.post(std::move(t)));
}
void ok_cond_discharge_temp(Chan &c) { discharge(c.post(make())); }
void ok_cond_discharge_bool_var(Chan &c) {
  Tok t = make();
  bool ok = c.post(std::move(t));
  discharge(ok);
}
// A consumer with a non-matching tag does not discharge.
void err_cond_discharge_wrong_tag(Chan &c) {
  Tok t = make();
  discharge_other(c.post(std::move(t))); // expected-note {{consumed here}}
} // expected-error {{linear variable 't' of type 'Tok' is not consumed on every control-flow path}}

// A fresh temporary of a *trivially-destructible* linear type bound to a
// conditional consumer has no tracked identity (no CXXBindTemporaryExpr)
// and no handle a failure branch could recover; it is reported even when
// the result is branched on, unless the result is explicitly discharged.
// This mirrors the maybe-unconsumed report that a temporary with a
// destructor gets at its dtor.
struct ChanTriv {
  bool post([[clang::linear_consumer("trivial", conditional)]] Triv &&t);
};
void err_cond_triv_temp(ChanTriv &c) {
  c.post(make_triv()); // expected-error {{temporary of linear type 'Triv' is not consumed on every control-flow path}} expected-note {{consumed here}}
}
void err_cond_triv_temp_branched(ChanTriv &c) {
  if (!c.post(make_triv())) { // expected-error {{temporary of linear type 'Triv' is not consumed on every control-flow path}} expected-note {{consumed here}}
  }
}
void ok_cond_triv_temp_discharged(ChanTriv &c) {
  discharge_triv(c.post(make_triv()));
}

// Sentinel-mode (drain-style) consumption:
// [[clang::linear_consumer("tag", sentinel)]] consumes the object it is
// invoked on only when the call's result compares equal to the value of the
// class's [[clang::linear_sentinel]] member. Models multiplexers that must
// be awaited until they report completion (co_await mux == mux.end()).
using size_t = decltype(sizeof(0));

class [[clang::linear("mux")]] Mux {
public:
  Mux();          // empty: does not require draining until fork()
  explicit Mux(int); // eagerly armed
  [[clang::linear_consumer("mux", sentinel)]] size_t await_resume();
  [[clang::linear_sentinel("mux")]] size_t end() const;
  [[clang::linear_producer("mux")]] void fork(int);
  size_t operator[](size_t);
  Mux(const Mux &) = delete;
  Mux &operator=(const Mux &) = delete;
  ~Mux();
};
template <typename... A> void consume_mux([[clang::linear_consumer("mux")]] A &&...);
void expect_eq(size_t, size_t); // opaque comparison helper (EXPECT_EQ shape)
void use(size_t);

// Attribute misuse.
struct NotLinearMux {
  [[clang::linear_sentinel("mux")]] size_t end() const; // expected-warning {{'clang::linear_sentinel' attribute on 'end' has no effect: class 'NotLinearMux' has no 'linear' attribute}}
};
struct [[clang::linear("other2")]] WrongTagMux {
  [[clang::linear_sentinel("mux")]] size_t end() const; // expected-warning {{'clang::linear_sentinel' attribute on 'end' has no effect: its tag does not match the 'linear' attribute tag on class 'WrongTagMux'}}
};

// The canonical drain loop is clean.
void ok_mux_drain_for() {
  Mux m(2);
  for (size_t i = m.await_resume(); i != m.end(); i = m.await_resume())
    use(m[i]);
}
// While-true with a break on the sentinel.
void ok_mux_drain_break() {
  Mux m(2);
  while (true) {
    size_t i = m.await_resume();
    if (i == m.end())
      break;
    use(m[i]);
  }
}
// Do-while drain: the split applies across the loop back edge.
void ok_mux_drain_do_while() {
  Mux m(2);
  size_t i;
  do {
    i = m.await_resume();
  } while (i != m.end());
}
// Assignment inside the condition.
void ok_mux_assign_in_condition() {
  Mux m(2);
  size_t i;
  while ((i = m.await_resume()) != m.end())
    use(m[i]);
}
// Negations and literal-first comparisons resolve.
void ok_mux_negated() {
  Mux m(2);
  size_t i = m.await_resume();
  while (!(i == m.end()))
    i = m.await_resume();
}
void ok_mux_sentinel_first() {
  Mux m(1);
  size_t i = m.await_resume();
  while (m.end() != i)
    i = m.await_resume();
}
// A cached sentinel variable works like the direct call.
void ok_mux_cached_sentinel() {
  Mux m(2);
  auto e = m.end();
  size_t i = m.await_resume();
  while (i != e)
    i = m.await_resume();
}
// Direct comparison of the call result (no variable).
void ok_mux_direct_compare() {
  Mux m(1);
  if (m.await_resume() == m.end())
    return;
  size_t i = m.await_resume();
  expect_eq(i, m.end());
}
// A drained mux may be re-awaited (it reports the sentinel again), and a
// known number of results may be consumed untested as long as a later drain
// is proven: sentinel-mode calls re-park from any state without diagnosing
// double consumption.
void ok_mux_count_then_drain() {
  Mux m(3);
  size_t a = m.await_resume();
  size_t b = m.await_resume();
  use(a);
  use(b);
  for (size_t i = m.await_resume(); i != m.end(); i = m.await_resume())
    use(m[i]);
}
// fork() re-arms a drained (or empty) mux; a second drain proves it again.
void ok_mux_fork_rearm() {
  Mux m(2);
  for (size_t i = m.await_resume(); i != m.end(); i = m.await_resume())
    use(m[i]);
  m.fork(0);
  for (size_t i = m.await_resume(); i != m.end(); i = m.await_resume())
    use(m[i]);
}
// An empty mux does not require draining; forking into it arms it.
void ok_mux_empty() { Mux m; }
void ok_mux_empty_fork_drain() {
  Mux m;
  m.fork(0);
  for (size_t i = m.await_resume(); i != m.end(); i = m.await_resume())
    use(m[i]);
}
// Passing the result and the object's sentinel together to one opaque call
// (an equality-assertion helper) discharges the obligation.
void ok_mux_opaque_compare() {
  Mux m(1);
  size_t i = m.await_resume();
  expect_eq(i, m.end());
}
// Passing the mux itself to a matching-tag annotated consumer discharges,
// even while parked by an untested await (the count-based escape hatch).
void ok_mux_consume_parked() {
  Mux m(2);
  size_t i = m.await_resume();
  use(i);
  consume_mux(m);
}
// Discharging the pending *result* also releases the park (same idiom as
// the bool mode's consume(post(...))).
void ok_mux_result_discharge() {
  Mux m(2);
  size_t i = m.await_resume();
  consume_mux(i);
}

// Never awaited.
void err_mux_never_awaited() {
  Mux m(2); // expected-note {{value created here}}
} // expected-error {{linear variable 'm' of type 'Mux' is never drained; it must be awaited until it returns its end() sentinel (or passed to a consuming operation) before it is destroyed}}
// Awaited, result never compared against the sentinel.
void err_mux_unchecked_await() {
  Mux m(2);
  size_t i = m.await_resume(); // expected-note {{last awaited here; the result was not compared against the end() sentinel on this path}}
  use(i);
} // expected-error {{linear variable 'm' of type 'Mux' is not proven drained on every control-flow path; compare the awaited result against the end() sentinel to prove completion}}
// Comparing against something other than the sentinel proves nothing; in
// particular `i == 1` must not resolve as a boolean test of the result.
void err_mux_wrong_compare() {
  Mux m(2);
  size_t i = m.await_resume(); // expected-note {{last awaited here}}
  if (i == 1)
    use(m[i]);
} // expected-error {{linear variable 'm' of type 'Mux' is not proven drained on every control-flow path}}
// Comparing against a *different* mux's sentinel proves nothing.
void err_mux_cross_compare() {
  Mux m1(2); // m1 is diagnosed
  Mux m2(2);
  size_t i = m1.await_resume(); // expected-note {{last awaited here}}
  if (i == m2.end()) {
  }
  for (size_t j = m2.await_resume(); j != m2.end(); j = m2.await_resume())
    use(j);
} // expected-error {{linear variable 'm1' of type 'Mux' is not proven drained on every control-flow path}}
// fork() after a proven drain re-arms the obligation.
void err_mux_fork_rearm_leak() {
  Mux m(2);
  for (size_t i = m.await_resume(); i != m.end(); i = m.await_resume())
    use(m[i]);
  m.fork(0); // expected-note {{value created here}}
} // expected-error {{linear variable 'm' of type 'Mux' is never drained}}
// An opaque call without the sentinel does not discharge.
void err_mux_opaque_no_sentinel() {
  Mux m(2);
  size_t i = m.await_resume(); // expected-note {{last awaited here}}
  expect_eq(i, 3);
} // expected-error {{linear variable 'm' of type 'Mux' is not proven drained on every control-flow path}}
// The forked-but-never-drained empty mux.
void err_mux_empty_fork_leak() {
  Mux m;
  m.fork(0); // expected-note {{value created here}}
} // expected-error {{linear variable 'm' of type 'Mux' is never drained}}

// Sentinel-mode drain refinement across a `switch` on the awaited result
// (`switch (idx) { ... case mux.end(): ...; }`). A switch is not a
// two-successor boolean branch, but when its condition is the pending result
// of a drain-consumer call each outgoing edge is decidable from its case
// label: the `case mux.end():` edge is taken only when the result equalled
// the sentinel (drained), every other case and the default edge restore the
// pre-await owned state. The label is a constant expression, so end() must be
// constexpr to be usable as one; it must not read *this.
class [[clang::linear("mux")]] SwMux {
public:
  explicit SwMux(int);
  [[clang::linear_consumer("mux", sentinel)]] size_t await_resume();
  [[clang::linear_sentinel("mux")]] constexpr size_t end() const { return 8; }
  size_t operator[](size_t);
  SwMux(const SwMux &) = delete;
  SwMux &operator=(const SwMux &) = delete;
  ~SwMux();
};
// A distinct drainable type whose sentinel is a different constant, for the
// cross-object identity check.
class [[clang::linear("mux")]] SwMux9 {
public:
  explicit SwMux9(int);
  [[clang::linear_consumer("mux", sentinel)]] size_t await_resume();
  [[clang::linear_sentinel("mux")]] constexpr size_t end() const { return 9; }
  ~SwMux9();
};

// The batch-processor shape: a `case mux.end():` proves the drain; the other
// cases restart work and loop. Clean.
void ok_switch_drain() {
  SwMux m(2);
  while (true) {
    size_t idx = m.await_resume();
    switch (idx) {
    case 0: use(m[idx]); break;
    case 1: use(m[idx]); break;
    case m.end(): return;
    }
  }
}
// The idiomatic form with a `default:` that is *not* the drain: the drain is
// the explicit `case mux.end():` and default just processes an active slot
// and keeps looping. The default edge restores the owned state (so the loop
// head stays consistent) without being mistaken for a drain.
void ok_switch_drain_default_continues() {
  SwMux m(2);
  while (true) {
    size_t idx = m.await_resume();
    switch (idx) {
    case m.end(): return;
    default: use(m[idx]); break;
    }
  }
}
// No `case end():` and no exit at all: the mux dtor is unreachable, so there
// is nothing to leak. The back edge carries the restored owned state, so the
// loop-iteration consistency check is also satisfied (no spurious mismatch).
void ok_switch_no_end_infinite() {
  SwMux m(2);
  while (true) {
    size_t idx = m.await_resume();
    switch (idx) {
    case 0: use(m[idx]); break;
    case 1: use(m[idx]); break;
    }
  }
}
// Soundness: a switch that exits on a *non-drain* edge leaves the mux owned,
// and the leak is still reported at that exit. Restoring the owned state on
// the non-drain edges never masks a leak.
void err_switch_non_drain_exit() {
  SwMux m(2); // expected-note {{value created here}}
  while (true) {
    size_t idx = m.await_resume();
    switch (idx) {
    case 0:
      return; // expected-error {{linear variable 'm' of type 'SwMux' is never drained; it must be awaited until it returns its end() sentinel (or passed to a consuming operation) before it is destroyed}}
    case 1:
      use(m[idx]);
      break;
    case m.end():
      return;
    }
  }
}
// A `default:` cannot prove `idx == end()` (it also covers every other value),
// so using it as the drain edge is a conservative false positive: rewrite as
// an explicit `case mux.end():`.
void err_switch_default_as_drain() {
  SwMux m(2); // expected-note {{value created here}}
  while (true) {
    size_t idx = m.await_resume();
    switch (idx) {
    case 0: use(m[idx]); break;
    default:
      return; // expected-error {{linear variable 'm' of type 'SwMux' is never drained}}
    }
  }
}
// Identity: a case label that is a *different* object's sentinel proves
// nothing about this mux. 'm' must still be reported.
void err_switch_cross_mux() {
  SwMux m(2); // expected-note {{value created here}}
  SwMux9 other(2);
  consume_mux(other); // discharge 'other' so only 'm' is in question
  while (true) {
    size_t idx = m.await_resume();
    switch (idx) {
    case 0: use(m[idx]); break;
    case other.end():
      return; // expected-error {{linear variable 'm' of type 'SwMux' is never drained}}
    }
  }
}
// Soundness against stacked case labels: when the sentinel case shares its
// body with a non-sentinel case, that body is reachable when idx != end()
// (undrained). The CFG gives each label its own edge — the non-sentinel
// case's edge restores the owned state and falls through into the shared
// body — so the merge is maybe-consumed and the leak is still reported (not
// silently treated as drained).
void err_switch_stacked_sentinel() {
  SwMux m(2);
  while (true) {
    size_t idx = m.await_resume(); // expected-note {{last awaited here; the result was not compared against the end() sentinel on this path}}
    switch (idx) {
    case 0:
    case m.end():
      use(m[idx]);
      return; // expected-error {{linear variable 'm' of type 'SwMux' is not proven drained on every control-flow path}}
    case 1:
      use(m[idx]);
      break;
    }
  }
}

// The same tracking works through the coroutine await machinery: the mux is
// forwarded by reference through the promise's await_transform (borrow
// pass-through), the pending consumption is re-keyed to the co_await
// expression, and `size_t i = co_await mux` ties `i` to it.
namespace std {
template <class Ret, typename... T>
struct coroutine_traits { using promise_type = typename Ret::promise_type; };
template <class Promise = void> struct coroutine_handle {
  static coroutine_handle from_address(void *) noexcept;
};
template <> struct coroutine_handle<void> {
  template <class P> coroutine_handle(coroutine_handle<P>) noexcept;
  static coroutine_handle from_address(void *) noexcept;
};
struct suspend_never {
  bool await_ready() noexcept;
  void await_suspend(coroutine_handle<>) noexcept;
  void await_resume() noexcept;
};
} // namespace std

class [[clang::linear("mux")]] AwaitableMux {
public:
  AwaitableMux();
  explicit AwaitableMux(int);
  bool await_ready() const noexcept;
  void await_suspend(std::coroutine_handle<>) noexcept;
  [[clang::linear_consumer("mux", sentinel)]] size_t await_resume() noexcept;
  AwaitableMux &operator co_await() & noexcept { return *this; }
  [[clang::linear_sentinel("mux")]] size_t end() const noexcept;
  [[clang::linear_producer("mux")]] void fork(int);
  size_t operator[](size_t);
  AwaitableMux(const AwaitableMux &) = delete;
  AwaitableMux &operator=(const AwaitableMux &) = delete;
  ~AwaitableMux();
};

struct CoroTask {
  struct promise_type {
    CoroTask get_return_object();
    std::suspend_never initial_suspend();
    std::suspend_never final_suspend() noexcept;
    void return_void();
    void unhandled_exception();
    template <typename Awaitable>
    decltype(auto) await_transform(Awaitable &&awaitable) noexcept {
      return static_cast<Awaitable &&>(awaitable).operator co_await();
    }
  };
};

CoroTask ok_coro_mux_drain() {
  AwaitableMux m(2);
  for (size_t i = co_await m; i != m.end(); i = co_await m)
    use(m[i]);
}
CoroTask ok_coro_mux_break() {
  AwaitableMux m(2);
  while (true) {
    size_t i = co_await m;
    if (i == m.end())
      break;
    use(m[i]);
  }
}
CoroTask ok_coro_mux_direct() {
  AwaitableMux m(1);
  while ((co_await m) != m.end()) {
  }
}
CoroTask err_coro_mux_unchecked() {
  AwaitableMux m(2);
  size_t i = co_await m; // expected-note {{last awaited here}}
  use(i);
} // expected-error {{linear variable 'm' of type 'AwaitableMux' is not proven drained on every control-flow path}}
CoroTask err_coro_mux_never_awaited() {
  AwaitableMux m(2); // expected-note {{value created here}}
  co_return; // expected-error {{linear variable 'm' of type 'AwaitableMux' is never drained}}
}

// Deferred conditional consumption through an awaitable: a conditional
// consumer that returns an awaitable object parks its arguments at the
// call; co_awaiting the result attributes the awaited value back to the
// call. A bool resume value is the deferred success result — test it like
// any conditional result. A void resume value completes the consumption at
// the await (an always-enqueues bounded-queue push). Any other resume type
// proves nothing. An awaitable that is never awaited, or an awaited bool
// that is never tested, leaves the value unproven (strict).
struct BoolPushResult {
  bool await_ready() const noexcept;
  void await_suspend(std::coroutine_handle<>) noexcept;
  bool await_resume() noexcept;
};
struct BoolPushAwaitable {
  BoolPushResult operator co_await() && noexcept;
};
struct VoidPushResult {
  bool await_ready() const noexcept;
  void await_suspend(std::coroutine_handle<>) noexcept;
  void await_resume() noexcept;
};
struct VoidPushAwaitable {
  VoidPushResult operator co_await() && noexcept;
};
struct IntPushResult {
  bool await_ready() const noexcept;
  void await_suspend(std::coroutine_handle<>) noexcept;
  int await_resume() noexcept;
};
struct IntPushAwaitable {
  IntPushResult operator co_await() && noexcept;
};
struct AsyncChan {
  BoolPushAwaitable push([[clang::linear_consumer("tok", conditional)]] Tok &&t);
  VoidPushAwaitable push_always([[clang::linear_consumer("tok", conditional)]] Tok &&t);
  IntPushAwaitable push_int([[clang::linear_consumer("tok", conditional)]] Tok &&t);
};

CoroTask ok_push_fallback(AsyncChan &c) {
  Tok t = make();
  if (!co_await c.push(std::move(t)))
    t.finish();
}
CoroTask ok_push_else(AsyncChan &c) {
  Tok t = make();
  if (co_await c.push(std::move(t))) {
  } else {
    t.finish();
  }
}
CoroTask ok_push_bool_var(AsyncChan &c) {
  Tok t = make();
  bool ok = co_await c.push(std::move(t));
  if (!ok)
    t.finish();
}
CoroTask ok_push_awaitable_var(AsyncChan &c) {
  Tok t = make();
  auto aw = c.push(std::move(t));
  if (!co_await std::move(aw))
    t.finish();
}
CoroTask ok_push_retry(AsyncChan &c) {
  Tok t = make();
  while (!co_await c.push(std::move(t))) {
  }
}
// Deliberate ignore: discharging the awaited result.
CoroTask ok_push_result_discharged(AsyncChan &c) {
  Tok t = make();
  discharge(co_await c.push(std::move(t)));
}
// Awaiting a void-resume awaitable completes the consumption; there is
// nothing to test.
CoroTask ok_void_push(AsyncChan &c) {
  Tok t = make();
  co_await c.push_always(std::move(t));
}
CoroTask err_push_result_ignored(AsyncChan &c) {
  Tok t = make();
  co_await c.push(std::move(t)); // expected-note {{consumed here}}
} // expected-error {{linear variable 't' of type 'Tok' is not consumed on every control-flow path}}
CoroTask err_push_never_awaited(AsyncChan &c) {
  Tok t = make();
  auto aw = c.push(std::move(t)); // expected-note {{consumed here}}
  co_return; // expected-error {{linear variable 't' of type 'Tok' is not consumed on every control-flow path}}
}
CoroTask err_push_failure_drops(AsyncChan &c) {
  Tok t = make();
  if (!co_await c.push(std::move(t))) { // expected-note {{consumed here}}
    /* t still owned here, then dropped */
  }
} // expected-error {{linear variable 't' of type 'Tok' is not consumed on every control-flow path}}
CoroTask err_push_use_after_success(AsyncChan &c) {
  Tok t = make();
  if (co_await c.push(std::move(t))) // expected-note {{consumed here}}
    t.finish(); // expected-error {{linear variable 't' of type 'Tok' is used after being consumed}}
  else
    sink(std::move(t));
}
// A temporary argument is unrecoverable on the failure path even when the
// result is tested: it dies at the end of the full-expression, before the
// branch.
CoroTask err_push_temporary(AsyncChan &c) {
  if (!co_await c.push(make())) { // expected-error {{temporary of linear type 'Tok' is not consumed on every control-flow path}} expected-note {{consumed here}}
  }
}
// A non-bool, non-void resume type cannot deliver the result; the pending
// obligation stays strict.
CoroTask err_push_int_resume(AsyncChan &c) {
  Tok t = make();
  int n = co_await c.push_int(std::move(t)); // expected-note {{consumed here}}
  use(n);
} // expected-error {{linear variable 't' of type 'Tok' is not consumed on every control-flow path}}
