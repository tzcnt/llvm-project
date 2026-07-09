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
  [[clang::linear_consumer("tok")]] void finish(); // expected-warning {{'linear_consumer' attribute on 'finish' does not consume anything: class 'NotLinear' has no 'linear' attribute}}
};
struct [[clang::linear("other")]] WrongTag {
  [[clang::linear_consumer("tok")]] void finish(); // expected-warning {{'linear_consumer' attribute on 'finish' does not consume anything: its tag does not match the 'linear' attribute tag on class 'WrongTag'}}
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
