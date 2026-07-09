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
