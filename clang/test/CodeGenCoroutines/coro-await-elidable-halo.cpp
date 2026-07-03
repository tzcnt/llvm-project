// This file tests that [[clang::coro_await_elidable]] results in the callee
// coroutine's allocation actually being elided at -O2. It complements
// coro-await-elidable.cpp, which only verifies that the frontend marks the
// call sites with the coro_elide_safe attribute; the elision itself is
// performed later, by CoroAnnotationElide in the middle end, subject to a
// block frequency check of the call site in the (still unsplit, unsimplified)
// caller.
//
// Allocations are made observable by giving the promise type an operator new
// which calls an external marker function that optimization cannot remove or
// invent: task_int_alloc() for Task<int> and task_long_alloc() for
// Task<long>. Task uses an initial_suspend that always suspends, so each
// coroutine's own frame allocation (and its marker) stays in its ramp
// function, while the body - including any callee frame allocation that
// failed to be elided - runs in its .resume function. An elided callee is
// therefore visible as the absence of Task<int>'s marker in the caller's
// .resume function.
//
// RUN: %clang_cc1 -triple x86_64-unknown-linux-gnu -std=c++20 -O2 -emit-llvm %s -o - | FileCheck %s

#include "Inputs/coroutine.h"
#include "Inputs/utility.h"

extern "C" void task_int_alloc();
extern "C" void task_long_alloc();

inline void note_alloc(int *) { task_int_alloc(); }
inline void note_alloc(long *) { task_long_alloc(); }

template <typename T>
struct [[clang::coro_await_elidable]] Task {
  struct promise_type {
    struct FinalAwaiter {
      bool await_ready() const noexcept { return false; }

      template <typename P>
      std::coroutine_handle<> await_suspend(std::coroutine_handle<P> coro) noexcept {
        if (!coro)
          return std::noop_coroutine();
        return coro.promise().continuation;
      }
      void await_resume() noexcept {}
    };

    Task get_return_object() noexcept {
      return std::coroutine_handle<promise_type>::from_promise(*this);
    }

    void *operator new(decltype(sizeof(0)) size) {
      note_alloc(static_cast<T *>(nullptr));
      return ::operator new(size);
    }

    std::suspend_always initial_suspend() noexcept { return {}; }
    FinalAwaiter final_suspend() noexcept { return {}; }
    void unhandled_exception() noexcept {}
    void return_value(T x) noexcept {
      value = x;
    }

    std::coroutine_handle<> continuation;
    T value;
  };

  Task(std::coroutine_handle<promise_type> handle) : handle(handle) {}
  ~Task() {
    if (handle)
      handle.destroy();
  }

  struct Awaiter {
    Awaiter(Task *t) : task(t) {}
    bool await_ready() const noexcept { return false; }
    void await_suspend(std::coroutine_handle<void> continuation) noexcept {}
    T await_resume() noexcept {
      return task->handle.promise().value;
    }

    Task *task;
  };

  auto operator co_await() {
    return Awaiter{this};
  }

private:
  std::coroutine_handle<promise_type> handle;
};

Task<int> callee() { co_return 1; }

// A directly awaited prvalue is elide-safe: the callee's frame must be
// allocated inline in the caller's frame instead of on the heap.
Task<long> caller() { co_return co_await callee(); }

// Negative control, proving the markers can detect a non-elided allocation:
// awaiting an xvalue is not elide-safe, so this caller's body must still
// heap-allocate the callee's frame.
Task<long> caller_no_elide() {
  Task<int> t = callee();
  co_return co_await std::move(t);
}

// The ramp functions each allocate their own coroutine's frame.
//
// CHECK-LABEL: define{{.*}} @_Z6calleev(
// CHECK: call void @task_int_alloc()
//
// CHECK-LABEL: define{{.*}} @_Z6callerv(
// CHECK: call void @task_long_alloc()
//
// CHECK-LABEL: define{{.*}} @_Z15caller_no_elidev(
// CHECK: call void @task_long_alloc()

// The body of caller() runs in its .resume function. Its await of callee()
// is elide-safe, so no callee frame may be heap-allocated there. The
// CHECK-NOTs extend through the following .destroy function up to the next
// CHECK-LABEL match, which must not allocate either.
//
// CHECK-LABEL: define{{.*}} @_Z6callerv.resume(
// CHECK-NOT: call void @task_int_alloc()
// CHECK-NOT: call void @task_long_alloc()

// The body of caller_no_elide() must still heap-allocate the callee frame.
//
// CHECK-LABEL: define{{.*}} @_Z15caller_no_elidev.resume(
// CHECK: call void @task_int_alloc()
