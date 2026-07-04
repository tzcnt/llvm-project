// Tests the frontend marking for [[clang::coro_await_elidable_range]]: the
// llvm.coro.await.suspend.* call of a directly awaited prvalue of a marked
// type, inside a coroutine whose return type is coro_await_elidable, carries
// the "coro-elide-range" call site attribute. The coroutine passes use that
// call's first operand to locate the awaiter object and elide the frames of
// the coroutines linked to it (bulk spawn sites whose tasks are consumed
// from an iterator or range).
// RUN: %clang_cc1 -triple=x86_64-unknown-linux-gnu -std=c++20 -disable-llvm-passes -emit-llvm %s -o - | FileCheck %s

#include "Inputs/coroutine.h"
#include "Inputs/utility.h"

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

private:
  std::coroutine_handle<promise_type> handle;
};

// A non-elidable task type, to check the enclosing-function gating.
template <typename T>
struct PlainTask {
  struct promise_type {
    PlainTask get_return_object() noexcept {
      return std::coroutine_handle<promise_type>::from_promise(*this);
    }
    std::suspend_always initial_suspend() noexcept { return {}; }
    std::suspend_always final_suspend() noexcept { return {}; }
    void unhandled_exception() noexcept {}
    void return_value(T) noexcept {}
  };

  PlainTask(std::coroutine_handle<promise_type> handle) : handle(handle) {}
  ~PlainTask() {
    if (handle)
      handle.destroy();
  }

private:
  std::coroutine_handle<promise_type> handle;
};

// Models a bulk spawn awaitable: the coroutines it runs and joins are
// consumed from a range at runtime and never appear as arguments.
struct [[clang::coro_await_elidable_range]] BulkSpawner {
  struct Awaiter {
    bool await_ready() const noexcept { return false; }
    std::coroutine_handle<> await_suspend(std::coroutine_handle<> h) noexcept {
      return h;
    }
    int await_resume() noexcept { return 0; }
  };
  Awaiter operator co_await() && noexcept { return {}; }
};

BulkSpawner spawn_bulk();

// CHECK-LABEL: define{{.*}} @_Z13caller_directv
// CHECK: call void @llvm.coro.await.suspend.handle(ptr {{.*}}, ptr {{.*}}, ptr @_Z13caller_directv.__await_suspend_wrapper__await) #[[ELIDE_RANGE:[0-9]+]]{{$}}
Task<int> caller_direct() {
  co_return co_await spawn_bulk();
}

// A named awaitable is not a direct prvalue await; no marking.
// CHECK-LABEL: define{{.*}} @_Z13caller_xvaluev
// CHECK: call void @llvm.coro.await.suspend.handle(ptr {{.*}}, ptr {{.*}}, ptr @_Z13caller_xvaluev.__await_suspend_wrapper__await){{$}}
Task<int> caller_xvalue() {
  auto b = spawn_bulk();
  co_return co_await std::move(b);
}

// The enclosing coroutine's return type is not coro_await_elidable; no
// marking.
// CHECK-LABEL: define{{.*}} @_Z12caller_plainv
// CHECK: call void @llvm.coro.await.suspend.handle(ptr {{.*}}, ptr {{.*}}, ptr @_Z12caller_plainv.__await_suspend_wrapper__await){{$}}
PlainTask<int> caller_plain() {
  co_return co_await spawn_bulk();
}

// CHECK: attributes #[[ELIDE_RANGE]] = {{.*}}"coro-elide-range"
