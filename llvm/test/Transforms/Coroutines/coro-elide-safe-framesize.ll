; Elision nests the callee's frame inside the caller's frame, and the
; callee's frame size at decision time already includes every frame
; previously elided into the callee. Unlimited elision therefore compounds
; through nested awaits: a recursive task tree accretes into a single
; enormous root frame. To bound this, a `coro_elide_safe` callee whose
; frame exceeds -coro-elide-max-frame-size stays dynamically allocated no
; matter how hot the call site is.
;
; @callee_small (32-byte frame) is elided under the default limit;
; @callee_big (40000-byte frame) is not. Raising the limit admits
; @callee_big; lowering it below 32 rejects @callee_small too.
;
; RUN: opt < %s -S -passes='cgscc(coro-annotation-elide)' | FileCheck %s --check-prefixes=CHECK,DEFAULT
; RUN: opt < %s -S -passes='cgscc(coro-annotation-elide)' -coro-elide-max-frame-size=65536 | FileCheck %s --check-prefixes=CHECK,BIGCAP
; RUN: opt < %s -S -passes='cgscc(coro-annotation-elide)' -coro-elide-max-frame-size=16 | FileCheck %s --check-prefixes=CHECK,TINYCAP
; RUN: opt < %s -passes='cgscc(coro-annotation-elide)' -pass-remarks-missed=coro-annotation-elide -S -o /dev/null 2>&1 | FileCheck %s --check-prefix=REMARK

%struct.Task = type { ptr }

declare void @print(i32) nounwind

define fastcc void @callee_small.resume(ptr dereferenceable(1)) {
  tail call void @print(i32 0)
  ret void
}
define fastcc void @callee_small.destroy(ptr) {
  tail call void @print(i32 1)
  ret void
}
define fastcc void @callee_small.cleanup(ptr) {
  tail call void @print(i32 2)
  ret void
}
@callee_small.resumers = internal constant [3 x ptr] [
  ptr @callee_small.resume, ptr @callee_small.destroy,
  ptr @callee_small.cleanup]

define fastcc void @callee_big.resume(ptr dereferenceable(1)) {
  tail call void @print(i32 3)
  ret void
}
define fastcc void @callee_big.destroy(ptr) {
  tail call void @print(i32 4)
  ret void
}
define fastcc void @callee_big.cleanup(ptr) {
  tail call void @print(i32 5)
  ret void
}
@callee_big.resumers = internal constant [3 x ptr] [
  ptr @callee_big.resume, ptr @callee_big.destroy, ptr @callee_big.cleanup]

define ptr @callee_small(i8 %arg) {
entry:
  %task = alloca %struct.Task, align 8
  %id = call token @llvm.coro.id(i32 0, ptr null,
                          ptr @callee_small,
                          ptr @callee_small.resumers)
  %alloc = call i1 @llvm.coro.alloc(token %id)
  %hdl = call ptr @llvm.coro.begin(token %id, ptr null)
  store ptr %hdl, ptr %task
  ret ptr %task
}

define ptr @callee_small.noalloc(i8 %arg,
                                 ptr dereferenceable(32) align(8) %frame) {
entry:
  %task = alloca %struct.Task, align 8
  %id = call token @llvm.coro.id(i32 0, ptr null,
                          ptr @callee_small,
                          ptr @callee_small.resumers)
  %hdl = call ptr @llvm.coro.begin(token %id, ptr null)
  store ptr %hdl, ptr %task
  ret ptr %task
}

define ptr @callee_big(i8 %arg) {
entry:
  %task = alloca %struct.Task, align 8
  %id = call token @llvm.coro.id(i32 0, ptr null,
                          ptr @callee_big,
                          ptr @callee_big.resumers)
  %alloc = call i1 @llvm.coro.alloc(token %id)
  %hdl = call ptr @llvm.coro.begin(token %id, ptr null)
  store ptr %hdl, ptr %task
  ret ptr %task
}

define ptr @callee_big.noalloc(i8 %arg,
                               ptr dereferenceable(40000) align(8) %frame) {
entry:
  %task = alloca %struct.Task, align 8
  %id = call token @llvm.coro.id(i32 0, ptr null,
                          ptr @callee_big,
                          ptr @callee_big.resumers)
  %hdl = call ptr @llvm.coro.begin(token %id, ptr null)
  store ptr %hdl, ptr %task
  ret ptr %task
}

; CHECK-LABEL: define ptr @caller_small()
define ptr @caller_small() #0 {
entry:
  ; DEFAULT: alloca [32 x i8], align 8
  ; BIGCAP: alloca [32 x i8], align 8
  ; TINYCAP-NOT: alloca [32 x i8]
  ; TINYCAP: %task = call ptr @callee_small(i8 0)
  %task = call ptr @callee_small(i8 0) coro_elide_safe
  ret ptr %task
}

; CHECK-LABEL: define ptr @caller_big()
define ptr @caller_big() #0 {
entry:
  ; DEFAULT-NOT: alloca [40000 x i8]
  ; DEFAULT: %task = call ptr @callee_big(i8 0)
  ; BIGCAP: alloca [40000 x i8], align 8
  ; TINYCAP-NOT: alloca [40000 x i8]
  ; TINYCAP: %task = call ptr @callee_big(i8 0)
  %task = call ptr @callee_big(i8 0) coro_elide_safe
  ret ptr %task
}

; REMARK: 'callee_big' not elided in 'caller_big' because its frame is too large: 40000 (max: 32768)

declare token @llvm.coro.id(i32, ptr, ptr, ptr)
declare ptr @llvm.coro.begin(token, ptr)
declare i1 @llvm.coro.alloc(token)

attributes #0 = { presplitcoroutine }
