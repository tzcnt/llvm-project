; Elision nests the callee's frame inside the caller's frame, and the
; callee's frame size at decision time already includes every frame
; previously elided into the callee. Unlimited elision therefore compounds
; through nested awaits: a recursive task tree accretes into a single
; enormous root frame. Two limits bound this:
; -coro-elide-max-frame-size rejects any single callee frame larger than
; the limit, and -coro-elide-max-accumulated-frame-size rejects a callee
; once the total frame bytes elided into its caller (including the
; candidate) would exceed the limit. Callees that do not fit stay
; dynamically allocated no matter how hot the call site is.
;
; @callee_small (32-byte frame) is elided under the default limits;
; @callee_big (40000-byte frame) is not. Raising the limits admits
; @callee_big; lowering the per-callee limit below 32 rejects @callee_small
; too. @caller_twice awaits @callee_big twice: with both limits at 65536
; only one of the two 40000-byte frames fits under the accumulated limit,
; so exactly one call site is elided.
;
; RUN: opt < %s -S -passes='cgscc(coro-annotation-elide)' | FileCheck %s --check-prefixes=CHECK,DEFAULT
; RUN: opt < %s -S -passes='cgscc(coro-annotation-elide)' -coro-elide-max-frame-size=65536 -coro-elide-max-accumulated-frame-size=65536 | FileCheck %s --check-prefixes=CHECK,BIGCAP
; RUN: opt < %s -S -passes='cgscc(coro-annotation-elide)' -coro-elide-max-frame-size=16 | FileCheck %s --check-prefixes=CHECK,TINYCAP
; RUN: opt < %s -passes='cgscc(coro-annotation-elide)' -pass-remarks-missed=coro-annotation-elide -S -o /dev/null 2>&1 | FileCheck %s --check-prefix=REMARK
; RUN: opt < %s -passes='cgscc(coro-annotation-elide)' -coro-elide-max-frame-size=65536 -coro-elide-max-accumulated-frame-size=65536 -pass-remarks-missed=coro-annotation-elide -S -o /dev/null 2>&1 | FileCheck %s --check-prefix=REMARK2

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

; Two elidable awaits of the same large callee: the limit applies to the
; caller's accumulated elided frame bytes, so under BIGCAP (65536) only one
; of the two 40000-byte frames fits and exactly one call site is elided.
; CHECK-LABEL: define ptr @caller_twice()
define ptr @caller_twice() #0 {
entry:
  ; DEFAULT-NOT: alloca [40000 x i8]
  ; DEFAULT: call ptr @callee_big(i8
  ; BIGCAP: alloca [40000 x i8], align 8
  ; BIGCAP-NOT: alloca [40000 x i8]
  ; BIGCAP: call ptr @callee_big(i8
  ; TINYCAP-NOT: alloca [40000 x i8]
  ; TINYCAP: call ptr @callee_big(i8
  %task1 = call ptr @callee_big(i8 0) coro_elide_safe
  %task2 = call ptr @callee_big(i8 1) coro_elide_safe
  ret ptr %task2
}

; REMARK: 'callee_big' not elided in 'caller_big' because its frame is too large: 40000 (max: 8192)
; REMARK2: 'callee_big' not elided in 'caller_twice' because the caller's accumulated elided frame size would be too large: 80000 (max: 65536)

declare token @llvm.coro.id(i32, ptr, ptr, ptr)
declare ptr @llvm.coro.begin(token, ptr)
declare i1 @llvm.coro.alloc(token)

attributes #0 = { presplitcoroutine }
