; Coroutine calls marked with `coro_elide_safe` should be elided.
; Inside `caller`, we expect the `callee` coroutine to be elided.
; Inside `caller_conditional`, `callee` is called on a conditional path
; carrying no evidence that the path is cold, hence we expect the `callee`
; coroutine to be elided as well.
; Inside `caller_after_suspend`, `callee` is called on the straight-line path
; but downstream of two suspend points, matching the shape of real frontend
; output; we expect the `callee` coroutine to be elided.
; Inside `caller_conditional_unlikely`, `callee` is only called on a path
; whose branch weights mark it as very unlikely. With the frequency gate
; enabled (a positive -coro-elide-branch-ratio), we expect the `callee`
; coroutine NOT to be elided there. The gate is disabled by default
; (ratio 0, with the frame size limit acting as the elision heuristic
; instead), so by default even that call site is elided.
;
; RUN: opt < %s -S -passes='cgscc(coro-annotation-elide)' -coro-elide-branch-ratio=0.1 | FileCheck %s --check-prefixes=CHECK,RATIO
; RUN: opt < %s -S -passes='cgscc(coro-annotation-elide)' | FileCheck %s --check-prefixes=CHECK,DEFAULT

%struct.Task = type { ptr }

declare void @print(i32) nounwind

; resume part of the coroutine
define fastcc void @callee.resume(ptr dereferenceable(1)) {
  tail call void @print(i32 0)
  ret void
}

; destroy part of the coroutine
define fastcc void @callee.destroy(ptr) {
  tail call void @print(i32 1)
  ret void
}

; cleanup part of the coroutine
define fastcc void @callee.cleanup(ptr) {
  tail call void @print(i32 2)
  ret void
}

@callee.resumers = internal constant [3 x ptr] [
  ptr @callee.resume, ptr @callee.destroy, ptr @callee.cleanup]

declare void @alloc(i1) nounwind

; CHECK-LABEL: define ptr @callee
define ptr @callee(i8 %arg) {
entry:
  %task = alloca %struct.Task, align 8
  %id = call token @llvm.coro.id(i32 0, ptr null,
                          ptr @callee,
                          ptr @callee.resumers)
  %alloc = call i1 @llvm.coro.alloc(token %id)
  %hdl = call ptr @llvm.coro.begin(token %id, ptr null)
  store ptr %hdl, ptr %task
  ret ptr %task
}

; CHECK-LABEL: define ptr @callee.noalloc
define ptr @callee.noalloc(i8 %arg, ptr dereferenceable(32) align(8) %frame) {
 entry:
  %task = alloca %struct.Task, align 8
  %id = call token @llvm.coro.id(i32 0, ptr null,
                          ptr @callee,
                          ptr @callee.resumers)
  %hdl = call ptr @llvm.coro.begin(token %id, ptr null)
  store ptr %hdl, ptr %task
  ret ptr %task
}

; CHECK-LABEL: define ptr @caller()
; Function Attrs: presplitcoroutine
define ptr @caller() #0 {
entry:
  %task = call ptr @callee(i8 0) coro_elide_safe
  ret ptr %task
  ; CHECK: %[[TASK:.+]] = alloca %struct.Task, align 8
  ; CHECK-NEXT: %[[FRAME:.+]] = alloca [32 x i8], align 8
  ; CHECK-NEXT: call void @llvm.lifetime.start.p0(ptr %[[TASK]])
  ; CHECK-NEXT: %[[ID:.+]] = call token @llvm.coro.id(i32 0, ptr null, ptr @callee, ptr @callee.resumers)
  ; CHECK-NEXT: %[[HDL:.+]] = call ptr @llvm.coro.begin(token %[[ID]], ptr null)
  ; CHECK-NEXT: store ptr %[[HDL]], ptr %[[TASK]], align 8
  ; CHECK-NEXT: call void @llvm.lifetime.end.p0(ptr %[[TASK]])
  ; CHECK-NEXT: ret ptr %[[TASK]]
}

; CHECK-LABEL: define ptr @caller_conditional(i1 %cond)
; Function Attrs: presplitcoroutine
define ptr @caller_conditional(i1 %cond) #0 {
entry:
  ; CHECK: %[[TASK:.+]] = alloca %struct.Task, align 8
  ; CHECK-NEXT: %[[FRAME:.+]] = alloca [32 x i8], align 8
  ; CHECK-NEXT: br i1 %cond, label %call, label %ret
  br i1 %cond, label %call, label %ret

call:
  ; CHECK: call:
  ; CHECK-NEXT: call void @llvm.lifetime.start.p0(ptr %[[TASK]])
  ; CHECK-NEXT: %[[ID:.+]] = call token @llvm.coro.id(i32 0, ptr null, ptr @callee, ptr @callee.resumers)
  ; CHECK-NEXT: %[[HDL:.+]] = call ptr @llvm.coro.begin(token %[[ID]], ptr null)
  ; CHECK-NEXT: store ptr %[[HDL]], ptr %[[TASK]], align 8
  ; CHECK-NEXT: call void @llvm.lifetime.end.p0(ptr %[[TASK]])
  ; CHECK-NEXT: br label %ret
  %task = call ptr @callee(i8 0) coro_elide_safe
  br label %ret

ret:
  %retval = phi ptr [ %task, %call ], [ null, %entry ]
  ret ptr %retval
}

; A caller whose call site follows suspend points, modeled on real frontend
; output: every co_await lowers to a three-way switch on llvm.coro.suspend
; followed by a shared cleanup block dispatching on a constant PHI, and any
; directly awaited call site sits downstream of at least the caller's initial
; suspend. BranchProbabilityInfo must model the resume path of the suspend
; points as likely for the frequency of such call sites to reflect their real
; execution rate (~once per entry); otherwise the generic heuristics compound
; a spurious dilution per suspend point and the call site is mistaken as cold.
; We expect the `callee` coroutine to be elided.

; CHECK-LABEL: define ptr @caller_after_suspend()
; Function Attrs: presplitcoroutine
define ptr @caller_after_suspend() #0 {
entry:
  ; CHECK: %[[TASK:.+]] = alloca %struct.Task, align 8
  ; CHECK-NEXT: %[[FRAME:.+]] = alloca [32 x i8], align 8
  %save1 = call token @llvm.coro.save(ptr null)
  %s1 = call i8 @llvm.coro.suspend(token %save1, i1 false)
  switch i8 %s1, label %suspend.ret [
    i8 0, label %resume1
    i8 1, label %cleanup1
  ]

resume1:
  br label %cleanup1

cleanup1:
  %dest1 = phi i32 [ 0, %resume1 ], [ 2, %entry ]
  %cmp1 = icmp eq i32 %dest1, 0
  br i1 %cmp1, label %cont1, label %coro.cleanup

cont1:
  %save2 = call token @llvm.coro.save(ptr null)
  %s2 = call i8 @llvm.coro.suspend(token %save2, i1 false)
  switch i8 %s2, label %suspend.ret [
    i8 0, label %resume2
    i8 1, label %cleanup2
  ]

resume2:
  br label %cleanup2

cleanup2:
  %dest2 = phi i32 [ 0, %resume2 ], [ 2, %cont1 ]
  %cmp2 = icmp eq i32 %dest2, 0
  br i1 %cmp2, label %cont2, label %coro.cleanup

cont2:
  ; CHECK: cont2:
  ; CHECK-NEXT: call void @llvm.lifetime.start.p0(ptr %[[TASK]])
  ; CHECK-NEXT: %[[ID:.+]] = call token @llvm.coro.id(i32 0, ptr null, ptr @callee, ptr @callee.resumers)
  ; CHECK-NEXT: %[[HDL:.+]] = call ptr @llvm.coro.begin(token %[[ID]], ptr null)
  ; CHECK-NEXT: store ptr %[[HDL]], ptr %[[TASK]], align 8
  ; CHECK-NEXT: call void @llvm.lifetime.end.p0(ptr %[[TASK]])
  ; CHECK-NEXT: ret ptr %[[TASK]]
  %task = call ptr @callee(i8 0) coro_elide_safe
  ret ptr %task

coro.cleanup:
  ret ptr null

suspend.ret:
  ret ptr null
}

; CHECK-LABEL: define ptr @caller_conditional_unlikely(i1 %cond)
; Function Attrs: presplitcoroutine
define ptr @caller_conditional_unlikely(i1 %cond) #0 {
entry:
  br i1 %cond, label %call, label %ret, !prof !0

call:
  ; RATIO-NOT: alloca [32 x i8]
  ; RATIO-NOT: @llvm.coro.id({{.*}}, ptr @callee, {{.*}})
  ; RATIO: %task = call ptr @callee(i8 0)
  ; RATIO-NEXT: br label %ret
  ; DEFAULT: @llvm.coro.id({{.*}}, ptr @callee, {{.*}})
  ; DEFAULT-NOT: %task = call ptr @callee(i8 0)
  %task = call ptr @callee(i8 0) coro_elide_safe
  br label %ret

ret:
  %retval = phi ptr [ %task, %call ], [ null, %entry ]
  ret ptr %retval
}

declare token @llvm.coro.id(i32, ptr, ptr, ptr)
declare ptr @llvm.coro.begin(token, ptr)
declare ptr @llvm.coro.frame()
declare ptr @llvm.coro.subfn.addr(ptr, i8)
declare i1 @llvm.coro.alloc(token)
declare token @llvm.coro.save(ptr)
declare i8 @llvm.coro.suspend(token, i1)

attributes #0 = { presplitcoroutine }

!0 = !{!"branch_weights", i32 1, i32 2000}
