; Bulk range elision: coroutines created in a loop (or straight-line code)
; and joined through a bulk awaitable whose llvm.coro.await.suspend.* call
; carries the frontend's "coro-elide-safe range" marking. The creation calls
; have no attribute; they are recovered from the IR by following stores of
; pointers into the marked awaiter object through the created coroutine's
; handle (the linking a bulk awaitable performs on each coroutine it runs
; and joins).
;
; @f creates one child in straight-line code (one in-frame slot, direct
; rewrite) and four children in a self-recursive loop: the loop site gets a
; per-activation heap arena, ensured in the preheader (the trip count is
; computable there), whose slots hold this same generation's `.noalloc`
; frames -- the creation is rewritten to a guarded dispatch between that
; `.noalloc` and the published symbol. @g's loop bound is a runtime value:
; the same arena form, sized by the expanded count.
;
; RUN: opt < %s -S -passes='coro-recursion-stash' | FileCheck %s --check-prefix=STASH
; RUN: opt < %s -S -passes='coro-recursion-stash,cgscc(coro-split),coro-recursive-elide' -coro-elide-max-frame-size=100000 -coro-elide-max-accumulated-frame-size=400000 -coro-recursive-elide-max-generations=1 -coro-elide-bulk-default-slots=2 | FileCheck %s
;
; With the arena rejected (threshold zero), a self-recursive loop site is
; skipped outright -- in-frame slots would charge every activation for the
; worst case -- and a straight-line site whose slot does not fit the
; remaining accumulated budget abandons the generation entirely: no
; partially elided blocks anywhere.
; RUN: opt < %s -S -passes='coro-recursion-stash,cgscc(coro-split),coro-recursive-elide' -coro-elide-max-accumulated-frame-size=48 -coro-elide-bulk-arena-max-frame-size=0 -coro-recursive-elide-max-generations=1 | FileCheck %s --check-prefix=PARTIAL

; The stash accepts an SCC whose qualifying evidence is a range-marked bulk
; await (no coro_elide_safe cycle site exists here), and the template keeps
; the marked suspend.
; STASH-LABEL: define internal ptr @f.recursive.template
; STASH: call void @llvm.coro.await.suspend.handle(ptr %awaiter, ptr %hdl, ptr @f.wrap) [[RANGEATTR:#[0-9]+]]
; STASH-DAG: attributes [[RANGEATTR]] = { "coro-elide-range" }

; PARTIAL-NOT: .block.

; After the full pipeline, the republished @f embeds the straight-line
; child's frame and gives the loop children a per-activation arena.
; CHECK-LABEL: define ptr @f(i64 %n)
; The straight-line child is initialized in place with generation 0's
; resume pointer (its `.noalloc` was inlined; generation 0 keeps the
; original's artifact names).
; CHECK: store ptr @f.resume
; The arena is ensured in the preheader, sized count x padded-frame-size
; (the count folded to 4, clamped and floored by the slot knobs).
; CHECK: call i64 @llvm.umin.i64(i64 4,
; CHECK: call i64 @llvm.umax.i64(
; CHECK: call ptr @malloc(
; The loop children select an arena slot by counter * padded size and call
; this generation's own `.noalloc`, which stays outlined.
; CHECK: mul nuw i64
; CHECK: select i1 %{{.*}}, ptr %{{.*}}, ptr null
; CHECK: call ptr @f.block.1.noalloc(i64 %{{.*}}, ptr %{{.*}})
; CHECK-NOT: call ptr @f.block.0(

define ptr @f(i64 %n) #0 {
entry:
  %awaiter = alloca [24 x i8], align 8
  %id = call token @llvm.coro.id(i32 16, ptr null, ptr @f, ptr null)
  %need.alloc = call i1 @llvm.coro.alloc(token %id)
  br i1 %need.alloc, label %dyn.alloc, label %begin

dyn.alloc:
  %size = call i64 @llvm.coro.size.i64()
  %alloc = call ptr @malloc(i64 %size)
  br label %begin

begin:
  %phi = phi ptr [ null, %entry ], [ %alloc, %dyn.alloc ]
  %hdl = call ptr @llvm.coro.begin(token %id, ptr %phi)
  %n.dec = add i64 %n, -1
  %cont.gep = getelementptr i8, ptr %awaiter, i64 8
  ; One straight-line child.
  %extra = call ptr @f(i64 %n.dec)
  %extra.link = getelementptr i8, ptr %extra, i64 16
  store ptr %cont.gep, ptr %extra.link
  br label %loop

loop:
  %i = phi i64 [ 0, %begin ], [ %i.next, %loop ]
  ; Four loop children, one per iteration.
  %child = call ptr @f(i64 %n.dec)
  %child.link = getelementptr i8, ptr %child, i64 16
  store ptr %cont.gep, ptr %child.link
  %i.next = add nuw i64 %i, 1
  %cond = icmp ult i64 %i.next, 4
  br i1 %cond, label %loop, label %joined

joined:
  %tok = call token @llvm.coro.save(ptr null)
  call void @llvm.coro.await.suspend.handle(ptr %awaiter, ptr %hdl, ptr @f.wrap) "coro-elide-range"
  %susp = call i8 @llvm.coro.suspend(token %tok, i1 false)
  switch i8 %susp, label %suspend [i8 0, label %resume
                                   i8 1, label %cleanup]
resume:
  call void @print(i64 %n)
  br label %cleanup

cleanup:
  %mem = call ptr @llvm.coro.free(token %id, ptr %hdl)
  call void @free(ptr %mem)
  br label %suspend

suspend:
  call void @llvm.coro.end(ptr %hdl, i1 false, token none)
  ret ptr %hdl
}

define ptr @f.wrap(ptr %awaiter, ptr %frame) {
  ret ptr %frame
}

; The loop bound is a runtime value: the arena is sized by the expanded
; trip count (clamped to the slot maximum, floored by the default target),
; and executions past the reserved slots -- or with the allocation failed
; -- fall back to the published @g.
; CHECK-LABEL: define ptr @g(i64 %n)
; CHECK: call i64 @llvm.umin.i64(
; CHECK: call i64 @llvm.umax.i64(
; CHECK: call ptr @malloc(
; CHECK: select i1 %{{.*}}, ptr %{{.*}}, ptr null
; CHECK: call ptr @g.block.1.noalloc(i64 %{{.*}}, ptr %{{.*}})
; CHECK: call ptr @g(i64 %{{.*}})
; The dispatch helper is consumed by inlining (only its name survives in
; inherited basic block labels).
; CHECK-NOT: @g.bulk.dispatch(

define ptr @g(i64 %n) #0 {
entry:
  %awaiter = alloca [24 x i8], align 8
  %id = call token @llvm.coro.id(i32 16, ptr null, ptr @g, ptr null)
  %need.alloc = call i1 @llvm.coro.alloc(token %id)
  br i1 %need.alloc, label %dyn.alloc, label %begin

dyn.alloc:
  %size = call i64 @llvm.coro.size.i64()
  %alloc = call ptr @malloc(i64 %size)
  br label %begin

begin:
  %phi = phi ptr [ null, %entry ], [ %alloc, %dyn.alloc ]
  %hdl = call ptr @llvm.coro.begin(token %id, ptr %phi)
  %n.dec = add i64 %n, -1
  %cont.gep = getelementptr i8, ptr %awaiter, i64 8
  br label %loop

loop:
  %i = phi i64 [ 0, %begin ], [ %i.next, %loop ]
  %child = call ptr @g(i64 %n.dec)
  %child.link = getelementptr i8, ptr %child, i64 16
  store ptr %cont.gep, ptr %child.link
  %i.next = add nuw i64 %i, 1
  %cond = icmp ult i64 %i.next, %n
  br i1 %cond, label %loop, label %joined

joined:
  %tok = call token @llvm.coro.save(ptr null)
  call void @llvm.coro.await.suspend.handle(ptr %awaiter, ptr %hdl, ptr @g.wrap) "coro-elide-range"
  %susp = call i8 @llvm.coro.suspend(token %tok, i1 false)
  switch i8 %susp, label %suspend [i8 0, label %resume
                                   i8 1, label %cleanup]
resume:
  call void @print(i64 %n)
  br label %cleanup

cleanup:
  %mem = call ptr @llvm.coro.free(token %id, ptr %hdl)
  call void @free(ptr %mem)
  br label %suspend

suspend:
  call void @llvm.coro.end(ptr %hdl, i1 false, token none)
  ret ptr %hdl
}

define ptr @g.wrap(ptr %awaiter, ptr %frame) {
  ret ptr %frame
}

declare token @llvm.coro.id(i32, ptr, ptr, ptr)
declare i1 @llvm.coro.alloc(token)
declare i64 @llvm.coro.size.i64()
declare ptr @llvm.coro.begin(token, ptr)
declare token @llvm.coro.save(ptr)
declare void @llvm.coro.await.suspend.handle(ptr, ptr, ptr)
declare i8 @llvm.coro.suspend(token, i1)
declare ptr @llvm.coro.free(token, ptr)
declare void @llvm.coro.end(ptr, i1, token)

declare void @print(i64)
declare noalias ptr @malloc(i64)
declare void @free(ptr)

attributes #0 = { presplitcoroutine }
