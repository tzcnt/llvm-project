; Bulk range elision: coroutines created in a loop (or straight-line code)
; and joined through a bulk awaitable whose llvm.coro.await.suspend.* call
; carries the frontend's "coro-elide-safe range" marking. The creation calls
; have no attribute; they are recovered from the IR by following stores of
; pointers into the marked awaiter object through the created coroutine's
; handle (the linking a bulk awaitable performs on each coroutine it runs
; and joins).
;
; @f creates one child in straight-line code (one slot, direct rewrite) and
; four children in a loop with a computable trip bound (four slots selected
; by a synthesized counter, direct rewrite). @g's loop has no computable
; bound: it gets the default number of slots and a guarded dispatch whose
; fallback keeps calling the runtime-allocating published symbol.
;
; RUN: opt < %s -S -passes='coro-recursion-stash' | FileCheck %s --check-prefix=STASH
; RUN: opt < %s -S -passes='coro-recursion-stash,cgscc(coro-split),coro-recursive-elide' -coro-elide-max-frame-size=100000 -coro-elide-max-accumulated-frame-size=400000 -coro-recursive-elide-max-generations=1 -coro-elide-bulk-default-slots=8 | FileCheck %s
;
; A loop site whose slot target does not fit the remaining accumulated
; budget abandons the generation entirely (no partially elided blocks).
; RUN: opt < %s -S -passes='coro-recursion-stash,cgscc(coro-split),coro-recursive-elide' -coro-elide-max-accumulated-frame-size=48 -coro-recursive-elide-max-generations=1 | FileCheck %s --check-prefix=PARTIAL

; The stash accepts an SCC whose qualifying evidence is a range-marked bulk
; await (no coro_elide_safe cycle site exists here), and the template keeps
; the marked suspend.
; STASH-LABEL: define internal ptr @f.recursive.template
; STASH: call void @llvm.coro.await.suspend.handle(ptr %awaiter, ptr %hdl, ptr @f.wrap) [[RANGEATTR:#[0-9]+]]
; STASH-DAG: attributes [[RANGEATTR]] = { "coro-elide-range" }

; PARTIAL-NOT: .block.

; After the full pipeline, the republished @f embeds five child frames: the
; straight-line child and four loop children indexed by a counter.
; CHECK-LABEL: define ptr @f(i64 %n)
; The straight-line child's frame is the array itself; the loop children
; select their slot by counter * padded-frame-size.
; CHECK: phi i64
; CHECK: mul nuw i64
; CHECK: getelementptr i8, ptr
; The elided creations initialize the child frames in place with the
; original split's resume pointer (generation 0 keeps the original's split
; artifact names).
; CHECK: store ptr @f.resume
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

; The loop bound is a runtime value: the site gets the default slot count
; behind a guard, and executions past the last slot call the published @g.
; CHECK-LABEL: define ptr @g(i64 %n)
; CHECK: icmp ult i64 %{{.*}}, 8
; CHECK: select i1 %{{.*}}, ptr %{{.*}}, ptr null
; CHECK: store ptr @g.resume
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
