; The block ramp republished under the original symbol is folded into the
; cycle re-entry call sites in the original's split clones. Those sites were
; kept outlined symbol references only so the republish RAUW could retarget
; them, and no inliner runs after this pass; without the fold every re-entry
; pays an outlined call into the (tiny) block ramp forever.
;
; Unlike coro-recursive-elide.ll, the recursive creation here happens after
; the first suspend -- the lazy-task shape -- so the re-entry site lands in
; @f.resume when the original is split, which is where the fold applies.
;
; RUN: opt < %s -S -passes='coro-recursion-stash,cgscc(coro-split),coro-recursive-elide' -coro-elide-max-frame-size=100000 -coro-elide-max-accumulated-frame-size=400000 -coro-recursive-elide-max-generations=3 | FileCheck %s
; RUN: opt < %s -S -passes='coro-recursion-stash,cgscc(coro-split),coro-recursive-elide' -coro-elide-max-frame-size=100000 -coro-elide-max-accumulated-frame-size=400000 -coro-recursive-elide-max-generations=3 -coro-recursive-elide-inline-ramp=false | FileCheck %s --check-prefix=PINNED

; With the fold (default): the re-entry in @f.resume allocates the block
; directly instead of calling the republished ramp.
; CHECK-LABEL: define internal void @f.resume(
; CHECK-NOT: call ptr @f(
; CHECK: call ptr @malloc(
; CHECK-NOT: call ptr @f(
; CHECK: call void @use(

; With the fold disabled, the re-entry stays an outlined call to the
; republished symbol.
; PINNED-LABEL: define internal void @f.resume(
; PINNED-NOT: call ptr @malloc(
; PINNED: call ptr @f(i64
; PINNED: call void @use(

define ptr @f(i64 %n) #0 {
entry:
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
  %tok = call token @llvm.coro.save(ptr null)
  %susp = call i8 @llvm.coro.suspend(token %tok, i1 false)
  switch i8 %susp, label %suspend [i8 0, label %resume
                                   i8 1, label %cleanup]
resume:
  %n.dec = add i64 %n, -1
  %rec = call ptr @f(i64 %n.dec) coro_elide_safe
  call void @use(ptr %rec)
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

declare token @llvm.coro.id(i32, ptr, ptr, ptr)
declare i1 @llvm.coro.alloc(token)
declare i64 @llvm.coro.size.i64()
declare ptr @llvm.coro.begin(token, ptr)
declare token @llvm.coro.save(ptr)
declare i8 @llvm.coro.suspend(token, i1)
declare ptr @llvm.coro.free(token, ptr)
declare void @llvm.coro.end(ptr, i1, token)

declare void @print(i64)
declare void @use(ptr)
declare noalias ptr @malloc(i64)
declare void @free(ptr)

attributes #0 = { presplitcoroutine }
