; A self-recursive presplit coroutine with a coro_elide_safe self-call site
; is stashed as a template before splitting; after splitting, generations
; are grown from the template, each eliding the recursive call site into the
; previous generation's frame, and the top generation is republished under
; the original symbol. The template is consumed in the process.
;
; Determinism: with a generous frame-size limit the ladder is terminated by
; -coro-recursive-elide-max-generations, so exactly three generations exist.
;
; RUN: opt < %s -S -passes='coro-recursion-stash' | FileCheck %s --check-prefix=STASH
; RUN: opt < %s -S -passes='coro-recursion-stash,cgscc(coro-split),coro-recursive-elide' -coro-elide-max-frame-size=100000 -coro-elide-max-accumulated-frame-size=400000 -coro-recursive-elide-max-generations=3 | FileCheck %s
; RUN: opt < %s -S -passes='coro-recursion-stash,cgscc(coro-split),coro-recursive-elide' -coro-recursive-elide-max-generations=0 | FileCheck %s --check-prefix=OFF

; The stash pass clones a presplit template, points its coro.id at itself,
; and keeps it alive through the pipeline.
; STASH: @llvm.compiler.used{{.*}}@f.recursive.template
; STASH-LABEL: define internal ptr @f.recursive.template
; STASH-SAME: (i64 %n) [[TATTR:#[0-9]+]]
; STASH: call token @llvm.coro.id(i32 16, ptr null, ptr @f.recursive.template, ptr null)
; STASH: call ptr @f(i64 {{.*}}) [[SITEATTR:#[0-9]+]]
; STASH-DAG: attributes [[TATTR]] = { presplitcoroutine "coro.recursive.group"="0" "coro.recursive.template"="f" }
; STASH-DAG: attributes [[SITEATTR]] = { coro_elide_safe noinline }

; With generations disabled, no blocks are created and the template is
; removed again.
; OFF-NOT: .block.
; OFF-NOT: recursive.template

; After the full pipeline: the original ramp is demoted to @f.block.0 (its
; split artifacts keep their names, e.g. @f.resume), three generations exist
; with strictly growing frames, and @f is the republished top generation
; (generation 3, whose split artifacts are @f.block.3.*).
; CHECK-NOT: recursive.template
; CHECK-DAG: define internal ptr @f.block.0(i64 %n)
; CHECK-DAG: define internal void @f.block.1.resume(ptr noundef nonnull align 8 dereferenceable([[S1:[0-9]+]]) %hdl)
; CHECK-DAG: define internal void @f.block.2.resume(ptr noundef nonnull align 8 dereferenceable([[S2:[0-9]+]]) %hdl)
; CHECK-DAG: define internal void @f.block.3.resume(ptr noundef nonnull align 8 dereferenceable([[S3:[0-9]+]]) %hdl)
; CHECK-DAG: define ptr @f(i64 %n)

%f.frame_ish = type { ptr, i64 }

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
  %n.dec = add i64 %n, -1
  %rec = call ptr @f(i64 %n.dec) coro_elide_safe
  call void @use(ptr %rec)
  %tok = call token @llvm.coro.save(ptr null)
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
