; A self-recursive presplit coroutine with coro_elide_safe self-call sites is
; peeled into a chain of clones: the root's elide-safe sites call the first
; copy, each copy's elide-safe sites call the next copy, and the last copy
; returns to the root through llvm.coro.recursion.anchor so that the call
; graph does not observe the cycle. Self-call sites that are not elide-safe
; are left alone in the root (its self-loop is harmless) but must be anchored
; in the copies, since a direct call back to the root would merge the whole
; chain into one SCC. Each copy's coro.id must identify the copy itself.
;
; RUN: opt < %s -S -passes=coro-recursion-peel -coro-recursion-peel-depth=3 | FileCheck %s
; RUN: opt < %s -S -passes=coro-recursion-peel -coro-recursion-peel-depth=0 | FileCheck %s --check-prefix=OFF

; OFF-NOT: peel

; CHECK-LABEL: define ptr @rec(i64 %n)
; CHECK: call token @llvm.coro.id(i32 0, ptr null, ptr @rec, ptr null)
; CHECK: call ptr @rec.peel.1(i64 %n)
; CHECK: %plain = call ptr @rec(i64 %n)
define ptr @rec(i64 %n) #0 {
entry:
  %id = call token @llvm.coro.id(i32 0, ptr null, ptr @rec, ptr null)
  %hdl = call ptr @llvm.coro.begin(token %id, ptr null)
  %t = call ptr @rec(i64 %n) coro_elide_safe
  %plain = call ptr @rec(i64 %n)
  ret ptr %hdl
}

; CHECK-LABEL: define internal ptr @rec.peel.1(i64 %n)
; CHECK: call token @llvm.coro.id(i32 0, ptr null, ptr @rec.peel.1, ptr null)
; CHECK: call ptr @rec.peel.2(i64 %n)
; CHECK: [[A1:%.+]] = call ptr @llvm.coro.recursion.anchor(ptr @rec)
; CHECK: call ptr [[A1]](i64 %n)

; CHECK-LABEL: define internal ptr @rec.peel.2(i64 %n)
; CHECK: call token @llvm.coro.id(i32 0, ptr null, ptr @rec.peel.2, ptr null)
; CHECK: call ptr @rec.peel.3(i64 %n)
; CHECK: [[A2:%.+]] = call ptr @llvm.coro.recursion.anchor(ptr @rec)
; CHECK: call ptr [[A2]](i64 %n)

; The bottom copy has no next copy: its elide-safe site is anchored back to
; the root as well.
; CHECK-LABEL: define internal ptr @rec.peel.3(i64 %n)
; CHECK: call token @llvm.coro.id(i32 0, ptr null, ptr @rec.peel.3, ptr null)
; CHECK: [[A3:%.+]] = call ptr @llvm.coro.recursion.anchor(ptr @rec)
; CHECK: call ptr [[A3]](i64 %n)
; CHECK: [[A4:%.+]] = call ptr @llvm.coro.recursion.anchor(ptr @rec)
; CHECK: call ptr [[A4]](i64 %n)

declare token @llvm.coro.id(i32, ptr, ptr, ptr)
declare ptr @llvm.coro.begin(token, ptr)

attributes #0 = { presplitcoroutine }
