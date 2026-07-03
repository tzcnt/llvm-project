; Unreduced frontend output, testing that CoroAnnotationElide's frequency
; gate admits a directly awaited call site in real IR (as opposed to the
; hand-written flat CFGs in coro-elide-safe.ll).
;
; This module is the caller/callee pair exactly as CoroAnnotationElide sees
; it: clang codegen output after early module simplification, captured at the
; visit of the callee's SCC (callee already split, .noalloc present; caller
; still an unsimplified presplit coroutine). The caller's directly awaited
; call site sits downstream of the initial suspend point's machinery: an
; opaque await_ready() branch, the three-way llvm.coro.suspend switch, and a
; constant-PHI cleanup dispatch. Generic branch heuristics estimate that call
; site at 0.3125 of the caller's entry frequency, below the elide threshold,
; even though it executes once per entry; BranchProbabilityInfo's coroutine
; heuristic models the resume path as likely, which estimates it at ~1.0.
;
; Generated from the Task<T> type of
; clang/test/CodeGenCoroutines/coro-await-elidable.cpp with:
;
;   Task<int> callee() { co_return 1; }
;   Task<int> caller() { co_return co_await callee(); }
;
;   clang++ -O2 -std=c++20 -fno-exceptions -stdlib=libc++ \
;     -mllvm -print-before=coro-annotation-elide -mllvm -print-module-scope
;
; taking the module printed at the first "on (_Z6calleev)" SCC visit,
; unmodified except for this comment and the source filename.
;
; RUN: opt < %s -passes='cgscc(coro-annotation-elide)' -disable-output \
; RUN:   --pass-remarks=coro-annotation-elide 2>&1 | FileCheck %s
;
; CHECK: '_Z6calleev' elided in '_Z6callerv'

; ModuleID = 'coro-elide-safe-frontend.cpp'
source_filename = "coro-elide-safe-frontend.cpp"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%struct.Task = type { %"struct.std::__1::coroutine_handle" }
%"struct.std::__1::coroutine_handle" = type { ptr }
%"struct.Task<int>::promise_type" = type <{ %"struct.std::__1::coroutine_handle.0", i32, [4 x i8] }>
%"struct.std::__1::coroutine_handle.0" = type { ptr }
%"struct.std::__1::suspend_always" = type { i8 }
%"struct.Task<int>::Awaiter" = type { ptr }
%"struct.Task<int>::promise_type::FinalAwaiter" = type { i8 }

$_ZN4TaskIiE12promise_typeC2Ev = comdat any

$_ZN4TaskIiE12promise_type17get_return_objectEv = comdat any

$_ZN4TaskIiE12promise_type15initial_suspendEv = comdat any

$_ZNKSt3__114suspend_always11await_readyB8nn220000Ev = comdat any

$_ZNKSt3__114suspend_always13await_suspendB8nn220000ENS_16coroutine_handleIvEE = comdat any

$_ZNSt3__116coroutine_handleIN4TaskIiE12promise_typeEE12from_addressB8nn220000EPv = comdat any

$_ZNKSt3__116coroutine_handleIN4TaskIiE12promise_typeEEcvNS0_IvEEB8nn220000Ev = comdat any

$_ZNKSt3__114suspend_always12await_resumeB8nn220000Ev = comdat any

$_ZN4TaskIiE12promise_type12return_valueEi = comdat any

$_ZN4TaskIiE12promise_type13final_suspendEv = comdat any

$_ZNK4TaskIiE12promise_type12FinalAwaiter11await_readyEv = comdat any

$_ZN4TaskIiE12promise_type12FinalAwaiter13await_suspendIS1_EENSt3__116coroutine_handleIvEENS5_IT_EE = comdat any

$_ZNKSt3__116coroutine_handleIvE7addressB8nn220000Ev = comdat any

$_ZN4TaskIiE12promise_type12FinalAwaiter12await_resumeEv = comdat any

$_ZN4TaskIiEawEv = comdat any

$_ZNK4TaskIiE7Awaiter11await_readyEv = comdat any

$_ZN4TaskIiE7Awaiter13await_suspendENSt3__116coroutine_handleIvEE = comdat any

$_ZN4TaskIiE7Awaiter12await_resumeEv = comdat any

$_ZN4TaskIiED2Ev = comdat any

$_ZNSt3__116coroutine_handleIvEC2Ev = comdat any

$_ZNSt3__116coroutine_handleIN4TaskIiE12promise_typeEEC2Ev = comdat any

$_ZNSt3__116coroutine_handleIvE12from_addressB8nn220000EPv = comdat any

$_ZNKSt3__116coroutine_handleIN4TaskIiE12promise_typeEE7addressB8nn220000Ev = comdat any

$_ZN4TaskIiE7AwaiterC2EPS0_ = comdat any

$_ZNKSt3__116coroutine_handleIN4TaskIiE12promise_typeEEcvbB8nn220000Ev = comdat any

$_ZNSt3__114noop_coroutineB8nn220000Ev = comdat any

$_ZNKSt3__116coroutine_handleINS_22noop_coroutine_promiseEEcvNS0_IvEEB8nn220000Ev = comdat any

$_ZNKSt3__116coroutine_handleIN4TaskIiE12promise_typeEE7promiseB8nn220000Ev = comdat any

$_ZNSt3__116coroutine_handleINS_22noop_coroutine_promiseEEC2B8nn220000Ev = comdat any

$_ZNKSt3__116coroutine_handleINS_22noop_coroutine_promiseEE7addressB8nn220000Ev = comdat any

$_ZNSt3__116coroutine_handleIN4TaskIiE12promise_typeEE12from_promiseB8nn220000ERS3_ = comdat any

$_ZN4TaskIiEC2ENSt3__116coroutine_handleINS0_12promise_typeEEE = comdat any

$_ZNKSt3__116coroutine_handleIN4TaskIiE12promise_typeEE7destroyB8nn220000Ev = comdat any

@_Z6calleev.resumers = private constant [3 x ptr] [ptr @_Z6calleev.resume, ptr @_Z6calleev.destroy, ptr @_Z6calleev.cleanup]
@_Z6calleev.resumers.1 = private constant [4 x ptr] [ptr @_Z6calleev.resume, ptr @_Z6calleev.destroy, ptr @_Z6calleev.cleanup, ptr @_Z6calleev.noalloc]

; Function Attrs: mustprogress nounwind uwtable
define dso_local void @_Z6calleev(ptr dead_on_unwind writable sret(%struct.Task) align 8 %agg.result) #0 {
entry:
  %0 = call token @llvm.coro.id(i32 16, ptr nonnull null, ptr nonnull @_Z6calleev, ptr @_Z6calleev.resumers.1)
  %1 = call i1 @llvm.coro.alloc(token %0)
  br i1 %1, label %coro.alloc, label %init.suspend.from.entry

init.suspend.from.entry:                          ; preds = %entry
  %.init.suspend = phi ptr [ null, %entry ]
  br label %init.suspend

coro.alloc:                                       ; preds = %entry
  %call = call noalias noundef nonnull ptr @_Znwm(i64 noundef 40) #16
  br label %init.suspend.from.coro.alloc

init.suspend.from.coro.alloc:                     ; preds = %coro.alloc
  %call.init.suspend = phi ptr [ %call, %coro.alloc ]
  br label %init.suspend

init.suspend:                                     ; preds = %init.suspend.from.entry, %init.suspend.from.coro.alloc
  %2 = phi ptr [ %.init.suspend, %init.suspend.from.entry ], [ %call.init.suspend, %init.suspend.from.coro.alloc ]
  %3 = call noalias nonnull ptr @llvm.coro.begin(token %0, ptr %2)
  store ptr @_Z6calleev.resume, ptr %3, align 8
  %4 = select i1 %1, ptr @_Z6calleev.destroy, ptr @_Z6calleev.cleanup
  %destroy.addr = getelementptr inbounds i8, ptr %3, i64 8
  store ptr %4, ptr %destroy.addr, align 8
  br label %AllocaSpillBB

AllocaSpillBB:                                    ; preds = %init.suspend
  %ref.tmp.reload.addr = getelementptr inbounds i8, ptr %3, i64 33
  %ref.tmp2.reload.addr = getelementptr inbounds i8, ptr %3, i64 33
  %__promise.reload.addr = getelementptr inbounds i8, ptr %3, i64 16
  br label %PostSpill

PostSpill:                                        ; preds = %AllocaSpillBB
  store ptr null, ptr %__promise.reload.addr, align 8, !tbaa !9
  %5 = getelementptr inbounds i8, ptr %__promise.reload.addr, i64 -16
  store ptr %5, ptr %agg.result, align 8, !tbaa !12, !alias.scope !13
  br label %CoroSave

CoroSave:                                         ; preds = %PostSpill
  %index.addr13 = getelementptr inbounds i8, ptr %3, i64 32
  store i1 false, ptr %index.addr13, align 1
  br label %AfterCoroSave

AfterCoroSave:                                    ; preds = %CoroSave
  call void @_Z6calleev.__await_suspend_wrapper__init(ptr nonnull %ref.tmp.reload.addr, ptr %3) #2
  br label %CoroSuspend

CoroSuspend:                                      ; preds = %AfterCoroSave
  br label %resume.0.landing

resume.0.landing:                                 ; preds = %CoroSuspend
  br label %AfterCoroSuspend

AfterCoroSuspend:                                 ; preds = %resume.0.landing
  switch i8 -1, label %coro.ret [
    i8 0, label %final.suspend
    i8 1, label %cleanup
  ]

cleanup:                                          ; preds = %AfterCoroSuspend
  br label %coro.cleanup

final.suspend:                                    ; preds = %AfterCoroSuspend
  %value.i = getelementptr inbounds nuw i8, ptr %__promise.reload.addr, i64 8
  store i32 1, ptr %value.i, align 8, !tbaa !16
  br label %CoroSave9

CoroSave9:                                        ; preds = %final.suspend
  store ptr null, ptr %3, align 8
  br label %AfterCoroSave10

AfterCoroSave10:                                  ; preds = %CoroSave9
  %6 = call ptr @_Z6calleev.__await_suspend_wrapper__final(ptr nonnull %ref.tmp2.reload.addr, ptr %3) #2
  %7 = call ptr @llvm.coro.subfn.addr(ptr %6, i8 0)
  call void %7(ptr %6)
  br label %CoroSuspend11

CoroSuspend11:                                    ; preds = %AfterCoroSave10
  br label %resume.1.landing

resume.1.landing:                                 ; preds = %CoroSuspend11
  br label %AfterCoroSuspend12

AfterCoroSuspend12:                               ; preds = %resume.1.landing
  %switch = icmp ult i8 -1, 2
  br i1 %switch, label %cleanup5, label %coro.ret

cleanup5:                                         ; preds = %AfterCoroSuspend12
  br label %coro.cleanup

coro.cleanup:                                     ; preds = %cleanup, %cleanup5
  %8 = call ptr @llvm.coro.free(token %0, ptr %3)
  %.not = icmp eq ptr %8, null
  br i1 %.not, label %after.coro.free, label %coro.free

coro.free:                                        ; preds = %coro.cleanup
  call void @_ZdlPvm(ptr noundef nonnull %8, i64 noundef 40) #2
  br label %after.coro.free

after.coro.free:                                  ; preds = %coro.cleanup, %coro.free
  call void @llvm.coro.dead(ptr %3)
  br label %coro.ret

coro.ret:                                         ; preds = %AfterCoroSuspend, %AfterCoroSuspend12, %after.coro.free
  br label %CoroEnd

CoroEnd:                                          ; preds = %coro.ret
  br label %AfterCoroEnd

AfterCoroEnd:                                     ; preds = %CoroEnd
  ret void
}

; Function Attrs: mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: read)
declare token @llvm.coro.id(i32, ptr readnone, ptr readonly captures(none), ptr) #1

; Function Attrs: nounwind
declare i1 @llvm.coro.alloc(token) #2

; Function Attrs: nobuiltin allocsize(0)
declare noundef nonnull ptr @_Znwm(i64 noundef) local_unnamed_addr #3

; Function Attrs: nofree nosync nounwind memory(none)
declare i64 @llvm.coro.size.i64() #4

; Function Attrs: nounwind
declare ptr @llvm.coro.begin(token, ptr writeonly) #2

; Function Attrs: mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #5

; Function Attrs: inlinehint mustprogress nounwind uwtable
define linkonce_odr dso_local void @_ZN4TaskIiE12promise_typeC2Ev(ptr noundef nonnull align 8 dereferenceable(12) %this) unnamed_addr #6 comdat align 2 {
entry:
  store ptr null, ptr %this, align 8, !tbaa !9
  ret void
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr dso_local void @_ZN4TaskIiE12promise_type17get_return_objectEv(ptr dead_on_unwind noalias writable sret(%struct.Task) align 8 %agg.result, ptr noundef nonnull align 8 dereferenceable(12) %this) local_unnamed_addr #0 comdat align 2 {
entry:
  %0 = getelementptr inbounds i8, ptr %this, i64 -16
  store ptr %0, ptr %agg.result, align 8, !tbaa !12
  ret void
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr dso_local void @_ZN4TaskIiE12promise_type15initial_suspendEv(ptr noundef nonnull align 8 dereferenceable(12) %this) local_unnamed_addr #0 comdat align 2 {
entry:
  ret void
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr hidden noundef zeroext i1 @_ZNKSt3__114suspend_always11await_readyB8nn220000Ev(ptr noundef nonnull align 1 dereferenceable(1) %this) local_unnamed_addr #0 comdat align 2 {
entry:
  ret i1 false
}

; Function Attrs: nomerge nounwind
declare token @llvm.coro.save(ptr) #7

; Function Attrs: alwaysinline mustprogress nofree norecurse nosync nounwind willreturn memory(none)
define internal void @_Z6calleev.__await_suspend_wrapper__init(ptr nofree noundef nonnull readnone captures(none) %0, ptr nofree noundef readnone captures(none) %1) #8 {
entry:
  ret void
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr hidden void @_ZNKSt3__114suspend_always13await_suspendB8nn220000ENS_16coroutine_handleIvEE(ptr noundef nonnull align 1 dereferenceable(1) %this, ptr %.coerce) local_unnamed_addr #0 comdat align 2 {
entry:
  ret void
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr hidden ptr @_ZNSt3__116coroutine_handleIN4TaskIiE12promise_typeEE12from_addressB8nn220000EPv(ptr noundef %__addr) local_unnamed_addr #0 comdat align 2 {
entry:
  ret ptr %__addr
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr hidden ptr @_ZNKSt3__116coroutine_handleIN4TaskIiE12promise_typeEEcvNS0_IvEEB8nn220000Ev(ptr noundef nonnull align 8 dereferenceable(8) %this) local_unnamed_addr #0 comdat align 2 {
entry:
  %0 = load ptr, ptr %this, align 8, !tbaa !18
  ret ptr %0
}

; Function Attrs: mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #5

declare void @llvm.coro.await.suspend.void(ptr, ptr, ptr)

; Function Attrs: nounwind
declare i8 @llvm.coro.suspend(token, i1) #2

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr hidden void @_ZNKSt3__114suspend_always12await_resumeB8nn220000Ev(ptr noundef nonnull align 1 dereferenceable(1) %this) local_unnamed_addr #0 comdat align 2 {
entry:
  ret void
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr dso_local void @_ZN4TaskIiE12promise_type12return_valueEi(ptr noundef nonnull align 8 dereferenceable(12) %this, i32 noundef %x) local_unnamed_addr #0 comdat align 2 {
entry:
  %value = getelementptr inbounds nuw i8, ptr %this, i64 8
  store i32 %x, ptr %value, align 8, !tbaa !16
  ret void
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr dso_local void @_ZN4TaskIiE12promise_type13final_suspendEv(ptr noundef nonnull align 8 dereferenceable(12) %this) local_unnamed_addr #0 comdat align 2 {
entry:
  ret void
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr dso_local noundef zeroext i1 @_ZNK4TaskIiE12promise_type12FinalAwaiter11await_readyEv(ptr noundef nonnull align 1 dereferenceable(1) %this) local_unnamed_addr #0 comdat align 2 {
entry:
  ret i1 false
}

; Function Attrs: alwaysinline mustprogress nofree nosync nounwind willreturn memory(argmem: read)
define internal noundef ptr @_Z6calleev.__await_suspend_wrapper__final(ptr nofree noundef nonnull readnone captures(none) %0, ptr nofree noundef readonly captures(address_is_null) %1) #9 {
entry:
  %cmp.i.not.i = icmp eq ptr %1, null
  br i1 %cmp.i.not.i, label %if.then.i, label %if.end.i

if.then.i:                                        ; preds = %entry
  %2 = tail call ptr @llvm.coro.noop()
  br label %_ZN4TaskIiE12promise_type12FinalAwaiter13await_suspendIS1_EENSt3__116coroutine_handleIvEENS5_IT_EE.exit

if.end.i:                                         ; preds = %entry
  %3 = getelementptr inbounds nuw i8, ptr %1, i64 16
  %retval.sroa.0.0.copyload.i = load ptr, ptr %3, align 8, !tbaa !12
  br label %_ZN4TaskIiE12promise_type12FinalAwaiter13await_suspendIS1_EENSt3__116coroutine_handleIvEENS5_IT_EE.exit

_ZN4TaskIiE12promise_type12FinalAwaiter13await_suspendIS1_EENSt3__116coroutine_handleIvEENS5_IT_EE.exit: ; preds = %if.then.i, %if.end.i
  %retval.sroa.0.0.i = phi ptr [ %retval.sroa.0.0.copyload.i, %if.end.i ], [ %2, %if.then.i ]
  ret ptr %retval.sroa.0.0.i
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr dso_local ptr @_ZN4TaskIiE12promise_type12FinalAwaiter13await_suspendIS1_EENSt3__116coroutine_handleIvEENS5_IT_EE(ptr noundef nonnull align 1 dereferenceable(1) %this, ptr %coro.coerce) local_unnamed_addr #0 comdat align 2 {
entry:
  %cmp.i.not = icmp eq ptr %coro.coerce, null
  br i1 %cmp.i.not, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  %0 = tail call ptr @llvm.coro.noop()
  br label %return

if.end:                                           ; preds = %entry
  %1 = getelementptr inbounds nuw i8, ptr %coro.coerce, i64 16
  %retval.sroa.0.0.copyload = load ptr, ptr %1, align 8, !tbaa !12
  br label %return

return:                                           ; preds = %if.end, %if.then
  %retval.sroa.0.0 = phi ptr [ %retval.sroa.0.0.copyload, %if.end ], [ %0, %if.then ]
  ret ptr %retval.sroa.0.0
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr hidden noundef ptr @_ZNKSt3__116coroutine_handleIvE7addressB8nn220000Ev(ptr noundef nonnull align 8 dereferenceable(8) %this) local_unnamed_addr #0 comdat align 2 {
entry:
  %0 = load ptr, ptr %this, align 8, !tbaa !9
  ret ptr %0
}

declare void @llvm.coro.await.suspend.handle(ptr, ptr, ptr)

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr dso_local void @_ZN4TaskIiE12promise_type12FinalAwaiter12await_resumeEv(ptr noundef nonnull align 1 dereferenceable(1) %this) local_unnamed_addr #0 comdat align 2 {
entry:
  ret void
}

; Function Attrs: nobuiltin nounwind
declare void @_ZdlPvm(ptr noundef, i64 noundef) local_unnamed_addr #10

; Function Attrs: nofree nounwind memory(argmem: read)
declare ptr @llvm.coro.free(token, ptr readonly captures(none)) #11

; Function Attrs: nofree nosync nounwind memory(none)
declare void @llvm.coro.dead(ptr) #4

; Function Attrs: nounwind
declare void @llvm.coro.end(ptr, i1, token) #2

; Function Attrs: mustprogress nounwind presplitcoroutine uwtable
define dso_local void @_Z6callerv(ptr dead_on_unwind writable sret(%struct.Task) align 8 %agg.result) #12 {
entry:
  %__promise = alloca %"struct.Task<int>::promise_type", align 8
  %ref.tmp = alloca %"struct.std::__1::suspend_always", align 1
  %ref.tmp2 = alloca %"struct.Task<int>::Awaiter", align 8
  %ref.tmp3 = alloca %struct.Task, align 8
  %ref.tmp12 = alloca %"struct.Task<int>::promise_type::FinalAwaiter", align 1
  %0 = call token @llvm.coro.id(i32 16, ptr nonnull %__promise, ptr nonnull @_Z6callerv, ptr null)
  %1 = call i1 @llvm.coro.alloc(token %0)
  br i1 %1, label %coro.alloc, label %coro.init

coro.alloc:                                       ; preds = %entry
  %2 = call i64 @llvm.coro.size.i64()
  %call = call noalias noundef nonnull ptr @_Znwm(i64 noundef %2) #16
  br label %coro.init

coro.init:                                        ; preds = %coro.alloc, %entry
  %3 = phi ptr [ null, %entry ], [ %call, %coro.alloc ]
  %4 = call ptr @llvm.coro.begin(token %0, ptr %3) #17
  call void @llvm.lifetime.start.p0(ptr nonnull %__promise) #2
  call void @_ZN4TaskIiE12promise_typeC2Ev(ptr noundef nonnull align 8 dereferenceable(12) %__promise) #2
  call void @_ZN4TaskIiE12promise_type17get_return_objectEv(ptr dead_on_unwind writable sret(%struct.Task) align 8 %agg.result, ptr noundef nonnull align 8 dereferenceable(12) %__promise) #2
  call void @llvm.lifetime.start.p0(ptr nonnull %ref.tmp) #2
  call void @_ZN4TaskIiE12promise_type15initial_suspendEv(ptr noundef nonnull align 8 dereferenceable(12) %__promise) #2
  %call1 = call noundef zeroext i1 @_ZNKSt3__114suspend_always11await_readyB8nn220000Ev(ptr noundef nonnull align 1 dereferenceable(1) %ref.tmp) #2
  br i1 %call1, label %init.ready, label %init.suspend

init.suspend:                                     ; preds = %coro.init
  %5 = call token @llvm.coro.save(ptr null)
  call void @llvm.coro.await.suspend.void(ptr nonnull %ref.tmp, ptr %4, ptr nonnull @_Z6callerv.__await_suspend_wrapper__init) #2
  %6 = call i8 @llvm.coro.suspend(token %5, i1 false)
  switch i8 %6, label %coro.ret [
    i8 0, label %init.ready
    i8 1, label %cleanup
  ]

init.ready:                                       ; preds = %init.suspend, %coro.init
  call void @_ZNKSt3__114suspend_always12await_resumeB8nn220000Ev(ptr noundef nonnull align 1 dereferenceable(1) %ref.tmp) #2
  br label %cleanup

cleanup:                                          ; preds = %init.suspend, %init.ready
  %cleanup.dest.slot.0 = phi i32 [ 0, %init.ready ], [ 2, %init.suspend ]
  call void @llvm.lifetime.end.p0(ptr nonnull %ref.tmp) #2
  %7 = icmp eq i32 %cleanup.dest.slot.0, 0
  br i1 %7, label %cleanup.cont, label %coro.cleanup

cleanup.cont:                                     ; preds = %cleanup
  call void @llvm.lifetime.start.p0(ptr nonnull %ref.tmp2) #2
  call void @llvm.lifetime.start.p0(ptr nonnull %ref.tmp3) #2
  call void @_Z6calleev(ptr dead_on_unwind nonnull writable sret(%struct.Task) align 8 %ref.tmp3) #18
  %call4 = call ptr @_ZN4TaskIiEawEv(ptr noundef nonnull align 8 dereferenceable(8) %ref.tmp3)
  store ptr %call4, ptr %ref.tmp2, align 8
  %call5 = call noundef zeroext i1 @_ZNK4TaskIiE7Awaiter11await_readyEv(ptr noundef nonnull align 8 dereferenceable(8) %ref.tmp2) #2
  br i1 %call5, label %await.ready, label %await.suspend

await.suspend:                                    ; preds = %cleanup.cont
  %8 = call token @llvm.coro.save(ptr null)
  call void @llvm.coro.await.suspend.void(ptr nonnull %ref.tmp2, ptr %4, ptr nonnull @_Z6callerv.__await_suspend_wrapper__await) #2
  %9 = call i8 @llvm.coro.suspend(token %8, i1 false)
  switch i8 %9, label %coro.ret [
    i8 0, label %await.ready
    i8 1, label %cleanup7
  ]

await.ready:                                      ; preds = %await.suspend, %cleanup.cont
  %call6 = call noundef i32 @_ZN4TaskIiE7Awaiter12await_resumeEv(ptr noundef nonnull align 8 dereferenceable(8) %ref.tmp2) #2
  call void @_ZN4TaskIiE12promise_type12return_valueEi(ptr noundef nonnull align 8 dereferenceable(12) %__promise, i32 noundef %call6) #2
  br label %cleanup7

cleanup7:                                         ; preds = %await.suspend, %await.ready
  %cleanup.dest.slot.1 = phi i32 [ 0, %await.ready ], [ 2, %await.suspend ]
  call void @_ZN4TaskIiED2Ev(ptr noundef nonnull align 8 dead_on_return(8) dereferenceable(8) %ref.tmp3) #2
  call void @llvm.lifetime.end.p0(ptr nonnull %ref.tmp3) #2
  call void @llvm.lifetime.end.p0(ptr nonnull %ref.tmp2) #2
  %10 = icmp eq i32 %cleanup.dest.slot.1, 0
  br i1 %10, label %coro.final, label %coro.cleanup

coro.final:                                       ; preds = %cleanup7
  call void @llvm.lifetime.start.p0(ptr nonnull %ref.tmp12) #2
  call void @_ZN4TaskIiE12promise_type13final_suspendEv(ptr noundef nonnull align 8 dereferenceable(12) %__promise) #2
  %call14 = call noundef zeroext i1 @_ZNK4TaskIiE12promise_type12FinalAwaiter11await_readyEv(ptr noundef nonnull align 1 dereferenceable(1) %ref.tmp12) #2
  br i1 %call14, label %final.ready, label %final.suspend

final.suspend:                                    ; preds = %coro.final
  %11 = call token @llvm.coro.save(ptr null)
  call void @llvm.coro.await.suspend.handle(ptr nonnull %ref.tmp12, ptr %4, ptr nonnull @_Z6callerv.__await_suspend_wrapper__final) #2
  %12 = call i8 @llvm.coro.suspend(token %11, i1 true) #17
  switch i8 %12, label %coro.ret [
    i8 0, label %final.ready
    i8 1, label %cleanup15
  ]

final.ready:                                      ; preds = %final.suspend, %coro.final
  call void @_ZN4TaskIiE12promise_type12FinalAwaiter12await_resumeEv(ptr noundef nonnull align 1 dereferenceable(1) %ref.tmp12) #2
  br label %cleanup15

cleanup15:                                        ; preds = %final.suspend, %final.ready
  call void @llvm.lifetime.end.p0(ptr nonnull %ref.tmp12) #2
  br label %coro.cleanup

coro.cleanup:                                     ; preds = %cleanup7, %cleanup, %cleanup15
  call void @llvm.lifetime.end.p0(ptr nonnull %__promise) #2
  %13 = call ptr @llvm.coro.free(token %0, ptr %4)
  %.not = icmp eq ptr %13, null
  br i1 %.not, label %after.coro.free, label %coro.free

coro.free:                                        ; preds = %coro.cleanup
  %14 = call i64 @llvm.coro.size.i64()
  call void @_ZdlPvm(ptr noundef nonnull %13, i64 noundef %14) #2
  br label %after.coro.free

after.coro.free:                                  ; preds = %coro.cleanup, %coro.free
  call void @llvm.coro.dead(ptr %4)
  br label %coro.ret

coro.ret:                                         ; preds = %after.coro.free, %final.suspend, %await.suspend, %init.suspend
  call void @llvm.coro.end(ptr null, i1 false, token none) #17
  ret void
}

; Function Attrs: alwaysinline mustprogress
define internal void @_Z6callerv.__await_suspend_wrapper__init(ptr noundef nonnull %0, ptr noundef %1) #13 {
entry:
  %ref.tmp = alloca %"struct.std::__1::coroutine_handle", align 8
  call void @llvm.lifetime.start.p0(ptr nonnull %ref.tmp) #2
  %call = call ptr @_ZNSt3__116coroutine_handleIN4TaskIiE12promise_typeEE12from_addressB8nn220000EPv(ptr noundef %1) #2
  store ptr %call, ptr %ref.tmp, align 8
  %call2 = call ptr @_ZNKSt3__116coroutine_handleIN4TaskIiE12promise_typeEEcvNS0_IvEEB8nn220000Ev(ptr noundef nonnull align 8 dereferenceable(8) %ref.tmp) #2
  call void @_ZNKSt3__114suspend_always13await_suspendB8nn220000ENS_16coroutine_handleIvEE(ptr noundef nonnull align 1 dereferenceable(1) %0, ptr %call2) #2
  call void @llvm.lifetime.end.p0(ptr nonnull %ref.tmp) #2
  ret void
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr dso_local ptr @_ZN4TaskIiEawEv(ptr noundef nonnull align 8 dereferenceable(8) %this) local_unnamed_addr #0 comdat align 2 {
entry:
  %retval = alloca %"struct.Task<int>::Awaiter", align 8
  call void @_ZN4TaskIiE7AwaiterC2EPS0_(ptr noundef nonnull align 8 dereferenceable(8) %retval, ptr noundef nonnull %this)
  %0 = load ptr, ptr %retval, align 8
  ret ptr %0
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr dso_local noundef zeroext i1 @_ZNK4TaskIiE7Awaiter11await_readyEv(ptr noundef nonnull align 8 dereferenceable(8) %this) local_unnamed_addr #0 comdat align 2 {
entry:
  ret i1 false
}

; Function Attrs: alwaysinline mustprogress
define internal void @_Z6callerv.__await_suspend_wrapper__await(ptr noundef nonnull %0, ptr noundef %1) #13 {
entry:
  %ref.tmp = alloca %"struct.std::__1::coroutine_handle", align 8
  call void @llvm.lifetime.start.p0(ptr nonnull %ref.tmp) #2
  %call = call ptr @_ZNSt3__116coroutine_handleIN4TaskIiE12promise_typeEE12from_addressB8nn220000EPv(ptr noundef %1) #2
  store ptr %call, ptr %ref.tmp, align 8
  %call2 = call ptr @_ZNKSt3__116coroutine_handleIN4TaskIiE12promise_typeEEcvNS0_IvEEB8nn220000Ev(ptr noundef nonnull align 8 dereferenceable(8) %ref.tmp) #2
  call void @_ZN4TaskIiE7Awaiter13await_suspendENSt3__116coroutine_handleIvEE(ptr noundef nonnull align 8 dereferenceable(8) %0, ptr %call2) #2
  call void @llvm.lifetime.end.p0(ptr nonnull %ref.tmp) #2
  ret void
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr dso_local void @_ZN4TaskIiE7Awaiter13await_suspendENSt3__116coroutine_handleIvEE(ptr noundef nonnull align 8 dereferenceable(8) %this, ptr %continuation.coerce) local_unnamed_addr #0 comdat align 2 {
entry:
  ret void
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr dso_local noundef i32 @_ZN4TaskIiE7Awaiter12await_resumeEv(ptr noundef nonnull align 8 dereferenceable(8) %this) local_unnamed_addr #0 comdat align 2 {
entry:
  %0 = load ptr, ptr %this, align 8, !tbaa !20
  %call = call noundef nonnull align 8 dereferenceable(12) ptr @_ZNKSt3__116coroutine_handleIN4TaskIiE12promise_typeEE7promiseB8nn220000Ev(ptr noundef nonnull align 8 dereferenceable(8) %0)
  %value = getelementptr inbounds nuw i8, ptr %call, i64 8
  %1 = load i32, ptr %value, align 8, !tbaa !16
  ret i32 %1
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr dso_local void @_ZN4TaskIiED2Ev(ptr noundef nonnull align 8 dead_on_return(8) dereferenceable(8) %this) unnamed_addr #0 comdat align 2 {
entry:
  %call = call noundef zeroext i1 @_ZNKSt3__116coroutine_handleIN4TaskIiE12promise_typeEEcvbB8nn220000Ev(ptr noundef nonnull align 8 dereferenceable(8) %this) #2
  br i1 %call, label %if.then, label %if.end

if.then:                                          ; preds = %entry
  call void @_ZNKSt3__116coroutine_handleIN4TaskIiE12promise_typeEE7destroyB8nn220000Ev(ptr noundef nonnull align 8 dereferenceable(8) %this)
  br label %if.end

if.end:                                           ; preds = %if.then, %entry
  ret void
}

; Function Attrs: alwaysinline mustprogress
define internal noundef ptr @_Z6callerv.__await_suspend_wrapper__final(ptr noundef nonnull %0, ptr noundef %1) #13 {
entry:
  %ref.tmp = alloca %"struct.std::__1::coroutine_handle.0", align 8
  call void @llvm.lifetime.start.p0(ptr nonnull %ref.tmp) #2
  %call = call ptr @_ZNSt3__116coroutine_handleIN4TaskIiE12promise_typeEE12from_addressB8nn220000EPv(ptr noundef %1) #2
  %call3 = call ptr @_ZN4TaskIiE12promise_type12FinalAwaiter13await_suspendIS1_EENSt3__116coroutine_handleIvEENS5_IT_EE(ptr noundef nonnull align 1 dereferenceable(1) %0, ptr %call) #2
  store ptr %call3, ptr %ref.tmp, align 8
  %call5 = call noundef ptr @_ZNKSt3__116coroutine_handleIvE7addressB8nn220000Ev(ptr noundef nonnull align 8 dereferenceable(8) %ref.tmp) #2
  call void @llvm.lifetime.end.p0(ptr nonnull %ref.tmp) #2
  ret ptr %call5
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr dso_local void @_ZNSt3__116coroutine_handleIvEC2Ev(ptr noundef nonnull align 8 dereferenceable(8) %this) unnamed_addr #0 comdat align 2 {
  unreachable
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr dso_local void @_ZNSt3__116coroutine_handleIN4TaskIiE12promise_typeEEC2Ev(ptr noundef nonnull align 8 dereferenceable(8) %this) unnamed_addr #0 comdat align 2 {
  unreachable
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr hidden ptr @_ZNSt3__116coroutine_handleIvE12from_addressB8nn220000EPv(ptr noundef %__addr) local_unnamed_addr #0 comdat align 2 {
  unreachable
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr hidden noundef ptr @_ZNKSt3__116coroutine_handleIN4TaskIiE12promise_typeEE7addressB8nn220000Ev(ptr noundef nonnull align 8 dereferenceable(8) %this) local_unnamed_addr #0 comdat align 2 {
  unreachable
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr dso_local void @_ZN4TaskIiE7AwaiterC2EPS0_(ptr noundef nonnull align 8 dereferenceable(8) %this, ptr noundef %t) unnamed_addr #0 comdat align 2 {
entry:
  store ptr %t, ptr %this, align 8, !tbaa !20
  ret void
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr hidden noundef zeroext i1 @_ZNKSt3__116coroutine_handleIN4TaskIiE12promise_typeEEcvbB8nn220000Ev(ptr noundef nonnull align 8 dereferenceable(8) %this) local_unnamed_addr #0 comdat align 2 {
entry:
  %0 = load ptr, ptr %this, align 8, !tbaa !18
  %cmp = icmp ne ptr %0, null
  ret i1 %cmp
}

; Function Attrs: inlinehint mustprogress nounwind uwtable
define linkonce_odr hidden ptr @_ZNSt3__114noop_coroutineB8nn220000Ev() local_unnamed_addr #6 comdat {
  unreachable
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr hidden ptr @_ZNKSt3__116coroutine_handleINS_22noop_coroutine_promiseEEcvNS0_IvEEB8nn220000Ev(ptr noundef nonnull align 8 dereferenceable(8) %this) local_unnamed_addr #0 comdat align 2 {
  unreachable
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr hidden noundef nonnull align 8 dereferenceable(12) ptr @_ZNKSt3__116coroutine_handleIN4TaskIiE12promise_typeEE7promiseB8nn220000Ev(ptr noundef nonnull align 8 dereferenceable(8) %this) local_unnamed_addr #0 comdat align 2 {
entry:
  %0 = load ptr, ptr %this, align 8, !tbaa !18
  %1 = getelementptr inbounds nuw i8, ptr %0, i64 16
  ret ptr %1
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr hidden void @_ZNSt3__116coroutine_handleINS_22noop_coroutine_promiseEEC2B8nn220000Ev(ptr noundef nonnull align 8 dereferenceable(8) %this) unnamed_addr #0 comdat align 2 {
  unreachable
}

; Function Attrs: nofree nosync nounwind memory(none)
declare ptr @llvm.coro.noop() #4

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr hidden noundef ptr @_ZNKSt3__116coroutine_handleINS_22noop_coroutine_promiseEE7addressB8nn220000Ev(ptr noundef nonnull align 8 dereferenceable(8) %this) local_unnamed_addr #0 comdat align 2 {
  unreachable
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr hidden ptr @_ZNSt3__116coroutine_handleIN4TaskIiE12promise_typeEE12from_promiseB8nn220000ERS3_(ptr noundef nonnull align 8 dereferenceable(12) %__promise) local_unnamed_addr #0 comdat align 2 {
  unreachable
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr dso_local void @_ZN4TaskIiEC2ENSt3__116coroutine_handleINS0_12promise_typeEEE(ptr noundef nonnull align 8 dereferenceable(8) %this, ptr %handle.coerce) unnamed_addr #0 comdat align 2 {
  unreachable
}

; Function Attrs: mustprogress nounwind uwtable
define linkonce_odr hidden void @_ZNKSt3__116coroutine_handleIN4TaskIiE12promise_typeEE7destroyB8nn220000Ev(ptr noundef nonnull align 8 dereferenceable(8) %this) local_unnamed_addr #0 comdat align 2 {
entry:
  %0 = load ptr, ptr %this, align 8, !tbaa !18
  %1 = call ptr @llvm.coro.subfn.addr(ptr %0, i8 1)
  call void %1(ptr %0) #2
  ret void
}

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: read)
declare ptr @llvm.coro.subfn.addr(ptr readonly captures(none), i8) #14

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite)
declare void @llvm.experimental.noalias.scope.decl(metadata) #15

; Function Attrs: mustprogress nounwind uwtable
define internal void @_Z6calleev.resume(ptr noundef nonnull align 8 dereferenceable(40) %0) #0 {
entry.resume:
  %ref.tmp.reload.addr = getelementptr inbounds i8, ptr %0, i64 33
  %ref.tmp2.reload.addr = getelementptr inbounds i8, ptr %0, i64 33
  %__promise.reload.addr = getelementptr inbounds i8, ptr %0, i64 16
  br label %resume.entry

resume.entry:                                     ; preds = %entry.resume
  br label %resume.0

resume.0:                                         ; preds = %resume.entry
  br label %resume.0.landing

resume.0.landing:                                 ; preds = %resume.0
  br label %AfterCoroSuspend

AfterCoroSuspend:                                 ; preds = %resume.0.landing
  switch i8 0, label %coro.ret [
    i8 0, label %final.suspend
    i8 1, label %cleanup
  ]

cleanup:                                          ; preds = %AfterCoroSuspend
  br label %coro.cleanup

final.suspend:                                    ; preds = %AfterCoroSuspend
  %value.i = getelementptr inbounds nuw i8, ptr %__promise.reload.addr, i64 8
  store i32 1, ptr %value.i, align 8, !tbaa !16
  br label %CoroSave9

CoroSave9:                                        ; preds = %final.suspend
  store ptr null, ptr %0, align 8
  br label %AfterCoroSave10

AfterCoroSave10:                                  ; preds = %CoroSave9
  %1 = call ptr @_Z6calleev.__await_suspend_wrapper__final(ptr nonnull %ref.tmp2.reload.addr, ptr %0) #2
  %2 = call ptr @llvm.coro.subfn.addr(ptr %1, i8 0)
  musttail call void %2(ptr %1)
  ret void

coro.cleanup:                                     ; preds = %cleanup
  %3 = call ptr @llvm.coro.free(token poison, ptr %0)
  %.not = icmp eq ptr %3, null
  br i1 %.not, label %after.coro.free, label %coro.free

coro.free:                                        ; preds = %coro.cleanup
  call void @_ZdlPvm(ptr noundef nonnull %3, i64 noundef 40) #2
  br label %after.coro.free

after.coro.free:                                  ; preds = %coro.free, %coro.cleanup
  call void @llvm.coro.dead(ptr %0)
  br label %coro.ret

coro.ret:                                         ; preds = %after.coro.free, %AfterCoroSuspend
  br label %CoroEnd

CoroEnd:                                          ; preds = %coro.ret
  ret void
}

; Function Attrs: mustprogress nounwind uwtable
define internal void @_Z6calleev.destroy(ptr noundef nonnull align 8 dereferenceable(40) %0) #0 {
entry.destroy:
  %ref.tmp.reload.addr = getelementptr inbounds i8, ptr %0, i64 33
  %ref.tmp2.reload.addr = getelementptr inbounds i8, ptr %0, i64 33
  %__promise.reload.addr = getelementptr inbounds i8, ptr %0, i64 16
  br label %resume.entry

resume.entry:                                     ; preds = %entry.destroy
  %1 = load ptr, ptr %0, align 8
  %2 = icmp eq ptr %1, null
  br i1 %2, label %resume.1, label %Switch

Switch:                                           ; preds = %resume.entry
  br label %resume.0

resume.0:                                         ; preds = %Switch
  br label %resume.0.landing

resume.0.landing:                                 ; preds = %resume.0
  br label %AfterCoroSuspend

AfterCoroSuspend:                                 ; preds = %resume.0.landing
  switch i8 1, label %coro.ret [
    i8 0, label %final.suspend
    i8 1, label %cleanup
  ]

cleanup:                                          ; preds = %AfterCoroSuspend
  br label %coro.cleanup

final.suspend:                                    ; preds = %AfterCoroSuspend
  %value.i = getelementptr inbounds nuw i8, ptr %__promise.reload.addr, i64 8
  store i32 1, ptr %value.i, align 8, !tbaa !16
  br label %CoroSave9

CoroSave9:                                        ; preds = %final.suspend
  store ptr null, ptr %0, align 8
  br label %AfterCoroSave10

AfterCoroSave10:                                  ; preds = %CoroSave9
  %3 = call ptr @_Z6calleev.__await_suspend_wrapper__final(ptr nonnull %ref.tmp2.reload.addr, ptr %0) #2
  %4 = call ptr @llvm.coro.subfn.addr(ptr %3, i8 0)
  musttail call void %4(ptr %3)
  ret void

resume.1:                                         ; preds = %resume.entry
  br label %resume.1.landing

resume.1.landing:                                 ; preds = %resume.1
  br label %AfterCoroSuspend12

AfterCoroSuspend12:                               ; preds = %resume.1.landing
  %switch = icmp ult i8 1, 2
  br i1 %switch, label %cleanup5, label %coro.ret

cleanup5:                                         ; preds = %AfterCoroSuspend12
  br label %coro.cleanup

coro.cleanup:                                     ; preds = %cleanup5, %cleanup
  %5 = call ptr @llvm.coro.free(token poison, ptr %0)
  %.not = icmp eq ptr %5, null
  br i1 %.not, label %after.coro.free, label %coro.free

coro.free:                                        ; preds = %coro.cleanup
  call void @_ZdlPvm(ptr noundef nonnull %5, i64 noundef 40) #2
  br label %after.coro.free

after.coro.free:                                  ; preds = %coro.free, %coro.cleanup
  call void @llvm.coro.dead(ptr %0)
  br label %coro.ret

coro.ret:                                         ; preds = %after.coro.free, %AfterCoroSuspend12, %AfterCoroSuspend
  br label %CoroEnd

CoroEnd:                                          ; preds = %coro.ret
  ret void
}

; Function Attrs: mustprogress nounwind uwtable
define internal void @_Z6calleev.cleanup(ptr noundef nonnull align 8 dereferenceable(40) %0) #0 {
entry.cleanup:
  %ref.tmp.reload.addr = getelementptr inbounds i8, ptr %0, i64 33
  %ref.tmp2.reload.addr = getelementptr inbounds i8, ptr %0, i64 33
  %__promise.reload.addr = getelementptr inbounds i8, ptr %0, i64 16
  br label %resume.entry

resume.entry:                                     ; preds = %entry.cleanup
  %1 = load ptr, ptr %0, align 8
  %2 = icmp eq ptr %1, null
  br i1 %2, label %resume.1, label %Switch

Switch:                                           ; preds = %resume.entry
  br label %resume.0

resume.0:                                         ; preds = %Switch
  br label %resume.0.landing

resume.0.landing:                                 ; preds = %resume.0
  br label %AfterCoroSuspend

AfterCoroSuspend:                                 ; preds = %resume.0.landing
  switch i8 1, label %coro.ret [
    i8 0, label %final.suspend
    i8 1, label %cleanup
  ]

cleanup:                                          ; preds = %AfterCoroSuspend
  br label %coro.cleanup

final.suspend:                                    ; preds = %AfterCoroSuspend
  %value.i = getelementptr inbounds nuw i8, ptr %__promise.reload.addr, i64 8
  store i32 1, ptr %value.i, align 8, !tbaa !16
  br label %CoroSave9

CoroSave9:                                        ; preds = %final.suspend
  store ptr null, ptr %0, align 8
  br label %AfterCoroSave10

AfterCoroSave10:                                  ; preds = %CoroSave9
  %3 = call ptr @_Z6calleev.__await_suspend_wrapper__final(ptr nonnull %ref.tmp2.reload.addr, ptr %0) #2
  %4 = call ptr @llvm.coro.subfn.addr(ptr %3, i8 0)
  musttail call void %4(ptr %3)
  ret void

resume.1:                                         ; preds = %resume.entry
  br label %resume.1.landing

resume.1.landing:                                 ; preds = %resume.1
  br label %AfterCoroSuspend12

AfterCoroSuspend12:                               ; preds = %resume.1.landing
  %switch = icmp ult i8 1, 2
  br i1 %switch, label %cleanup5, label %coro.ret

cleanup5:                                         ; preds = %AfterCoroSuspend12
  br label %coro.cleanup

coro.cleanup:                                     ; preds = %cleanup5, %cleanup
  %.not = icmp eq ptr null, null
  br i1 %.not, label %after.coro.free, label %coro.free

coro.free:                                        ; preds = %coro.cleanup
  call void @_ZdlPvm(ptr noundef nonnull null, i64 noundef 40) #2
  br label %after.coro.free

after.coro.free:                                  ; preds = %coro.free, %coro.cleanup
  br label %coro.ret

coro.ret:                                         ; preds = %after.coro.free, %AfterCoroSuspend12, %AfterCoroSuspend
  br label %CoroEnd

CoroEnd:                                          ; preds = %coro.ret
  ret void
}

; Function Attrs: mustprogress nounwind uwtable
define internal void @_Z6calleev.noalloc(ptr dead_on_unwind writable sret(%struct.Task) align 8 %0, ptr noundef nonnull align 8 dereferenceable(40) %1) #0 {
entry:
  %2 = call token @llvm.coro.id(i32 16, ptr nonnull null, ptr nonnull @_Z6calleev, ptr @_Z6calleev.resumers)
  br label %init.suspend.from.entry

init.suspend.from.entry:                          ; preds = %entry
  %.init.suspend = phi ptr [ null, %entry ]
  br label %init.suspend

init.suspend:                                     ; preds = %init.suspend.from.entry
  store ptr @_Z6calleev.resume, ptr %1, align 8
  %3 = select i1 false, ptr @_Z6calleev.destroy, ptr @_Z6calleev.cleanup
  %destroy.addr = getelementptr inbounds i8, ptr %1, i64 8
  store ptr %3, ptr %destroy.addr, align 8
  br label %AllocaSpillBB

AllocaSpillBB:                                    ; preds = %init.suspend
  %ref.tmp.reload.addr = getelementptr inbounds i8, ptr %1, i64 33
  %ref.tmp2.reload.addr = getelementptr inbounds i8, ptr %1, i64 33
  %__promise.reload.addr = getelementptr inbounds i8, ptr %1, i64 16
  br label %PostSpill

PostSpill:                                        ; preds = %AllocaSpillBB
  store ptr null, ptr %__promise.reload.addr, align 8, !tbaa !9
  %4 = getelementptr inbounds i8, ptr %__promise.reload.addr, i64 -16
  store ptr %4, ptr %0, align 8, !tbaa !12, !alias.scope !23
  br label %CoroSave

CoroSave:                                         ; preds = %PostSpill
  %index.addr13 = getelementptr inbounds i8, ptr %1, i64 32
  store i1 false, ptr %index.addr13, align 1
  br label %AfterCoroSave

AfterCoroSave:                                    ; preds = %CoroSave
  call void @_Z6calleev.__await_suspend_wrapper__init(ptr nonnull %ref.tmp.reload.addr, ptr %1) #2
  br label %CoroSuspend

CoroSuspend:                                      ; preds = %AfterCoroSave
  br label %resume.0.landing

resume.0.landing:                                 ; preds = %CoroSuspend
  br label %AfterCoroSuspend

AfterCoroSuspend:                                 ; preds = %resume.0.landing
  switch i8 -1, label %coro.ret [
    i8 0, label %final.suspend
    i8 1, label %cleanup
  ]

cleanup:                                          ; preds = %AfterCoroSuspend
  br label %coro.cleanup

final.suspend:                                    ; preds = %AfterCoroSuspend
  %value.i = getelementptr inbounds nuw i8, ptr %__promise.reload.addr, i64 8
  store i32 1, ptr %value.i, align 8, !tbaa !16
  br label %CoroSave9

CoroSave9:                                        ; preds = %final.suspend
  store ptr null, ptr %1, align 8
  br label %AfterCoroSave10

AfterCoroSave10:                                  ; preds = %CoroSave9
  %5 = call ptr @_Z6calleev.__await_suspend_wrapper__final(ptr nonnull %ref.tmp2.reload.addr, ptr %1) #2
  %6 = call ptr @llvm.coro.subfn.addr(ptr %5, i8 0)
  call void %6(ptr %5)
  br label %CoroSuspend11

CoroSuspend11:                                    ; preds = %AfterCoroSave10
  br label %resume.1.landing

resume.1.landing:                                 ; preds = %CoroSuspend11
  br label %AfterCoroSuspend12

AfterCoroSuspend12:                               ; preds = %resume.1.landing
  %switch = icmp ult i8 -1, 2
  br i1 %switch, label %cleanup5, label %coro.ret

cleanup5:                                         ; preds = %AfterCoroSuspend12
  br label %coro.cleanup

coro.cleanup:                                     ; preds = %cleanup5, %cleanup
  %.not = icmp eq ptr null, null
  br i1 %.not, label %after.coro.free, label %coro.free

coro.free:                                        ; preds = %coro.cleanup
  call void @_ZdlPvm(ptr noundef nonnull null, i64 noundef 40) #2
  br label %after.coro.free

after.coro.free:                                  ; preds = %coro.free, %coro.cleanup
  br label %coro.ret

coro.ret:                                         ; preds = %after.coro.free, %AfterCoroSuspend12, %AfterCoroSuspend
  br label %CoroEnd

CoroEnd:                                          ; preds = %coro.ret
  br label %AfterCoroEnd

AfterCoroEnd:                                     ; preds = %CoroEnd
  ret void
}

attributes #0 = { mustprogress nounwind uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: read) }
attributes #2 = { nounwind }
attributes #3 = { nobuiltin allocsize(0) "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { nofree nosync nounwind memory(none) }
attributes #5 = { mustprogress nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #6 = { inlinehint mustprogress nounwind uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #7 = { nomerge nounwind }
attributes #8 = { alwaysinline mustprogress nofree norecurse nosync nounwind willreturn memory(none) "min-legal-vector-width"="0" "sample-profile-suffix-elision-policy"="selected" }
attributes #9 = { alwaysinline mustprogress nofree nosync nounwind willreturn memory(argmem: read) "min-legal-vector-width"="0" "sample-profile-suffix-elision-policy"="selected" }
attributes #10 = { nobuiltin nounwind "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #11 = { nofree nounwind memory(argmem: read) }
attributes #12 = { mustprogress nounwind presplitcoroutine uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #13 = { alwaysinline mustprogress "min-legal-vector-width"="0" "sample-profile-suffix-elision-policy"="selected" }
attributes #14 = { nocallback nofree nosync nounwind willreturn memory(argmem: read) }
attributes #15 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite) }
attributes #16 = { nounwind allocsize(0) }
attributes #17 = { noduplicate }
attributes #18 = { coro_elide_safe }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}
!llvm.errno.tbaa = !{!4}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 7, !"PIE Level", i32 2}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"clang version 23.0.0git (github-as-tzcnt:tzcnt/llvm-project.git 1d27df1eff67e101ebe70a1c8b32e4e28f0027d5)"}
!4 = !{!5, !6, i64 0}
!5 = !{!"__libc_errno", !6, i64 0}
!6 = !{!"int", !7, i64 0}
!7 = !{!"omnipotent char", !8, i64 0}
!8 = !{!"Simple C++ TBAA"}
!9 = !{!10, !11, i64 0}
!10 = !{!"_ZTSNSt3__116coroutine_handleIvEE", !11, i64 0}
!11 = !{!"any pointer", !7, i64 0}
!12 = !{!11, !11, i64 0}
!13 = !{!14}
!14 = distinct !{!14, !15, !"_ZN4TaskIiE12promise_type17get_return_objectEv: %agg.result"}
!15 = distinct !{!15, !"_ZN4TaskIiE12promise_type17get_return_objectEv"}
!16 = !{!17, !6, i64 8}
!17 = !{!"_ZTSN4TaskIiE12promise_typeE", !10, i64 0, !6, i64 8}
!18 = !{!19, !11, i64 0}
!19 = !{!"_ZTSNSt3__116coroutine_handleIN4TaskIiE12promise_typeEEE", !11, i64 0}
!20 = !{!21, !22, i64 0}
!21 = !{!"_ZTSN4TaskIiE7AwaiterE", !22, i64 0}
!22 = !{!"p1 _ZTS4TaskIiE", !11, i64 0}
!23 = !{!24}
!24 = distinct !{!24, !25, !"_ZN4TaskIiE12promise_type17get_return_objectEv: %agg.result"}
!25 = distinct !{!25, !"_ZN4TaskIiE12promise_type17get_return_objectEv"}
