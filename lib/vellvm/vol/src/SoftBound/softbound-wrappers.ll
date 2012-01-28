; ModuleID = 'softbound-wrappers.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"

%0 = type { i32, void ()* }
%struct.DIR = type opaque
%struct.FILE = type { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, %struct._IO_marker*, %struct.FILE*, i32, i32, i32, i16, i8, [1 x i8], i8*, i64, i8*, i8*, i8*, i8*, i32, i32, [40 x i8] }
%struct.PtrBaseBound = type { i8*, i8*, i8* }
%struct._IO_marker = type { %struct._IO_marker*, %struct.FILE*, i32 }
%struct.addrinfo = type { i32, i32, i32, i32, i32, %struct.sockaddr*, i8*, %struct.addrinfo* }
%struct.dirent = type { i32, i32, i16, i8, [256 x i8] }
%struct.fd_set = type { [32 x i32] }
%struct.glob_t = type { i32, i8**, i32, i32, void (i8*)*, i8* (i8*)*, i8* (i8*)*, i32 (i8*, i8*)*, i32 (i8*, i8*)* }
%struct.group = type { i8*, i8*, i32, i8** }
%struct.hostent = type { i8*, i8**, i32, i32, i8** }
%struct.in_addr = type { i32 }
%struct.option = type { i8*, i32, i32*, i32 }
%struct.passwd = type { i8*, i8*, i32, i32, i8*, i8*, i8* }
%struct.rlimit = type { i32, i32 }
%struct.rusage = type { %struct.rlimit, %struct.rlimit, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32 }
%struct.servent = type { i8*, i8**, i32, i8* }
%struct.sockaddr = type { i16, [14 x i8] }
%struct.stat = type { i64, i16, i32, i32, i32, i32, i32, i64, i16, i32, i32, i32, %struct.rlimit, %struct.rlimit, %struct.rlimit, i32, i32 }
%struct.tm = type { i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i8* }
%struct.tms = type { i32, i32, i32, i32 }
%struct.ttyent = type { i8*, i8*, i8*, i32, i8*, i8* }

@__softboundcetswithss_shadow_stack_ptr = external global i32* ; <i32**> [#uses=13]
@__softbound_hash_table_begin = external global %struct.PtrBaseBound* ; <%struct.PtrBaseBound**> [#uses=3]
@stdout = external global %struct.FILE*           ; <%struct.FILE**> [#uses=2]
@.str = private constant [50 x i8] c"[ctype_toupper_loc] pts->ptr = %p, *ptrs->ptr=%p\0A\00", align 1 ; <[50 x i8]*> [#uses=1]
@.str1 = private constant [53 x i8] c"This case not handled, requesting memory from system\00", align 1 ; <[53 x i8]*> [#uses=1]
@.str2 = private constant [17 x i8] c"Hash table full\0A\00", align 1 ; <[17 x i8]*> [#uses=1]
@.str3 = private constant [77 x i8] c"(read_value >=0 && read_value <= __SOFTBOUNDCETSWITHSS_SHADOW_STACK_ENTRIES)\00", align 1 ; <[77 x i8]*> [#uses=1]
@.str4 = private constant [34 x i8] c"softbound-shadowstack/softbound.h\00", align 1 ; <[34 x i8]*> [#uses=1]
@__PRETTY_FUNCTION__.6393 = internal constant [52 x i8] c"__softboundcetswithss_deallocate_shadow_stack_space\00", align 32 ; <[52 x i8]*> [#uses=1]
@.str5 = private constant [12 x i8] c"arg_no >= 0\00", align 1 ; <[12 x i8]*> [#uses=1]
@__PRETTY_FUNCTION__.6382 = internal constant [46 x i8] c"__softboundcetswithss_store_lock_shadow_stack\00", align 32 ; <[46 x i8]*> [#uses=1]
@__PRETTY_FUNCTION__.6372 = internal constant [45 x i8] c"__softboundcetswithss_store_key_shadow_stack\00", align 32 ; <[45 x i8]*> [#uses=1]
@__PRETTY_FUNCTION__.6361 = internal constant [47 x i8] c"__softboundcetswithss_store_bound_shadow_stack\00", align 32 ; <[47 x i8]*> [#uses=1]
@__PRETTY_FUNCTION__.6350 = internal constant [46 x i8] c"__softboundcetswithss_store_base_shadow_stack\00", align 32 ; <[46 x i8]*> [#uses=1]
@__PRETTY_FUNCTION__.6337 = internal constant [45 x i8] c"__softboundcetswithss_load_lock_shadow_stack\00", align 32 ; <[45 x i8]*> [#uses=1]
@__PRETTY_FUNCTION__.6326 = internal constant [44 x i8] c"__softboundcetswithss_load_key_shadow_stack\00", align 32 ; <[44 x i8]*> [#uses=1]
@__PRETTY_FUNCTION__.6314 = internal constant [46 x i8] c"__softboundcetswithss_load_bound_shadow_stack\00", align 32 ; <[46 x i8]*> [#uses=1]
@__PRETTY_FUNCTION__.6302 = internal constant [45 x i8] c"__softboundcetswithss_load_base_shadow_stack\00", align 32 ; <[45 x i8]*> [#uses=1]
@llvm.global_ctors = appending global [1 x %0] [%0 { i32 65535, void ()* @__softbound_global_init }] ; <[1 x %0]*> [#uses=0]

define weak void @__softboundcetswithss_allocate_shadow_stack_space(i32 %num_pointer_args) nounwind alwaysinline {
entry:
  %0 = load i32** @__softboundcetswithss_shadow_stack_ptr, align 4 ; <i32*> [#uses=2]
  %1 = getelementptr inbounds i32* %0, i32 1      ; <i32*> [#uses=1]
  %2 = load i32* %1, align 4                      ; <i32> [#uses=2]
  %.sum = add i32 %2, 2                           ; <i32> [#uses=1]
  %3 = getelementptr inbounds i32* %0, i32 %.sum  ; <i32*> [#uses=2]
  store i32* %3, i32** @__softboundcetswithss_shadow_stack_ptr, align 4
  store i32 %2, i32* %3, align 4
  %4 = load i32** @__softboundcetswithss_shadow_stack_ptr, align 4 ; <i32*> [#uses=1]
  %5 = getelementptr inbounds i32* %4, i32 1      ; <i32*> [#uses=1]
  %6 = shl i32 %num_pointer_args, 2               ; <i32> [#uses=1]
  store i32 %6, i32* %5, align 4
  ret void
}

define weak i8* @__softboundcetswithss_load_base_shadow_stack(i32 %arg_no) nounwind alwaysinline {
entry:
  %0 = icmp slt i32 %arg_no, 0                    ; <i1> [#uses=1]
  br i1 %0, label %bb, label %bb1

bb:                                               ; preds = %entry
  tail call void @__assert_fail(i8* getelementptr inbounds ([12 x i8]* @.str5, i32 0, i32 0), i8* getelementptr inbounds ([34 x i8]* @.str4, i32 0, i32 0), i32 181, i8* getelementptr inbounds ([45 x i8]* @__PRETTY_FUNCTION__.6302, i32 0, i32 0)) noreturn nounwind
  unreachable

bb1:                                              ; preds = %entry
  %1 = shl i32 %arg_no, 2                         ; <i32> [#uses=1]
  %2 = or i32 %1, 2                               ; <i32> [#uses=1]
  %3 = load i32** @__softboundcetswithss_shadow_stack_ptr, align 4 ; <i32*> [#uses=1]
  %4 = getelementptr inbounds i32* %3, i32 %2     ; <i32*> [#uses=1]
  %5 = bitcast i32* %4 to i8**                    ; <i8**> [#uses=1]
  %6 = load i8** %5, align 4                      ; <i8*> [#uses=1]
  ret i8* %6
}

define weak i8* @__softboundcetswithss_load_bound_shadow_stack(i32 %arg_no) nounwind alwaysinline {
entry:
  %0 = icmp slt i32 %arg_no, 0                    ; <i1> [#uses=1]
  br i1 %0, label %bb, label %bb1

bb:                                               ; preds = %entry
  tail call void @__assert_fail(i8* getelementptr inbounds ([12 x i8]* @.str5, i32 0, i32 0), i8* getelementptr inbounds ([34 x i8]* @.str4, i32 0, i32 0), i32 193, i8* getelementptr inbounds ([46 x i8]* @__PRETTY_FUNCTION__.6314, i32 0, i32 0)) noreturn nounwind
  unreachable

bb1:                                              ; preds = %entry
  %1 = shl i32 %arg_no, 2                         ; <i32> [#uses=1]
  %2 = or i32 %1, 3                               ; <i32> [#uses=1]
  %3 = load i32** @__softboundcetswithss_shadow_stack_ptr, align 4 ; <i32*> [#uses=1]
  %4 = getelementptr inbounds i32* %3, i32 %2     ; <i32*> [#uses=1]
  %5 = bitcast i32* %4 to i8**                    ; <i8**> [#uses=1]
  %6 = load i8** %5, align 4                      ; <i8*> [#uses=1]
  ret i8* %6
}

define weak i32 @__softboundcetswithss_load_key_shadow_stack(i32 %arg_no) nounwind alwaysinline {
entry:
  %0 = icmp slt i32 %arg_no, 0                    ; <i1> [#uses=1]
  br i1 %0, label %bb, label %bb1

bb:                                               ; preds = %entry
  tail call void @__assert_fail(i8* getelementptr inbounds ([12 x i8]* @.str5, i32 0, i32 0), i8* getelementptr inbounds ([34 x i8]* @.str4, i32 0, i32 0), i32 206, i8* getelementptr inbounds ([44 x i8]* @__PRETTY_FUNCTION__.6326, i32 0, i32 0)) noreturn nounwind
  unreachable

bb1:                                              ; preds = %entry
  %1 = shl i32 %arg_no, 2                         ; <i32> [#uses=1]
  %2 = add i32 %1, 4                              ; <i32> [#uses=1]
  %3 = load i32** @__softboundcetswithss_shadow_stack_ptr, align 4 ; <i32*> [#uses=1]
  %4 = getelementptr inbounds i32* %3, i32 %2     ; <i32*> [#uses=1]
  %5 = load i32* %4, align 4                      ; <i32> [#uses=1]
  ret i32 %5
}

define weak i8* @__softboundcetswithss_load_lock_shadow_stack(i32 %arg_no) nounwind alwaysinline {
entry:
  %0 = icmp slt i32 %arg_no, 0                    ; <i1> [#uses=1]
  br i1 %0, label %bb, label %bb1

bb:                                               ; preds = %entry
  tail call void @__assert_fail(i8* getelementptr inbounds ([12 x i8]* @.str5, i32 0, i32 0), i8* getelementptr inbounds ([34 x i8]* @.str4, i32 0, i32 0), i32 218, i8* getelementptr inbounds ([45 x i8]* @__PRETTY_FUNCTION__.6337, i32 0, i32 0)) noreturn nounwind
  unreachable

bb1:                                              ; preds = %entry
  %1 = shl i32 %arg_no, 2                         ; <i32> [#uses=1]
  %2 = add nsw i32 %1, 5                          ; <i32> [#uses=1]
  %3 = load i32** @__softboundcetswithss_shadow_stack_ptr, align 4 ; <i32*> [#uses=1]
  %4 = getelementptr inbounds i32* %3, i32 %2     ; <i32*> [#uses=1]
  %5 = bitcast i32* %4 to i8**                    ; <i8**> [#uses=1]
  %6 = load i8** %5, align 4                      ; <i8*> [#uses=1]
  ret i8* %6
}

define weak void @__softboundcetswithss_store_base_shadow_stack(i8* %base, i32 %arg_no) nounwind alwaysinline {
entry:
  %0 = icmp slt i32 %arg_no, 0                    ; <i1> [#uses=1]
  br i1 %0, label %bb, label %bb1

bb:                                               ; preds = %entry
  tail call void @__assert_fail(i8* getelementptr inbounds ([12 x i8]* @.str5, i32 0, i32 0), i8* getelementptr inbounds ([34 x i8]* @.str4, i32 0, i32 0), i32 230, i8* getelementptr inbounds ([46 x i8]* @__PRETTY_FUNCTION__.6350, i32 0, i32 0)) noreturn nounwind
  unreachable

bb1:                                              ; preds = %entry
  %1 = shl i32 %arg_no, 2                         ; <i32> [#uses=1]
  %2 = or i32 %1, 2                               ; <i32> [#uses=1]
  %3 = load i32** @__softboundcetswithss_shadow_stack_ptr, align 4 ; <i32*> [#uses=1]
  %4 = getelementptr inbounds i32* %3, i32 %2     ; <i32*> [#uses=1]
  %base.c = ptrtoint i8* %base to i32             ; <i32> [#uses=1]
  store i32 %base.c, i32* %4
  ret void
}

define weak void @__softboundcetswithss_store_bound_shadow_stack(i8* %bound, i32 %arg_no) nounwind alwaysinline {
entry:
  %0 = icmp slt i32 %arg_no, 0                    ; <i1> [#uses=1]
  br i1 %0, label %bb, label %bb1

bb:                                               ; preds = %entry
  tail call void @__assert_fail(i8* getelementptr inbounds ([12 x i8]* @.str5, i32 0, i32 0), i8* getelementptr inbounds ([34 x i8]* @.str4, i32 0, i32 0), i32 243, i8* getelementptr inbounds ([47 x i8]* @__PRETTY_FUNCTION__.6361, i32 0, i32 0)) noreturn nounwind
  unreachable

bb1:                                              ; preds = %entry
  %1 = shl i32 %arg_no, 2                         ; <i32> [#uses=1]
  %2 = or i32 %1, 3                               ; <i32> [#uses=1]
  %3 = load i32** @__softboundcetswithss_shadow_stack_ptr, align 4 ; <i32*> [#uses=1]
  %4 = getelementptr inbounds i32* %3, i32 %2     ; <i32*> [#uses=1]
  %bound.c = ptrtoint i8* %bound to i32           ; <i32> [#uses=1]
  store i32 %bound.c, i32* %4
  ret void
}

define weak void @__softboundcetswithss_store_key_shadow_stack(i32 %key, i32 %arg_no) nounwind alwaysinline {
entry:
  %0 = icmp slt i32 %arg_no, 0                    ; <i1> [#uses=1]
  br i1 %0, label %bb, label %bb1

bb:                                               ; preds = %entry
  tail call void @__assert_fail(i8* getelementptr inbounds ([12 x i8]* @.str5, i32 0, i32 0), i8* getelementptr inbounds ([34 x i8]* @.str4, i32 0, i32 0), i32 254, i8* getelementptr inbounds ([45 x i8]* @__PRETTY_FUNCTION__.6372, i32 0, i32 0)) noreturn nounwind
  unreachable

bb1:                                              ; preds = %entry
  %1 = shl i32 %arg_no, 2                         ; <i32> [#uses=1]
  %2 = add i32 %1, 4                              ; <i32> [#uses=1]
  %3 = load i32** @__softboundcetswithss_shadow_stack_ptr, align 4 ; <i32*> [#uses=1]
  %4 = getelementptr inbounds i32* %3, i32 %2     ; <i32*> [#uses=1]
  store i32 %key, i32* %4, align 4
  ret void
}

define weak void @__softboundcetswithss_store_lock_shadow_stack(i8* %lock, i32 %arg_no) nounwind alwaysinline {
entry:
  %0 = icmp slt i32 %arg_no, 0                    ; <i1> [#uses=1]
  br i1 %0, label %bb, label %bb1

bb:                                               ; preds = %entry
  tail call void @__assert_fail(i8* getelementptr inbounds ([12 x i8]* @.str5, i32 0, i32 0), i8* getelementptr inbounds ([34 x i8]* @.str4, i32 0, i32 0), i32 266, i8* getelementptr inbounds ([46 x i8]* @__PRETTY_FUNCTION__.6382, i32 0, i32 0)) noreturn nounwind
  unreachable

bb1:                                              ; preds = %entry
  %1 = shl i32 %arg_no, 2                         ; <i32> [#uses=1]
  %2 = add nsw i32 %1, 5                          ; <i32> [#uses=1]
  %3 = load i32** @__softboundcetswithss_shadow_stack_ptr, align 4 ; <i32*> [#uses=1]
  %4 = getelementptr inbounds i32* %3, i32 %2     ; <i32*> [#uses=1]
  %lock.c = ptrtoint i8* %lock to i32             ; <i32> [#uses=1]
  store i32 %lock.c, i32* %4
  ret void
}

define weak void @__shrinkBounds(i8* %new_base, i8* %new_bound, i8* %old_base, i8* %old_bound, i8** %base_alloca, i8** %bound_alloca) nounwind alwaysinline {
entry:
  %0 = icmp uge i8* %new_base, %old_base          ; <i1> [#uses=1]
  %max = select i1 %0, i8* %new_base, i8* %old_base ; <i8*> [#uses=1]
  store i8* %max, i8** %base_alloca, align 4
  %1 = icmp ule i8* %new_bound, %old_bound        ; <i1> [#uses=1]
  %min = select i1 %1, i8* %new_bound, i8* %old_bound ; <i8*> [#uses=1]
  store i8* %min, i8** %bound_alloca, align 4
  ret void
}

define weak void @__callDereferenceCheck(i8* %base, i8* %bound, i8* %ptr) nounwind alwaysinline {
entry:
  %0 = icmp ne i8* %base, %bound                  ; <i1> [#uses=1]
  %1 = icmp ne i8* %ptr, %base                    ; <i1> [#uses=1]
  %2 = and i1 %1, %0                              ; <i1> [#uses=1]
  br i1 %2, label %bb, label %return

bb:                                               ; preds = %entry
  tail call void (...)* @__softbound_abort() noreturn nounwind
  unreachable

return:                                           ; preds = %entry
  ret void
}

define weak void @__loadDereferenceCheck(i8* %base, i8* %bound, i8* %ptr, i32 %size_of_type, i32 %ptr_safe) nounwind alwaysinline {
entry:
  %0 = icmp ult i8* %ptr, %base                   ; <i1> [#uses=1]
  br i1 %0, label %bb1, label %bb

bb:                                               ; preds = %entry
  %1 = getelementptr inbounds i8* %ptr, i32 %size_of_type ; <i8*> [#uses=1]
  %2 = icmp ugt i8* %1, %bound                    ; <i1> [#uses=1]
  br i1 %2, label %bb1, label %return

bb1:                                              ; preds = %bb, %entry
  tail call void (...)* @__softbound_abort() noreturn nounwind
  unreachable

return:                                           ; preds = %bb
  ret void
}

define weak void @__storeDereferenceCheck(i8* %base, i8* %bound, i8* %ptr, i32 %size_of_type, i32 %ptr_safe) nounwind alwaysinline {
entry:
  %0 = icmp ult i8* %ptr, %base                   ; <i1> [#uses=1]
  br i1 %0, label %bb1, label %bb

bb:                                               ; preds = %entry
  %1 = getelementptr inbounds i8* %ptr, i32 %size_of_type ; <i8*> [#uses=1]
  %2 = icmp ugt i8* %1, %bound                    ; <i1> [#uses=1]
  br i1 %2, label %bb1, label %return

bb1:                                              ; preds = %bb, %entry
  tail call void (...)* @__softbound_abort() noreturn nounwind
  unreachable

return:                                           ; preds = %bb
  ret void
}

define weak void @__memcopyCheck_i64(i8* %ptr, i8* %ptr_base, i8* %ptr_bound, i32 %size) nounwind alwaysinline {
entry:
  %0 = icmp ugt i32 %size, -2147483648            ; <i1> [#uses=1]
  br i1 %0, label %bb, label %bb1

bb:                                               ; preds = %entry
  tail call void (...)* @__softbound_abort() noreturn nounwind
  unreachable

bb1:                                              ; preds = %entry
  %1 = icmp ult i8* %ptr, %ptr_base               ; <i1> [#uses=1]
  br i1 %1, label %bb6, label %bb2

bb2:                                              ; preds = %bb1
  %2 = getelementptr inbounds i8* %ptr, i32 %size ; <i8*> [#uses=2]
  %3 = icmp ult i8* %2, %ptr_base                 ; <i1> [#uses=1]
  br i1 %3, label %bb6, label %bb3

bb3:                                              ; preds = %bb2
  %4 = icmp ugt i8* %2, %ptr_bound                ; <i1> [#uses=1]
  %5 = inttoptr i32 %size to i8*                  ; <i8*> [#uses=1]
  %6 = icmp ugt i8* %5, %ptr_bound                ; <i1> [#uses=1]
  %7 = or i1 %4, %6                               ; <i1> [#uses=1]
  br i1 %7, label %bb6, label %return

bb6:                                              ; preds = %bb3, %bb2, %bb1
  tail call void (...)* @__softbound_abort() noreturn nounwind
  unreachable

return:                                           ; preds = %bb3
  ret void
}

define weak void @__memcopyCheck(i8* %ptr, i8* %ptr_base, i8* %ptr_bound, i32 %size) nounwind alwaysinline {
entry:
  %0 = icmp ugt i32 %size, -2147483648            ; <i1> [#uses=1]
  br i1 %0, label %bb, label %bb1

bb:                                               ; preds = %entry
  tail call void (...)* @__softbound_abort() noreturn nounwind
  unreachable

bb1:                                              ; preds = %entry
  %1 = icmp ult i8* %ptr, %ptr_base               ; <i1> [#uses=1]
  br i1 %1, label %bb6, label %bb2

bb2:                                              ; preds = %bb1
  %2 = getelementptr inbounds i8* %ptr, i32 %size ; <i8*> [#uses=2]
  %3 = icmp ult i8* %2, %ptr_base                 ; <i1> [#uses=1]
  br i1 %3, label %bb6, label %bb3

bb3:                                              ; preds = %bb2
  %4 = icmp ugt i8* %2, %ptr_bound                ; <i1> [#uses=1]
  %5 = inttoptr i32 %size to i8*                  ; <i8*> [#uses=1]
  %6 = icmp ugt i8* %5, %ptr_bound                ; <i1> [#uses=1]
  %7 = or i1 %4, %6                               ; <i1> [#uses=1]
  br i1 %7, label %bb6, label %return

bb6:                                              ; preds = %bb3, %bb2, %bb1
  tail call void (...)* @__softbound_abort() noreturn nounwind
  unreachable

return:                                           ; preds = %bb3
  ret void
}

define weak void @__hashStoreBaseBound(i8* %addr_of_ptr, i8* %base, i8* %bound, i8* %actual_ptr, i32 %size_of_type, i32 %ptr_safe) nounwind alwaysinline {
entry:
  %0 = ptrtoint i8* %addr_of_ptr to i32           ; <i32> [#uses=1]
  %1 = lshr i32 %0, 2                             ; <i32> [#uses=1]
  %2 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4 ; <%struct.PtrBaseBound*> [#uses=3]
  br label %bb

bb:                                               ; preds = %bb8, %entry
  %3 = phi i32 [ 0, %entry ], [ %13, %bb8 ]       ; <i32> [#uses=3]
  %tmp = add i32 %3, %1                           ; <i32> [#uses=1]
  %4 = and i32 %tmp, 134217727                    ; <i32> [#uses=3]
  %5 = getelementptr inbounds %struct.PtrBaseBound* %2, i32 %4, i32 2 ; <i8**> [#uses=2]
  %6 = load i8** %5, align 4                      ; <i8*> [#uses=2]
  %7 = icmp eq i8* %6, %addr_of_ptr               ; <i1> [#uses=1]
  %8 = icmp eq i8* %6, null                       ; <i1> [#uses=1]
  %9 = or i1 %7, %8                               ; <i1> [#uses=1]
  br i1 %9, label %bb3, label %bb6

bb3:                                              ; preds = %bb
  %10 = getelementptr inbounds %struct.PtrBaseBound* %2, i32 %4, i32 0 ; <i8**> [#uses=1]
  store i8* %base, i8** %10, align 4
  %11 = getelementptr inbounds %struct.PtrBaseBound* %2, i32 %4, i32 1 ; <i8**> [#uses=1]
  store i8* %bound, i8** %11, align 4
  store i8* %addr_of_ptr, i8** %5, align 4
  ret void

bb6:                                              ; preds = %bb
  %12 = icmp ugt i32 %3, 134217727                ; <i1> [#uses=1]
  br i1 %12, label %bb7, label %bb8

bb7:                                              ; preds = %bb6
  tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr inbounds ([17 x i8]* @.str2, i32 0, i32 0)) nounwind
  tail call void (...)* @__softbound_abort() noreturn nounwind
  unreachable

bb8:                                              ; preds = %bb6
  %13 = add i32 %3, 1                             ; <i32> [#uses=1]
  br label %bb
}

define weak i32 @__hashProbeAddrOfPtr(i8* %addr_of_ptr, i8** %base, i8** %bound) nounwind alwaysinline {
entry:
  %0 = ptrtoint i8* %addr_of_ptr to i32           ; <i32> [#uses=1]
  %1 = lshr i32 %0, 2                             ; <i32> [#uses=1]
  %2 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4 ; <%struct.PtrBaseBound*> [#uses=3]
  br label %bb

bb:                                               ; preds = %bb6, %entry
  %counter.0 = phi i32 [ 0, %entry ], [ %16, %bb6 ] ; <i32> [#uses=2]
  %tmp = add i32 %counter.0, %1                   ; <i32> [#uses=1]
  %3 = and i32 %tmp, 134217727                    ; <i32> [#uses=3]
  %4 = getelementptr inbounds %struct.PtrBaseBound* %2, i32 %3, i32 2 ; <i8**> [#uses=1]
  %5 = load i8** %4, align 4                      ; <i8*> [#uses=2]
  %6 = icmp eq i8* %5, %addr_of_ptr               ; <i1> [#uses=1]
  br i1 %6, label %bb1, label %bb4

bb1:                                              ; preds = %bb
  %7 = getelementptr inbounds %struct.PtrBaseBound* %2, i32 %3, i32 0 ; <i8**> [#uses=1]
  %8 = load i8** %7, align 4                      ; <i8*> [#uses=2]
  %9 = getelementptr inbounds %struct.PtrBaseBound* %2, i32 %3, i32 1 ; <i8**> [#uses=1]
  %10 = load i8** %9, align 4                     ; <i8*> [#uses=2]
  store i8* %8, i8** %base, align 4
  store i8* %10, i8** %bound, align 4
  %11 = ptrtoint i8* %8 to i32                    ; <i32> [#uses=1]
  %12 = ptrtoint i8* %10 to i32                   ; <i32> [#uses=1]
  %13 = or i32 %12, %11                           ; <i32> [#uses=1]
  %14 = inttoptr i32 %13 to i8*                   ; <i8*> [#uses=1]
  %not. = icmp ne i8* %14, null                   ; <i1> [#uses=1]
  %retval = zext i1 %not. to i32                  ; <i32> [#uses=1]
  ret i32 %retval

bb4:                                              ; preds = %bb
  %15 = icmp eq i8* %5, null                      ; <i1> [#uses=1]
  br i1 %15, label %bb7, label %bb6

bb6:                                              ; preds = %bb4
  %16 = add i32 %counter.0, 1                     ; <i32> [#uses=1]
  br label %bb

bb7:                                              ; preds = %bb4
  ret i32 0
}

define weak void @__hashLoadBaseBound(i8* %addr_of_ptr, i8** %base, i8** %bound, i8* %actual_ptr, i32 %size_of_type, i32* %ptr_safe) nounwind alwaysinline {
entry:
  %0 = ptrtoint i8* %addr_of_ptr to i32           ; <i32> [#uses=1]
  %1 = lshr i32 %0, 2                             ; <i32> [#uses=1]
  %2 = load %struct.PtrBaseBound** @__softbound_hash_table_begin, align 4 ; <%struct.PtrBaseBound*> [#uses=3]
  br label %bb

bb:                                               ; preds = %bb2, %entry
  %counter.0 = phi i32 [ 0, %entry ], [ %tmp, %bb2 ] ; <i32> [#uses=2]
  %tmp = add i32 %counter.0, 1                    ; <i32> [#uses=2]
  %tmp17 = add i32 %counter.0, %1                 ; <i32> [#uses=1]
  %3 = and i32 %tmp17, 134217727                  ; <i32> [#uses=3]
  %4 = getelementptr inbounds %struct.PtrBaseBound* %2, i32 %3, i32 2 ; <i8**> [#uses=1]
  %5 = load i8** %4, align 4                      ; <i8*> [#uses=2]
  %6 = icmp eq i8* %5, %addr_of_ptr               ; <i1> [#uses=1]
  br i1 %6, label %bb1, label %bb2

bb1:                                              ; preds = %bb
  %7 = getelementptr inbounds %struct.PtrBaseBound* %2, i32 %3, i32 0 ; <i8**> [#uses=1]
  %8 = load i8** %7, align 4                      ; <i8*> [#uses=1]
  %9 = getelementptr inbounds %struct.PtrBaseBound* %2, i32 %3, i32 1 ; <i8**> [#uses=1]
  %10 = load i8** %9, align 4                     ; <i8*> [#uses=1]
  br label %bb4

bb2:                                              ; preds = %bb
  %11 = icmp eq i8* %5, null                      ; <i1> [#uses=1]
  br i1 %11, label %bb4, label %bb

bb4:                                              ; preds = %bb2, %bb1
  %final_bound.0 = phi i8* [ %10, %bb1 ], [ null, %bb2 ] ; <i8*> [#uses=1]
  %final_base.0 = phi i8* [ %8, %bb1 ], [ null, %bb2 ] ; <i8*> [#uses=1]
  store i8* %final_base.0, i8** %base, align 4
  store i8* %final_bound.0, i8** %bound, align 4
  %12 = icmp ugt i32 %tmp, 134217727              ; <i1> [#uses=1]
  br i1 %12, label %bb5, label %return

bb5:                                              ; preds = %bb4
  tail call void (...)* @__softbound_abort() noreturn nounwind
  unreachable

return:                                           ; preds = %bb4
  ret void
}

define weak i32 @softbound_system(i8* %ptr, i8* %ptr_base, i8* %ptr_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @system(i8* %ptr) nounwind   ; <i32> [#uses=1]
  ret i32 %0
}

define weak i32 @softbound_setreuid(i32 %ruid, i32 %euid) nounwind alwaysinline {
entry:
  %0 = tail call i32 @setreuid(i32 %ruid, i32 %euid) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

define weak i32 @softbound_mkstemp(i8* %template, i8* %template_base, i8* %template_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @mkstemp(i8* %template) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

define weak i32 @softbound_getuid() nounwind alwaysinline {
entry:
  %0 = tail call i32 @getuid() nounwind           ; <i32> [#uses=1]
  ret i32 %0
}

define weak i32 @softbound_getrlimit(i32 %resource, %struct.rlimit* %rlim, i8* %rlim_base, i8* %rlim_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @getrlimit(i32 %resource, %struct.rlimit* %rlim) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

define weak i32 @softbound_setrlimit(i32 %resource, %struct.rlimit* %rlim, i8* %rlim_base, i8* %rlim_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @setrlimit(i32 %resource, %struct.rlimit* %rlim) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

define weak void @softbound_qsort(i8* %base, i32 %nmemb, i32 %size, i32 (i8*, i8*)* %compar, i8* %base_base, i8* %base_bound, i8* %compar_base, i8* %compar_bound) nounwind alwaysinline {
entry:
  tail call void @qsort(i8* %base, i32 %nmemb, i32 %size, i32 (i8*, i8*)* %compar) nounwind
  ret void
}

define weak i32 @softbound_fread(i8* %ptr, i32 %size, i32 %nmemb, %struct.FILE* %stream, i8* %ptr_base, i8* %ptr_bound, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @fread(i8* noalias %ptr, i32 %size, i32 %nmemb, %struct.FILE* noalias %stream) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

define weak i32 @softbound_umask(i32 %mask) nounwind alwaysinline {
entry:
  %0 = tail call i32 @umask(i32 %mask) nounwind   ; <i32> [#uses=1]
  ret i32 %0
}

define weak i32 @softbound_mkdir(i8* %pathname, i32 %mode, i8* %pathname_base, i8* %pathname_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @mkdir(i8* %pathname, i32 %mode) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

define weak i32 @softbound_chroot(i8* %path, i8* %path_base, i8* %path_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @chroot(i8* %path) nounwind  ; <i32> [#uses=1]
  ret i32 %0
}

define weak i32 @softbound_rmdir(i8* %pathname, i8* %pathname_base, i8* %pathname_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @rmdir(i8* %pathname) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

define weak i32 @softbound_stat(i8* %path, %struct.stat* %buf, i8* %path_base, i8* %path_bound, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @__xstat(i32 3, i8* %path, %struct.stat* %buf) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

define weak i32 @softbound_fputc(i32 %c, %struct.FILE* %stream, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @fputc(i32 %c, %struct.FILE* %stream) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

define weak i32 @softbound_fileno(%struct.FILE* %stream, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @fileno(%struct.FILE* %stream) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

define weak i32 @softbound_fgetc(%struct.FILE* %stream, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @fgetc(%struct.FILE* %stream) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

define weak i32 @softbound_strncmp(i8* %s1, i8* %s2, i32 %n, i8* %s1_base, i8* %s1_bound, i8* %s2_base, i8* %s2_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @strncmp(i8* %s1, i8* %s2, i32 %n) nounwind readonly ; <i32> [#uses=1]
  ret i32 %0
}

define weak double @softbound_log(double %x) nounwind alwaysinline {
entry:
  %0 = tail call double @llvm.log.f64(double %x)  ; <double> [#uses=1]
  ret double %0
}

define i64 @softbound_fwrite(i8* nocapture %ptr, i32 %size, i32 %nmemb, %struct.FILE* nocapture %stream, i8* nocapture %ptr_base, i8* nocapture %ptr_bound, i8* nocapture %stream_base, i8* nocapture %stream_bound) nounwind {
entry:
  %0 = tail call i32 @fwrite(i8* noalias %ptr, i32 %size, i32 %nmemb, %struct.FILE* noalias %stream) nounwind ; <i32> [#uses=1]
  %1 = zext i32 %0 to i64                         ; <i64> [#uses=1]
  ret i64 %1
}

define weak double @softbound_fabs(double %x) nounwind alwaysinline {
entry:
  %0 = tail call double @fabs(double %x) nounwind readnone ; <double> [#uses=1]
  ret double %0
}

declare double @fabs(double)

define weak float @softbound_fabsf(float %x) nounwind alwaysinline {
entry:
  %0 = tail call float @fabsf(float %x) nounwind readnone ; <float> [#uses=1]
  ret float %0
}

declare float @fabsf(float)

define weak void @softbound_bcopy(i8* %src, i8* %dest, i32 %n, i8* %src_base, i8* %src_bound, i8* %dest_base, i8* %dest_bound) nounwind alwaysinline {
entry:
  tail call void @bcopy(i8* %src, i8* %dest, i32 %n) nounwind
  ret void
}

declare void @bcopy(i8* nocapture, i8* nocapture, i32) nounwind

define weak i32 @softbound_strlen(i8* %s, i8* %base, i8* %bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @strlen(i8* %s) nounwind readonly ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @strlen(i8* nocapture) nounwind readonly

define void @softbound_globfree(%struct.glob_t* %pglob, i8* nocapture %pglob_base, i8* nocapture %pglob_bound) nounwind {
entry:
  tail call void @globfree(%struct.glob_t* %pglob) nounwind
  ret void
}

declare void @globfree(%struct.glob_t*) nounwind

define weak void @softbound_my_mmap(%struct.PtrBaseBound* %ptrs, i8* %start, i32 %length, i32 %prot, i32 %flags, i32 %fd, i32 %offset, i8* %start_base, i8* %start_bound) nounwind alwaysinline {
entry:
  %0 = tail call i8* @mmap(i8* %start, i32 %length, i32 %prot, i32 %flags, i32 %fd, i32 %offset) nounwind ; <i8*> [#uses=4]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = icmp eq i8* %0, null                       ; <i1> [#uses=1]
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=2]
  br i1 %2, label %bb1, label %bb

bb:                                               ; preds = %entry
  store i8* %0, i8** %3, align 4
  %4 = getelementptr inbounds i8* %0, i32 %length ; <i8*> [#uses=1]
  %5 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %4, i8** %5, align 4
  ret void

bb1:                                              ; preds = %entry
  store i8* null, i8** %3, align 4
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* null, i8** %6, align 4
  ret void
}

declare i8* @mmap(i8*, i32, i32, i32, i32, i32) nounwind

declare i32 @vfprintf(%struct.FILE* noalias nocapture, i8* noalias nocapture, i8*) nounwind

define weak i32 @softbound_vprintf(i8* %format, i8* %ap, i8* %format_base, i8* %format_bound, i8* %ap_base, i8* %ap_bound) nounwind alwaysinline {
entry:
  %0 = load %struct.FILE** @stdout, align 4       ; <%struct.FILE*> [#uses=1]
  %1 = tail call i32 @vfprintf(%struct.FILE* noalias %0, i8* noalias %format, i8* %ap) nounwind ; <i32> [#uses=1]
  ret i32 %1
}

define weak void @softbound_crypt(%struct.PtrBaseBound* %ptrs, i8* %key, i8* %salt, i8* %key_base, i8* %key_bound, i8* %salt_base, i8* %salt_bound) nounwind alwaysinline {
entry:
  %0 = tail call i8* @crypt(i8* %key, i8* %salt) nounwind ; <i8*> [#uses=4]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %0, i8** %2, align 4
  %3 = tail call i32 @strlen(i8* %0) nounwind readonly ; <i32> [#uses=1]
  %.sum = add i32 %3, 1                           ; <i32> [#uses=1]
  %4 = getelementptr inbounds i8* %0, i32 %.sum   ; <i8*> [#uses=1]
  %5 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %4, i8** %5, align 4
  ret void
}

declare i8* @crypt(i8*, i8*)

define weak i32 @softbound_usleep(i32 %usec) nounwind alwaysinline {
entry:
  %0 = tail call i32 @usleep(i32 %usec) nounwind  ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @usleep(i32)

define weak i32 @softbound_strftime(i8* %s, i32 %max, i8* %format, %struct.tm* %tm, i8* %s_base, i8* %s_bound, i8* %format_base, i8* %format_bound, i8* %tm_base, i8* %tm_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @strftime(i8* noalias %s, i32 %max, i8* noalias %format, %struct.tm* noalias %tm) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @strftime(i8* noalias, i32, i8* noalias, %struct.tm* noalias) nounwind

define weak i32 @softbound_select(i32 %nfds, %struct.fd_set* %readfds, %struct.fd_set* %writefds, %struct.fd_set* %exceptfds, %struct.rlimit* %timeout, i8* %readfds_base, i8* %readfds_bound, i8* %writefds_base, i8* %writefds_bound, i8* %exceptfds_base, i8* %exceptfds_bound, i8* %timeout_base, i8* %timeout_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @select(i32 %nfds, %struct.fd_set* noalias %readfds, %struct.fd_set* noalias %writefds, %struct.fd_set* noalias %exceptfds, %struct.rlimit* noalias %timeout) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @select(i32, %struct.fd_set* noalias, %struct.fd_set* noalias, %struct.fd_set* noalias, %struct.rlimit* noalias)

define weak i32 @softbound_alphasort(i8* %a, i8* %b, i8* %a_base, i8* %a_bound, i8* %b_base, i8* %b_bound) nounwind alwaysinline {
entry:
  %0 = bitcast i8* %b to %struct.dirent**         ; <%struct.dirent**> [#uses=1]
  %1 = bitcast i8* %a to %struct.dirent**         ; <%struct.dirent**> [#uses=1]
  %2 = tail call i32 @alphasort(%struct.dirent** %1, %struct.dirent** %0) nounwind readonly ; <i32> [#uses=1]
  ret i32 %2
}

declare i32 @alphasort(%struct.dirent**, %struct.dirent**) nounwind readonly

define weak i32 @softbound_getnameinfo(%struct.sockaddr* %sa, i32 %salen, i8* %host, i32 %hostlen, i8* %serv, i32 %servlen, i32 %flags, i8* %sa_base, i8* %sa_bound, i8* %host_base, i8* %host_bound, i8* %serv_base, i8* %serv_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @getnameinfo(%struct.sockaddr* noalias %sa, i32 %salen, i8* noalias %host, i32 %hostlen, i8* noalias %serv, i32 %servlen, i32 %flags) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @getnameinfo(%struct.sockaddr* noalias, i32, i8* noalias, i32, i8* noalias, i32, i32)

define weak i32 @softbound_fchmod(i32 %fildes, i32 %mode) nounwind alwaysinline {
entry:
  %0 = tail call i32 @fchmod(i32 %fildes, i32 %mode) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @fchmod(i32, i32) nounwind

define weak i32 @softbound_setsockopt(i32 %s, i32 %level, i32 %optname, i8* %optval, i32 %optlen, i8* %optval_base, i8* %optval_bound, i8* %optlen_base, i8* %optlen_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @setsockopt(i32 %s, i32 %level, i32 %optname, i8* %optval, i32 %optlen) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @setsockopt(i32, i32, i32, i8*, i32) nounwind

define weak i32 @softbound_munmap(i8* %start, i32 %length, i8* %start_base, i8* %start_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @munmap(i8* %start, i32 %length) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @munmap(i8*, i32) nounwind

define weak i32 @softbound_alarm(i32 %seconds) nounwind alwaysinline {
entry:
  %0 = tail call i32 @alarm(i32 %seconds) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @alarm(i32) nounwind

define weak void @softbound_realpath(%struct.PtrBaseBound* %ptrs, i8* %path, i8* %resolved_path, i8* %path_base, i8* %path_bound, i8* %resolved_path_base, i8* %resolved_path_bound) nounwind alwaysinline {
entry:
  %0 = tail call i8* @realpath(i8* noalias %path, i8* noalias %resolved_path) nounwind ; <i8*> [#uses=1]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %resolved_path_base, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %resolved_path_bound, i8** %3, align 4
  ret void
}

declare i8* @realpath(i8* noalias nocapture, i8* noalias) nounwind

define weak i32 @softbound_getdtablesize() nounwind alwaysinline {
entry:
  %0 = tail call i32 @getdtablesize() nounwind    ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @getdtablesize() nounwind

define weak void @softbound_getusershell(%struct.PtrBaseBound* %ptrs) nounwind alwaysinline {
entry:
  %0 = tail call i8* @getusershell() nounwind     ; <i8*> [#uses=5]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = icmp eq i8* %0, null                       ; <i1> [#uses=1]
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=2]
  br i1 %2, label %bb1, label %bb

bb:                                               ; preds = %entry
  store i8* %0, i8** %3, align 4
  %4 = tail call i32 @strlen(i8* %0) nounwind readonly ; <i32> [#uses=1]
  %.sum = add i32 %4, 1                           ; <i32> [#uses=1]
  %5 = getelementptr inbounds i8* %0, i32 %.sum   ; <i8*> [#uses=1]
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %5, i8** %6, align 4
  ret void

bb1:                                              ; preds = %entry
  store i8* null, i8** %3, align 4
  %7 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* null, i8** %7, align 4
  ret void
}

declare i8* @getusershell() nounwind

define weak void @softbound_endusershell() nounwind alwaysinline {
entry:
  tail call void @endusershell() nounwind
  ret void
}

declare void @endusershell() nounwind

define weak void @softbound__exit(i32 %status) nounwind alwaysinline {
entry:
  tail call void @_exit(i32 %status) noreturn nounwind
  unreachable
}

declare void @_exit(i32) noreturn nounwind

define weak i32 @softbound_wait3(i32* %status, i32 %options, %struct.rusage* %rusage, i8* %status_base, i8* %status_bound, i8* %rusage_base, i8* %rusage_bound) nounwind alwaysinline {
entry:
  %tmp2 = bitcast i32* %status to %struct.in_addr* ; <%struct.in_addr*> [#uses=1]
  %0 = tail call i32 @wait3(%struct.in_addr* %tmp2, i32 %options, %struct.rusage* %rusage) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @wait3(%struct.in_addr*, i32, %struct.rusage*) nounwind

define weak i32 @softbound_recv(i32 %s, i8* %buf, i32 %len, i32 %flags, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @recv(i32 %s, i8* %buf, i32 %len, i32 %flags) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @recv(i32, i8*, i32, i32)

define weak i32 @softbound_htonl(i32 %hostlong) nounwind alwaysinline {
entry:
  %asmtmp = tail call i32 asm "rorw $$8, ${0:w};rorl $$16, $0;rorw $$8, ${0:w}", "=r,0,~{dirflag},~{fpsr},~{flags},~{cc}"(i32 %hostlong) nounwind ; <i32> [#uses=1]
  ret i32 %asmtmp
}

define weak zeroext i16 @softbound_htons(i16 zeroext %hostshort) nounwind alwaysinline {
entry:
  %asmtmp2 = tail call i16 @llvm.bswap.i16(i16 %hostshort) ; <i16> [#uses=1]
  ret i16 %asmtmp2
}

declare i16 @llvm.bswap.i16(i16) nounwind readnone

define weak zeroext i16 @softbound_ntohs(i16 zeroext %netshort) nounwind alwaysinline {
entry:
  %asmtmp2 = tail call i16 @llvm.bswap.i16(i16 %netshort) ; <i16> [#uses=1]
  ret i16 %asmtmp2
}

define weak i32 @softbound_accept(i32 %sockfd, %struct.sockaddr* %addr, i32* %addrlen, i8* %addr_base, i8* %addr_bound, i8* %addrlen_base, i8* %addrlen_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @accept(i32 %sockfd, %struct.sockaddr* noalias %addr, i32* noalias %addrlen) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @accept(i32, %struct.sockaddr* noalias, i32* noalias)

define weak i32 @softbound_waitpid(i32 %pid, i32* %status, i32 %options, i8* %status_base, i8* %status_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @waitpid(i32 %pid, i32* %status, i32 %options) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @waitpid(i32, i32*, i32)

define weak i32 @softbound_getpid() nounwind alwaysinline {
entry:
  %0 = tail call i32 @getpid() nounwind           ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @getpid() nounwind

define weak i32 @softbound_listen(i32 %sockfd, i32 %backlog) nounwind alwaysinline {
entry:
  %0 = tail call i32 @listen(i32 %sockfd, i32 %backlog) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @listen(i32, i32) nounwind

define weak void @softbound_closelog() nounwind alwaysinline {
entry:
  tail call void @closelog() nounwind
  ret void
}

declare void @closelog()

define weak i32 @softbound_setenv(i8* %name, i8* %value, i32 %overwrite, i8* %name_base, i8* %name_bound, i8* %value_base, i8* %value_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @setenv(i8* %name, i8* %value, i32 %overwrite) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @setenv(i8*, i8*, i32) nounwind

define weak i32 @softbound_setuid(i32 %uid) nounwind alwaysinline {
entry:
  %0 = tail call i32 @setuid(i32 %uid) nounwind   ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @setuid(i32) nounwind

define weak i32 @softbound_setgid(i32 %gid) nounwind alwaysinline {
entry:
  %0 = tail call i32 @setgid(i32 %gid) nounwind   ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @setgid(i32) nounwind

define weak i32 @softbound_send(i32 %s, i8* %buf, i32 %len, i32 %flags, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @send(i32 %s, i8* %buf, i32 %len, i32 %flags) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @send(i32, i8*, i32, i32)

define weak void @softbound_openlog(i8* %ident, i32 %option, i32 %facility, i8* %ident_base, i8* %ident_bound) nounwind alwaysinline {
entry:
  tail call void @openlog(i8* %ident, i32 %option, i32 %facility) nounwind
  ret void
}

declare void @openlog(i8*, i32, i32)

define weak i32 @softbound_lseek(i32 %fildes, i32 %offset, i32 %whence) nounwind alwaysinline {
entry:
  %0 = tail call i32 @lseek(i32 %fildes, i32 %offset, i32 %whence) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @lseek(i32, i32, i32) nounwind

define weak i32 @softbound_write(i32 %fd, i8* %buf, i32 %count, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @write(i32 %fd, i8* %buf, i32 %count) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @write(i32, i8* nocapture, i32)

define weak i32 @softbound_read(i32 %fd, i8* %buf, i32 %count, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @read(i32 %fd, i8* %buf, i32 %count) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @read(i32, i8* nocapture, i32)

define weak i32 @softbound_open(i8* %pathname, i32 %flags, i8* %pathname_base, i8* %pathname_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 (i8*, i32, ...)* @open(i8* %pathname, i32 %flags) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @open(i8* nocapture, i32, ...)

define weak i32 @softbound_close(i32 %fd) nounwind alwaysinline {
entry:
  %0 = tail call i32 @close(i32 %fd) nounwind     ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @close(i32)

define weak i32 @softbound_unlink(i8* %pathname, i8* %pathname_base, i8* %pathname_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @unlink(i8* %pathname) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @unlink(i8* nocapture) nounwind

define weak i32 @softbound_connect(i32 %sockfd, %struct.sockaddr* %serv_addr, i32 %addrlen, i8* %serv_addr_base, i8* %serv_addr_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @connect(i32 %sockfd, %struct.sockaddr* %serv_addr, i32 %addrlen) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @connect(i32, %struct.sockaddr*, i32)

define weak i32 @softbound_bind(i32 %sockfd, %struct.sockaddr* %my_addr, i32 %addrlen, i8* %my_addr_base, i8* %my_addr_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @bind(i32 %sockfd, %struct.sockaddr* %my_addr, i32 %addrlen) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @bind(i32, %struct.sockaddr*, i32) nounwind

define weak i32 @softbound_socket(i32 %domain, i32 %type, i32 %protocol) nounwind alwaysinline {
entry:
  %0 = tail call i32 @socket(i32 %domain, i32 %type, i32 %protocol) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @socket(i32, i32, i32) nounwind

define weak void @softbound_inet_ntoa(%struct.PtrBaseBound* %ptrs, i32 %in.0) nounwind alwaysinline {
entry:
  %0 = tail call i8* @inet_ntoa(i32 %in.0) nounwind ; <i8*> [#uses=4]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %0, i8** %2, align 4
  %3 = tail call i32 @strlen(i8* %0) nounwind readonly ; <i32> [#uses=1]
  %.sum = add i32 %3, 1                           ; <i32> [#uses=1]
  %4 = getelementptr inbounds i8* %0, i32 %.sum   ; <i8*> [#uses=1]
  %5 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %4, i8** %5, align 4
  ret void
}

declare i8* @inet_ntoa(i32) nounwind

define weak i32 @softbound_getsockname(i32 %s, %struct.sockaddr* %name, i32* %namelen, i8* %name_base, i8* %name_bound, i8* %namelen_base, i8* %namelen_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @getsockname(i32 %s, %struct.sockaddr* noalias %name, i32* noalias %namelen) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @getsockname(i32, %struct.sockaddr* noalias, i32* noalias) nounwind

define weak i32 @softbound_getpeername(i32 %s, %struct.sockaddr* %name, i32* %namelen, i8* %name_base, i8* %name_bound, i8* %namelen_base, i8* %namelen_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @getpeername(i32 %s, %struct.sockaddr* noalias %name, i32* noalias %namelen) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @getpeername(i32, %struct.sockaddr* noalias, i32* noalias) nounwind

define weak i32 @softbound_inet_addr(i8* %cp, i8* %cp_base, i8* %cp_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @inet_addr(i8* %cp) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @inet_addr(i8*) nounwind

define weak void @softbound_strerror(%struct.PtrBaseBound* %ptrs, i32 %errnum) nounwind alwaysinline {
entry:
  %0 = tail call i8* @strerror(i32 %errnum) nounwind ; <i8*> [#uses=4]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %0, i8** %2, align 4
  %3 = tail call i32 @strlen(i8* %0) nounwind readonly ; <i32> [#uses=1]
  %.sum = add i32 %3, 1                           ; <i32> [#uses=1]
  %4 = getelementptr inbounds i8* %0, i32 %.sum   ; <i8*> [#uses=1]
  %5 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %4, i8** %5, align 4
  ret void
}

declare i8* @strerror(i32) nounwind

define weak void @softbound___ctype_tolower_loc(%struct.PtrBaseBound* %ptrs) nounwind alwaysinline {
entry:
  %0 = tail call i32** @__ctype_tolower_loc() nounwind readnone ; <i32**> [#uses=2]
  %1 = bitcast i32** %0 to i8*                    ; <i8*> [#uses=2]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %1, i8** %3, align 4
  %4 = getelementptr inbounds i32** %0, i32 1     ; <i32**> [#uses=1]
  %5 = bitcast i32** %4 to i8*                    ; <i8*> [#uses=1]
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %5, i8** %6, align 4
  ret void
}

declare i32** @__ctype_tolower_loc() nounwind readnone

define weak i32 @softbound_tolower(i32 %c) nounwind alwaysinline {
entry:
  %0 = add i32 %c, 128                            ; <i32> [#uses=1]
  %1 = icmp ugt i32 %0, 383                       ; <i1> [#uses=1]
  br i1 %1, label %tolower.exit, label %bb.i

bb.i:                                             ; preds = %entry
  %2 = tail call i32** @__ctype_tolower_loc() nounwind readnone ; <i32**> [#uses=1]
  %3 = load i32** %2, align 4                     ; <i32*> [#uses=1]
  %4 = getelementptr inbounds i32* %3, i32 %c     ; <i32*> [#uses=1]
  %5 = load i32* %4, align 4                      ; <i32> [#uses=1]
  ret i32 %5

tolower.exit:                                     ; preds = %entry
  ret i32 %c
}

declare i32** @__ctype_toupper_loc() nounwind readnone

define weak i32 @softbound_toupper(i32 %c) nounwind alwaysinline {
entry:
  %0 = add i32 %c, 128                            ; <i32> [#uses=1]
  %1 = icmp ugt i32 %0, 383                       ; <i1> [#uses=1]
  br i1 %1, label %toupper.exit, label %bb.i

bb.i:                                             ; preds = %entry
  %2 = tail call i32** @__ctype_toupper_loc() nounwind readnone ; <i32**> [#uses=1]
  %3 = load i32** %2, align 4                     ; <i32*> [#uses=1]
  %4 = getelementptr inbounds i32* %3, i32 %c     ; <i32*> [#uses=1]
  %5 = load i32* %4, align 4                      ; <i32> [#uses=1]
  ret i32 %5

toupper.exit:                                     ; preds = %entry
  ret i32 %c
}

define weak void @softbound___ctype_toupper_loc(%struct.PtrBaseBound* %ptrs) nounwind alwaysinline {
entry:
  %0 = tail call i32** @__ctype_toupper_loc() nounwind readnone ; <i32**> [#uses=3]
  %1 = bitcast i32** %0 to i8*                    ; <i8*> [#uses=1]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=2]
  store i8* %1, i8** %2, align 4
  %3 = load i32** %0                              ; <i32*> [#uses=1]
  %4 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr inbounds ([50 x i8]* @.str, i32 0, i32 0), i32** %0, i32* %3) nounwind ; <i32> [#uses=0]
  %5 = load i8** %2, align 4                      ; <i8*> [#uses=2]
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %5, i8** %6, align 4
  %7 = getelementptr inbounds i8* %5, i32 4       ; <i8*> [#uses=1]
  %8 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %7, i8** %8, align 4
  ret void
}

declare i32 @printf(i8* nocapture, ...) nounwind

define weak void @softbound___ctype_b_loc(%struct.PtrBaseBound* %ptrs) nounwind alwaysinline {
entry:
  %0 = tail call i16** @__ctype_b_loc() nounwind readnone ; <i16**> [#uses=2]
  %1 = bitcast i16** %0 to i8*                    ; <i8*> [#uses=2]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %1, i8** %3, align 4
  %4 = getelementptr inbounds i16** %0, i32 1     ; <i16**> [#uses=1]
  %5 = bitcast i16** %4 to i8*                    ; <i8*> [#uses=1]
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %5, i8** %6, align 4
  ret void
}

declare i16** @__ctype_b_loc() nounwind readnone

define weak void @softbound___errno_location(%struct.PtrBaseBound* %ptrs) nounwind alwaysinline {
entry:
  %0 = tail call i32* @__errno_location() nounwind readnone ; <i32*> [#uses=2]
  %1 = bitcast i32* %0 to i8*                     ; <i8*> [#uses=2]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %1, i8** %3, align 4
  %4 = getelementptr inbounds i32* %0, i32 1      ; <i32*> [#uses=1]
  %5 = bitcast i32* %4 to i8*                     ; <i8*> [#uses=1]
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %5, i8** %6, align 4
  ret void
}

declare i32* @__errno_location() nounwind readnone

define weak i32 @softbound_atexit(void ()* %function, i8* %function_base, i8* %function_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @atexit(void ()* %function) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @atexit(void ()*) nounwind

declare i32 @__lxstat(i32, i8*, %struct.stat*) nounwind

define weak i32 @softbound_lstat(i8* %path, %struct.stat* %buf, i8* %path_base, i8* %path_bound, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @__lxstat(i32 3, i8* %path, %struct.stat* %buf) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

define weak i32 @softbound_chmod(i8* %path, i32 %mode, i8* %path_base, i8* %path_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @chmod(i8* %path, i32 %mode) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @chmod(i8* nocapture, i32) nounwind

define weak i32 @softbound_getopt_long(i32 %argc, i8** %argv, i8* %optstring, %struct.option* %longopts, i32* %longindex, i8* %argv_base, i8* %argv_bound, i8* %optstring_base, i8* %optstring_bound, i8* %longopts_base, i8* %longopts_bound, i8* %longindex_base, i8* %longindex_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @getopt_long(i32 %argc, i8** %argv, i8* %optstring, %struct.option* %longopts, i32* %longindex) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @getopt_long(i32, i8**, i8*, %struct.option*, i32*) nounwind

define weak i32 @softbound_getopt(i32 %argc, i8** %argv, i8* %optstring, i8* %argv_base, i8* %argv_bound, i8* %optstring_base, i8* %optstring_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @getopt(i32 %argc, i8** %argv, i8* %optstring) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @getopt(i32, i8**, i8*) nounwind

define weak void @softbound_getenv(%struct.PtrBaseBound* %ptrs, i8* %name, i8* %name_base, i8* %name_bound) nounwind alwaysinline {
entry:
  %0 = tail call i8* @getenv(i8* %name) nounwind  ; <i8*> [#uses=5]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = icmp eq i8* %0, null                       ; <i1> [#uses=1]
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=2]
  br i1 %2, label %bb1, label %bb

bb:                                               ; preds = %entry
  store i8* %0, i8** %3, align 4
  %4 = tail call i32 @strlen(i8* %0) nounwind readonly ; <i32> [#uses=1]
  %.sum = add i32 %4, 1                           ; <i32> [#uses=1]
  %5 = getelementptr inbounds i8* %0, i32 %.sum   ; <i8*> [#uses=1]
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %5, i8** %6, align 4
  ret void

bb1:                                              ; preds = %entry
  store i8* null, i8** %3, align 4
  %7 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* null, i8** %7, align 4
  ret void
}

declare i8* @getenv(i8* nocapture) nounwind readonly

define weak void @softbound_setbuf(%struct.FILE* %stream, i8* %buf, i8* %stream_base, i8* %stream_bound, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
  tail call void @setbuf(%struct.FILE* noalias %stream, i8* noalias %buf) nounwind
  ret void
}

declare void @setbuf(%struct.FILE* noalias nocapture, i8* noalias) nounwind

define weak double @softbound_difftime(i32 %time1, i32 %time0) nounwind alwaysinline {
entry:
  %0 = tail call double @difftime(i32 %time1, i32 %time0) nounwind readnone ; <double> [#uses=1]
  ret double %0
}

declare double @difftime(i32, i32) nounwind readnone

define weak void @softbound_ctime(%struct.PtrBaseBound* %ptrs, i32* %timep, i8* %timep_base, i8* %timep_bound) nounwind alwaysinline {
entry:
  %0 = tail call i8* @ctime(i32* %timep) nounwind ; <i8*> [#uses=4]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %0, i8** %2, align 4
  %3 = tail call i32 @strlen(i8* %0) nounwind readonly ; <i32> [#uses=1]
  %.sum = add i32 %3, 1                           ; <i32> [#uses=1]
  %4 = getelementptr inbounds i8* %0, i32 %.sum   ; <i8*> [#uses=1]
  %5 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %4, i8** %5, align 4
  ret void
}

declare i8* @ctime(i32*) nounwind

define weak i32 @softbound_utime(i8* %filename, %struct.rlimit* %buf, i8* %filename_base, i8* %filename_bound, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @utime(i8* %filename, %struct.rlimit* %buf) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @utime(i8* nocapture, %struct.rlimit* nocapture) nounwind

define weak i32 @softbound_lrand48() nounwind alwaysinline {
entry:
  %0 = tail call i32 @lrand48() nounwind          ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @lrand48() nounwind

define weak void @softbound_free(i8* %ptr, i8* %ptr_base, i8* %ptr_bound) nounwind alwaysinline {
entry:
  free i8* %ptr
  ret void
}

define weak double @softbound_drand48() nounwind alwaysinline {
entry:
  %0 = tail call double @drand48() nounwind       ; <double> [#uses=1]
  ret double %0
}

declare double @drand48() nounwind

define weak i32 @softbound_time(i32* %t, i8* %t_base, i8* %t_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @time(i32* %t) nounwind      ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @time(i32*) nounwind

define weak void @softbound_localtime(%struct.PtrBaseBound* %ptrs, i32* %timep, i8* %timep_base, i8* %timep_bound) nounwind alwaysinline {
entry:
  %0 = tail call %struct.tm* @localtime(i32* %timep) nounwind ; <%struct.tm*> [#uses=2]
  %1 = bitcast %struct.tm* %0 to i8*              ; <i8*> [#uses=2]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %1, i8** %3, align 4
  %4 = getelementptr inbounds %struct.tm* %0, i32 1 ; <%struct.tm*> [#uses=1]
  %5 = bitcast %struct.tm* %4 to i8*              ; <i8*> [#uses=1]
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %5, i8** %6, align 4
  ret void
}

declare %struct.tm* @localtime(i32*) nounwind

define weak void @softbound_gmtime(%struct.PtrBaseBound* %ptrs, i32* %timep, i8* %timep_base, i8* %timep_bound) nounwind alwaysinline {
entry:
  %0 = tail call %struct.tm* @gmtime(i32* %timep) nounwind ; <%struct.tm*> [#uses=2]
  %1 = bitcast %struct.tm* %0 to i8*              ; <i8*> [#uses=2]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %1, i8** %3, align 4
  %4 = getelementptr inbounds %struct.tm* %0, i32 1 ; <%struct.tm*> [#uses=1]
  %5 = bitcast %struct.tm* %4 to i8*              ; <i8*> [#uses=1]
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %5, i8** %6, align 4
  ret void
}

declare %struct.tm* @gmtime(i32*) nounwind

define weak i32 @softbound_times(%struct.tms* %buf, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @times(%struct.tms* %buf) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @times(%struct.tms* nocapture) nounwind

declare i32 @_IO_putc(i32, %struct.FILE* nocapture) nounwind

define weak i32 @softbound_putchar(i32 %c) nounwind alwaysinline {
entry:
  %0 = load %struct.FILE** @stdout, align 4       ; <%struct.FILE*> [#uses=1]
  %1 = tail call i32 @_IO_putc(i32 %c, %struct.FILE* %0) nounwind ; <i32> [#uses=1]
  ret i32 %1
}

define weak i32 @softbound_strcmp(i8* %s1, i8* %s2, i8* %s1_base, i8* %s1_bound, i8* %s2_base, i8* %s2_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @strcmp(i8* %s1, i8* %s2) nounwind readonly ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @strcmp(i8* nocapture, i8* nocapture) nounwind readonly

declare void @__softbound_abort(...) noreturn

declare i32 @strtol(i8* noalias, i8** noalias nocapture, i32) nounwind

define weak i32 @softbound_atoi(i8* %ptr, i8* %base_ptr, i8* %bound_ptr) nounwind alwaysinline {
entry:
  %0 = icmp eq i8* %ptr, null                     ; <i1> [#uses=1]
  br i1 %0, label %bb, label %bb1

bb:                                               ; preds = %entry
  tail call void (...)* @__softbound_abort() noreturn nounwind
  unreachable

bb1:                                              ; preds = %entry
  %1 = tail call i32 @strtol(i8* noalias nocapture %ptr, i8** noalias null, i32 10) nounwind readonly ; <i32> [#uses=1]
  ret i32 %1
}

define weak i32 @softbound_atol(i8* %nptr, i8* %base, i8* %bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @strtol(i8* noalias nocapture %nptr, i8** noalias null, i32 10) nounwind readonly ; <i32> [#uses=1]
  ret i32 %0
}

define weak void @softbound_puts(i8* %ptr, i8* %ptr_base, i8* %ptr_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @puts(i8* %ptr) nounwind     ; <i32> [#uses=0]
  ret void
}

declare i32 @puts(i8* nocapture) nounwind

define weak i32 @softbound_rand() nounwind alwaysinline {
entry:
  %0 = tail call i32 @rand() nounwind             ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @rand() nounwind

define weak void @softbound_abort() nounwind alwaysinline {
entry:
  tail call void @abort() noreturn nounwind
  unreachable
}

declare void @abort() noreturn nounwind

define weak void @softbound_malloc(%struct.PtrBaseBound* %ptrs, i32 %size) nounwind alwaysinline {
entry:
  %0 = malloc i8, i32 %size                       ; <i8*> [#uses=3]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %0, i8** %2, align 4
  %3 = getelementptr inbounds i8* %0, i32 %size   ; <i8*> [#uses=1]
  %4 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %3, i8** %4, align 4
  ret void
}

define weak void @softbound_realloc(%struct.PtrBaseBound* %ptrs, i8* %ptr, i32 %size, i8* %ptr_base, i8* %ptr_bound) nounwind alwaysinline {
entry:
  %0 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=2]
  store i8* %ptr, i8** %0, align 4
  %1 = tail call i8* @realloc(i8* %ptr, i32 %size) nounwind ; <i8*> [#uses=3]
  store i8* %1, i8** %0, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = getelementptr inbounds i8* %1, i32 %size   ; <i8*> [#uses=1]
  %4 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %3, i8** %4, align 4
  ret void
}

declare noalias i8* @realloc(i8* nocapture, i32) nounwind

define weak void @softbound_calloc(%struct.PtrBaseBound* %ptrs, i32 %nmemb, i32 %size) nounwind alwaysinline {
entry:
  %0 = tail call noalias i8* @calloc(i32 %nmemb, i32 %size) nounwind ; <i8*> [#uses=3]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %0, i8** %2, align 4
  %3 = mul i32 %size, %nmemb                      ; <i32> [#uses=1]
  %4 = getelementptr inbounds i8* %0, i32 %3      ; <i8*> [#uses=1]
  %5 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %4, i8** %5, align 4
  ret void
}

declare noalias i8* @calloc(i32, i32) nounwind

define weak void @softbound_exit(i32 %status) nounwind alwaysinline {
entry:
  tail call void @exit(i32 %status) noreturn nounwind
  unreachable
}

declare void @exit(i32) noreturn nounwind

define weak i32 @softbound_clock() nounwind alwaysinline {
entry:
  %0 = tail call i32 @clock() nounwind            ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @clock() nounwind

define weak i32 @softbound_fclose(%struct.FILE* %fp, i8* %fp_base, i8* %fp_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @fclose(%struct.FILE* %fp) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @fclose(%struct.FILE* nocapture) nounwind

define weak void @softbound_signal(%struct.PtrBaseBound* %ptrs, i32 %signum, void (i32)* %handler, void (i32)* %handler_base, void (i32)* %handler_bound) nounwind alwaysinline {
entry:
  %0 = tail call void (i32)* (i32, void (i32)*)* @signal(i32 %signum, void (i32)* %handler) nounwind ; <void (i32)*> [#uses=1]
  %1 = bitcast void (i32)* %0 to i8*              ; <i8*> [#uses=3]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %1, i8** %3, align 4
  %4 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %1, i8** %4, align 4
  ret void
}

declare void (i32)* @signal(i32, void (i32)*) nounwind

define weak i32 @softbound_gethostname(i8* %name, i32 %len, i8* %name_base, i8* %name_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @gethostname(i8* %name, i32 %len) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @gethostname(i8*, i32) nounwind

define weak i32 @softbound_sigaddset(%struct.fd_set* %set, i32 %signum, i8* %set_base, i8* %set_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @sigaddset(%struct.fd_set* %set, i32 %signum) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @sigaddset(%struct.fd_set*, i32) nounwind

define weak void @softbound_tzset() nounwind alwaysinline {
entry:
  tail call void @tzset() nounwind
  ret void
}

declare void @tzset() nounwind

define weak i32 @softbound_sigprocmask(i32 %how, %struct.fd_set* %set, %struct.fd_set* %oldset, i8* %set_base, i8* %set_bound, i8* %oldset_base, i8* %oldset_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @sigprocmask(i32 %how, %struct.fd_set* noalias %set, %struct.fd_set* noalias %oldset) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @sigprocmask(i32, %struct.fd_set* noalias, %struct.fd_set* noalias) nounwind

define weak i32 @softbound_sigfillset(%struct.fd_set* %set, i8* %set_base, i8* %set_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @sigfillset(%struct.fd_set* %set) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @sigfillset(%struct.fd_set*) nounwind

define weak i32 @softbound_daemon(i32 %nochdir, i32 %noclose) nounwind alwaysinline {
entry:
  %0 = tail call i32 @daemon(i32 %nochdir, i32 %noclose) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @daemon(i32, i32) nounwind

define weak i32 @softbound_seteuid(i32 %euid) nounwind alwaysinline {
entry:
  %0 = tail call i32 @seteuid(i32 %euid) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @seteuid(i32) nounwind

define weak i32 @softbound_initgroups(i8* %user, i32 %group, i8* %user_base, i8* %user_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @initgroups(i8* %user, i32 %group) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @initgroups(i8*, i32)

define weak i32 @softbound_setegid(i32 %egid) nounwind alwaysinline {
entry:
  %0 = tail call i32 @setegid(i32 %egid) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @setegid(i32) nounwind

define weak i32 @softbound_sigemptyset(%struct.fd_set* %set, i8* %set_base, i8* %set_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @sigemptyset(%struct.fd_set* %set) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @sigemptyset(%struct.fd_set*) nounwind

define weak i32 @softbound_memcmp(i8* %s1, i8* %s2, i32 %n, i8* %s1_base, i8* %s1_bound, i8* %s2_base, i8* %s2_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @memcmp(i8* %s1, i8* %s2, i32 %n) nounwind readonly ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @memcmp(i8* nocapture, i8* nocapture, i32) nounwind readonly

define weak void @softbound_strstr(%struct.PtrBaseBound* %ptrs, i8* %haystack, i8* %needle, i8* %haystack_base, i8* %haystack_bound, i8* %needle_base, i8* %needle_bound) nounwind alwaysinline {
entry:
  %0 = tail call i8* @strstr(i8* %haystack, i8* %needle) nounwind readonly ; <i8*> [#uses=1]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %haystack_base, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %haystack_bound, i8** %3, align 4
  ret void
}

declare i8* @strstr(i8*, i8* nocapture) nounwind readonly

define weak void @softbound_strncpy(%struct.PtrBaseBound* %ptrs, i8* %dest, i8* %src, i32 %n, i8* %dest_base, i8* %dest_bound, i8* %src_base, i8* %src_bound) nounwind alwaysinline {
entry:
  %0 = tail call i8* @strncpy(i8* %dest, i8* %src, i32 %n) nounwind ; <i8*> [#uses=1]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %dest_base, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %dest_bound, i8** %3, align 4
  ret void
}

declare i8* @strncpy(i8*, i8* nocapture, i32) nounwind

define weak void @softbound_strrchr(%struct.PtrBaseBound* %ptrs, i8* %s, i32 %c, i8* %s_base, i8* %s_bound) nounwind alwaysinline {
entry:
  %0 = tail call i8* @strrchr(i8* %s, i32 %c) nounwind readonly ; <i8*> [#uses=1]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %s_base, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %s_bound, i8** %3, align 4
  ret void
}

declare i8* @strrchr(i8*, i32) nounwind readonly

define weak void @softbound_strcpy(%struct.PtrBaseBound* %ptrs, i8* %dest, i8* %src, i8* %dest_base, i8* %dest_bound, i8* %src_base, i8* %src_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @strlen(i8* %src) nounwind readonly ; <i32> [#uses=1]
  %1 = getelementptr inbounds i8* %dest, i32 %0   ; <i8*> [#uses=2]
  %2 = icmp ult i8* %1, %dest_base                ; <i1> [#uses=1]
  %3 = icmp ugt i8* %1, %dest_bound               ; <i1> [#uses=1]
  %or.cond = or i1 %2, %3                         ; <i1> [#uses=1]
  br i1 %or.cond, label %bb1, label %bb2

bb1:                                              ; preds = %entry
  tail call void @abort() noreturn nounwind
  unreachable

bb2:                                              ; preds = %entry
  %4 = tail call i8* @strcpy(i8* noalias %dest, i8* noalias %src) nounwind ; <i8*> [#uses=1]
  %5 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %4, i8** %5, align 4
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %dest_base, i8** %6, align 4
  %7 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %dest_bound, i8** %7, align 4
  ret void
}

declare i8* @strcpy(i8*, i8* nocapture) nounwind

define weak void @softbound_strchr(%struct.PtrBaseBound* %ptrs, i8* %s, i32 %c, i8* %s_base, i8* %s_bound) nounwind alwaysinline {
entry:
  %0 = tail call i8* @strchr(i8* %s, i32 %c) nounwind readonly ; <i8*> [#uses=1]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %s_base, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %s_bound, i8** %3, align 4
  ret void
}

declare i8* @strchr(i8*, i32) nounwind readonly

define weak void @softbound_strncat(%struct.PtrBaseBound* %ptrs, i8* %dest, i8* %src, i32 %n, i8* %dest_base, i8* %dest_bound, i8* %src_base, i8* %src_bound) nounwind alwaysinline {
entry:
  %0 = tail call i8* @strncat(i8* %dest, i8* %src, i32 %n) nounwind ; <i8*> [#uses=1]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %dest_base, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %dest_bound, i8** %3, align 4
  ret void
}

declare i8* @strncat(i8*, i8* nocapture, i32) nounwind

define weak void @softbound_strcat(%struct.PtrBaseBound* %ptrs, i8* %dest, i8* %src, i8* %dest_base, i8* %dest_bound, i8* %src_base, i8* %src_bound) nounwind alwaysinline {
entry:
  %0 = tail call i8* @strcat(i8* noalias %dest, i8* noalias %src) nounwind ; <i8*> [#uses=1]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %dest_base, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %dest_bound, i8** %3, align 4
  ret void
}

declare i8* @strcat(i8*, i8* nocapture) nounwind

define weak i32 @softbound_strcspn(i8* %s, i8* %reject, i8* %s_base, i8* %s_bound, i8* %reject_base, i8* %reject_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @strcspn(i8* %s, i8* %reject) nounwind readonly ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @strcspn(i8*, i8*) nounwind readonly

define weak i32 @softbound_strspn(i8* %s, i8* %accept, i8* %s_base, i8* %s_bound, i8* %accept_base, i8* %accept_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @strspn(i8* %s, i8* %accept) nounwind readonly ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @strspn(i8* nocapture, i8* nocapture) nounwind readonly

define weak void @softbound_strdup(%struct.PtrBaseBound* %ptrs, i8* %s, i8* %s_base, i8* %s_bound) nounwind alwaysinline {
entry:
  %0 = tail call noalias i8* @__strdup(i8* %s) nounwind ; <i8*> [#uses=3]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %0, i8** %2, align 4
  %3 = tail call i32 @strlen(i8* %s) nounwind readonly ; <i32> [#uses=1]
  %.sum = add i32 %3, 1                           ; <i32> [#uses=1]
  %4 = getelementptr inbounds i8* %0, i32 %.sum   ; <i8*> [#uses=1]
  %5 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %4, i8** %5, align 4
  ret void
}

declare noalias i8* @__strdup(i8* nocapture) nounwind

define weak void @softbound___strdup(%struct.PtrBaseBound* %ptrs, i8* %s, i8* %s_base, i8* %s_bound) nounwind alwaysinline {
entry:
  %0 = tail call noalias i8* @__strdup(i8* %s) nounwind ; <i8*> [#uses=3]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %0, i8** %2, align 4
  %3 = tail call i32 @strlen(i8* %s) nounwind readonly ; <i32> [#uses=1]
  %.sum = add i32 %3, 1                           ; <i32> [#uses=1]
  %4 = getelementptr inbounds i8* %0, i32 %.sum   ; <i8*> [#uses=1]
  %5 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %4, i8** %5, align 4
  ret void
}

define weak void @softbound_strtok(%struct.PtrBaseBound* %ptrs, i8* %str, i8* %delim, i8* %str_base, i8* %str_bound, i8* %delim_base, i8* %delim_bound) nounwind alwaysinline {
entry:
  %0 = tail call i8* @strtok(i8* noalias %str, i8* noalias %delim) nounwind ; <i8*> [#uses=1]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* null, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* inttoptr (i64 2147483647 to i8*), i8** %3, align 4
  ret void
}

declare i8* @strtok(i8* noalias, i8* noalias nocapture) nounwind

define weak void @softbound_perror(i8* %s, i8* %s_base, i8* %s_bound) nounwind alwaysinline {
entry:
  tail call void @perror(i8* %s) nounwind
  ret void
}

declare void @perror(i8* nocapture) nounwind

define weak void @softbound_fgets(%struct.PtrBaseBound* %return_ptr, i8* %s, i32 %size, %struct.FILE* %stream, i8* %s_base, i8* %s_bound, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
  %0 = tail call i8* @fgets(i8* noalias %s, i32 %size, %struct.FILE* noalias %stream) nounwind ; <i8*> [#uses=1]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %return_ptr, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %return_ptr, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %s_base, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %return_ptr, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %s_bound, i8** %3, align 4
  ret void
}

declare i8* @fgets(i8* noalias, i32, %struct.FILE* noalias nocapture) nounwind

define weak void @softbound_gets(%struct.PtrBaseBound* %return_ptr, i8* %s, i8* %s_base, i8* %s_bound) nounwind alwaysinline {
entry:
  %0 = tail call i8* @gets(i8* %s) nounwind       ; <i8*> [#uses=1]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %return_ptr, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %return_ptr, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %s_base, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %return_ptr, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %s_bound, i8** %3, align 4
  ret void
}

declare i8* @gets(i8*) nounwind

define weak void @softbound_strpbrk(%struct.PtrBaseBound* %return_ptr, i8* %s, i8* %accept, i8* %s_base, i8* %s_bound, i8* %accept_base, i8* %accept_bound) nounwind alwaysinline {
entry:
  %0 = tail call i8* @strpbrk(i8* %s, i8* %accept) nounwind readonly ; <i8*> [#uses=2]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %return_ptr, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = icmp eq i8* %0, null                       ; <i1> [#uses=1]
  %3 = getelementptr inbounds %struct.PtrBaseBound* %return_ptr, i32 0, i32 1 ; <i8**> [#uses=2]
  br i1 %2, label %bb1, label %bb

bb:                                               ; preds = %entry
  store i8* %s_base, i8** %3, align 4
  %4 = getelementptr inbounds %struct.PtrBaseBound* %return_ptr, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %s_bound, i8** %4, align 4
  ret void

bb1:                                              ; preds = %entry
  store i8* null, i8** %3, align 4
  %5 = getelementptr inbounds %struct.PtrBaseBound* %return_ptr, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* null, i8** %5, align 4
  ret void
}

declare i8* @strpbrk(i8*, i8* nocapture) nounwind readonly

define weak void @softbound___strpbrk_c3(%struct.PtrBaseBound* %return_ptr, i8* %s, i8* %accept, i8* %s_base, i8* %s_bound, i8* %accept_base, i8* %accept_bound) nounwind alwaysinline {
entry:
  %0 = tail call i8* @strpbrk(i8* %s, i8* %accept) nounwind readonly ; <i8*> [#uses=2]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %return_ptr, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = icmp eq i8* %0, null                       ; <i1> [#uses=1]
  %3 = getelementptr inbounds %struct.PtrBaseBound* %return_ptr, i32 0, i32 1 ; <i8**> [#uses=2]
  br i1 %2, label %bb1, label %bb

bb:                                               ; preds = %entry
  store i8* %s_base, i8** %3, align 4
  %4 = getelementptr inbounds %struct.PtrBaseBound* %return_ptr, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %s_bound, i8** %4, align 4
  ret void

bb1:                                              ; preds = %entry
  store i8* null, i8** %3, align 4
  %5 = getelementptr inbounds %struct.PtrBaseBound* %return_ptr, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* null, i8** %5, align 4
  ret void
}

define weak i32 @softbound_strncasecmp(i8* %s1, i8* %s2, i32 %n, i8* %s1_base, i8* %s1_bound, i8* %s2_base, i8* %s2_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @strncasecmp(i8* %s1, i8* %s2, i32 %n) nounwind readonly ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @strncasecmp(i8* nocapture, i8* nocapture, i32) nounwind readonly

define weak i32 @softbound_strcasecmp(i8* %s1, i8* %s2, i8* %s1_base, i8* %s1_bound, i8* %s2_base, i8* %s2_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @strcasecmp(i8* %s1, i8* %s2) nounwind readonly ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @strcasecmp(i8* nocapture, i8* nocapture) nounwind readonly

define weak void @softbound_memchr(%struct.PtrBaseBound* %ptrs, i8* %s, i32 %c, i32 %n, i8* %s_base, i8* %s_bound) nounwind alwaysinline {
entry:
  %0 = tail call i8* @memchr(i8* %s, i32 %c, i32 %n) nounwind readonly ; <i8*> [#uses=2]
  %1 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %1, align 4
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=2]
  store i8* null, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=2]
  store i8* null, i8** %3, align 4
  %4 = icmp eq i8* %0, null                       ; <i1> [#uses=1]
  br i1 %4, label %return, label %bb

bb:                                               ; preds = %entry
  store i8* %s_base, i8** %2, align 4
  store i8* %s_bound, i8** %3, align 4
  ret void

return:                                           ; preds = %entry
  ret void
}

declare i8* @memchr(i8*, i32, i32) nounwind readonly

define weak i32 @softbound_chdir(i8* %path, i8* %path_base, i8* %path_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @chdir(i8* %path) nounwind   ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @chdir(i8*) nounwind

define weak i32 @softbound_isatty(i32 %desc) nounwind alwaysinline {
entry:
  %0 = tail call i32 @isatty(i32 %desc) nounwind  ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @isatty(i32) nounwind

define weak i32 @softbound_chown(i8* %path, i32 %owner, i32 %group, i8* %path_base, i8* %path_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @chown(i8* %path, i32 %owner, i32 %group) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @chown(i8* nocapture, i32, i32) nounwind

define weak void @softbound_getcwd(%struct.PtrBaseBound* %ptrs, i8* %buf, i32 %size, i8* %buf_base, i8* %buf_bound) nounwind alwaysinline {
entry:
  %0 = icmp eq i8* %buf, null                     ; <i1> [#uses=1]
  br i1 %0, label %bb, label %bb1

bb:                                               ; preds = %entry
  %1 = tail call i32 @puts(i8* getelementptr inbounds ([53 x i8]* @.str1, i32 0, i32 0)) nounwind ; <i32> [#uses=0]
  tail call void (...)* @__softbound_abort() noreturn nounwind
  unreachable

bb1:                                              ; preds = %entry
  %2 = tail call i8* @getcwd(i8* %buf, i32 %size) nounwind ; <i8*> [#uses=1]
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %2, i8** %3, align 4
  %4 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %buf_base, i8** %4, align 4
  %5 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %buf_bound, i8** %5, align 4
  ret void
}

declare i8* @getcwd(i8*, i32) nounwind

define weak i32 @softbound_sleep(i32 %seconds) nounwind alwaysinline {
entry:
  %0 = tail call i32 @sleep(i32 %seconds) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @sleep(i32)

define weak i32 @softbound_rename(i8* %old_path, i8* %new_path, i8* %oldpath_base, i8* %oldpath_bound, i8* %new_path_base, i8* %new_path_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @rename(i8* %old_path, i8* %new_path) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @rename(i8* nocapture, i8* nocapture) nounwind

define weak i32 @softbound_closedir(%struct.DIR* %dir, i8* %dir_base, i8* %dir_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @closedir(%struct.DIR* %dir) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @closedir(%struct.DIR* nocapture) nounwind

define weak void @softbound_opendir(%struct.PtrBaseBound* %ptrs, i8* %name, i8* %name_base, i8* %name_bound) nounwind alwaysinline {
entry:
  %0 = tail call %struct.DIR* @opendir(i8* %name) nounwind ; <%struct.DIR*> [#uses=1]
  %1 = bitcast %struct.DIR* %0 to i8*             ; <i8*> [#uses=3]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %1, i8** %3, align 4
  %4 = getelementptr inbounds i8* %1, i32 1048576 ; <i8*> [#uses=1]
  %5 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %4, i8** %5, align 4
  ret void
}

declare noalias %struct.DIR* @opendir(i8* nocapture) nounwind

define weak void @softbound_readdir(%struct.PtrBaseBound* %ptrs, %struct.DIR* %dir, i8* %dir_base, i8* %dir_bound) nounwind alwaysinline {
entry:
  %0 = tail call %struct.dirent* @readdir(%struct.DIR* %dir) nounwind ; <%struct.dirent*> [#uses=2]
  %1 = bitcast %struct.dirent* %0 to i8*          ; <i8*> [#uses=2]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %1, i8** %3, align 4
  %4 = getelementptr inbounds %struct.dirent* %0, i32 1 ; <%struct.dirent*> [#uses=1]
  %5 = bitcast %struct.dirent* %4 to i8*          ; <i8*> [#uses=1]
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %5, i8** %6, align 4
  ret void
}

declare %struct.dirent* @readdir(%struct.DIR*)

define weak void @softbound_rewind(%struct.FILE* %stream, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
  tail call void @rewind(%struct.FILE* %stream) nounwind
  ret void
}

declare void @rewind(%struct.FILE* nocapture) nounwind

define weak i32 @softbound_pclose(%struct.FILE* %stream, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @pclose(%struct.FILE* %stream) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @pclose(%struct.FILE* nocapture) nounwind

define weak void @softbound_popen(%struct.PtrBaseBound* %ptrs, i8* %command, i8* %type, i8* %command_base, i8* %command_bound, i8* %type_base, i8* %type_bound) nounwind alwaysinline {
entry:
  %0 = tail call %struct.FILE* @popen(i8* %command, i8* %type) nounwind ; <%struct.FILE*> [#uses=2]
  %1 = bitcast %struct.FILE* %0 to i8*            ; <i8*> [#uses=2]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %1, i8** %3, align 4
  %4 = getelementptr inbounds %struct.FILE* %0, i32 1 ; <%struct.FILE*> [#uses=1]
  %5 = bitcast %struct.FILE* %4 to i8*            ; <i8*> [#uses=1]
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %5, i8** %6, align 4
  ret void
}

declare noalias %struct.FILE* @popen(i8* nocapture, i8* nocapture) nounwind

define weak i32 @softbound_ftruncate(i32 %fd, i32 %length) nounwind alwaysinline {
entry:
  %0 = tail call i32 @ftruncate(i32 %fd, i32 %length) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @ftruncate(i32, i32) nounwind

define weak i32 @softbound_fseek(%struct.FILE* %stream, i32 %offset, i32 %whence, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @fseek(%struct.FILE* %stream, i32 %offset, i32 %whence) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @fseek(%struct.FILE* nocapture, i32, i32) nounwind

define weak void @softbound_fdopen(%struct.PtrBaseBound* %ptrs, i32 %fildes, i8* %mode, i8* %mode_base, i8* %mode_bound) nounwind alwaysinline {
entry:
  %0 = tail call %struct.FILE* @fdopen(i32 %fildes, i8* %mode) nounwind ; <%struct.FILE*> [#uses=2]
  %1 = bitcast %struct.FILE* %0 to i8*            ; <i8*> [#uses=2]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %1, i8** %3, align 4
  %4 = getelementptr inbounds %struct.FILE* %0, i32 1 ; <%struct.FILE*> [#uses=1]
  %5 = bitcast %struct.FILE* %4 to i8*            ; <i8*> [#uses=1]
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %5, i8** %6, align 4
  ret void
}

declare noalias %struct.FILE* @fdopen(i32, i8* nocapture) nounwind

define weak void @softbound_fopen(%struct.PtrBaseBound* %ptrs, i8* %path, i8* %mode, i8* %path_base, i8* %path_bound, i8* %mode_base, i8* %mode_bound) nounwind alwaysinline {
entry:
  %0 = tail call %struct.FILE* @fopen(i8* noalias %path, i8* noalias %mode) nounwind ; <%struct.FILE*> [#uses=2]
  %1 = bitcast %struct.FILE* %0 to i8*            ; <i8*> [#uses=2]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %1, i8** %3, align 4
  %4 = getelementptr inbounds %struct.FILE* %0, i32 1 ; <%struct.FILE*> [#uses=1]
  %5 = bitcast %struct.FILE* %4 to i8*            ; <i8*> [#uses=1]
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %5, i8** %6, align 4
  ret void
}

declare noalias %struct.FILE* @fopen(i8* noalias nocapture, i8* noalias nocapture) nounwind

define weak i32 @softbound_fputs(i8* %s, %struct.FILE* %stream, i8* %s_base, i8* %s_bound, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @fputs(i8* noalias %s, %struct.FILE* noalias %stream) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @fputs(i8* noalias nocapture, %struct.FILE* noalias nocapture) nounwind

define weak i32 @softbound_fflush(%struct.FILE* %stream, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @fflush(%struct.FILE* %stream) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @fflush(%struct.FILE* nocapture) nounwind

declare i32 @__fxstat(i32, i32, %struct.stat*) nounwind

define weak i32 @softbound_fstat(i32 %filedes, %struct.stat* %buff, i8* %buff_base, i8* %buff_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @__fxstat(i32 3, i32 %filedes, %struct.stat* %buff) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

define weak i32 @softbound_ftell(%struct.FILE* %stream, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @ftell(%struct.FILE* %stream) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @ftell(%struct.FILE* nocapture) nounwind

define weak i32 @softbound_ferror(%struct.FILE* %stream, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @ferror(%struct.FILE* %stream) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @ferror(%struct.FILE* nocapture) nounwind readonly

define weak void @softbound_tmpfile(%struct.PtrBaseBound* %ptrs) nounwind alwaysinline {
entry:
  %0 = tail call %struct.FILE* @tmpfile() nounwind ; <%struct.FILE*> [#uses=2]
  %1 = bitcast %struct.FILE* %0 to i8*            ; <i8*> [#uses=2]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %1, i8** %3, align 4
  %4 = getelementptr inbounds %struct.FILE* %0, i32 1 ; <%struct.FILE*> [#uses=1]
  %5 = bitcast %struct.FILE* %4 to i8*            ; <i8*> [#uses=1]
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %5, i8** %6, align 4
  ret void
}

declare noalias %struct.FILE* @tmpfile() nounwind

define weak double @softbound_ldexp(double %x, i32 %exp) nounwind alwaysinline {
entry:
  %0 = tail call double @ldexp(double %x, i32 %exp) nounwind readonly ; <double> [#uses=1]
  ret double %0
}

declare double @ldexp(double, i32) nounwind readonly

define weak double @softbound_exp(double %x) nounwind alwaysinline {
entry:
  %0 = tail call double @llvm.exp.f64(double %x)  ; <double> [#uses=1]
  ret double %0
}

declare double @llvm.exp.f64(double) nounwind readonly

define weak x86_fp80 @softbound_cosl(x86_fp80 %x) nounwind alwaysinline {
entry:
  %0 = tail call x86_fp80 @cosl(x86_fp80 %x) nounwind readonly ; <x86_fp80> [#uses=1]
  ret x86_fp80 %0
}

declare x86_fp80 @cosl(x86_fp80) nounwind readonly

define weak float @softbound_cosf(float %x) nounwind alwaysinline {
entry:
  %0 = tail call float @cosf(float %x) nounwind readonly ; <float> [#uses=1]
  ret float %0
}

declare float @cosf(float) nounwind readonly

define weak double @softbound_cos(double %x) nounwind alwaysinline {
entry:
  %0 = tail call double @cos(double %x) nounwind readonly ; <double> [#uses=1]
  ret double %0
}

declare double @cos(double) nounwind readonly

define weak x86_fp80 @softbound_sinl(x86_fp80 %x) nounwind alwaysinline {
entry:
  %0 = tail call x86_fp80 @sinl(x86_fp80 %x) nounwind readonly ; <x86_fp80> [#uses=1]
  ret x86_fp80 %0
}

declare x86_fp80 @sinl(x86_fp80) nounwind readonly

define weak float @softbound_sinf(float %x) nounwind alwaysinline {
entry:
  %0 = tail call float @sinf(float %x) nounwind readonly ; <float> [#uses=1]
  ret float %0
}

declare float @sinf(float) nounwind readonly

define weak double @softbound_sin(double %x) nounwind alwaysinline {
entry:
  %0 = tail call double @sin(double %x) nounwind readonly ; <double> [#uses=1]
  ret double %0
}

declare double @sin(double) nounwind readonly

define weak double @softbound_log10(double %x) nounwind alwaysinline {
entry:
  %0 = tail call double @llvm.log10.f64(double %x) ; <double> [#uses=1]
  ret double %0
}

declare double @llvm.log10.f64(double) nounwind readonly

define weak x86_fp80 @softbound_tanl(x86_fp80 %x) nounwind alwaysinline {
entry:
  %0 = tail call x86_fp80 @tanl(x86_fp80 %x) nounwind readonly ; <x86_fp80> [#uses=1]
  ret x86_fp80 %0
}

declare x86_fp80 @tanl(x86_fp80) nounwind readonly

define weak float @softbound_tanf(float %x) nounwind alwaysinline {
entry:
  %0 = tail call float @tanf(float %x) nounwind readonly ; <float> [#uses=1]
  ret float %0
}

declare float @tanf(float) nounwind readonly

define weak double @softbound_tan(double %x) nounwind alwaysinline {
entry:
  %0 = tail call double @tan(double %x) nounwind readonly ; <double> [#uses=1]
  ret double %0
}

declare double @tan(double) nounwind readonly

define weak double @softbound_pow(double %x, double %y) nounwind alwaysinline {
entry:
  %0 = tail call double @llvm.pow.f64(double %x, double %y) ; <double> [#uses=1]
  ret double %0
}

declare double @llvm.pow.f64(double, double) nounwind readonly

define weak void @softbound_srand48(i32 %seed) nounwind alwaysinline {
entry:
  tail call void @srand48(i32 %seed) nounwind
  ret void
}

declare void @srand48(i32) nounwind

define weak void @softbound_srand(i32 %seed) nounwind alwaysinline {
entry:
  tail call void @srand(i32 %seed) nounwind
  ret void
}

declare void @srand(i32) nounwind

define weak double @softbound_sqrt(double %x) nounwind alwaysinline {
entry:
  %0 = tail call double @llvm.sqrt.f64(double %x) ; <double> [#uses=1]
  ret double %0
}

declare double @llvm.sqrt.f64(double) nounwind readonly

define weak double @softbound_floor(double %x) nounwind alwaysinline {
entry:
  %0 = tail call double @floor(double %x) nounwind readnone ; <double> [#uses=1]
  ret double %0
}

declare double @floor(double) nounwind readnone

define weak float @softbound_ceilf(float %x) nounwind alwaysinline {
entry:
  %0 = tail call float @ceilf(float %x) nounwind readnone ; <float> [#uses=1]
  ret float %0
}

declare float @ceilf(float) nounwind readnone

define weak double @softbound_ceil(double %x) nounwind alwaysinline {
entry:
  %0 = tail call double @ceil(double %x) nounwind readnone ; <double> [#uses=1]
  ret double %0
}

declare double @ceil(double) nounwind readnone

define weak float @softbound_floorf(float %x) nounwind alwaysinline {
entry:
  %0 = tail call float @floorf(float %x) nounwind readnone ; <float> [#uses=1]
  ret float %0
}

declare float @floorf(float) nounwind readnone

define weak double @softbound_exp2(double %x) nounwind alwaysinline {
entry:
  %0 = tail call double @llvm.exp2.f64(double %x) ; <double> [#uses=1]
  ret double %0
}

declare double @llvm.exp2.f64(double) nounwind readonly

define weak float @softbound_expf(float %x) nounwind alwaysinline {
entry:
  %0 = tail call float @llvm.exp.f32(float %x)    ; <float> [#uses=1]
  ret float %0
}

declare float @llvm.exp.f32(float) nounwind readonly

define weak float @softbound_sqrtf(float %x) nounwind alwaysinline {
entry:
  %0 = tail call float @llvm.sqrt.f32(float %x)   ; <float> [#uses=1]
  ret float %0
}

declare float @llvm.sqrt.f32(float) nounwind readonly

define weak double @softbound_atan2(double %y, double %x) nounwind alwaysinline {
entry:
  %0 = tail call double @atan2(double %y, double %x) nounwind readonly ; <double> [#uses=1]
  ret double %0
}

declare double @atan2(double, double) nounwind readonly

define weak double @softbound_acos(double %x) nounwind alwaysinline {
entry:
  %0 = tail call double @acos(double %x) nounwind readonly ; <double> [#uses=1]
  ret double %0
}

declare double @acos(double) nounwind readonly

define weak i32 @softbound_remove(i8* %pathname, i8* %pathname_base, i8* %pathname_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @remove(i8* %pathname) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @remove(i8* nocapture) nounwind

define weak i32 @softbound_feof(%struct.FILE* %stream, i8* %stream_base, i8* %stream_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @feof(%struct.FILE* %stream) nounwind ; <i32> [#uses=1]
  ret i32 %0
}

declare i32 @feof(%struct.FILE* nocapture) nounwind

declare double @strtod(i8* noalias, i8** noalias nocapture) nounwind

define weak double @softbound_atof(i8* %ptr, i8* %base, i8* %bound) nounwind alwaysinline {
entry:
  %0 = tail call double @strtod(i8* noalias nocapture %ptr, i8** noalias null) nounwind readonly ; <double> [#uses=1]
  ret double %0
}

declare i32 @fwrite(i8* noalias nocapture, i32, i32, %struct.FILE* noalias nocapture) nounwind

declare double @llvm.log.f64(double) nounwind readonly

declare i32 @strncmp(i8* nocapture, i8* nocapture, i32) nounwind readonly

declare i32 @fgetc(%struct.FILE* nocapture) nounwind

declare i32 @fileno(%struct.FILE* nocapture) nounwind

declare i32 @fputc(i32, %struct.FILE* nocapture) nounwind

declare i32 @__xstat(i32, i8*, %struct.stat*) nounwind

declare i32 @rmdir(i8* nocapture) nounwind

declare i32 @chroot(i8*) nounwind

declare i32 @mkdir(i8* nocapture, i32) nounwind

declare i32 @umask(i32) nounwind

declare i32 @fread(i8* noalias nocapture, i32, i32, %struct.FILE* noalias nocapture) nounwind

declare void @qsort(i8*, i32, i32, i32 (i8*, i8*)* nocapture)

declare i32 @setrlimit(i32, %struct.rlimit*) nounwind

declare i32 @getrlimit(i32, %struct.rlimit*) nounwind

declare i32 @getuid() nounwind

declare i32 @mkstemp(i8*)

declare i32 @setreuid(i32, i32) nounwind

declare i32 @system(i8* nocapture)

declare void @__softbound_printf(i8*, ...)

define weak void @softbound_getttyent(%struct.PtrBaseBound* %ptrs) nounwind alwaysinline {
entry:
  %0 = tail call %struct.ttyent* @getttyent() nounwind ; <%struct.ttyent*> [#uses=7]
  %1 = bitcast %struct.ttyent* %0 to i8*          ; <i8*> [#uses=3]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %1, i8** %3, align 4
  %4 = getelementptr inbounds %struct.ttyent* %0, i32 1 ; <%struct.ttyent*> [#uses=1]
  %5 = bitcast %struct.ttyent* %4 to i8*          ; <i8*> [#uses=1]
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %5, i8** %6, align 4
  %7 = getelementptr inbounds %struct.ttyent* %0, i32 0, i32 0 ; <i8**> [#uses=1]
  %8 = load i8** %7, align 4                      ; <i8*> [#uses=4]
  %9 = tail call i32 @strlen(i8* %8) nounwind readonly ; <i32> [#uses=1]
  %.sum4 = add i32 %9, 1                          ; <i32> [#uses=1]
  %10 = getelementptr inbounds i8* %8, i32 %.sum4 ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %1, i8* %8, i8* %10, i8* %8, i32 1, i32 1) nounwind alwaysinline
  %11 = getelementptr inbounds %struct.ttyent* %0, i32 0, i32 1 ; <i8**> [#uses=2]
  %12 = bitcast i8** %11 to i8*                   ; <i8*> [#uses=1]
  %13 = load i8** %11                             ; <i8*> [#uses=4]
  %14 = tail call i32 @strlen(i8* %13) nounwind readonly ; <i32> [#uses=1]
  %.sum3 = add i32 %14, 1                         ; <i32> [#uses=1]
  %15 = getelementptr inbounds i8* %13, i32 %.sum3 ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %12, i8* %13, i8* %15, i8* %13, i32 1, i32 1) nounwind alwaysinline
  %16 = getelementptr inbounds %struct.ttyent* %0, i32 0, i32 2 ; <i8**> [#uses=3]
  %17 = bitcast i8** %16 to i8*                   ; <i8*> [#uses=1]
  %18 = load i8** %16                             ; <i8*> [#uses=4]
  %19 = tail call i32 @strlen(i8* %18) nounwind readonly ; <i32> [#uses=1]
  %.sum2 = add i32 %19, 1                         ; <i32> [#uses=1]
  %20 = getelementptr inbounds i8* %18, i32 %.sum2 ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %17, i8* %18, i8* %20, i8* %18, i32 1, i32 1) nounwind alwaysinline
  %21 = getelementptr inbounds %struct.ttyent* %0, i32 0, i32 4 ; <i8**> [#uses=2]
  %22 = bitcast i8** %21 to i8*                   ; <i8*> [#uses=1]
  %23 = load i8** %21                             ; <i8*> [#uses=3]
  %24 = load i8** %16                             ; <i8*> [#uses=1]
  %25 = tail call i32 @strlen(i8* %23) nounwind readonly ; <i32> [#uses=1]
  %.sum1 = add i32 %25, 1                         ; <i32> [#uses=1]
  %26 = getelementptr inbounds i8* %24, i32 %.sum1 ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %22, i8* %23, i8* %26, i8* %23, i32 1, i32 1) nounwind alwaysinline
  %27 = getelementptr inbounds %struct.ttyent* %0, i32 0, i32 5 ; <i8**> [#uses=2]
  %28 = bitcast i8** %27 to i8*                   ; <i8*> [#uses=1]
  %29 = load i8** %27                             ; <i8*> [#uses=4]
  %30 = tail call i32 @strlen(i8* %29) nounwind readonly ; <i32> [#uses=1]
  %.sum = add i32 %30, 1                          ; <i32> [#uses=1]
  %31 = getelementptr inbounds i8* %29, i32 %.sum ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %28, i8* %29, i8* %31, i8* %29, i32 1, i32 1) nounwind alwaysinline
  ret void
}

declare %struct.ttyent* @getttyent() nounwind

define weak i32 @softbound_glob(i8* %pattern, i32 %flags, i32 (i8*, i32)* %errfunc, %struct.glob_t* %pglob, i8* %pattern_base, i8* %pattern_bound, i8* %errfunc_base, i8* %errfunc_bound, i8* %pglob_base, i8* %pglob_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @glob(i8* noalias %pattern, i32 %flags, i32 (i8*, i32)* %errfunc, %struct.glob_t* noalias %pglob) nounwind ; <i32> [#uses=1]
  %1 = getelementptr inbounds %struct.glob_t* %pglob, i32 0, i32 2 ; <i32*> [#uses=1]
  %2 = load i32* %1, align 4                      ; <i32> [#uses=4]
  %3 = getelementptr inbounds %struct.glob_t* %pglob, i32 0, i32 1 ; <i8***> [#uses=3]
  %4 = load i8*** %3, align 4                     ; <i8**> [#uses=5]
  %5 = getelementptr inbounds i8** %4, i32 %2     ; <i8**> [#uses=1]
  %6 = load i8** %5, align 4                      ; <i8*> [#uses=1]
  %7 = icmp eq i8* %6, null                       ; <i1> [#uses=1]
  br i1 %7, label %bb2, label %bb.nph

bb.nph:                                           ; preds = %entry
  %tmp13 = add i32 %2, 1                          ; <i32> [#uses=1]
  br label %bb

bb:                                               ; preds = %bb, %bb.nph
  %8 = phi i8** [ %4, %bb.nph ], [ %14, %bb ]     ; <i8**> [#uses=1]
  %indvar = phi i32 [ 0, %bb.nph ], [ %indvar.next, %bb ] ; <i32> [#uses=3]
  %9 = phi i8** [ %4, %bb.nph ], [ %14, %bb ]     ; <i8**> [#uses=1]
  %tmp = add i32 %indvar, %2                      ; <i32> [#uses=2]
  %tmp14 = add i32 %indvar, %tmp13                ; <i32> [#uses=2]
  %scevgep = getelementptr i8** %9, i32 %tmp      ; <i8**> [#uses=1]
  %10 = load i8** %scevgep, align 4               ; <i8*> [#uses=1]
  %scevgep10 = getelementptr i8** %8, i32 %tmp    ; <i8**> [#uses=2]
  %11 = load i8** %scevgep10, align 4             ; <i8*> [#uses=3]
  %12 = tail call i32 @strlen(i8* %11) nounwind readonly ; <i32> [#uses=1]
  %.sum = add i32 %12, 1                          ; <i32> [#uses=1]
  %13 = getelementptr inbounds i8* %11, i32 %.sum ; <i8*> [#uses=1]
  %scevgep1112 = bitcast i8** %scevgep10 to i8*   ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %scevgep1112, i8* %11, i8* %13, i8* %10, i32 1, i32 1) nounwind alwaysinline
  %14 = load i8*** %3, align 4                    ; <i8**> [#uses=5]
  %scevgep15 = getelementptr i8** %14, i32 %tmp14 ; <i8**> [#uses=1]
  %15 = load i8** %scevgep15, align 4             ; <i8*> [#uses=1]
  %16 = icmp eq i8* %15, null                     ; <i1> [#uses=1]
  %indvar.next = add i32 %indvar, 1               ; <i32> [#uses=1]
  br i1 %16, label %bb2, label %bb

bb2:                                              ; preds = %bb, %entry
  %17 = phi i8** [ %4, %entry ], [ %14, %bb ]     ; <i8**> [#uses=2]
  %.lcssa = phi i8** [ %4, %entry ], [ %14, %bb ] ; <i8**> [#uses=1]
  %i.0.lcssa = phi i32 [ %2, %entry ], [ %tmp14, %bb ] ; <i32> [#uses=1]
  %.sum4 = add i32 %i.0.lcssa, 1                  ; <i32> [#uses=1]
  %18 = getelementptr inbounds i8** %17, i32 %.sum4 ; <i8**> [#uses=1]
  %19 = bitcast i8*** %3 to i8*                   ; <i8*> [#uses=1]
  %20 = bitcast i8** %17 to i8*                   ; <i8*> [#uses=1]
  %21 = bitcast i8** %18 to i8*                   ; <i8*> [#uses=1]
  %22 = bitcast i8** %.lcssa to i8*               ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %19, i8* %20, i8* %21, i8* %22, i32 8, i32 1) nounwind alwaysinline
  ret i32 %0
}

declare i32 @glob(i8* noalias, i32, i32 (i8*, i32)*, %struct.glob_t* noalias) nounwind

define weak void @softbound_getservbyname(%struct.PtrBaseBound* %ptrs, i8* %name, i8* %proto, i8* %name_base, i8* %name_bound, i8* %proto_base, i8* %proto_bound) nounwind alwaysinline {
entry:
  %0 = tail call %struct.servent* @getservbyname(i8* %name, i8* %proto) nounwind ; <%struct.servent*> [#uses=5]
  %1 = bitcast %struct.servent* %0 to i8*         ; <i8*> [#uses=3]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %1, i8** %3, align 4
  %4 = getelementptr inbounds %struct.servent* %0, i32 1 ; <%struct.servent*> [#uses=1]
  %5 = bitcast %struct.servent* %4 to i8*         ; <i8*> [#uses=1]
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %5, i8** %6, align 4
  %7 = getelementptr inbounds %struct.servent* %0, i32 0, i32 0 ; <i8**> [#uses=1]
  %8 = load i8** %7, align 4                      ; <i8*> [#uses=4]
  %9 = tail call i32 @strlen(i8* %8) nounwind readonly ; <i32> [#uses=1]
  %.sum5 = add i32 %9, 1                          ; <i32> [#uses=1]
  %10 = getelementptr inbounds i8* %8, i32 %.sum5 ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %1, i8* %8, i8* %10, i8* %8, i32 1, i32 1) nounwind alwaysinline
  %11 = getelementptr inbounds %struct.servent* %0, i32 0, i32 1 ; <i8***> [#uses=3]
  %12 = bitcast i8*** %11 to i8*                  ; <i8*> [#uses=1]
  %13 = load i8*** %11                            ; <i8**> [#uses=6]
  %14 = icmp eq i8** %13, null                    ; <i1> [#uses=1]
  br i1 %14, label %bb3, label %bb1.preheader

bb1.preheader:                                    ; preds = %entry
  %15 = load i8** %13                             ; <i8*> [#uses=1]
  %16 = icmp eq i8* %15, null                     ; <i1> [#uses=1]
  br i1 %16, label %bb2, label %bb

bb:                                               ; preds = %bb, %bb1.preheader
  %17 = phi i8** [ %13, %bb1.preheader ], [ %25, %bb ] ; <i8**> [#uses=1]
  %18 = phi i8** [ %13, %bb1.preheader ], [ %25, %bb ] ; <i8**> [#uses=1]
  %19 = phi i32 [ 0, %bb1.preheader ], [ %24, %bb ] ; <i32> [#uses=4]
  %scevgep = getelementptr i8** %18, i32 %19      ; <i8**> [#uses=1]
  %20 = load i8** %scevgep, align 4               ; <i8*> [#uses=1]
  %scevgep10 = getelementptr i8** %17, i32 %19    ; <i8**> [#uses=2]
  %21 = load i8** %scevgep10, align 4             ; <i8*> [#uses=3]
  %22 = tail call i32 @strlen(i8* %21) nounwind readonly ; <i32> [#uses=1]
  %.sum = add i32 %22, 1                          ; <i32> [#uses=1]
  %23 = getelementptr inbounds i8* %21, i32 %.sum ; <i8*> [#uses=1]
  %scevgep1213 = bitcast i8** %scevgep10 to i8*   ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %scevgep1213, i8* %21, i8* %23, i8* %20, i32 1, i32 1) nounwind alwaysinline
  %24 = add nsw i32 %19, 1                        ; <i32> [#uses=2]
  %25 = load i8*** %11                            ; <i8**> [#uses=5]
  %scevgep14 = getelementptr i8** %25, i32 %24    ; <i8**> [#uses=1]
  %26 = load i8** %scevgep14, align 4             ; <i8*> [#uses=1]
  %27 = icmp eq i8* %26, null                     ; <i1> [#uses=1]
  br i1 %27, label %bb1.bb2_crit_edge, label %bb

bb1.bb2_crit_edge:                                ; preds = %bb
  %phitmp = add i32 %19, 2                        ; <i32> [#uses=1]
  br label %bb2

bb2:                                              ; preds = %bb1.bb2_crit_edge, %bb1.preheader
  %28 = phi i8** [ %25, %bb1.bb2_crit_edge ], [ %13, %bb1.preheader ] ; <i8**> [#uses=2]
  %.lcssa = phi i8** [ %25, %bb1.bb2_crit_edge ], [ %13, %bb1.preheader ] ; <i8**> [#uses=1]
  %i.0.lcssa = phi i32 [ %phitmp, %bb1.bb2_crit_edge ], [ 1, %bb1.preheader ] ; <i32> [#uses=1]
  %29 = getelementptr inbounds i8** %28, i32 %i.0.lcssa ; <i8**> [#uses=1]
  %30 = bitcast i8** %28 to i8*                   ; <i8*> [#uses=1]
  %31 = bitcast i8** %29 to i8*                   ; <i8*> [#uses=1]
  %32 = bitcast i8** %.lcssa to i8*               ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %12, i8* %30, i8* %31, i8* %32, i32 8, i32 1) nounwind alwaysinline
  br label %bb3

bb3:                                              ; preds = %bb2, %entry
  %33 = getelementptr inbounds %struct.servent* %0, i32 0, i32 3 ; <i8**> [#uses=2]
  %34 = bitcast i8** %33 to i8*                   ; <i8*> [#uses=1]
  %35 = load i8** %33                             ; <i8*> [#uses=4]
  %36 = tail call i32 @strlen(i8* %35) nounwind readonly ; <i32> [#uses=1]
  %.sum4 = add i32 %36, 1                         ; <i32> [#uses=1]
  %37 = getelementptr inbounds i8* %35, i32 %.sum4 ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %34, i8* %35, i8* %37, i8* %35, i32 1, i32 1) nounwind alwaysinline
  ret void
}

declare %struct.servent* @getservbyname(i8*, i8*)

define weak i32 @softbound_getaddrinfo(i8* %node, i8* %service, %struct.addrinfo* %hints, %struct.addrinfo** %res, i8* %node_base, i8* %node_bound, i8* %service_base, i8* %service_bound, i8* %hints_base, i8* %hints_bound, i8* %res_base, i8* %res_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @getaddrinfo(i8* noalias %node, i8* noalias %service, %struct.addrinfo* noalias %hints, %struct.addrinfo** noalias %res) nounwind ; <i32> [#uses=1]
  %1 = load %struct.addrinfo** %res, align 4      ; <%struct.addrinfo*> [#uses=4]
  %2 = getelementptr inbounds %struct.addrinfo* %1, i32 1 ; <%struct.addrinfo*> [#uses=1]
  %3 = bitcast %struct.addrinfo* %2 to i8*        ; <i8*> [#uses=1]
  %4 = bitcast %struct.addrinfo** %res to i8*     ; <i8*> [#uses=1]
  %5 = bitcast %struct.addrinfo* %1 to i8*        ; <i8*> [#uses=2]
  tail call void @__hashStoreBaseBound(i8* %4, i8* %5, i8* %3, i8* %5, i32 1, i32 1) nounwind alwaysinline
  %6 = icmp eq %struct.addrinfo* %1, null         ; <i1> [#uses=1]
  br i1 %6, label %bb4, label %bb

bb:                                               ; preds = %bb2, %entry
  %temp.06 = phi %struct.addrinfo* [ %1, %entry ], [ %25, %bb2 ] ; <%struct.addrinfo*> [#uses=3]
  %7 = getelementptr inbounds %struct.addrinfo* %temp.06, i32 0, i32 5 ; <%struct.sockaddr**> [#uses=2]
  %8 = load %struct.sockaddr** %7, align 4        ; <%struct.sockaddr*> [#uses=2]
  %9 = getelementptr inbounds %struct.sockaddr* %8, i32 1 ; <%struct.sockaddr*> [#uses=1]
  %10 = bitcast %struct.sockaddr* %9 to i8*       ; <i8*> [#uses=1]
  %11 = bitcast %struct.sockaddr** %7 to i8*      ; <i8*> [#uses=1]
  %12 = bitcast %struct.sockaddr* %8 to i8*       ; <i8*> [#uses=2]
  tail call void @__hashStoreBaseBound(i8* %11, i8* %12, i8* %10, i8* %12, i32 1, i32 1) nounwind alwaysinline
  %13 = getelementptr inbounds %struct.addrinfo* %temp.06, i32 0, i32 6 ; <i8**> [#uses=2]
  %14 = load i8** %13, align 4                    ; <i8*> [#uses=4]
  %15 = tail call i32 @strlen(i8* %14) nounwind readonly ; <i32> [#uses=1]
  %.sum = add i32 %15, 1                          ; <i32> [#uses=1]
  %16 = getelementptr inbounds i8* %14, i32 %.sum ; <i8*> [#uses=1]
  %17 = bitcast i8** %13 to i8*                   ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %17, i8* %14, i8* %16, i8* %14, i32 1, i32 1) nounwind alwaysinline
  %18 = getelementptr inbounds %struct.addrinfo* %temp.06, i32 0, i32 7 ; <%struct.addrinfo**> [#uses=3]
  %19 = load %struct.addrinfo** %18, align 4      ; <%struct.addrinfo*> [#uses=4]
  %20 = icmp eq %struct.addrinfo* %19, null       ; <i1> [#uses=1]
  br i1 %20, label %bb2, label %bb1

bb1:                                              ; preds = %bb
  %21 = getelementptr inbounds %struct.addrinfo* %19, i32 1 ; <%struct.addrinfo*> [#uses=1]
  %22 = bitcast %struct.addrinfo* %21 to i8*      ; <i8*> [#uses=1]
  %23 = bitcast %struct.addrinfo** %18 to i8*     ; <i8*> [#uses=1]
  %24 = bitcast %struct.addrinfo* %19 to i8*      ; <i8*> [#uses=2]
  tail call void @__hashStoreBaseBound(i8* %23, i8* %24, i8* %22, i8* %24, i32 1, i32 1) nounwind alwaysinline
  %.pre = load %struct.addrinfo** %18, align 4    ; <%struct.addrinfo*> [#uses=1]
  br label %bb2

bb2:                                              ; preds = %bb1, %bb
  %25 = phi %struct.addrinfo* [ %.pre, %bb1 ], [ %19, %bb ] ; <%struct.addrinfo*> [#uses=2]
  %phitmp = icmp eq %struct.addrinfo* %25, null   ; <i1> [#uses=1]
  br i1 %phitmp, label %bb4, label %bb

bb4:                                              ; preds = %bb2, %entry
  ret i32 %0
}

declare i32 @getaddrinfo(i8* noalias, i8* noalias, %struct.addrinfo* noalias, %struct.addrinfo** noalias)

define weak void @softbound_gethostbyname(%struct.PtrBaseBound* %ptrs, i8* %name, i8* %name_base, i8* %name_bound) nounwind alwaysinline {
entry:
  %0 = tail call %struct.hostent* @gethostbyname(i8* %name) nounwind ; <%struct.hostent*> [#uses=5]
  %1 = bitcast %struct.hostent* %0 to i8*         ; <i8*> [#uses=3]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %1, i8** %3, align 4
  %4 = getelementptr inbounds %struct.hostent* %0, i32 1 ; <%struct.hostent*> [#uses=1]
  %5 = bitcast %struct.hostent* %4 to i8*         ; <i8*> [#uses=1]
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %5, i8** %6, align 4
  %7 = getelementptr inbounds %struct.hostent* %0, i32 0, i32 0 ; <i8**> [#uses=1]
  %8 = load i8** %7, align 4                      ; <i8*> [#uses=4]
  %9 = tail call i32 @strlen(i8* %8) nounwind readonly ; <i32> [#uses=1]
  %10 = getelementptr inbounds i8* %8, i32 %9     ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %1, i8* %8, i8* %10, i8* %8, i32 1, i32 1) nounwind alwaysinline
  %11 = getelementptr inbounds %struct.hostent* %0, i32 0, i32 1 ; <i8***> [#uses=3]
  %12 = bitcast i8*** %11 to i8*                  ; <i8*> [#uses=1]
  %13 = load i8*** %11                            ; <i8**> [#uses=6]
  %14 = icmp eq i8** %13, null                    ; <i1> [#uses=1]
  br i1 %14, label %bb3, label %bb1.preheader

bb1.preheader:                                    ; preds = %entry
  %15 = load i8** %13                             ; <i8*> [#uses=1]
  %16 = icmp eq i8* %15, null                     ; <i1> [#uses=1]
  br i1 %16, label %bb2, label %bb

bb:                                               ; preds = %bb, %bb1.preheader
  %17 = phi i8** [ %13, %bb1.preheader ], [ %25, %bb ] ; <i8**> [#uses=1]
  %18 = phi i8** [ %13, %bb1.preheader ], [ %25, %bb ] ; <i8**> [#uses=1]
  %19 = phi i32 [ 0, %bb1.preheader ], [ %24, %bb ] ; <i32> [#uses=4]
  %scevgep = getelementptr i8** %18, i32 %19      ; <i8**> [#uses=1]
  %20 = load i8** %scevgep, align 4               ; <i8*> [#uses=1]
  %scevgep18 = getelementptr i8** %17, i32 %19    ; <i8**> [#uses=2]
  %21 = load i8** %scevgep18, align 4             ; <i8*> [#uses=3]
  %22 = tail call i32 @strlen(i8* %21) nounwind readonly ; <i32> [#uses=1]
  %23 = getelementptr inbounds i8* %21, i32 %22   ; <i8*> [#uses=1]
  %scevgep1920 = bitcast i8** %scevgep18 to i8*   ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %scevgep1920, i8* %21, i8* %23, i8* %20, i32 1, i32 1) nounwind alwaysinline
  %24 = add nsw i32 %19, 1                        ; <i32> [#uses=2]
  %25 = load i8*** %11                            ; <i8**> [#uses=5]
  %scevgep21 = getelementptr i8** %25, i32 %24    ; <i8**> [#uses=1]
  %26 = load i8** %scevgep21, align 4             ; <i8*> [#uses=1]
  %27 = icmp eq i8* %26, null                     ; <i1> [#uses=1]
  br i1 %27, label %bb1.bb2_crit_edge, label %bb

bb1.bb2_crit_edge:                                ; preds = %bb
  %phitmp16 = add i32 %19, 2                      ; <i32> [#uses=1]
  br label %bb2

bb2:                                              ; preds = %bb1.bb2_crit_edge, %bb1.preheader
  %28 = phi i8** [ %25, %bb1.bb2_crit_edge ], [ %13, %bb1.preheader ] ; <i8**> [#uses=2]
  %.lcssa = phi i8** [ %25, %bb1.bb2_crit_edge ], [ %13, %bb1.preheader ] ; <i8**> [#uses=1]
  %i.0.lcssa = phi i32 [ %phitmp16, %bb1.bb2_crit_edge ], [ 1, %bb1.preheader ] ; <i32> [#uses=1]
  %29 = getelementptr inbounds i8** %28, i32 %i.0.lcssa ; <i8**> [#uses=1]
  %30 = bitcast i8** %28 to i8*                   ; <i8*> [#uses=1]
  %31 = bitcast i8** %29 to i8*                   ; <i8*> [#uses=1]
  %32 = bitcast i8** %.lcssa to i8*               ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %12, i8* %30, i8* %31, i8* %32, i32 4, i32 1) nounwind alwaysinline
  br label %bb3

bb3:                                              ; preds = %bb2, %entry
  %33 = getelementptr inbounds %struct.hostent* %0, i32 0, i32 4 ; <i8***> [#uses=3]
  %34 = bitcast i8*** %33 to i8*                  ; <i8*> [#uses=1]
  %35 = load i8*** %33                            ; <i8**> [#uses=6]
  %36 = icmp eq i8** %35, null                    ; <i1> [#uses=1]
  br i1 %36, label %return, label %bb5.preheader

bb5.preheader:                                    ; preds = %bb3
  %37 = load i8** %35                             ; <i8*> [#uses=1]
  %38 = icmp eq i8* %37, null                     ; <i1> [#uses=1]
  br i1 %38, label %bb6, label %bb4

bb4:                                              ; preds = %bb4, %bb5.preheader
  %39 = phi i8** [ %35, %bb5.preheader ], [ %47, %bb4 ] ; <i8**> [#uses=1]
  %40 = phi i8** [ %35, %bb5.preheader ], [ %47, %bb4 ] ; <i8**> [#uses=1]
  %41 = phi i32 [ 0, %bb5.preheader ], [ %46, %bb4 ] ; <i32> [#uses=4]
  %scevgep23 = getelementptr i8** %40, i32 %41    ; <i8**> [#uses=1]
  %42 = load i8** %scevgep23, align 4             ; <i8*> [#uses=1]
  %scevgep24 = getelementptr i8** %39, i32 %41    ; <i8**> [#uses=2]
  %43 = load i8** %scevgep24, align 4             ; <i8*> [#uses=3]
  %44 = tail call i32 @strlen(i8* %43) nounwind readonly ; <i32> [#uses=1]
  %45 = getelementptr inbounds i8* %43, i32 %44   ; <i8*> [#uses=1]
  %scevgep2526 = bitcast i8** %scevgep24 to i8*   ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %scevgep2526, i8* %43, i8* %45, i8* %42, i32 1, i32 1) nounwind alwaysinline
  %46 = add nsw i32 %41, 1                        ; <i32> [#uses=2]
  %47 = load i8*** %33                            ; <i8**> [#uses=5]
  %scevgep28 = getelementptr i8** %47, i32 %46    ; <i8**> [#uses=1]
  %48 = load i8** %scevgep28, align 4             ; <i8*> [#uses=1]
  %49 = icmp eq i8* %48, null                     ; <i1> [#uses=1]
  br i1 %49, label %bb5.bb6_crit_edge, label %bb4

bb5.bb6_crit_edge:                                ; preds = %bb4
  %phitmp = add i32 %41, 2                        ; <i32> [#uses=1]
  br label %bb6

bb6:                                              ; preds = %bb5.bb6_crit_edge, %bb5.preheader
  %50 = phi i8** [ %47, %bb5.bb6_crit_edge ], [ %35, %bb5.preheader ] ; <i8**> [#uses=2]
  %.lcssa11 = phi i8** [ %47, %bb5.bb6_crit_edge ], [ %35, %bb5.preheader ] ; <i8**> [#uses=1]
  %i.1.lcssa = phi i32 [ %phitmp, %bb5.bb6_crit_edge ], [ 1, %bb5.preheader ] ; <i32> [#uses=1]
  %51 = getelementptr inbounds i8** %50, i32 %i.1.lcssa ; <i8**> [#uses=1]
  %52 = bitcast i8** %50 to i8*                   ; <i8*> [#uses=1]
  %53 = bitcast i8** %51 to i8*                   ; <i8*> [#uses=1]
  %54 = bitcast i8** %.lcssa11 to i8*             ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %34, i8* %52, i8* %53, i8* %54, i32 1, i32 1) nounwind alwaysinline
  ret void

return:                                           ; preds = %bb3
  ret void
}

declare %struct.hostent* @gethostbyname(i8*)

define weak void @softbound_gethostbyaddr(%struct.PtrBaseBound* %ptrs, i8* %addr, i32 %len, i32 %type, i8* %addr_base, i8* %addr_bound) nounwind alwaysinline {
entry:
  %0 = tail call %struct.hostent* @gethostbyaddr(i8* %addr, i32 %len, i32 %type) nounwind ; <%struct.hostent*> [#uses=5]
  %1 = bitcast %struct.hostent* %0 to i8*         ; <i8*> [#uses=3]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %1, i8** %3, align 4
  %4 = getelementptr inbounds %struct.hostent* %0, i32 1 ; <%struct.hostent*> [#uses=1]
  %5 = bitcast %struct.hostent* %4 to i8*         ; <i8*> [#uses=1]
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %5, i8** %6, align 4
  %7 = getelementptr inbounds %struct.hostent* %0, i32 0, i32 0 ; <i8**> [#uses=1]
  %8 = load i8** %7, align 4                      ; <i8*> [#uses=4]
  %9 = tail call i32 @strlen(i8* %8) nounwind readonly ; <i32> [#uses=1]
  %10 = getelementptr inbounds i8* %8, i32 %9     ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %1, i8* %8, i8* %10, i8* %8, i32 1, i32 1) nounwind alwaysinline
  %11 = getelementptr inbounds %struct.hostent* %0, i32 0, i32 1 ; <i8***> [#uses=3]
  %12 = bitcast i8*** %11 to i8*                  ; <i8*> [#uses=1]
  %13 = load i8*** %11                            ; <i8**> [#uses=6]
  %14 = icmp eq i8** %13, null                    ; <i1> [#uses=1]
  br i1 %14, label %bb3, label %bb1.preheader

bb1.preheader:                                    ; preds = %entry
  %15 = load i8** %13                             ; <i8*> [#uses=1]
  %16 = icmp eq i8* %15, null                     ; <i1> [#uses=1]
  br i1 %16, label %bb2, label %bb

bb:                                               ; preds = %bb, %bb1.preheader
  %17 = phi i8** [ %13, %bb1.preheader ], [ %25, %bb ] ; <i8**> [#uses=1]
  %18 = phi i8** [ %13, %bb1.preheader ], [ %25, %bb ] ; <i8**> [#uses=1]
  %19 = phi i32 [ 0, %bb1.preheader ], [ %24, %bb ] ; <i32> [#uses=4]
  %scevgep = getelementptr i8** %18, i32 %19      ; <i8**> [#uses=1]
  %20 = load i8** %scevgep, align 4               ; <i8*> [#uses=1]
  %scevgep18 = getelementptr i8** %17, i32 %19    ; <i8**> [#uses=2]
  %21 = load i8** %scevgep18, align 4             ; <i8*> [#uses=3]
  %22 = tail call i32 @strlen(i8* %21) nounwind readonly ; <i32> [#uses=1]
  %23 = getelementptr inbounds i8* %21, i32 %22   ; <i8*> [#uses=1]
  %scevgep1920 = bitcast i8** %scevgep18 to i8*   ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %scevgep1920, i8* %21, i8* %23, i8* %20, i32 1, i32 1) nounwind alwaysinline
  %24 = add nsw i32 %19, 1                        ; <i32> [#uses=2]
  %25 = load i8*** %11                            ; <i8**> [#uses=5]
  %scevgep21 = getelementptr i8** %25, i32 %24    ; <i8**> [#uses=1]
  %26 = load i8** %scevgep21, align 4             ; <i8*> [#uses=1]
  %27 = icmp eq i8* %26, null                     ; <i1> [#uses=1]
  br i1 %27, label %bb1.bb2_crit_edge, label %bb

bb1.bb2_crit_edge:                                ; preds = %bb
  %phitmp16 = add i32 %19, 2                      ; <i32> [#uses=1]
  br label %bb2

bb2:                                              ; preds = %bb1.bb2_crit_edge, %bb1.preheader
  %28 = phi i8** [ %25, %bb1.bb2_crit_edge ], [ %13, %bb1.preheader ] ; <i8**> [#uses=2]
  %.lcssa = phi i8** [ %25, %bb1.bb2_crit_edge ], [ %13, %bb1.preheader ] ; <i8**> [#uses=1]
  %i.0.lcssa = phi i32 [ %phitmp16, %bb1.bb2_crit_edge ], [ 1, %bb1.preheader ] ; <i32> [#uses=1]
  %29 = getelementptr inbounds i8** %28, i32 %i.0.lcssa ; <i8**> [#uses=1]
  %30 = bitcast i8** %28 to i8*                   ; <i8*> [#uses=1]
  %31 = bitcast i8** %29 to i8*                   ; <i8*> [#uses=1]
  %32 = bitcast i8** %.lcssa to i8*               ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %12, i8* %30, i8* %31, i8* %32, i32 4, i32 1) nounwind alwaysinline
  br label %bb3

bb3:                                              ; preds = %bb2, %entry
  %33 = getelementptr inbounds %struct.hostent* %0, i32 0, i32 4 ; <i8***> [#uses=3]
  %34 = bitcast i8*** %33 to i8*                  ; <i8*> [#uses=1]
  %35 = load i8*** %33                            ; <i8**> [#uses=6]
  %36 = icmp eq i8** %35, null                    ; <i1> [#uses=1]
  br i1 %36, label %return, label %bb5.preheader

bb5.preheader:                                    ; preds = %bb3
  %37 = load i8** %35                             ; <i8*> [#uses=1]
  %38 = icmp eq i8* %37, null                     ; <i1> [#uses=1]
  br i1 %38, label %bb6, label %bb4

bb4:                                              ; preds = %bb4, %bb5.preheader
  %39 = phi i8** [ %35, %bb5.preheader ], [ %47, %bb4 ] ; <i8**> [#uses=1]
  %40 = phi i8** [ %35, %bb5.preheader ], [ %47, %bb4 ] ; <i8**> [#uses=1]
  %41 = phi i32 [ 0, %bb5.preheader ], [ %46, %bb4 ] ; <i32> [#uses=4]
  %scevgep23 = getelementptr i8** %40, i32 %41    ; <i8**> [#uses=1]
  %42 = load i8** %scevgep23, align 4             ; <i8*> [#uses=1]
  %scevgep24 = getelementptr i8** %39, i32 %41    ; <i8**> [#uses=2]
  %43 = load i8** %scevgep24, align 4             ; <i8*> [#uses=3]
  %44 = tail call i32 @strlen(i8* %43) nounwind readonly ; <i32> [#uses=1]
  %45 = getelementptr inbounds i8* %43, i32 %44   ; <i8*> [#uses=1]
  %scevgep2526 = bitcast i8** %scevgep24 to i8*   ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %scevgep2526, i8* %43, i8* %45, i8* %42, i32 1, i32 1) nounwind alwaysinline
  %46 = add nsw i32 %41, 1                        ; <i32> [#uses=2]
  %47 = load i8*** %33                            ; <i8**> [#uses=5]
  %scevgep28 = getelementptr i8** %47, i32 %46    ; <i8**> [#uses=1]
  %48 = load i8** %scevgep28, align 4             ; <i8*> [#uses=1]
  %49 = icmp eq i8* %48, null                     ; <i1> [#uses=1]
  br i1 %49, label %bb5.bb6_crit_edge, label %bb4

bb5.bb6_crit_edge:                                ; preds = %bb4
  %phitmp = add i32 %41, 2                        ; <i32> [#uses=1]
  br label %bb6

bb6:                                              ; preds = %bb5.bb6_crit_edge, %bb5.preheader
  %50 = phi i8** [ %47, %bb5.bb6_crit_edge ], [ %35, %bb5.preheader ] ; <i8**> [#uses=2]
  %.lcssa11 = phi i8** [ %47, %bb5.bb6_crit_edge ], [ %35, %bb5.preheader ] ; <i8**> [#uses=1]
  %i.1.lcssa = phi i32 [ %phitmp, %bb5.bb6_crit_edge ], [ 1, %bb5.preheader ] ; <i32> [#uses=1]
  %51 = getelementptr inbounds i8** %50, i32 %i.1.lcssa ; <i8**> [#uses=1]
  %52 = bitcast i8** %50 to i8*                   ; <i8*> [#uses=1]
  %53 = bitcast i8** %51 to i8*                   ; <i8*> [#uses=1]
  %54 = bitcast i8** %.lcssa11 to i8*             ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %34, i8* %52, i8* %53, i8* %54, i32 1, i32 1) nounwind alwaysinline
  ret void

return:                                           ; preds = %bb3
  ret void
}

declare %struct.hostent* @gethostbyaddr(i8*, i32, i32)

define weak i32 @softbound_scandir(i8* %dir, %struct.dirent*** %namelist, i32 (%struct.dirent*)* %filter, i32 (i8*, i8*)* %compar, i8* %dir_base, i8* %dir_bound, i8* %namelist_base, i8* %namelist_bound, i8* %filter_base, i8* %filter_bound, i8* %compar_base, i8* %compar_bound) nounwind alwaysinline {
entry:
  %0 = bitcast i32 (i8*, i8*)* %compar to i32 (%struct.dirent**, %struct.dirent**)* ; <i32 (%struct.dirent**, %struct.dirent**)*> [#uses=1]
  %1 = tail call i32 @scandir(i8* noalias %dir, %struct.dirent*** noalias %namelist, i32 (%struct.dirent*)* %filter, i32 (%struct.dirent**, %struct.dirent**)* %0) nounwind ; <i32> [#uses=4]
  %2 = icmp eq %struct.dirent*** %namelist, null  ; <i1> [#uses=1]
  br i1 %2, label %bb4, label %bb

bb:                                               ; preds = %entry
  %3 = load %struct.dirent*** %namelist, align 4  ; <%struct.dirent**> [#uses=5]
  %4 = icmp sgt i32 %1, 0                         ; <i1> [#uses=1]
  br i1 %4, label %bb.nph, label %bb3

bb.nph:                                           ; preds = %bb
  %5 = bitcast %struct.dirent** %3 to i8*         ; <i8*> [#uses=1]
  br label %bb1.us

bb1.us:                                           ; preds = %bb1.us, %bb.nph
  %6 = load %struct.dirent** %3, align 4          ; <%struct.dirent*> [#uses=2]
  %7 = getelementptr inbounds %struct.dirent* %6, i32 0, i32 4, i32 0 ; <i8*> [#uses=3]
  %8 = getelementptr inbounds %struct.dirent* %6, i32 0, i32 4, i32 256 ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %7, i8* %7, i8* %8, i8* %7, i32 1, i32 1) nounwind alwaysinline
  %9 = load %struct.dirent** %3, align 4          ; <%struct.dirent*> [#uses=2]
  %10 = getelementptr inbounds %struct.dirent* %9, i32 268 ; <%struct.dirent*> [#uses=1]
  %11 = bitcast %struct.dirent* %9 to i8*         ; <i8*> [#uses=2]
  %12 = bitcast %struct.dirent* %10 to i8*        ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %5, i8* %11, i8* %12, i8* %11, i32 1, i32 1) nounwind alwaysinline
  br label %bb1.us

bb3:                                              ; preds = %bb
  %13 = getelementptr inbounds %struct.dirent** %3, i32 %1 ; <%struct.dirent**> [#uses=1]
  %14 = bitcast %struct.dirent*** %namelist to i8* ; <i8*> [#uses=1]
  %15 = bitcast %struct.dirent** %3 to i8*        ; <i8*> [#uses=2]
  %16 = bitcast %struct.dirent** %13 to i8*       ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %14, i8* %15, i8* %16, i8* %15, i32 8, i32 1) nounwind alwaysinline
  ret i32 %1

bb4:                                              ; preds = %entry
  ret i32 %1
}

declare i32 @scandir(i8* noalias, %struct.dirent*** noalias, i32 (%struct.dirent*)*, i32 (%struct.dirent**, %struct.dirent**)*)

define weak void @softbound_getpwnam(%struct.PtrBaseBound* %ptrs, i8* %name, i8* %name_base, i8* %name_bound) nounwind alwaysinline {
entry:
  %0 = tail call %struct.passwd* @getpwnam(i8* %name) nounwind ; <%struct.passwd*> [#uses=8]
  %1 = bitcast %struct.passwd* %0 to i8*          ; <i8*> [#uses=3]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = icmp eq %struct.passwd* %0, null           ; <i1> [#uses=1]
  %4 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=2]
  br i1 %3, label %bb1, label %bb

bb:                                               ; preds = %entry
  store i8* %1, i8** %4, align 4
  %5 = getelementptr inbounds %struct.passwd* %0, i32 1 ; <%struct.passwd*> [#uses=1]
  %6 = bitcast %struct.passwd* %5 to i8*          ; <i8*> [#uses=1]
  %7 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %6, i8** %7, align 4
  %8 = getelementptr inbounds %struct.passwd* %0, i32 0, i32 0 ; <i8**> [#uses=1]
  %9 = load i8** %8, align 4                      ; <i8*> [#uses=4]
  %10 = tail call i32 @strlen(i8* %9) nounwind readonly ; <i32> [#uses=1]
  %.sum6 = add i32 %10, 1                         ; <i32> [#uses=1]
  %11 = getelementptr inbounds i8* %9, i32 %.sum6 ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %1, i8* %9, i8* %11, i8* %9, i32 0, i32 1) nounwind alwaysinline
  %12 = getelementptr inbounds %struct.passwd* %0, i32 0, i32 1 ; <i8**> [#uses=2]
  %13 = bitcast i8** %12 to i8*                   ; <i8*> [#uses=1]
  %14 = load i8** %12                             ; <i8*> [#uses=4]
  %15 = tail call i32 @strlen(i8* %14) nounwind readonly ; <i32> [#uses=1]
  %.sum5 = add i32 %15, 1                         ; <i32> [#uses=1]
  %16 = getelementptr inbounds i8* %14, i32 %.sum5 ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %13, i8* %14, i8* %16, i8* %14, i32 0, i32 1) nounwind alwaysinline
  %17 = getelementptr inbounds %struct.passwd* %0, i32 0, i32 4 ; <i8**> [#uses=2]
  %18 = bitcast i8** %17 to i8*                   ; <i8*> [#uses=1]
  %19 = load i8** %17                             ; <i8*> [#uses=4]
  %20 = tail call i32 @strlen(i8* %19) nounwind readonly ; <i32> [#uses=1]
  %.sum4 = add i32 %20, 1                         ; <i32> [#uses=1]
  %21 = getelementptr inbounds i8* %19, i32 %.sum4 ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %18, i8* %19, i8* %21, i8* %19, i32 0, i32 1) nounwind alwaysinline
  %22 = getelementptr inbounds %struct.passwd* %0, i32 0, i32 5 ; <i8**> [#uses=2]
  %23 = bitcast i8** %22 to i8*                   ; <i8*> [#uses=1]
  %24 = load i8** %22                             ; <i8*> [#uses=4]
  %25 = tail call i32 @strlen(i8* %24) nounwind readonly ; <i32> [#uses=1]
  %.sum3 = add i32 %25, 1                         ; <i32> [#uses=1]
  %26 = getelementptr inbounds i8* %24, i32 %.sum3 ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %23, i8* %24, i8* %26, i8* %24, i32 0, i32 1) nounwind alwaysinline
  %27 = getelementptr inbounds %struct.passwd* %0, i32 0, i32 6 ; <i8**> [#uses=2]
  %28 = bitcast i8** %27 to i8*                   ; <i8*> [#uses=1]
  %29 = load i8** %27                             ; <i8*> [#uses=4]
  %30 = tail call i32 @strlen(i8* %29) nounwind readonly ; <i32> [#uses=1]
  %.sum = add i32 %30, 1                          ; <i32> [#uses=1]
  %31 = getelementptr inbounds i8* %29, i32 %.sum ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %28, i8* %29, i8* %31, i8* %29, i32 0, i32 1) nounwind alwaysinline
  ret void

bb1:                                              ; preds = %entry
  store i8* null, i8** %4, align 4
  %32 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* null, i8** %32, align 4
  ret void
}

declare %struct.passwd* @getpwnam(i8* nocapture) nounwind

define weak void @softbound_getgrgid(%struct.PtrBaseBound* %ptrs, i32 %gid) nounwind alwaysinline {
entry:
  %0 = tail call %struct.group* @getgrgid(i32 %gid) nounwind ; <%struct.group*> [#uses=2]
  %1 = bitcast %struct.group* %0 to i8*           ; <i8*> [#uses=1]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = icmp eq %struct.group* %0, null            ; <i1> [#uses=1]
  br i1 %3, label %bb5, label %bb

bb:                                               ; preds = %entry
  %4 = tail call %struct.group* @getgrgid(i32 %gid) nounwind ; <%struct.group*> [#uses=4]
  %5 = getelementptr inbounds %struct.group* %4, i32 0, i32 0 ; <i8**> [#uses=1]
  %6 = load i8** %5, align 4                      ; <i8*> [#uses=4]
  %7 = tail call i32 @strlen(i8* %6) nounwind readonly ; <i32> [#uses=1]
  %.sum8 = add i32 %7, 1                          ; <i32> [#uses=1]
  %8 = getelementptr inbounds i8* %6, i32 %.sum8  ; <i8*> [#uses=1]
  %9 = bitcast %struct.group* %4 to i8*           ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %9, i8* %6, i8* %8, i8* %6, i32 1, i32 1) nounwind alwaysinline
  %10 = getelementptr inbounds %struct.group* %4, i32 0, i32 1 ; <i8**> [#uses=2]
  %11 = load i8** %10, align 4                    ; <i8*> [#uses=4]
  %12 = tail call i32 @strlen(i8* %11) nounwind readonly ; <i32> [#uses=1]
  %.sum7 = add i32 %12, 1                         ; <i32> [#uses=1]
  %13 = getelementptr inbounds i8* %11, i32 %.sum7 ; <i8*> [#uses=1]
  %14 = bitcast i8** %10 to i8*                   ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %14, i8* %11, i8* %13, i8* %11, i32 1, i32 1) nounwind alwaysinline
  %15 = getelementptr inbounds %struct.group* %4, i32 0, i32 3 ; <i8***> [#uses=3]
  %16 = load i8*** %15, align 4                   ; <i8**> [#uses=5]
  %17 = icmp eq i8** %16, null                    ; <i1> [#uses=1]
  br i1 %17, label %return, label %bb3.preheader

bb3.preheader:                                    ; preds = %bb
  %18 = load i8** %16, align 4                    ; <i8*> [#uses=1]
  %19 = icmp eq i8* %18, null                     ; <i1> [#uses=1]
  br i1 %19, label %bb4, label %bb2

bb2:                                              ; preds = %bb2, %bb3.preheader
  %20 = phi i32 [ 0, %bb3.preheader ], [ %24, %bb2 ] ; <i32> [#uses=3]
  %scevgep = getelementptr i8** %16, i32 %20      ; <i8**> [#uses=2]
  %scevgep11 = bitcast i8** %scevgep to i8*       ; <i8*> [#uses=1]
  %21 = load i8** %scevgep, align 4               ; <i8*> [#uses=4]
  %22 = tail call i32 @strlen(i8* %21) nounwind readonly ; <i32> [#uses=1]
  %.sum = add i32 %22, 1                          ; <i32> [#uses=1]
  %23 = getelementptr inbounds i8* %21, i32 %.sum ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %scevgep11, i8* %21, i8* %23, i8* %21, i32 1, i32 1) nounwind alwaysinline
  %24 = add nsw i32 %20, 1                        ; <i32> [#uses=2]
  %scevgep12 = getelementptr i8** %16, i32 %24    ; <i8**> [#uses=1]
  %25 = load i8** %scevgep12, align 4             ; <i8*> [#uses=1]
  %26 = icmp eq i8* %25, null                     ; <i1> [#uses=1]
  br i1 %26, label %bb3.bb4_crit_edge, label %bb2

bb3.bb4_crit_edge:                                ; preds = %bb2
  %phitmp = add i32 %20, 2                        ; <i32> [#uses=1]
  %.pre = load i8*** %15, align 4                 ; <i8**> [#uses=1]
  br label %bb4

bb4:                                              ; preds = %bb3.bb4_crit_edge, %bb3.preheader
  %27 = phi i8** [ %.pre, %bb3.bb4_crit_edge ], [ %16, %bb3.preheader ] ; <i8**> [#uses=2]
  %i.0.lcssa = phi i32 [ %phitmp, %bb3.bb4_crit_edge ], [ 1, %bb3.preheader ] ; <i32> [#uses=1]
  %28 = getelementptr inbounds i8** %27, i32 %i.0.lcssa ; <i8**> [#uses=1]
  %29 = bitcast i8*** %15 to i8*                  ; <i8*> [#uses=1]
  %30 = bitcast i8** %27 to i8*                   ; <i8*> [#uses=2]
  %31 = bitcast i8** %28 to i8*                   ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %29, i8* %30, i8* %31, i8* %30, i32 1, i32 1) nounwind alwaysinline
  ret void

bb5:                                              ; preds = %entry
  %32 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* null, i8** %32, align 4
  %33 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* null, i8** %33, align 4
  ret void

return:                                           ; preds = %bb
  ret void
}

declare %struct.group* @getgrgid(i32)

define weak void @softbound_getpwuid(%struct.PtrBaseBound* %ptrs, i32 %uid) nounwind alwaysinline {
entry:
  %0 = tail call %struct.passwd* @getpwuid(i32 %uid) nounwind ; <%struct.passwd*> [#uses=8]
  %1 = bitcast %struct.passwd* %0 to i8*          ; <i8*> [#uses=3]
  %2 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %1, i8** %2, align 4
  %3 = icmp eq %struct.passwd* %0, null           ; <i1> [#uses=1]
  %4 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=2]
  br i1 %3, label %bb1, label %bb

bb:                                               ; preds = %entry
  store i8* %1, i8** %4, align 4
  %5 = getelementptr inbounds %struct.passwd* %0, i32 1 ; <%struct.passwd*> [#uses=1]
  %6 = bitcast %struct.passwd* %5 to i8*          ; <i8*> [#uses=1]
  %7 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %6, i8** %7, align 4
  %8 = getelementptr inbounds %struct.passwd* %0, i32 0, i32 0 ; <i8**> [#uses=1]
  %9 = load i8** %8, align 4                      ; <i8*> [#uses=4]
  %10 = tail call i32 @strlen(i8* %9) nounwind readonly ; <i32> [#uses=1]
  %.sum6 = add i32 %10, 1                         ; <i32> [#uses=1]
  %11 = getelementptr inbounds i8* %9, i32 %.sum6 ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %1, i8* %9, i8* %11, i8* %9, i32 0, i32 1) nounwind alwaysinline
  %12 = getelementptr inbounds %struct.passwd* %0, i32 0, i32 1 ; <i8**> [#uses=2]
  %13 = bitcast i8** %12 to i8*                   ; <i8*> [#uses=1]
  %14 = load i8** %12                             ; <i8*> [#uses=4]
  %15 = tail call i32 @strlen(i8* %14) nounwind readonly ; <i32> [#uses=1]
  %.sum5 = add i32 %15, 1                         ; <i32> [#uses=1]
  %16 = getelementptr inbounds i8* %14, i32 %.sum5 ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %13, i8* %14, i8* %16, i8* %14, i32 0, i32 1) nounwind alwaysinline
  %17 = getelementptr inbounds %struct.passwd* %0, i32 0, i32 4 ; <i8**> [#uses=2]
  %18 = bitcast i8** %17 to i8*                   ; <i8*> [#uses=1]
  %19 = load i8** %17                             ; <i8*> [#uses=4]
  %20 = tail call i32 @strlen(i8* %19) nounwind readonly ; <i32> [#uses=1]
  %.sum4 = add i32 %20, 1                         ; <i32> [#uses=1]
  %21 = getelementptr inbounds i8* %19, i32 %.sum4 ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %18, i8* %19, i8* %21, i8* %19, i32 0, i32 1) nounwind alwaysinline
  %22 = getelementptr inbounds %struct.passwd* %0, i32 0, i32 5 ; <i8**> [#uses=2]
  %23 = bitcast i8** %22 to i8*                   ; <i8*> [#uses=1]
  %24 = load i8** %22                             ; <i8*> [#uses=4]
  %25 = tail call i32 @strlen(i8* %24) nounwind readonly ; <i32> [#uses=1]
  %.sum3 = add i32 %25, 1                         ; <i32> [#uses=1]
  %26 = getelementptr inbounds i8* %24, i32 %.sum3 ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %23, i8* %24, i8* %26, i8* %24, i32 0, i32 1) nounwind alwaysinline
  %27 = getelementptr inbounds %struct.passwd* %0, i32 0, i32 6 ; <i8**> [#uses=2]
  %28 = bitcast i8** %27 to i8*                   ; <i8*> [#uses=1]
  %29 = load i8** %27                             ; <i8*> [#uses=4]
  %30 = tail call i32 @strlen(i8* %29) nounwind readonly ; <i32> [#uses=1]
  %.sum = add i32 %30, 1                          ; <i32> [#uses=1]
  %31 = getelementptr inbounds i8* %29, i32 %.sum ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %28, i8* %29, i8* %31, i8* %29, i32 0, i32 1) nounwind alwaysinline
  ret void

bb1:                                              ; preds = %entry
  store i8* null, i8** %4, align 4
  %32 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* null, i8** %32, align 4
  ret void
}

declare %struct.passwd* @getpwuid(i32)

define weak void @softbound_new_realloc(%struct.PtrBaseBound* %ptrs, i8* %ptr, i32 %size, i8* %ptr_base, i8* %ptr_bound) nounwind alwaysinline {
entry:
  %ptr9 = ptrtoint i8* %ptr to i32                ; <i32> [#uses=1]
  %bound = alloca i8*, align 4                    ; <i8**> [#uses=3]
  %base = alloca i8*, align 4                     ; <i8**> [#uses=3]
  %0 = call i8* @realloc(i8* %ptr, i32 %size) nounwind ; <i8*> [#uses=6]
  %1 = icmp ne i8* %0, %ptr                       ; <i1> [#uses=1]
  %2 = icmp ne i8* %0, null                       ; <i1> [#uses=1]
  %3 = and i1 %1, %2                              ; <i1> [#uses=1]
  %4 = icmp ult i8* %ptr, %ptr_bound              ; <i1> [#uses=1]
  %or.cond = and i1 %3, %4                        ; <i1> [#uses=1]
  br i1 %or.cond, label %bb.nph, label %bb6

bb.nph:                                           ; preds = %entry
  %tmp = sub i32 0, %ptr9                         ; <i32> [#uses=1]
  %scevgep = getelementptr i8* %ptr_bound, i32 %tmp ; <i8*> [#uses=1]
  %scevgep10 = ptrtoint i8* %scevgep to i32       ; <i32> [#uses=1]
  br label %bb

bb:                                               ; preds = %bb4, %bb.nph
  %indvar = phi i32 [ 0, %bb.nph ], [ %indvar.next, %bb4 ] ; <i32> [#uses=3]
  %temp.08 = getelementptr i8* %0, i32 %indvar    ; <i8*> [#uses=2]
  %ptr_addr.07 = getelementptr i8* %ptr, i32 %indvar ; <i8*> [#uses=1]
  store i8* null, i8** %base, align 4
  store i8* null, i8** %bound, align 4
  %5 = call i32 @__hashProbeAddrOfPtr(i8* %ptr_addr.07, i8** %base, i8** %bound) nounwind alwaysinline ; <i32> [#uses=1]
  %6 = icmp eq i32 %5, 0                          ; <i1> [#uses=1]
  br i1 %6, label %bb4, label %bb3

bb3:                                              ; preds = %bb
  %7 = load i8** %bound, align 4                  ; <i8*> [#uses=1]
  %8 = load i8** %base, align 4                   ; <i8*> [#uses=1]
  call void @__hashStoreBaseBound(i8* %temp.08, i8* %8, i8* %7, i8* %temp.08, i32 1, i32 1) nounwind alwaysinline
  br label %bb4

bb4:                                              ; preds = %bb3, %bb
  %indvar.next = add i32 %indvar, 1               ; <i32> [#uses=2]
  %exitcond = icmp eq i32 %indvar.next, %scevgep10 ; <i1> [#uses=1]
  br i1 %exitcond, label %bb6, label %bb

bb6:                                              ; preds = %bb4, %entry
  %9 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %0, i8** %9, align 4
  %10 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %0, i8** %10, align 4
  %11 = getelementptr inbounds i8* %0, i32 %size  ; <i8*> [#uses=1]
  %12 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %11, i8** %12, align 4
  ret void
}

define weak void @softbound_new_memcpy(%struct.PtrBaseBound* %ptrs, i8* %dest, i8* %src, i32 %n, i8* %dest_base, i8* %dest_bound, i8* %src_base, i8* %src_bound) nounwind alwaysinline {
entry:
  %bound = alloca i8*, align 4                    ; <i8**> [#uses=3]
  %base = alloca i8*, align 4                     ; <i8**> [#uses=3]
  call void @llvm.memcpy.i32(i8* %dest, i8* %src, i32 %n, i32 1)
  %0 = icmp eq i32 %n, 0                          ; <i1> [#uses=1]
  br i1 %0, label %bb4, label %bb

bb:                                               ; preds = %bb2, %entry
  %count.05 = phi i32 [ 0, %entry ], [ %5, %bb2 ] ; <i32> [#uses=3]
  %temp2.06 = getelementptr i8* %src, i32 %count.05 ; <i8*> [#uses=2]
  store i8* null, i8** %base, align 4
  store i8* null, i8** %bound, align 4
  %1 = call i32 @__hashProbeAddrOfPtr(i8* %temp2.06, i8** %base, i8** %bound) nounwind alwaysinline ; <i32> [#uses=1]
  %2 = icmp eq i32 %1, 0                          ; <i1> [#uses=1]
  br i1 %2, label %bb2, label %bb1

bb1:                                              ; preds = %bb
  %temp1.07 = getelementptr i8* %dest, i32 %count.05 ; <i8*> [#uses=1]
  %3 = load i8** %bound, align 4                  ; <i8*> [#uses=1]
  %4 = load i8** %base, align 4                   ; <i8*> [#uses=1]
  call void @__hashStoreBaseBound(i8* %temp1.07, i8* %4, i8* %3, i8* %temp2.06, i32 1, i32 1) nounwind alwaysinline
  br label %bb2

bb2:                                              ; preds = %bb1, %bb
  %5 = add i32 %count.05, 1                       ; <i32> [#uses=2]
  %exitcond = icmp eq i32 %5, %n                  ; <i1> [#uses=1]
  br i1 %exitcond, label %bb4, label %bb

bb4:                                              ; preds = %bb2, %entry
  %6 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %dest, i8** %6, align 4
  %7 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %dest_base, i8** %7, align 4
  %8 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %dest_bound, i8** %8, align 4
  ret void
}

declare void @llvm.memcpy.i32(i8* nocapture, i8* nocapture, i32, i32) nounwind

define void @ptr_memcopy(i8** %fake_buffer, i8** %true_buffer, i32 %size) nounwind {
entry:
  %bound = alloca i8*, align 4                    ; <i8**> [#uses=3]
  %base = alloca i8*, align 4                     ; <i8**> [#uses=3]
  %ptr_safe = alloca i32, align 4                 ; <i32*> [#uses=2]
  %0 = icmp eq i32 %size, 0                       ; <i1> [#uses=1]
  br i1 %0, label %return, label %bb

bb:                                               ; preds = %bb, %entry
  %i.03 = phi i32 [ 0, %entry ], [ %7, %bb ]      ; <i32> [#uses=3]
  %scevgep = getelementptr i8** %true_buffer, i32 %i.03 ; <i8**> [#uses=3]
  %scevgep5 = bitcast i8** %scevgep to i8*        ; <i8*> [#uses=1]
  %scevgep4 = getelementptr i8** %fake_buffer, i32 %i.03 ; <i8**> [#uses=3]
  %scevgep46 = bitcast i8** %scevgep4 to i8*      ; <i8*> [#uses=1]
  store i8* null, i8** %base, align 4
  store i8* null, i8** %bound, align 4
  %1 = load i8** %scevgep, align 4                ; <i8*> [#uses=1]
  store i8* %1, i8** %scevgep4, align 4
  %2 = load i8** %scevgep, align 4                ; <i8*> [#uses=1]
  call void @__hashLoadBaseBound(i8* %scevgep5, i8** %base, i8** %bound, i8* %2, i32 8, i32* %ptr_safe) nounwind alwaysinline
  %3 = load i32* %ptr_safe, align 4               ; <i32> [#uses=1]
  %4 = load i8** %scevgep4, align 4               ; <i8*> [#uses=1]
  %5 = load i8** %bound, align 4                  ; <i8*> [#uses=1]
  %6 = load i8** %base, align 4                   ; <i8*> [#uses=1]
  call void @__hashStoreBaseBound(i8* %scevgep46, i8* %6, i8* %5, i8* %4, i32 8, i32 %3) nounwind alwaysinline
  %7 = add i32 %i.03, 1                           ; <i32> [#uses=2]
  %exitcond = icmp eq i32 %7, %size               ; <i1> [#uses=1]
  br i1 %exitcond, label %return, label %bb

return:                                           ; preds = %bb, %entry
  ret void
}

define weak void @softbound_changed_realloc(%struct.PtrBaseBound* %ptrs, i8** %current_ptr, i32 %n_gathers, i8* %current_ptr_base, i8* %current_ptr_bound) nounwind alwaysinline {
entry:
  %bound.i = alloca i8*, align 4                  ; <i8**> [#uses=3]
  %base.i = alloca i8*, align 4                   ; <i8**> [#uses=3]
  %ptr_safe.i = alloca i32, align 4               ; <i32*> [#uses=2]
  %0 = malloc i8*, i32 %n_gathers                 ; <i8**> [#uses=2]
  %tmpcast = bitcast i8** %0 to i8*               ; <i8*> [#uses=3]
  %1 = ptrtoint i8* %current_ptr_bound to i32     ; <i32> [#uses=1]
  %2 = ptrtoint i8* %current_ptr_base to i32      ; <i32> [#uses=1]
  %3 = sub i32 %1, %2                             ; <i32> [#uses=2]
  %.mask = and i32 %3, -4                         ; <i32> [#uses=1]
  %4 = icmp eq i32 %.mask, 4                      ; <i1> [#uses=1]
  br i1 %4, label %ptr_memcopy.exit, label %bb.i.preheader

bb.i.preheader:                                   ; preds = %entry
  %tmp2 = lshr i32 %3, 2                          ; <i32> [#uses=1]
  %tmp3 = add i32 %tmp2, -1                       ; <i32> [#uses=1]
  br label %bb.i

bb.i:                                             ; preds = %bb.i, %bb.i.preheader
  %i.03.i = phi i32 [ 0, %bb.i.preheader ], [ %10, %bb.i ] ; <i32> [#uses=3]
  %scevgep4.i = getelementptr i8** %0, i32 %i.03.i ; <i8**> [#uses=3]
  %scevgep46.i = bitcast i8** %scevgep4.i to i8*  ; <i8*> [#uses=1]
  %scevgep.i = getelementptr i8** %current_ptr, i32 %i.03.i ; <i8**> [#uses=2]
  %scevgep5.i = bitcast i8** %scevgep.i to i8*    ; <i8*> [#uses=1]
  store i8* null, i8** %base.i, align 4
  store i8* null, i8** %bound.i, align 4
  %5 = load i8** %scevgep.i, align 4              ; <i8*> [#uses=2]
  store i8* %5, i8** %scevgep4.i, align 4
  call void @__hashLoadBaseBound(i8* %scevgep5.i, i8** %base.i, i8** %bound.i, i8* %5, i32 8, i32* %ptr_safe.i) nounwind alwaysinline
  %6 = load i32* %ptr_safe.i, align 4             ; <i32> [#uses=1]
  %7 = load i8** %scevgep4.i, align 4             ; <i8*> [#uses=1]
  %8 = load i8** %bound.i, align 4                ; <i8*> [#uses=1]
  %9 = load i8** %base.i, align 4                 ; <i8*> [#uses=1]
  call void @__hashStoreBaseBound(i8* %scevgep46.i, i8* %9, i8* %8, i8* %7, i32 8, i32 %6) nounwind alwaysinline
  %10 = add i32 %i.03.i, 1                        ; <i32> [#uses=2]
  %exitcond = icmp eq i32 %10, %tmp3              ; <i1> [#uses=1]
  br i1 %exitcond, label %ptr_memcopy.exit, label %bb.i

ptr_memcopy.exit:                                 ; preds = %bb.i, %entry
  free i8** %current_ptr
  %11 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 0 ; <i8**> [#uses=1]
  store i8* %tmpcast, i8** %11, align 4
  %12 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 1 ; <i8**> [#uses=1]
  store i8* %tmpcast, i8** %12, align 4
  %13 = shl i32 %n_gathers, 2                     ; <i32> [#uses=1]
  %14 = getelementptr inbounds i8* %tmpcast, i32 %13 ; <i8*> [#uses=1]
  %15 = getelementptr inbounds %struct.PtrBaseBound* %ptrs, i32 0, i32 2 ; <i8**> [#uses=1]
  store i8* %14, i8** %15, align 4
  ret void
}

define weak i32 @softbound_strtol(i8* %nptr, i8** %endptr, i32 %base, i8* %nptr_base, i8* %nptr_bound, i8* %endptr_base, i8* %endptr_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @strtol(i8* noalias %nptr, i8** noalias %endptr, i32 %base) nounwind ; <i32> [#uses=1]
  %1 = load i8** %endptr, align 4                 ; <i8*> [#uses=4]
  %2 = tail call i32 @strlen(i8* %1) nounwind readonly ; <i32> [#uses=1]
  %.sum = add i32 %2, 1                           ; <i32> [#uses=1]
  %3 = getelementptr inbounds i8* %1, i32 %.sum   ; <i8*> [#uses=1]
  %4 = bitcast i8** %endptr to i8*                ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %4, i8* %1, i8* %3, i8* %1, i32 1, i32 1) nounwind alwaysinline
  ret i32 %0
}

define weak i32 @softbound_strtoul(i8* %nptr, i8** %endptr, i32 %base, i8* %nptr_base, i8* %nptr_bound, i8* %endptr_base, i8* %endptr_bound) nounwind alwaysinline {
entry:
  %0 = tail call i32 @strtoul(i8* noalias %nptr, i8** noalias %endptr, i32 %base) nounwind ; <i32> [#uses=1]
  %1 = load i8** %endptr, align 4                 ; <i8*> [#uses=4]
  %2 = tail call i32 @strlen(i8* %1) nounwind readonly ; <i32> [#uses=1]
  %.sum = add i32 %2, 1                           ; <i32> [#uses=1]
  %3 = getelementptr inbounds i8* %1, i32 %.sum   ; <i8*> [#uses=1]
  %4 = bitcast i8** %endptr to i8*                ; <i8*> [#uses=1]
  tail call void @__hashStoreBaseBound(i8* %4, i8* %1, i8* %3, i8* %1, i32 1, i32 1) nounwind alwaysinline
  ret i32 %0
}

declare i32 @strtoul(i8* noalias, i8** noalias nocapture, i32) nounwind

define weak void @__softboundcetswithss_deallocate_shadow_stack_space() nounwind alwaysinline {
entry:
  %0 = load i32** @__softboundcetswithss_shadow_stack_ptr, align 4 ; <i32*> [#uses=2]
  %1 = load i32* %0, align 4                      ; <i32> [#uses=2]
  %2 = icmp ugt i32 %1, 4096                      ; <i1> [#uses=1]
  br i1 %2, label %bb, label %bb1

bb:                                               ; preds = %entry
  tail call void @__assert_fail(i8* getelementptr inbounds ([77 x i8]* @.str3, i32 0, i32 0), i8* getelementptr inbounds ([34 x i8]* @.str4, i32 0, i32 0), i32 282, i8* getelementptr inbounds ([52 x i8]* @__PRETTY_FUNCTION__.6393, i32 0, i32 0)) noreturn nounwind
  unreachable

bb1:                                              ; preds = %entry
  %.sum = sub i32 -2, %1                          ; <i32> [#uses=1]
  %3 = getelementptr inbounds i32* %0, i32 %.sum  ; <i32*> [#uses=1]
  store i32* %3, i32** @__softboundcetswithss_shadow_stack_ptr, align 4
  ret void
}

declare void @__assert_fail(i8*, i8*, i32, i8*) noreturn nounwind

define internal void @__softbound_global_init() nounwind {
entry:
  tail call void @__softbound_init(i32 1, i32 0) nounwind
  ret void
}

declare void @__softbound_init(i32, i32)
