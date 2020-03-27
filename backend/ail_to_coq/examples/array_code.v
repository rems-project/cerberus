From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/array.c]. *)
Section code.
  (* Global variables. *)
  
  (* Functions. *)
  Context (main : loc).
  Context (test : loc).
  
  (* Definition of struct [S]. *)
  Program Definition struct_S := {|
    sl_members := [
      ("i", it_layout i32);
      ("b", mk_array_layout (it_layout i32) 2);
      ("c", LPtr);
      ("d", LPtr)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.
  

  (* Definition of function [main]. *)
  Definition impl_main : function := {|
    f_args := [
    ];
    f_local_vars := [
      ("c", LPtr);
      ("f", LPtr);
      ("d", LPtr);
      ("b", layout_of struct_S);
      ("nested", mk_array_layout (mk_array_layout (layout_of struct_S) 2) 1);
      ("a", mk_array_layout (layout_of struct_S) 5)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        expr: (use{layout_of struct_S} (("a") at_offset{layout_of struct_S, PtrOp, IntOp i32} (i2v 0 i32))) ;
        expr: (use{it_layout i32} ((("a") at_offset{layout_of struct_S, PtrOp, IntOp i32} (i2v 0 i32)) at{struct_S} "i")) ;
        expr: (use{it_layout i32} (("b") at{struct_S} "i")) ;
        expr: (use{it_layout i32} ((!{LPtr} ("c")) at{struct_S} "i")) ;
        expr: (use{it_layout i32} ((!{LPtr} (("c") at_offset{layout_of struct_S, PtrOp, IntOp i32} (i2v 0 i32))) at{struct_S} "i")) ;
        expr: (use{it_layout i32} ((!{LPtr} (("a") at_offset{layout_of struct_S, PtrOp, IntOp i32} (i2v 0 i32))) at{struct_S} "i")) ;
        expr: (use{it_layout i32} (((!{LPtr} ("d")) at_offset{layout_of struct_S, PtrOp, IntOp i32} (i2v 0 i32)) at{struct_S} "i")) ;
        expr: (use{it_layout i32} (((!{LPtr} ("f")) at_offset{layout_of struct_S, PtrOp, IntOp i32} (i2v 0 i32)) at{struct_S} "i")) ;
        (("a") at_offset{layout_of struct_S, PtrOp, IntOp i32} (i2v 0 i32)) at{struct_S} "i" <-{ it_layout i32 }
          i2v 1 i32 ;
        Return (i2v 0 i32)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test]. *)
  Definition impl_test : function := {|
    f_args := [
      ("a", LPtr);
      ("b", LPtr);
      ("c", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        Return (i2v 0 i32)
      ]> $∅
    )%E
  |}.
End code.
