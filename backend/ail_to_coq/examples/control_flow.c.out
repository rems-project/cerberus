From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/control_flow.c]. *)
Section code.
  (* Global variables. *)
  
  (* Functions. *)
  Context (main : loc).
  

  (* Definition of function [main]. *)
  Definition impl_main : function := {|
    f_args := [
    ];
    f_local_vars := [
      ("i", it_layout i32);
      ("toplevel", it_layout i32);
      ("nested", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        if: UnOp (CastOp $ IntOp bool_it) (IntOp i32) (i2v 1 i32)
        then
        expr: (i2v 1 i32) ;
          Goto "#5"
        else
        Goto "#5"
      ]> $
      <[ "#1" :=
        if: UnOp (CastOp $ IntOp bool_it) (IntOp i32) (i2v 1 i32)
        then
        expr: (i2v 2 i32) ;
          Goto "continue3"
        else
        Goto "#2"
      ]> $
      <[ "#2" :=
        "i" <-{ it_layout i32 } i2v 0 i32 ;
        Goto "#3"
      ]> $
      <[ "#3" :=
        if: UnOp (CastOp $ IntOp bool_it) (IntOp i32) ((use{it_layout i32} ("i")) <{IntOp i32, IntOp i32} (use{it_layout i32} ("toplevel")))
        then
        expr: (i2v 3 i32) ;
          Goto "continue5"
        else
        Goto "#4"
      ]> $
      <[ "#4" :=
        Return (VOID)
      ]> $
      <[ "#5" :=
        Goto "#1"
      ]> $
      <[ "continue3" :=
        Goto "#1"
      ]> $
      <[ "continue5" :=
        "i" <-{ it_layout i32 }
          (use{it_layout i32} ("i")) +{IntOp i32, IntOp i32} (i2v 1 i32) ;
        Goto "#3"
      ]> $∅
    )%E
  |}.
End code.
