From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/loop_annot.c]. *)
Section code.
  (* Global variables. *)
  
  (* Functions. *)
  Context (main : loc).
  

  (* Definition of function [main]. *)
  Definition impl_main : function := {|
    f_args := [
    ];
    f_local_vars := [
      ("i", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        Goto "#1"
      ]> $
      <[ "#1" :=
        if: UnOp (CastOp $ IntOp bool_it) (IntOp i32) (i2v 1 i32)
        then
        "i" <-{ it_layout i32 }
          (use{it_layout i32} ("i")) +{IntOp i32, IntOp i32} (i2v 1 i32) ;
          Goto "continue2"
        else
        Goto "#2"
      ]> $
      <[ "#2" :=
        Goto "#3"
      ]> $
      <[ "#3" :=
        "i" <-{ it_layout i32 }
          (use{it_layout i32} ("i")) +{IntOp i32, IntOp i32} (i2v 1 i32) ;
        Goto "continue4"
      ]> $
      <[ "#4" :=
        Return (i2v 0 i32)
      ]> $
      <[ "continue2" :=
        Goto "#1"
      ]> $
      <[ "continue4" :=
        if: UnOp (CastOp $ IntOp bool_it) (IntOp i32) (i2v 1 i32)
        then
        Goto "#3"
        else
        Goto "#4"
      ]> $∅
    )%E
  |}.
End code.
