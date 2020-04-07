From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/int.c]. *)
Section code.
  (* Global variables. *)

  (* Functions. *)
  Context (f : loc).
  Context (main : loc).

  (* Definition of function [f]. *)
  Definition impl_f : function := {|
    f_args := [
      ("i", it_layout i32);
      ("c", it_layout u8)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        Return (UnOp (CastOp $ IntOp i64) (IntOp i32) (use{it_layout i32} ("i")))
      ]> $∅
    )%E
  |}.

  (* Definition of function [main]. *)
  Definition impl_main : function := {|
    f_args := [
    ];
    f_local_vars := [
      ("i", it_layout i32);
      ("c", it_layout u8);
      ("ull", it_layout u64);
      ("sc", it_layout i8);
      ("sll", it_layout i64);
      ("uc", it_layout u8);
      ("us", it_layout u16);
      ("ui", it_layout u32);
      ("uptr", it_layout size_t);
      ("s", it_layout i16);
      ("sl", it_layout i64);
      ("ll", it_layout i64);
      ("ss", it_layout i16);
      ("si", it_layout i32);
      ("l", it_layout i64);
      ("ul", it_layout u64);
      ("iptr", LPtr);
      ("st", it_layout size_t);
      ("ptr", it_layout ssize_t);
      ("b", it_layout bool_it)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "c" <-{ it_layout u8 }
          UnOp (CastOp $ IntOp u8) (IntOp i32) (i2v 0 i32) ;
        "ull" <-{ it_layout u64 }
          UnOp (CastOp $ IntOp u64) (IntOp i64) (i2v 0 i64) ;
        "ull" <-{ it_layout u64 }
          UnOp (CastOp $ IntOp u64) (IntOp i64) (i2v 0 i64) ;
        "ull" <-{ it_layout u64 } i2v 0 u64 ;
        "ull" <-{ it_layout u64 } i2v 0 u64 ;
        "i" <-{ it_layout i32 }
          (UnOp (CastOp $ IntOp i32) (IntOp u8) (use{it_layout u8} ("c"))) +{IntOp i32, IntOp i32} (UnOp (CastOp $ IntOp i32) (IntOp u8) (use{it_layout u8} ("c"))) ;
        "i" <-{ it_layout i32 }
          UnOp (CastOp $ IntOp i32) (IntOp u64) ((UnOp (CastOp $ IntOp u64) (IntOp i32) (use{it_layout i32} ("i"))) +{IntOp u64, IntOp u64} (use{it_layout u64} ("ull"))) ;
        "i" <-{ it_layout i32 }
          UnOp (CastOp $ IntOp i32) (IntOp u8) (UnOp (CastOp $ IntOp u8) (IntOp i64) (use{it_layout i64} ("ll"))) ;
        "b" <-{ it_layout bool_it }
          UnOp (CastOp $ IntOp bool_it) (IntOp i32) (i2v 1 i32) ;
        "b" <-{ it_layout bool_it }
          UnOp (CastOp $ IntOp bool_it) (IntOp i32) (i2v 0 i32) ;
        "b" <-{ it_layout bool_it }
          UnOp (CastOp $ IntOp bool_it) (IntOp i32) ((use{it_layout i64} ("l")) ={IntOp i64, IntOp i64} (use{it_layout i64} ("l"))) ;
        "b" <-{ it_layout bool_it }
          UnOp (CastOp $ IntOp bool_it) (IntOp i32) ((UnOp (CastOp $ IntOp i64) (IntOp i32) (use{it_layout i32} ("i"))) ={IntOp i64, IntOp i64} (use{it_layout i64} ("l"))) ;
        "b" <-{ it_layout bool_it }
          UnOp (CastOp $ IntOp bool_it) (IntOp i64) ((use{it_layout i64} ("l")) +{IntOp i64, IntOp i64} (use{it_layout i64} ("l"))) ;
        "b" <-{ it_layout bool_it }
          UnOp (CastOp $ IntOp bool_it) (IntOp i64) ((UnOp (CastOp $ IntOp i64) (IntOp i32) (use{it_layout i32} ("i"))) +{IntOp i64, IntOp i64} (use{it_layout i64} ("l"))) ;
        if: UnOp (CastOp $ IntOp bool_it) (IntOp i32) ((use{it_layout i64} ("l")) ={IntOp i64, IntOp i64} (use{it_layout i64} ("l")))
        then
        assert: (UnOp (CastOp $ IntOp bool_it) (IntOp i32) ((use{it_layout i64} ("l")) ={IntOp i64, IntOp i64} (use{it_layout i64} ("l")))) ;
          Goto "#1"
        else
        Goto "#1"
      ]> $
      <[ "#1" :=
        "$0" <- f with
          [ UnOp (CastOp $ IntOp i32) (IntOp u8) (use{it_layout u8} ("c")) ;
              UnOp (CastOp $ IntOp u8) (IntOp i64) (use{it_layout i64} ("l"))  ] ;
        "i" <-{ it_layout i32 }
          UnOp (CastOp $ IntOp i32) (IntOp i64) ("$0") ;
        expr: (UnOp (CastOp $ PtrOp) (PtrOp) (use{LPtr} ("iptr"))) ;
        Return (i2v 0 i32)
      ]> $∅
    )%E
  |}.
End code.
