
Require Import Coq.Numbers.BinNums.
Require Import Coq.Strings.String.

Module Type PTRADDR.

  Parameter Inline t:Set.

  Parameter bitwise_complement: t -> t.

  Parameter eqb: t -> t -> bool.
  Parameter ltb: t -> t -> bool.
  Parameter leb: t -> t -> bool.
  Parameter ltb_irref: forall a:t, ltb a a = false.

  Parameter to_string: t -> string.       

End PTRADDR.
