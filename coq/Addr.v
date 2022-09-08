Require Import Coq.Numbers.BinNums.

  Module Type VADDR.

    Parameter Inline t:Set.

    Parameter bitwise_complement: t -> t.

    Parameter ltb: t -> t -> bool.
    Parameter leb: t -> t -> bool.
    Parameter ltb_irref: forall a:t, ltb a a = false.

  End VADDR.
