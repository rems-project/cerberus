Require Import AilTypes.
Require Import Implementation.

(* defns JisSigned *)
Inductive signed : implementation -> integerType -> Prop :=    (* defn isSigned *)
 | Signed_Int : forall (P:implementation) (ibt:integerBaseType),
     signed P (Signed ibt)
 | Signed_Char : forall (P:implementation),
     Implementation.signed P Char = true  ->
     signed P Char.
