Require Import Implementation.
Require Import Ctype.

Module AilTypesAux(IMP: Implementation).

  Fixpoint is_signed_ity (fuel:nat) (ity:integerType) : option bool
    :=
    match fuel with
    | O => None
    | S fuel =>
        match ity with
        | Char => Some (IMP.get.(Implementation.is_signed_ity) Char)
        | Bool => Some false
        | Signed _ => Some true
        | Unsigned _ => Some false
        | Enum tag_sym => @is_signed_ity fuel (IMP.get.(typeof_enum) tag_sym)
        | Size_t =>  Some false
        | Wchar_t => Some (IMP.get.(Implementation.is_signed_ity) Wchar_t)
        | Wint_t =>  Some (IMP.get.(Implementation.is_signed_ity) Wint_t)
        | Ptrdiff_t => Some true
        | Vaddr_t => Some false
        end
    end.

End AilTypesAux.
