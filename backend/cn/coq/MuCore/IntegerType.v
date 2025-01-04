Require Import Symbol.

Inductive integerBaseType : Type :=
 | Ichar: integerBaseType
 | Short: integerBaseType
 | Int_: integerBaseType
 | Long: integerBaseType
 | LongLong: integerBaseType
   (* Things defined in the standard libraries *)
 | IntN_t:  nat  -> integerBaseType
 | Int_leastN_t:  nat  -> integerBaseType
 | Int_fastN_t:  nat  -> integerBaseType
 | Intmax_t: integerBaseType
 | Intptr_t: integerBaseType.

(* STD Â§6.2.5#17, sentence 1 *)
Inductive integerType : Type := (* [name = "^\\(\\|\\([a-z A-Z]+_\\)\\)ity[0-9]*'?$"] *)
 | Char: integerType
 | Bool: integerType
 | Signed:  integerBaseType  -> integerType
 | Unsigned:  integerBaseType  -> integerType
 | Enum:  sym  -> integerType
   (* Things defined in the standard libraries *)
 | Wchar_t: integerType
 | Wint_t: integerType
 | Size_t: integerType
 | Ptrdiff_t: integerType
 | Ptraddr_t: integerType .
