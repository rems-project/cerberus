open AilTypes
open Colour

module P = PPrint
let (!^ ) = P.(!^)
let (^^)  = P.(^^)
let (^/^) = P.(^/^)

let (^^^) x y = x ^^ P.space ^^ y
let comma_list f = P.separate_map (P.comma ^^ P.space) f


let pp_id id = !^ (Pp_symbol.to_string_pretty id)

let pp_ctor w = pp_ansi_format [Bold; Cyan] (!^ w)


let pp_integerBaseType_raw = function
  | Ichar ->
      pp_ctor "Ichar"
  | Short ->
      pp_ctor "Short"
  | Int_ ->
      pp_ctor "Int_"
  | Long ->
      pp_ctor "Long"
  | LongLong ->
      pp_ctor "LongLong"
  | IntN_t n ->
      pp_ctor "IntN_t" ^^ P.brackets (!^ (string_of_int n))
  | Int_leastN_t n ->
      pp_ctor "Int_leastN_t" ^^ P.brackets (!^ (string_of_int n))
  | Int_fastN_t n ->
      pp_ctor "Int_fastN_t" ^^ P.brackets (!^ (string_of_int n))
  | Intmax_t ->
      pp_ctor "Intmax_t"
  | Intptr_t ->
      pp_ctor "Intptr_t"


let pp_integerType_raw = function
 | Char ->
     pp_ctor "Char"
 | Bool ->
     pp_ctor "Bool"
 | Signed ibty ->
     pp_ctor "Signed" ^^ P.brackets (pp_integerBaseType_raw ibty)
 | Unsigned ibty ->
     pp_ctor "Unsigned" ^^ P.brackets (pp_integerBaseType_raw ibty)
 | IBuiltin str ->
     pp_ctor str
 | Enum sym ->
     pp_ctor "enum" ^^^ pp_id sym
 | Size_t ->
     pp_ctor "Size_t"
 | Ptrdiff_t ->
     pp_ctor "Ptrdiff_t"



let pp_realFloatingType_raw = function
  | Float ->
      pp_ctor "Float"
  | Double ->
      pp_ctor "Double"
  | LongDouble ->
      pp_ctor "LongDouble"

let pp_floatingType_raw = function
  | RealFloating rfty ->
      pp_ctor "RealFloating" ^^ P.brackets(pp_realFloatingType_raw rfty)

let pp_basicType_raw = function
  | Integer ity ->
      pp_ctor "Integer" ^^ P.brackets (pp_integerType_raw ity)
  | Floating fty ->
      pp_ctor "Floating" ^^ P.brackets (pp_floatingType_raw fty)

let pp_qualifiers_raw qs =
  P.braces (
    List.fold_left (fun acc (str, b) ->
      if b then pp_ctor str ^^ P.comma ^^^ acc else acc
    ) P.empty [("const", qs.const); ("restrict", qs.restrict); ("volatile", qs.volatile) (*; ("atomic", qs.atomic)*)]
 )

let pp_integer i = P.string (Nat_big_num.to_string i)

let rec pp_ctype_raw = function
  | Void ->
      pp_ctor "Void"
  | Basic bty ->
      pp_ctor "Basic" ^^ P.brackets (pp_basicType_raw bty)
  | Array (qs, ty, None) ->
      pp_ctor "Array" ^^ P.brackets (pp_qualifiers_raw qs ^^ P.comma ^^^ pp_ctype_raw ty ^^ P.comma ^^^ pp_ctor "None")
  | Array (qs, ty, Some n) ->
      pp_ctor "Array" ^^ P.brackets (pp_qualifiers_raw qs ^^ P.comma ^^^ pp_ctype_raw ty ^^ P.comma ^^^ pp_ctor "Some" ^^ P.brackets (pp_integer n))
  | Function (has_proto, ty, params, is_variadic) ->
      pp_ctor "Function" ^^ P.brackets (
        !^ (if has_proto then "true" else "false") ^^ P.comma ^^^
        comma_list (fun (qs, ty, isRegister) -> 
          P.parens (pp_qualifiers_raw qs ^^ P.comma ^^^ pp_ctype_raw ty ^^
                    P.comma ^^^ !^ (if isRegister then "true" else "false"))
        ) params ^^ P.comma ^^
                                   !^ (if is_variadic then "true" else "false"))
  | Pointer (ref_qs, ref_ty) ->
      pp_ctor "Pointer" ^^ P.brackets (pp_qualifiers_raw ref_qs ^^ P.comma ^^^ pp_ctype_raw ref_ty)
  | Atomic ty ->
      pp_ctor "Atomic" ^^ P.brackets (pp_ctype_raw ty)
  | Struct sym ->
      pp_ctor "Struct" ^^^ pp_id sym
  | Union sym ->
      pp_ctor "Union" ^^^ pp_id sym
  | Builtin str ->
      pp_ctor "Builtin" ^^ P.brackets (!^ str)
