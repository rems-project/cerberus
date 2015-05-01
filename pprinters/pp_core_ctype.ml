open Core_ctype


module P = PPrint

let (!^ ) = P.(!^)
let (^^)  = P.(^^)
let (^/^) = P.(^/^)

let (^^^) x y = x ^^ P.space ^^ y
let comma_list f = P.separate_map (P.comma ^^ P.space) f



let pp_symbol  a = !^ (Pp_symbol.to_string_pretty a)

let pp_integer_base_ctype ibty =
  let open AilTypes in
  match ibty with
    | Ichar         -> !^ "ichar"
    | Short         -> !^ "short"
    | Int_          -> !^ "int"
    | Long          -> !^ "long"
    | LongLong      -> !^ "long_long"
    | IBBuiltin str -> !^ str


let pp_integer_ctype ity =
  let open AilTypes in
  match ity with
    | Char             -> !^ "char"
    | Bool             -> !^ "_Bool"
    | Signed (IBBuiltin (("int8_t" | "int16_t" | "int32_t" | "int64_t") as str)) ->
        !^ str
    | Unsigned (IBBuiltin (("int8_t" | "int16_t" | "int32_t" | "int64_t") as str)) ->
        !^ ("u" ^ str)
    | Signed ibty      -> !^ "signed"   ^^^ pp_integer_base_ctype ibty
    | Unsigned ibty    -> !^ "unsigned" ^^^ pp_integer_base_ctype ibty
    | IBuiltin str     -> !^ str
    | Enum sym         -> !^ "enum" ^^^ pp_symbol sym

let pp_floating_ctype fty =
  let open AilTypes in
  match fty with
    | RealFloating Float ->
        !^ "float"
    | RealFloating Double ->
        !^ "double"
    | RealFloating LongDouble ->
        !^ "long_double"


let pp_basic_ctype bty =
  let open AilTypes in
  match bty with
    | Integer ity -> pp_integer_ctype ity
    | Floating fty -> pp_floating_ctype fty

let rec pp_ctype = function
(*   let pp_mems = P.concat_map (fun (name, mbr) -> (pp_member mbr) name) in *)

  | Void0 ->
      !^ "void"
  | Basic0 bty ->
      pp_basic_ctype bty
  | Array0 (elem_ty, n_opt) ->
      pp_ctype elem_ty ^^ P.brackets (P.optional Pp_ail.pp_integer n_opt)
  | Function0 (return_ty, args_tys, is_variadic) ->
        pp_ctype return_ty ^^^ P.parens (
          comma_list (fun (qs, ty) -> Pp_ail.pp_qualifiers qs (pp_ctype ty)) args_tys ^^
          (if is_variadic then P.comma ^^^ P.dot ^^ P.dot ^^ P.dot else P.empty)
        )
  | Pointer0 (qs, ref_ty) ->
      Pp_ail.pp_qualifiers qs (pp_ctype ref_ty) ^^ P.star
  | Atomic0 atom_ty ->
      !^ "_Atomic" ^^^ P.parens (pp_ctype atom_ty)
  | Struct0 sym ->
      !^ "struct" ^^^ Pp_ail.pp_id sym
  | Union0 sym ->
      !^ "union" ^^^ Pp_ail.pp_id sym
  | Builtin0 str ->
      !^ str


(*
and pp_member = function
  | Core_ctype.MEMBER ty ->
      fun z -> pp_ctype ty ^^^ Pp_ail.pp_id z ^^ P.semi
  | Core_ctype.BITFIELD (ty, w, _) ->
      fun z -> pp_ctype ty ^^^ Pp_ail.pp_id z ^^ P.colon ^^^ Pp_ail.pp_integer w ^^ P.semi
 *)
