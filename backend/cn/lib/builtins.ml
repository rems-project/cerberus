module SBT = SurfaceBaseTypes
open Resultat

open Effectful.Make (Resultat)

open TypeErrors
open IndexTerms
module CF = Cerb_frontend

type builtin_fn_def = string * Sym.t * LogicalFunctions.definition

let loc = Cerb_location.other "<builtin>"

(* builtin function symbols *)

let mk_arg1 mk args loc =
  match args with
  | [ x ] -> return (mk x loc)
  | xs -> fail { loc; msg = Number_arguments { has = List.length xs; expect = 1 } }


let mk_arg2_err mk args loc =
  match args with
  | [ x; y ] -> mk (x, y) loc
  | xs -> fail { loc; msg = Number_arguments { has = List.length xs; expect = 2 } }


let mk_arg2 mk = mk_arg2_err (fun tup loc -> return (mk tup loc))

let mk_arg3_err mk args loc =
  match args with
  | [ x; y; z ] -> mk (x, y, z) loc
  | xs -> fail { loc; msg = Number_arguments { has = List.length xs; expect = 3 } }


let mk_arg3 mk = mk_arg3_err (fun tup loc -> return (mk tup loc))

let var_binop op ty ~left:(sym1, bt1) ~right:(sym2, bt2) =
  binop op (sym_ (sym1, bt1, loc), sym_ (sym2, bt2, loc)) loc ty


let definition name args body =
  ( name,
    Sym.fresh_named name,
    LogicalFunctions.
      { loc; emit_coq = false; args; definition = Def body; return_bt = bt body } )


let mk_builtin_arg0 name = definition name []

let mk_builtin_arg1 name bt mk : builtin_fn_def =
  let arg = (Sym.fresh_named "arg", bt) in
  mk arg |> definition name [ arg ]


let mk_builtin_arg2 name (bt1, bt2) mk : builtin_fn_def =
  let left = (Sym.fresh_named "arg1", bt1) in
  let right = (Sym.fresh_named "arg2", bt2) in
  mk ~left ~right |> definition name [ left; right ]


let min_bits_def (sign, n) =
  let num, letter =
    match sign with
    | BT.Unsigned -> (Z.zero, "u")
    | Signed -> (Z.(neg @@ shift_left one (Int.sub n 1)), "i")
  in
  let name = "MIN" ^ letter ^ Int.to_string n in
  num_lit_ num (BT.Bits (sign, n)) loc |> mk_builtin_arg0 name


let max_bits_def (sign, n) =
  let num, letter =
    match sign with
    | BT.Unsigned -> (Z.(shift_left one n - one), "u")
    | Signed -> (Z.(shift_left one (Int.sub n 1) - one), "i")
  in
  let name = "MAX" ^ letter ^ Int.to_string n in
  num_lit_ num (BT.Bits (sign, n)) loc |> mk_builtin_arg0 name


let max_min_bits =
  let sizes = [ 8; 16; 32; 64 ] in
  let signs = [ BT.Unsigned; Signed ] in
  List.fold_left
    (fun acc sign ->
      List.fold_left
        (fun acc size -> max_bits_def (sign, size) :: min_bits_def (sign, size) :: acc)
        acc
        sizes)
    []
    signs


let not_def =
  mk_builtin_arg1 "not" BT.Bool (fun (sym, bt) -> not_ (sym_ (sym, bt, loc)) loc)


let is_null_def : builtin_fn_def =
  mk_builtin_arg1 "is_null" BT.Loc (fun (sym, bt) ->
    (eq__ (sym_ (sym, bt, loc)) (null_ loc)) loc)


(* Cannot translate this to a logical function until the TODO in `cn_to_ail_expr_aux_internal` in `cn_internal_to_ail.ml` is resolved*)
let has_alloc_id_def =
  ( "has_alloc_id",
    Sym.fresh_named "has_alloc_id",
    mk_arg1 (fun p loc' -> IT.sterm_of_term @@ IT.hasAllocId_ (IT.term_of_sterm p) loc')
  )


let ptr_eq_def : builtin_fn_def =
  var_binop EQ BT.Bool |> mk_builtin_arg2 "ptr_eq" (BT.Loc, BT.Loc)


let prov_eq_def : builtin_fn_def =
  let left = (Sym.fresh_named "arg1", BT.Loc) in
  let right = (Sym.fresh_named "arg2", BT.Loc) in
  let left_cast = allocId_ (sym_ (fst left, BT.Loc, loc)) loc in
  let right_cast = allocId_ (sym_ (fst right, BT.Loc, loc)) loc in
  let body = binop EQ (left_cast, right_cast) loc BT.Bool in
  definition "prov_eq" [ left; right ] body


let addr_eq_def : builtin_fn_def =
  let left = (Sym.fresh_named "arg1", BT.Loc) in
  let right = (Sym.fresh_named "arg2", BT.Loc) in
  let left_cast = addr_ (sym_ (fst left, BT.Loc, loc)) loc in
  let right_cast = addr_ (sym_ (fst right, BT.Loc, loc)) loc in
  let body = binop EQ (left_cast, right_cast) loc BT.Bool in
  definition "addr_eq" [ left; right ] body


(* The remaining functions in this file, from here until array_to_list_def cannot yet be translated to
   LogicalFunction.definition types because they implicitly require basetype polymorphism.
   For example, the `mod` function allows inputs of any sign and size, but such a function cannot be defined
   yet with an index term *)
let mul_uf_def = ("mul_uf", Sym.fresh_named "mul_uf", mk_arg2 mul_no_smt_)

let div_uf_def = ("div_uf", Sym.fresh_named "div_uf", mk_arg2 div_no_smt_)

let power_uf_def = ("power_uf", Sym.fresh_named "power_uf", mk_arg2 exp_no_smt_)

let rem_uf_def = ("rem_uf", Sym.fresh_named "rem_uf", mk_arg2 rem_no_smt_)

let mod_uf_def = ("mod_uf", Sym.fresh_named "mod_uf", mk_arg2 mod_no_smt_)

let xor_uf_def = ("xor_uf", Sym.fresh_named "xor_uf", mk_arg2 (arith_binop BW_Xor))

let bw_and_uf_def =
  ("bw_and_uf", Sym.fresh_named "bw_and_uf", mk_arg2 (arith_binop BW_And))


let bw_or_uf_def = ("bw_or_uf", Sym.fresh_named "bw_or_uf", mk_arg2 (arith_binop BW_Or))

let bw_clz_uf_def =
  ("bw_clz_uf", Sym.fresh_named "bw_clz_uf", mk_arg1 (arith_unop BW_CLZ_NoSMT))


let bw_ctz_uf_def =
  ("bw_ctz_uf", Sym.fresh_named "bw_ctz_uf", mk_arg1 (arith_unop BW_CTZ_NoSMT))


let bw_ffs_uf_def =
  ("bw_ffs_uf", Sym.fresh_named "bw_ffs_uf", mk_arg1 (arith_unop BW_FFS_NoSMT))


let bw_fls_uf_def =
  ("bw_fls_uf", Sym.fresh_named "bw_fls_uf", mk_arg1 (arith_unop BW_FLS_NoSMT))


let shift_left_def =
  ("shift_left", Sym.fresh_named "shift_left", mk_arg2 (arith_binop ShiftLeft))


let shift_right_def =
  ("shift_right", Sym.fresh_named "shift_right", mk_arg2 (arith_binop ShiftRight))


let power_def = ("power", Sym.fresh_named "power", mk_arg2 exp_)

let rem_def = ("rem", Sym.fresh_named "rem", mk_arg2 rem_)

let mod_def = ("mod", Sym.fresh_named "mod", mk_arg2 mod_)

let nth_list_def = ("nth_list", Sym.fresh_named "nth_list", mk_arg3 nthList_)

let array_to_list_def =
  ( "array_to_list",
    Sym.fresh_named "array_to_list",
    mk_arg3_err (fun (arr, i, len) loc ->
      match SBT.is_map_bt (IT.bt arr) with
      | None ->
        let reason = "map/array operation" in
        let expected = "map/array" in
        fail
          { loc;
            msg =
              Illtyped_it { it = IT.pp arr; has = SBT.pp (IT.bt arr); expected; reason }
          }
      | Some (_, bt) -> return (array_to_list_ (arr, i, len) bt loc)) )


let builtin_funs =
  [ mul_uf_def;
    div_uf_def;
    power_uf_def;
    rem_uf_def;
    mod_uf_def;
    xor_uf_def;
    bw_and_uf_def;
    bw_or_uf_def;
    bw_clz_uf_def;
    bw_ctz_uf_def;
    bw_ffs_uf_def;
    bw_fls_uf_def;
    shift_left_def;
    shift_right_def;
    power_def;
    rem_def;
    mod_def;
    nth_list_def;
    array_to_list_def;
    has_alloc_id_def
  ]


let builtin_fun_defs =
  max_min_bits @ [ not_def; is_null_def; ptr_eq_def; prov_eq_def; addr_eq_def ]


let apply_builtin_funs fsym args loc =
  match List.find_opt (fun (_, fsym', _) -> Sym.equal fsym fsym') builtin_funs with
  | None -> return None
  | Some (_, _, mk) ->
    let@ t = mk args loc in
    return (Some t)


(* This list of names is later passed to the frontend in bin/main.ml so that these are available in the elaboration,
   so it should include all builtin function names *)
let cn_builtin_fun_names =
  List.map (fun (str, sym, _) -> (str, sym)) builtin_funs
  @ List.map (fun (str, sym, _) -> (str, sym)) builtin_fun_defs
