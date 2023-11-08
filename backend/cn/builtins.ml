module SBT = SurfaceBaseTypes
open Resultat
open Effectful.Make(Resultat)
open TypeErrors
open IndexTerms



(* builtin function symbols *)

let mk_arg1 mk loc = function
  | [x] -> return (mk x)
  | xs -> fail {loc; msg = Number_arguments {has = List.length xs; expect = 1}}

let mk_arg2_err mk loc = function
  | [x; y] -> mk loc (x, y)
  | xs -> fail {loc; msg = Number_arguments {has = List.length xs; expect = 2}}

let mk_arg2 mk = mk_arg2_err (fun loc tup -> return (mk tup))

let mk_arg3_err mk loc = function
  | [x; y; z] -> mk loc (x, y, z)
  | xs -> fail {loc; msg = Number_arguments {has = List.length xs; expect = 3}}

let mk_arg3 mk = mk_arg3_err (fun loc tup -> return (mk tup))


let mk_arg5 mk loc = function
  | [a;b;c;d;e] -> return (mk (a,b,c,d,e))
  | xs -> fail {loc; msg = Number_arguments {has = List.length xs; expect = 5}}


let mul_uf_def = ("mul_uf", Sym.fresh_named "mul_uf", mk_arg2 mul_no_smt_)
let div_uf_def = ("div_uf", Sym.fresh_named "div_uf", mk_arg2 div_no_smt_)
let power_uf_def = ("power_uf", Sym.fresh_named "power_uf", mk_arg2 exp_no_smt_)
let rem_uf_def = ("rem_uf", Sym.fresh_named "rem_uf", mk_arg2 rem_no_smt_)
let mod_uf_def = ("mod_uf", Sym.fresh_named "mod_uf", mk_arg2 mod_no_smt_)
let xor_uf_def = ("xor_uf", Sym.fresh_named "xor_uf", mk_arg2 (arith_binop XORNoSMT))
let bw_and_uf_def = ("bw_and_uf", Sym.fresh_named "bw_and_uf", mk_arg2 (arith_binop BWAndNoSMT))
let bw_or_uf_def = ("bw_or_uf", Sym.fresh_named "bw_or_uf", mk_arg2 (arith_binop BWOrNoSMT))

let bw_clz_uf_def = ("bw_clz_uf", Sym.fresh_named "bw_clz_uf", mk_arg1 (arith_unop BWCLZNoSMT))
let bw_ctz_uf_def = ("bw_ctz_uf", Sym.fresh_named "bw_ctz_uf", mk_arg1 (arith_unop BWCTZNoSMT))
let bw_ffs_uf_def = ("bw_ffs_uf", Sym.fresh_named "bw_ffs_uf", mk_arg1 (arith_unop BWFFSNoSMT))

let power_def = ("power", Sym.fresh_named "power", mk_arg2 exp_)
let rem_def = ("rem", Sym.fresh_named "rem", mk_arg2 rem_)
let mod_def = ("mod", Sym.fresh_named "mod", mk_arg2 mod_)

let not_def = ("not", Sym.fresh_named "not", mk_arg1 not_)

let nth_list_def = ("nth_list", Sym.fresh_named "nth_list", mk_arg3 nthList_)

let array_to_list_def =
  ("array_to_list", Sym.fresh_named "array_to_list", mk_arg3_err
  (fun loc (arr, i, len) -> match SBT.is_map_bt (IT.bt arr) with
    | None -> fail {loc; msg = Illtyped_it {it = IT.pp arr; has = SBT.pp (IT.bt arr); expected = "map"; o_ctxt = None}}
    | Some (_, bt) -> return (array_to_list_ (arr, i, len) bt)
  ))

let in_loc_list_def =
  ("in_loc_list", Sym.fresh_named "in_loc_list",
    mk_arg2_err (fun loc tup -> return (IT.mk_in_loc_list loc tup)))


let cellpointer_def =
  ("cellPointer",
   Sym.fresh_named "cellPointer",
   mk_arg5 (fun (base, step, starti, endi, p) ->
       let base = IT.term_of_sterm base in
       let step = IT.term_of_sterm step in
       let starti = IT.term_of_sterm starti in
       let endi = IT.term_of_sterm endi in
       let p = IT.term_of_sterm p in
       IT.sterm_of_term (IT.cellPointer_ ~base ~step ~starti ~endi ~p)
     )
  )

let is_null_def =
  ("is_null",
   Sym.fresh_named "is_null",
   mk_arg1 (fun p ->
       IT.sterm_of_term IT.(eq_ (IT.term_of_sterm p, null_))
     )
  )

let ptr_eq_def =
    ("ptr_eq",
        Sym.fresh_named "ptr_eq",
        mk_arg2 (fun (p1, p2) ->
       IT.sterm_of_term IT.(eq_ (IT.term_of_sterm p1, IT.term_of_sterm p2))
     )
   )


let builtin_funs =
  [
      mul_uf_def;
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

      power_def;
      rem_def;
      mod_def;

      not_def;

      nth_list_def;
      array_to_list_def;
      in_loc_list_def;

      cellpointer_def;
      is_null_def;
      ptr_eq_def;
    ]

let apply_builtin_funs loc fsym args =
  match List.find_opt (fun (_, fsym', _) -> Sym.equal fsym fsym') builtin_funs with
  | None -> return None
  | Some (_, _, mk) ->
    let@ t = mk loc args in
    return (Some t)

let cn_builtin_fun_names =
  List.map (fun (str,sym,_) -> (str, sym)) builtin_funs
