module IT=IndexTerms
module CF=Cerb_frontend
module BT = BaseTypes
module LS = LogicalSorts
module LRT = LogicalReturnTypes
module RT = ReturnTypes
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module TE = TypeErrors
module Loc = Locations
module LP = LogicalPredicates
module LC = LogicalConstraints

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)

module StringList = struct
  type t = string list
  let compare = List.compare String.compare
  let equal = List.equal String.equal
end
module StringListMap = Map.Make(StringList)


module PrevParams = struct
  type t = {present: (Sym.t list) StringListMap.t; defs: Pp.doc list;
        params: Pp.doc list}
  let init_t = {present = StringListMap.empty; defs = []; params = []}
  type ('a, 'e) m = t -> ('a * t)
  let return (x : 'a) : ('a, 'e) m = (fun st -> (x, st))
  let bind (x : ('a, 'e) m) (f : 'a -> ('b, 'e) m) : ('b, 'e) m = (fun st ->
    let (xv, st) = x st in
    f xv st
  )
  let get : (t, 'e) m = (fun st -> (st, st))
  let set (st : t) : (unit, 'e) m = (fun _ -> ((), st))
end
module ParamMonad = Effectful.Make(PrevParams)
open PrevParams
open ParamMonad


module Mu = Retype.New
module Muc = CF.Mucore
open Mu
open Pp


(* FIXME: clagged from check.ml *)
module PP_TYPS = struct
  module T = Retype.SR_Types
  let pp_bt = BT.pp
  let pp_ct ct = Sctypes.pp ct
  let pp_ft = AT.pp RT.pp
  let pp_gt = pp_ct
  let pp_lt = AT.pp False.pp
  let pp_ut _ = Pp.string "todo: implement union type printer"
  let pp_st _ = Pp.string "todo: implement struct type printer"
end


module PP_MUCORE = CF.Pp_mucore.Make(CF.Pp_mucore.Basic)(PP_TYPS)
(* let pp_budget () = Some !debug_level *)
let pp_budget () = Some 10
let pp_pexpr e = PP_MUCORE.pp_pexpr e
let pp_tpexpr e = PP_MUCORE.pp_tpexpr (pp_budget ()) e
let pp_expr e = PP_MUCORE.pp_expr e
let pp_texpr e = PP_MUCORE.pp_texpr (pp_budget ()) e


let emit_kind kinds k =
  StringSet.mem k kinds || StringSet.mem "all" kinds

let parse_directions directions =
  (directions, StringSet.singleton "all")

let header filename =
  !^"(*" ^^^ !^ filename ^^ !^": generated lemma specifications from CN *)"
  ^^ hardline ^^ hardline
  ^^ !^"Require Import ZArith Bool."
  ^^ hardline ^^ hardline

let fail msg details =
  let open Pp in
  print stdout (format [Bold; Red] msg ^^ colon ^^ space ^^ details);
  failwith msg

let fail_check_noop = function
  | body -> fail "non-noop lemma body element" (pp_texpr body)

let check_noop body = ()

let check_trusted_fun_body fsym = function
  | M_Proc (loc, ret_ty, arg_tys, body, labels) ->
    check_noop body
  | _ ->
    fail "non-proc trusted function" (Sym.pp fsym)

let add_it_funs it funs =
  let f _ funs it = match IT.term it with
    | IT.Pred (name, args) -> SymSet.add name funs
    | _ -> funs
  in
  IT.fold_subterms f funs it

(*
FIXME keep or not
let add_it_predef it ss =
  let f _ ss it = match IT.term it with
    | IT.Map_op op -> begin match op with
        | IT.Set _ -> StringListSet.add ["fun_upd"] ss
        | _ -> ss
    end
    | IT.Struct_op op -> begin match op with
        | IT.StructMember (t, m) ->
            let tag = BaseTypes.struct_bt (IT.bt t) in
            StringListSet.add ["struct"; Sym.pp_string tag; Id.pp_string m] ss
        | IT.StructUpdate ((t, m), _) ->
            let tag = BaseTypes.struct_bt (IT.bt t) in
            StringListSet.add ["struct"; Sym.pp_string tag; Id.pp_string m] ss
        | _ -> ss
    end
    | _ -> ss
  in
  IT.fold_subterms f ss it
*)

let all_undef_foralls =
  let add (nm, t) nms = StringMap.add nm (Sym.fresh_named nm, t) nms in
  let intf t = BaseTypes.Map (BaseTypes.Integer, t) in
  let int3 = intf (intf BaseTypes.Integer) in
  List.fold_right add [
    ("div_undef", int3);
    ("rem_undef", int3);
    ("mod_undef", int3)
  ] StringMap.empty

let it_undef_foralls it =
  let f _ nms it = match IT.term it with
    | IT.Arith_op op -> begin match op with
        | IT.Div _ -> StringSet.add "div_undef" nms
        | IT.Rem _ -> StringSet.add "rem_undef" nms
        | IT.Mod _ -> StringSet.add "mod_undef" nms
        | _ -> nms
    end
    | _ -> nms
  in
  IT.fold_subterms f StringSet.empty it

(* set of functions with boolean return type that are negated
   etc and must return bool (be computational) in Coq. the rest
   return Prop. FIXME: make this configurable. *)
let bool_funs = StringSet.add "order_aligned" StringSet.empty

exception Cannot_Coerce

(* attempt to coerce out the resources in this function type.
   we can do this for some lemmas where resources are passed and
   returned unchanged as a way of passing their return values. *)
let try_coerce_res ftyp =
  let rec erase_res r t = match t with
    | LRT.Define (v, info, t) -> LRT.Define (v, info, erase_res r t)
    | LRT.Constraint (lc, info, t) -> LRT.Constraint (lc, info, erase_res r t)
    | LRT.Resource ((name, (re, bt)), info, t) ->
        let (arg_name, arg_re) = r in
        if ResourceTypes.alpha_equivalent arg_re re
        then begin
          Pp.debug 2 (lazy (Pp.item "erasing" (Sym.pp name)));
          LRT.subst (IT.make_subst [(name, IT.sym_ (arg_name, bt))]) t
        end else LRT.Resource ((name, (re, bt)), info, erase_res r t)
    | LRT.I ->
        Pp.debug 2 (lazy (Pp.string "no counterpart found"));
        raise Cannot_Coerce (* did not find a matching resource *)
  in
  let erase_res2 r t =
    Pp.debug 2 (lazy (Pp.item "seeking to erase counterpart" (Sym.pp (fst r))));
    let res = LAT.map (RT.map (erase_res r)) t in
    res
  in
  let rec coerce_lat t = match t with
    | LAT.Resource ((name, (re, bt)), info, t) ->
       let computationals, t = coerce_lat (erase_res2 (name, re) t) in
       ((name, bt, info) :: computationals), t
    | LAT.Define (v, info, t) -> 
       let computationals, t = coerce_lat t in
       computationals, LAT.Define (v, info, t)
    | LAT.Constraint (lc, info, t) -> 
       let computationals, t = coerce_lat t in
       computationals, LAT.Constraint (lc, info, t)
    | LAT.I _ -> 
       [], t
  in
  let rec coerce_at t = match t with
    | AT.Computational (v, info, t) -> AT.Computational (v, info, coerce_at t)
    | AT.L t -> 
       let computationals, t = coerce_lat t in
       AT.mComputationals computationals (AT.L t)
  in
  try Some (coerce_at ftyp) with Cannot_Coerce -> None

type scan_res = {res: string option; ret: bool;
    res_coerce: RT.t AT.t option}

let init_scan_res = {res = None; ret = false; res_coerce = None}

(* recurse over a function type and detect resources (impureness),
   non-unit return types (non-lemma trusted functions), and the set
   of uninterpreted functions used. *)
let scan ftyp =
  let rec scan_lrt t = match t with
    | LRT.Define ((_, it), _, t) -> scan_lrt t
    | LRT.Resource ((name, _), _, t) -> {(scan_lrt t) with res = Some (Sym.pp_string name)}
    | LRT.Constraint (_, _, t) -> scan_lrt t
    | LRT.I -> init_scan_res
  in
  let scan_rt = function
    | RT.Computational ((_, bt), _, t) -> {(scan_lrt t) with ret =
        not (BaseTypes.equal bt BaseTypes.Unit)}
  in
  let rec scan_lat t = match t with
    | LAT.Define (_, _, t) -> scan_lat t
    | LAT.Resource ((name, _), _, t) -> {(scan_lat t) with res = Some (Sym.pp_string name)}
    | LAT.Constraint (_, _, t) -> scan_lat t
    | LAT.I t -> scan_rt t
  in
  let rec scan_at t = match t with
    | AT.Computational (_, _, t) -> scan_at t
    | AT.L t -> scan_lat t
  in
  let x = scan_at ftyp in
  if Option.is_none x.res then x
  else
  begin
  Pp.debug 2 (lazy (Pp.item "attempting to coerce ftyp" (Pp.string "")));
  match try_coerce_res ftyp with
    | None -> x
    | Some ftyp2 ->
    let y = scan_at ftyp2 in
    if Option.is_none y.res
    then begin
      Pp.debug 2 (lazy (Pp.item "coercion" (Pp.string "succeeded")));
      {x with res_coerce = Some ftyp2}
    end else begin
      Pp.debug 2 (lazy (Pp.item "coercion" (Pp.string "failed")));
      {x with res = y.res}
    end
  end

let struct_layout_field_bts xs =
  let open Memory in
  let xs2 = List.filter (fun x -> Option.is_some x.member_or_padding) xs
    |> List.sort (fun (x : struct_piece) y -> Int.compare x.offset y.offset)
    |> List.filter_map (fun x -> x.member_or_padding)
  in
  (List.map fst xs2, List.map (fun x -> BaseTypes.of_sct (snd x)) xs2)

let get_struct_xs struct_decls tag = match SymMap.find_opt tag struct_decls with
  | Some def -> struct_layout_field_bts def
  | None -> fail "undefined struct" (Sym.pp tag)

let binop s x y =
  let open Pp in
  parens (flow (break 1) [x; !^ s; y])

let doc_fun_app sd xs =
  let open Pp in
  parens (flow (break 1) (sd :: xs))

let fun_app s xs =
  let open Pp in
  doc_fun_app (!^ s) xs

let tuple_coq_ty doc fld_tys =
  let open Pp in
  let rec stars = function
    | [] -> fail "tuple_coq_ty: empty" doc
    | [x] -> [x]
    | x :: xs -> x :: star :: stars xs
  in
  parens (flow (break 1) (stars fld_tys))

type conv_info = {struct_decls : Memory.struct_layout SymMap.t;
    fun_info : LogicalPredicates.definition SymMap.t}

let bt_to_coq ci loc_info =
  let open Pp in
  let rec f bt = match bt with
  | BaseTypes.Bool -> !^ "bool"
  | BaseTypes.Integer -> !^ "Z"
  | BaseTypes.Map (x, y) -> parens (binop "->" (f x) (f y))
  | BaseTypes.Struct tag ->
    let (_, fld_bts) = get_struct_xs ci.struct_decls tag in
    tuple_coq_ty (Sym.pp tag) (List.map f fld_bts)
  | BaseTypes.Record mems ->
    tuple_coq_ty (!^ "record") (List.map f (List.map snd mems))
  | BaseTypes.Loc -> !^ "Z"
  | _ -> fail "bt_to_coq: unsupported" (BaseTypes.pp bt
        ^^^ !^ "in converting" ^^^ loc_info)
  in
  f

let it_adjust ci it =
  let rec f t =
    match IT.term t with
    | IT.Info _ -> IT.bool_ true
    | IT.Bool_op op -> begin match op with
        | IT.And xs ->
            let xs = List.map f xs |> List.partition IT.is_true |> snd in
            if List.length xs == 0 then IT.bool_ true else IT.and_ xs
        | IT.Or xs ->
            let xs = List.map f xs |> List.partition IT.is_false |> snd in
            if List.length xs == 0 then IT.bool_ true else IT.or_ xs
        | IT.EQ (x, y) ->
            let x = f x in
            let y = f y in
            if IT.equal x y then IT.bool_ true else IT.eq__ x y
        | IT.Impl (x, y) ->
            let x = f x in
            let y = f y in
            if IT.is_false x || IT.is_true y then IT.bool_ true else IT.impl_ (x, y)
        | IT.EachI ((i1, s, i2), x) ->
            let x = f x in
            let vs = IT.free_vars x in
            if SymSet.mem s vs then IT.eachI_ (i1, s, i2) x
            else (assert (i1 <= i2); x)
        | _ -> t
    end
    | IT.Pred (name, args) ->
        let open LogicalPredicates in
        let def = SymMap.find name ci.fun_info in
        begin match def.definition with
          | Uninterp -> t
          | Def body -> f (LogicalPredicates.open_pred def.args body args)
        end
    | IT.CT_pred (Good (ct, t2)) -> if Option.is_some (Sctypes.is_struct_ctype ct)
        then t else f (IT.good_value ci.struct_decls ct t2)
    | IT.CT_pred (Representable (ct, t2)) -> if Option.is_some (Sctypes.is_struct_ctype ct)
        then t else f (IT.representable ci.struct_decls ct t2)
    | IT.CT_pred (AlignedI t) ->
        f (IT.divisible_ (IT.pointerToIntegerCast_ t.t, t.align))
    | IT.CT_pred (Aligned (t, ct)) ->
        f (IT.alignedI_ ~t ~align:(IT.int_ (Memory.align_of_ctype ct)))
    | _ -> t
  in
  let res = f it in
  Pp.debug 9 (lazy (Pp.item "it_adjust" (binop "->" (IT.pp it) (IT.pp res))));
  f it

let fun_prop_ret ci nm = match SymMap.find_opt nm ci.fun_info with
  | None -> fail "fun_prop_ret: not found" (Sym.pp nm)
  | Some def ->
    let open LogicalPredicates in
    BaseTypes.equal BaseTypes.Bool def.return_bt
      && not (StringSet.mem (Sym.pp_string nm) bool_funs)

let mk_forall ci sym bt doc =
  let open Pp in
  let inf = !^"forall of" ^^^ Sym.pp sym in
  !^ "forall" ^^^ parens (typ (Sym.pp sym) (bt_to_coq ci inf bt))
  ^^ !^"," ^^ break 1 ^^ doc

let tuple_syn xs =
  let open Pp in
  parens (flow (comma ^^^ !^ "") xs)

let find_tuple_element (eq : 'a -> 'a -> bool) (x : 'a) (pp : 'a -> Pp.doc) (ys : 'a list) =
  let n_ys = List.mapi (fun i y -> (i, y)) ys in
  match List.find_opt (fun (i, y) -> eq x y) n_ys with
    | None -> fail "tuple element not found" (pp x)
    | Some (i, _) -> (i, List.length ys)

let tuple_element t (i, len) =
  let nm i = Pp.string ("x_t_" ^ Int.to_string i) in
  let lhs = Pp.string "'" ^^ tuple_syn (List.init len nm) in
  let open Pp in
  parens (!^ "let" ^^^ lhs ^^^ !^ ":=" ^^^ t ^^^ !^ "in" ^^ break 1 ^^ nm i)

let tuple_upd_element t (i, len) y =
  let nm i = Pp.string ("x_t_" ^ Int.to_string i) in
  let lhs = Pp.string "'" ^^ tuple_syn (List.init len nm) in
  let rhs = tuple_syn (List.init len (fun j -> if j = i then y else nm j)) in
  let open Pp in
  parens (!^ "let" ^^^ lhs ^^^ !^ ":=" ^^^ t ^^^ !^ "in" ^^ break 1 ^^ rhs)

let rets s = return (Pp.string s)
let build = function
  | [] -> fail "it_to_coq: build" (!^ "empty")
  | xs ->
    let@ docs = ListM.mapM (fun x -> x) xs in
    return (flow (break 1) docs)
let parensM x =
    let@ xd = x in
    return (parens xd)

let defn nm args opt_ty rhs =
  let open Pp in
  let tyeq = match opt_ty with
    | None -> []
    | Some ty -> [colon; ty]
  in
  flow (break 1) ([!^"  Definition"; !^ nm] @ args @ tyeq @ [!^":="])
  ^^ hardline ^^ !^"    " ^^ rhs ^^ !^ "." ^^ hardline

let fun_upd_def =
  defn "fun_upd" (List.map Pp.string ["{A B : Type}"; "(eq : A -> A -> bool)";
        "(f : A -> B)"; "x"; "y"; "z"]) None
    (Pp.string "if eq x z then y else f z")

let gen_ensure k is_def doc xs =
  let@ st = get in
  match StringListMap.find_opt k st.present with
  | None ->
    let@ fin_doc = Lazy.force doc in
    (* n.b. finalising the rhs-s of definitions might change the state *)
    let@ st = get in
    let st = if is_def then {st with defs = fin_doc :: st.defs}
        else {st with params = fin_doc :: st.params} in
    set {st with present = StringListMap.add k xs st.present}
  | Some ys ->
    if List.equal Sym.equal xs ys
    then return ()
    else fail "gen_ensure: mismatch/redef" (Pp.list Pp.string k)

let ensure_fun_upd () =
  let k = ["predefs"; "fun_upd"] in
  gen_ensure k true (lazy (return fun_upd_def)) []

let ensure_tuple_op is_upd nm (ix, l) =
  let ix_s = Int.to_string ix in
  let len_s = Int.to_string l in
  let dir_s = if is_upd then "upd" else "get" in
  let k = ["predefs"; "tuple"; dir_s; nm; ix_s; len_s] in
  let op_nm = dir_s ^ "_" ^ nm ^ "_" ^ ix_s ^ "_" ^ len_s in
  let doc = lazy (
    let open Pp in
    let ty i = !^ ("T_" ^ Int.to_string i) in
    let t_ty = tuple_coq_ty (!^ op_nm) (List.init l ty) in
    let t = parens (typ (!^ "t") t_ty) in
    let x = parens (typ (!^ "x") (ty ix)) in
    let infer = !^"{" ^^ flow (!^ " ") (List.init l ty) ^^ colon ^^^ !^"Type}" in
    return (if is_upd then defn op_nm [infer; t; x]
             None (tuple_upd_element t (ix, l) x)
        else defn op_nm [infer; t] None (tuple_element t (ix, l)))
  )
  in
  let@ () = gen_ensure k true doc [] in
  return op_nm

let ensure_pred ci name aux =
  let open LogicalPredicates in
  let def = SymMap.find name ci.fun_info in
  let inf = !^ "pred" ^^^ Sym.pp name in
  begin match def.definition with
  | Uninterp -> gen_ensure ["params"; "pred"; Sym.pp_string name] false
    (lazy (return (
      let arg_tys = List.map (fun (_, bt) -> bt_to_coq ci inf bt) def.args in
      let ret_ty = if fun_prop_ret ci name then !^ "Prop" else bt_to_coq ci inf def.return_bt in
      let ty = List.fold_right (fun at rt -> at ^^^ !^ "->" ^^^ rt) arg_tys ret_ty in
      !^ "  Parameter" ^^^ typ (Sym.pp name) ty ^^ !^ "." ^^ hardline
    ))) []
  | Def body -> gen_ensure ["predefs"; "pred"; Sym.pp_string name] true
    (lazy (
      let@ rhs = aux (it_adjust ci body) in
      let args = List.map (fun (sym, bt) -> parens (typ (Sym.pp sym) (bt_to_coq ci inf bt)))
          def.args in
      return (defn (Sym.pp_string name) args None rhs)
    )) []
  end

let ensure_struct_mem is_good ci ct aux = match Sctypes.is_struct_ctype ct with
  | None -> fail "ensure_struct_mem: not struct" (Sctypes.pp ct)
  | Some tag ->
  let bt = BaseTypes.Struct tag in
  let nm = if is_good then "good" else "representable" in
  let k = ["predefs"; "struct"; nm] in
  let op_nm = "struct_" ^ Sym.pp_string tag ^ "_" ^ nm in
  let@ () = gen_ensure k true
  (lazy (
      let ty = bt_to_coq ci (Pp.string op_nm) bt in
      let x = parens (typ (!^ "x") ty) in
      let x_it = IT.sym_ (Sym.fresh_named "x", bt) in
      let@ rhs = aux (it_adjust ci (IT.good_value ci.struct_decls ct x_it)) in
      return (defn op_nm [x] None rhs)
  )) [tag] in
  return op_nm

let it_to_coq ci it =
  let open Pp in
  let eq_of = function
    | BaseTypes.Integer -> "Z.eqb"
    | bt -> fail "eq_of" (BaseTypes.pp bt)
  in
  let rec f bool_eq_prop t =
    let aux t = f bool_eq_prop t in
    let abinop s x y = parensM (build [aux x; rets s; aux y]) in
    let with_is_true x = if bool_eq_prop && BaseTypes.equal (IT.bt t) BaseTypes.Bool
        then parensM (build [rets "Is_true"; x]) else x
    in
    let check_pos t = match IT.is_z t with
      | Some i when Z.gt i Z.zero -> ()
      | _ -> fail "it_to_coq: divisor not positive const" (IT.pp t)
    in
    match IT.term t with
    | IT.Lit l -> begin match l with
        | IT.Sym sym -> return (Sym.pp sym)
        | IT.Bool b -> with_is_true (rets (if b then "true" else "false"))
        | IT.Z z -> rets (Z.to_string z)
        | _ -> fail "it_to_coq: unsupported lit" (IT.pp t)
    end
    | IT.Info _ -> aux (IT.bool_ true)
    | IT.Arith_op op -> begin match op with
        | Add (x, y) -> abinop "+" x y
        | Sub (x, y) -> abinop "-" x y
        | Mul (x, y) -> abinop "*" x y
        | Div (x, y) -> check_pos y; abinop "/" x y
        | Mod (x, y) -> check_pos y; abinop "mod" x y
        | Rem (x, y) -> check_pos y; abinop "mod" x y
        | LT (x, y) -> abinop (if bool_eq_prop then "<" else "<?") x y
        | LE (x, y) -> abinop (if bool_eq_prop then "<=" else "<=?") x y
        | Exp (x, y) -> abinop "^" x y
        | ExpNoSMT (x, y) -> abinop "^" x y
        | XOR (x, y) -> parensM (build [rets "Z.lxor"; aux x; aux y])
        | _ -> fail "it_to_coq: unsupported arith op" (IT.pp t)
    end
    | IT.Bool_op op -> begin match op with
        | IT.And [] -> aux (IT.bool_ true)
        | IT.And [x] -> aux x
        | IT.And (x :: xs) -> abinop (if bool_eq_prop then "/\\" else "&&") x (IT.and_ xs)
        | IT.Or [] -> aux (IT.bool_ false)
        | IT.Or [x] -> aux x
        | IT.Or (x :: xs) -> abinop (if bool_eq_prop then "\\/" else "||") x (IT.or_ xs)
        | IT.Impl (x, y) -> abinop (if bool_eq_prop then "->" else "implb") x y
        | IT.Not x -> parensM (build [rets (if bool_eq_prop then "~" else "negb"); aux x])
        | IT.ITE (sw, x, y) -> parensM (build [rets "if"; f false sw; rets "then";
                aux x; rets "else"; aux y])
        | IT.EQ (x, y) -> abinop (if bool_eq_prop then "=" else "=?") x y
        | IT.EachI ((i1, s, i2), x) -> assert bool_eq_prop;
            let@ x = aux x in
            return (parens (mk_forall ci s BaseTypes.Integer
                (binop "->" (binop "/\\"
                    (binop "<=" (Pp.int i1) (Sym.pp s)) (binop "<=" (Sym.pp s) (Pp.int i2)))
                x)))
    end
    | IT.Map_op op -> begin match op with
        | IT.Set (m, x, y) ->
            let@ () = ensure_fun_upd () in
            parensM (build [rets "fun_upd"; rets (eq_of (IT.bt x)); aux m; aux x; aux y])
        | IT.Get (m, x) -> parensM (build [aux m; aux x])
        | _ -> fail "it_to_coq: unsupported map op" (IT.pp t)
    end
    | IT.Record_op op -> begin match op with
        | IT.RecordMember (t, m) ->
            let flds = BT.record_bt (IT.bt t) in
            if List.length flds == 1
            then aux t
            else
            let ix = find_tuple_element Sym.equal m Sym.pp (List.map fst flds) in
            let@ op_nm = ensure_tuple_op false (Sym.pp_string m) ix in
            parensM (build [rets op_nm; aux t])
        | IT.RecordUpdate ((t, m), x) ->
            let flds = BT.record_bt (IT.bt t) in
            if List.length flds == 1
            then aux x
            else
            let ix = find_tuple_element Sym.equal m Sym.pp (List.map fst flds) in
            let@ op_nm = ensure_tuple_op true (Sym.pp_string m) ix in
            parensM (build [rets op_nm; aux t; aux x])
        | _ -> fail "it_to_coq: unsupported record op" (IT.pp t)
    end
    | IT.Struct_op op -> begin match op with
        | IT.StructMember (t, m) ->
            let tag = BaseTypes.struct_bt (IT.bt t) in
            let (mems, bts) = get_struct_xs ci.struct_decls tag in
            let ix = find_tuple_element Id.equal m Id.pp mems in
            if List.length mems == 1
            then aux t
            else
            let@ op_nm = ensure_tuple_op false (Id.pp_string m) ix in
            parensM (build [rets op_nm; aux t])
        | IT.StructUpdate ((t, m), x) ->
            let tag = BaseTypes.struct_bt (IT.bt t) in
            let (mems, bts) = get_struct_xs ci.struct_decls tag in
            let ix = find_tuple_element Id.equal m Id.pp mems in
            if List.length mems == 1
            then aux x
            else
            let@ op_nm = ensure_tuple_op true (Id.pp_string m) ix in
            parensM (build [rets op_nm; aux t; aux x])
        | _ -> fail "it_to_coq: unsupported struct op" (IT.pp it)
    end
    | IT.Pointer_op op -> begin match op with
        | IT.IntegerToPointerCast t -> aux t
        | IT.PointerToIntegerCast t -> aux t
        | IT.LEPointer (x, y) -> abinop (if bool_eq_prop then "<=" else "<=?") x y
        | IT.LTPointer (x, y) -> abinop (if bool_eq_prop then "<" else "<?") x y
        | _ -> fail "it_to_coq: unsupported pointer op" (IT.pp it)
    end
    | IT.Pred (name, args) ->
        let prop_ret = fun_prop_ret ci name in
        let body_aux = f prop_ret in
        let@ () = ensure_pred ci name body_aux in
        let@ r = parensM (build ([return (Sym.pp name)] @ List.map (f false) args)) in
        if prop_ret then return r else with_is_true (return r)
    | IT.CT_pred p -> assert bool_eq_prop; begin match p with
        | IT.Good (ct, t2) when (Option.is_some (Sctypes.is_struct_ctype ct)) ->
        let@ op_nm = ensure_struct_mem true ci ct aux in
        parensM (build [rets op_nm; aux t2])
        | IT.Representable (ct, t2) when (Option.is_some (Sctypes.is_struct_ctype ct)) ->
        let@ op_nm = ensure_struct_mem true ci ct aux in
        parensM (build [rets op_nm; aux t2])
        | _ -> fail "it_to_coq: unexpected ctype pred" (IT.pp t)
    end
    | _ -> fail "it_to_coq: unsupported" (IT.pp t)
  in
  f true it

let mk_let sym rhs_doc doc =
  let open Pp in
  !^ "let" ^^^ Sym.pp sym ^^^ !^ ":=" ^^^ rhs_doc ^^^ !^ "in" ^^^ doc

let lc_to_coq_check_triv ci = function
  | LC.T it -> let it = it_adjust ci it in
    if IT.is_true it then return None
    else let@ v = it_to_coq ci it in return (Some v)
  | LC.Forall ((sym, bt), it) -> let it = it_adjust ci it in
    if IT.is_true it then return None
    else let@ v = it_to_coq ci it
    in return (Some (parens (mk_forall ci sym bt v)))

let nth_str_eq n s ss = Option.equal String.equal (List.nth_opt ss n) (Some s)

let param_spec params =
  let open Pp in
  !^"Module Type Parameters."
  ^^ hardline ^^ hardline
  ^^ flow hardline params
  ^^ hardline
  ^^ !^"End Parameters."
  ^^ hardline ^^ hardline

let ftyp_to_coq ci ftyp =
  let open Pp in
  let lc_to_coq_c = lc_to_coq_check_triv ci in
  let it_tc = it_to_coq ci in
  (* FIXME: handle underdefinition in division *)
  let oapp f opt_x y = match opt_x with
    | Some x -> f x y
    | None -> y
  in
  let mk_and doc doc2 = doc ^^^ !^ "/\\" ^^^ doc2 in
  let mk_imp doc doc2 = doc ^^^ !^ "->" ^^^ doc2 in
  let omap_split f = Option.map (fun doc -> f (break 1 ^^ doc)) in
  let rec lrt_doc t = match t with
    | LRT.Constraint (lc, _, t) ->
    let@ d = lrt_doc t in
    let@ c = lc_to_coq_c lc in
    begin match d, c with
        | None, _ -> return c
        | _, None -> return d
        | Some dd, Some cd -> return (Some (mk_and cd dd))
    end
    | LRT.Define ((sym, it), _, t) ->
        let@ d = lrt_doc t in
        let@ l = it_tc it in
        return (omap_split (mk_let sym l) d)
    | LRT.I -> return None
    | _ -> fail "ftyp_to_coq: unsupported" (LRT.pp t)
  in
  let rt_doc t = match t with
    | RT.Computational ((_, bt), _, t2) -> if BaseTypes.equal bt BaseTypes.Unit
        then lrt_doc t2
        else fail "ftyp_to_coq: unsupported return type" (RT.pp t)
  in
  let rec lat_doc t = match t with
    | LAT.Define ((sym, it), _, t) ->
        let@ d = lat_doc t in
        let@ l = it_tc it in
        return (omap_split (mk_let sym l) d)
    | LAT.Resource _ -> fail "ftyp_to_coq: unsupported" (LAT.pp RT.pp t)
    | LAT.Constraint (lc, _, t) ->
        let@ c = lc_to_coq_c lc in
        let@ d = lat_doc t in
        return (omap_split (oapp mk_imp c) d)
    | LAT.I t -> rt_doc t
  in
  let rec at_doc t = match t with
    | AT.Computational ((sym, bt), _, t) ->
        let@ d = at_doc t in
        return (omap_split (mk_forall ci sym bt) d)
    | AT.L t -> lat_doc t
  in
  let@ d = at_doc ftyp in
  (*
  let d2 = d |> Option.map (List.fold_right (fun nm d ->
    let (sym, bt) = StringMap.find nm all_undef_foralls in
    mk_forall ci sym bt d) extra_foralls)
  in
  *)
  match d with
  | Some doc -> return doc
  | None -> rets "Is_true true"

let convert_lemma_defs ci lemma_typs =
  let lemma_ty (nm, typ, kind) =
    progress_simple ("converting " ^ kind ^ " lemma type") (Sym.pp_string nm);
    let@ rhs = ftyp_to_coq ci typ in
    return (defn (Sym.pp_string nm ^ "_type") [] (Some (!^ "Prop")) rhs)
  in
  let (tys, st) = ListM.mapM lemma_ty lemma_typs init_t in
  Pp.debug 4 (lazy (Pp.item "saved conversion elements"
    (Pp.list (fun (ss, _) -> Pp.parens (Pp.list Pp.string ss))
        (StringListMap.bindings st.present))));
  (tys, List.rev st.defs, List.rev st.params)

let defs_module aux_defs lemma_tys =
  let open Pp in
  !^"Module Defs (P : Parameters)."
  ^^ hardline ^^ hardline
  ^^ !^"  Import P." ^^ hardline
  ^^ !^"  Open Scope Z." ^^ hardline ^^ hardline
  ^^ flow hardline aux_defs
  ^^ hardline
  ^^ flow hardline lemma_tys
  ^^ hardline
  ^^ !^"End Defs."
  ^^ hardline ^^ hardline

let mod_spec lemma_nms =
  let open Pp in
  let lemma nm =
    !^"  Parameter" ^^^ typ (Sym.pp nm) (Sym.pp nm ^^ !^ "_type")
        ^^ !^ "." ^^ hardline
  in
  !^"Module Type Lemma_Spec (P : Parameters)."
  ^^ hardline ^^ hardline
  ^^ !^"  Module D := Defs(P)." ^^ hardline
  ^^ !^"  Import D." ^^ hardline ^^ hardline
  ^^ flow hardline (List.map lemma lemma_nms)
  ^^ hardline
  ^^ !^"End Lemma_Spec."
  ^^ hardline ^^ hardline

let cmp_line_numbers = function
  | None, None -> 0
  | None, _ -> 1
  | _, None -> -1
  | Some (a, b), Some (c, d) ->
    let x = Int.compare a c in
    if x == 0 then Int.compare b d else x

let cmp_loc_line_numbers l1 l2 =
    cmp_line_numbers (Loc.line_numbers l1, Loc.line_numbers l2)

(* an experiment involving calling the Retype features again, this time
   with "CallByValue" set. this probably doesn't work, since the elaboration
   needs to be compatible
let do_re_retype mu_file trusted_funs prev_mode pred_defs pre_retype_mu_file =
  match prev_mode with
  | `CallByValue -> Ok mu_file
  | `CallByReference ->
  let prev_cut =
      let open Retype.Old in
      let info2 = Pmap.filter (fun fsym _ -> SymSet.mem fsym trusted_funs)
          pre_retype_mu_file.mu_funinfo in
      let funs2 = Pmap.filter (fun fsym _ -> SymSet.mem fsym trusted_funs)
          pre_retype_mu_file.mu_funs in
      { pre_retype_mu_file with mu_funs = funs2; mu_funinfo = info2 }
  in
  Retype.retype_file pred_defs `CallByValue prev_cut
*)

type scanned = {sym : Sym.t; loc: Loc.t; typ: RT.t AT.t; scan_res: scan_res}

let get_struct_decls mu_file =
  (* clagged from Retype *)
  Pmap.fold (fun sym def decls ->
        match def with
        | Retype.New.M_StructDef def ->
           SymMap.add sym def decls
        | _ -> decls
      ) mu_file.mu_tagDefs SymMap.empty

let generate directions mu_file =
  let (filename, kinds) = parse_directions directions in
  let channel = open_out filename in
  print channel (header filename);
  let trusted_funs = Pmap.fold (fun fsym (M_funinfo (loc, _, _, trusted, _)) funs ->
    match trusted with
      | Muc.Trusted _ -> SymSet.add fsym funs
      | _ -> funs
    ) mu_file.mu_funinfo SymSet.empty in
  let scan_trusted = SymSet.elements trusted_funs
    |> List.map (fun sym ->
        let (M_funinfo (loc, _, typ, _, _)) = Pmap.find sym mu_file.mu_funinfo in
        {sym; loc; typ; scan_res = scan typ})
    |> List.sort (fun x y -> cmp_loc_line_numbers x.loc y.loc)
  in
  let (returns, others) = List.partition (fun x -> x.scan_res.ret) scan_trusted in
  let (impure, pure) = List.partition (fun x -> Option.is_some x.scan_res.res) others in
  let (coerce, skip) = List.partition
        (fun x -> Option.is_some x.scan_res.res_coerce) impure in
  List.iter (fun x ->
    progress_simple "skipping trusted fun with return val" (Sym.pp_string x.sym)
  ) returns;
  List.iter (fun x ->
    progress_simple "skipping trusted fun with resource"
        (Sym.pp_string x.sym ^ ": " ^ (Option.get x.scan_res.res))
  ) skip;
  let fun_info = List.fold_right (fun (s, def) m -> SymMap.add s def m)
        mu_file.mu_logical_predicates SymMap.empty in
  let struct_decls = get_struct_decls mu_file in
  let ci = {struct_decls; fun_info} in
  let conv = List.map (fun x -> (x.sym, x.typ, "pure")) pure
    @ List.map (fun x -> (x.sym, Option.get x.scan_res.res_coerce, "coerced")) coerce in
  let (conv_defs, defs, params) = convert_lemma_defs ci conv in
  print channel (param_spec params);
  print channel (defs_module defs conv_defs);
  print channel (mod_spec (List.map (fun (nm, _, _) -> nm) conv));
  Ok ()



