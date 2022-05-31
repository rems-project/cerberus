module IT=IndexTerms
module CF=Cerb_frontend
module BT = BaseTypes
module LS = LogicalSorts
module LRT = LogicalReturnTypes
module RT = ReturnTypes
module AT = ArgumentTypes
module NAT = NormalisedArgumentTypes
module TE = TypeErrors
module Loc = Locations
module LP = LogicalPredicates
module LC = LogicalConstraints

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)


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
(*
  ^^ !^"Module Type Lemmas_Required."
  ^^ hardline ^^ hardline
*)

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

let it_uninterp_funs it =
  let f _ funs it = match IT.term it with
    | Pred (name, args) -> SymSet.add name funs
    | _ -> funs
  in
  IT.fold_subterms f SymSet.empty it

type scan_res = {res: bool; ret: bool; funs : SymSet.t}

(* recurse over a function type and detect resources (impureness),
   non-unit return types (non-lemma trusted functions), and the set
   of uninterpreted functions used. *)
let scan ftyp =
  let lc_funs = function
    | LC.T it -> it_uninterp_funs it
    | LC.Forall (_, it) -> it_uninterp_funs it
  in
  let add_lc_funs lc r = {r with funs = SymSet.union (lc_funs lc) r.funs} in
  let rec scan_lrt t = match t with
    | LRT.Define (_, _, t) -> scan_lrt t
    | LRT.Resource (_, _, t) -> {(scan_lrt t) with res = true}
    | LRT.Constraint (lc, _, t) -> add_lc_funs lc (scan_lrt t)
    | LRT.I -> {res = false; ret = false; funs = SymSet.empty}
  in
  let scan_rt = function
    | RT.Computational ((_, bt), _, t) -> {(scan_lrt t) with ret =
        not (BaseTypes.equal bt BaseTypes.Unit)}
  in
  let rec scan_at t = match t with
    | AT.Computational (_, _, t) -> scan_at t
    | AT.Define (_, _, t) -> scan_at t
    | AT.Resource (_, _, t) -> {(scan_at t) with res = true}
    | AT.Constraint (lc, _, t) -> add_lc_funs lc (scan_at t)
    | AT.I t -> scan_rt t
  in
  scan_at ftyp

(*
let nat_to_coq ftyp =
  let rec aux_lrt = function
    | LRT.Logical ((nm, ty), _, tm) -> "exists (" ^ nm ^ ": " ^ lsort_to_coq ty ^ ")"
        ^ aux_lrt tm
    | LRT.Constraint (c, _, tm) = aux_lc c ^ " /\ " ^ aux_lrt tm

let process fsym ftyp =
  let ftyp = NAT.normalise (fun rt -> rt) ftyp in
  let aux_lrt (Logical
  let rec aux_c (I rt) = 
  let rec aux = function
    | NAT.Computational 
  print stdout (item (Sym.pp_string fsym) (AT.pp RT.pp ftyp));
  ()
*)

let bt_to_coq bt =
  let open Pp in
  match bt with
  | BaseTypes.Bool -> !^ "bool"
  | BaseTypes.Integer -> !^ "Z"
  | _ -> fail "bt_to_coq: unsupported" (BaseTypes.pp bt)

let it_to_coq fun_ret_tys it =
  let open Pp in
  let rec f bool_eq_prop t =
    let aux t = f bool_eq_prop t in
    let binop s x y = parens (aux x ^^^ !^ s ^^^ aux y) in
    let with_is_true d = if bool_eq_prop
        then parens (!^ "Is_true" ^^^ d) else d
    in
    let pred_with_true nm d = if BaseTypes.equal (SymMap.find nm fun_ret_tys) BaseTypes.Bool
        then with_is_true d else d
    in
    match IT.term t with
    | IT.Lit l -> begin match l with
        | IT.Sym sym -> Sym.pp sym
        | IT.Bool b -> with_is_true (!^ (if b then "true" else "false"))
        | IT.Z z -> !^ (Z.to_string z)
        | _ -> fail "it_to_coq: unsupported lit" (IT.pp t)
    end
    | IT.Info _ -> aux (IT.bool_ true)
    | IT.Arith_op op -> begin match op with
        | Add (x, y) -> binop "+" x y
        | Sub (x, y) -> binop "-" x y
        | Mul (x, y) -> binop "*" x y
        | LT (x, y) -> binop (if bool_eq_prop then "<" else "<?") x y
        | LE (x, y) -> binop (if bool_eq_prop then "<=" else "<=?") x y
        | _ -> fail "it_to_coq: unsupported arith op" (IT.pp t)
    end
    | IT.Bool_op op -> begin match op with
        | IT.And [] -> aux (IT.bool_ true)
        | IT.And [x] -> aux x
        | IT.And (x :: xs) -> binop (if bool_eq_prop then "/\\" else "&&") x (IT.and_ xs)
        | IT.Or [] -> aux (IT.bool_ false)
        | IT.Or [x] -> aux x
        | IT.Or (x :: xs) -> binop (if bool_eq_prop then "\\/" else "||") x (IT.or_ xs)
        | IT.Impl (x, y) -> binop (if bool_eq_prop then "->" else "implb") x y
        | IT.Not x when not bool_eq_prop -> parens (!^ "negb" ^^^ aux x)
        | IT.ITE (sw, x, y) -> parens (!^ "if" ^^^ f false sw ^^^ !^ "then"
                ^^^ aux x ^^^ !^ "else" ^^^ aux y)
        | IT.EQ (x, y) -> binop (if bool_eq_prop then "=" else "=?") x y
        | _ -> fail "it_to_coq: unsupported bool op" (IT.pp t)
    end
    | Pred (name, args) -> pred_with_true name
        (parens (Sym.pp name ^^^ flow (break 1) (List.map (f false) args)))
    | CT_pred (Good (ct, t)) -> aux (IT.good_value SymMap.empty ct t)
    | _ -> fail "it_to_coq: unsupported" (IT.pp t)
  in
  f true it

let mk_forall sym bt doc =
  let open Pp in
  !^ "forall" ^^^ parens (Sym.pp sym ^^^ !^ ":" ^^^ bt_to_coq bt)
  ^^ !^"," ^^^ doc

let lc_to_coq fun_ret_tys = function
  | LC.T it -> it_to_coq fun_ret_tys it
  | LC.Forall ((sym, bt), it) -> parens (mk_forall sym bt (it_to_coq fun_ret_tys it))

let param_spec fun_defs =
  let open Pp in
  let open LogicalPredicates in
  let param (f, def) = match def.definition with
    | Uninterp ->
    let arg_tys = List.map (fun (_, bt) -> bt_to_coq bt) def.args in
    let ret_ty = bt_to_coq def.return_bt in
    let ty = List.fold_right (fun at rt -> at ^^^ !^ "->" ^^^ rt) arg_tys ret_ty in
    !^ "  Parameter" ^^^ typ (Sym.pp f) ty ^^ !^ "."
      ^^ hardline
    | _ -> fail "param_spec: defined logical fun" (Sym.pp f)
  in
  !^"Module Type CN_Lemma_Parameters."
  ^^ hardline ^^ hardline
  ^^ flow hardline (List.map param fun_defs)
  ^^ hardline
  ^^ !^"End CN_Lemma_Parameters."
  ^^ hardline ^^ hardline

let ftyp_to_coq fun_ret_tys ftyp =
  let rec lrt_lcs t = match t with
    | LRT.Constraint (lc, _, t) -> lc :: lrt_lcs t
    | LRT.I -> []
    | _ -> fail "ftyp_to_coq: unsupported" (LRT.pp t)
  in
  let rt_lcs t = match t with
    | RT.Computational ((_, bt), _, t2) -> if BaseTypes.equal bt BaseTypes.Unit
        then lrt_lcs t2
        else fail "ftyp_to_coq: unsupported return type" (RT.pp t)
  in
  let open Pp in
  let rt_doc t = List.fold_right (fun lc (triv, concl) -> if triv
        then (false, lc_to_coq fun_ret_tys lc)
        else (false, lc_to_coq fun_ret_tys lc ^^^ !^"/\\" ^^^ concl))
    (rt_lcs t) (true, !^ "true = true")
    |> snd
  in
  let rec at_doc t = match t with
    | AT.Computational ((sym, bt), _, t) -> mk_forall sym bt (at_doc t)
    | AT.Define _ -> fail "ftyp_to_coq: unsupported Define" (AT.pp RT.pp t)
    | AT.Resource _ -> fail "ftyp_to_coq: unsupported" (AT.pp RT.pp t)
    | AT.Constraint (lc, _, t) -> lc_to_coq fun_ret_tys lc ^^^ !^"->" ^^^ at_doc t
    | AT.I t -> rt_doc t
  in at_doc ftyp

let lemma_type_specs fun_ret_tys lemma_typs =
  let open Pp in
  let lemma_ty (nm, typ) =
    progress_simple "exporting pure lemma" (Sym.pp_string nm);
    let rhs = ftyp_to_coq fun_ret_tys typ in
    !^"  Definition" ^^^ Sym.pp nm ^^ !^ "_type :=" ^^^ rhs ^^ !^ "." ^^ hardline
  in
  !^"Module CN_Lemma_Types (P : CN_Lemma_Parameters)."
  ^^ hardline ^^ hardline
  ^^ !^"  Import P." ^^ hardline
  ^^ !^"  Open Scope Z." ^^ hardline ^^ hardline
  ^^ flow hardline (List.map lemma_ty lemma_typs)
  ^^ hardline
  ^^ !^"End CN_Lemma_Types."
  ^^ hardline ^^ hardline

let mod_spec lemma_nms =
  let open Pp in
  let lemma nm =
    !^"  Parameter" ^^^ typ (Sym.pp nm) (Sym.pp nm ^^ !^ "_type")
        ^^ !^ "." ^^ hardline
  in
  !^"Module Type CN_Lemma_Spec (P : CN_Lemma_Parameters)."
  ^^ hardline ^^ hardline
  ^^ !^"  Module Tys := CN_Lemma_Types(P)." ^^ hardline
  ^^ !^"  Import Tys." ^^ hardline ^^ hardline
  ^^ flow hardline (List.map lemma lemma_nms)
  ^^ hardline
  ^^ !^"End CN_Lemma_Spec."
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
  let (impure, pure) = List.partition (fun x -> x.scan_res.res || x.scan_res.ret)
    scan_trusted in
  List.iter (fun x ->
    progress_simple "skipping resource lemma" (Sym.pp_string x.sym)
  ) impure;
  let funs = List.fold_right (fun x -> SymSet.union x.scan_res.funs) pure SymSet.empty in
  let fun_defs = SymSet.elements funs
    |> List.map (fun s -> match List.assoc_opt Sym.equal s mu_file.mu_logical_predicates with
      | None -> fail "undefined logical function/predicate" (Sym.pp s)
      | Some def -> (s, def))
  in
  print channel (param_spec fun_defs);
  let fun_ret_tys = List.fold_right (fun (f, def) m ->
            let open LogicalPredicates in SymMap.add f def.return_bt m)
        fun_defs SymMap.empty in
  print channel (lemma_type_specs fun_ret_tys (List.map (fun x -> (x.sym, x.typ)) pure));
  print channel (mod_spec (List.map (fun x -> x.sym) pure));
  Ok ()



