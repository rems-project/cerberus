module CF=Cerb_frontend
module RE = Resources.RE
module RER = Resources.Requests
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module LRT = LogicalReturnTypes
module RT = ReturnTypes
module AT = ArgumentTypes
module NAT = NormalisedArgumentTypes
module TE = TypeErrors
module Loc = Locations
module LP = LogicalPredicates

module StringSet = Set.Make(String)
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
  ^^ !^"Require Import Z." ^^ hardline

let fail_check_noop = function
  | body ->
    (print stdout (item "non-noop lemma body element" (pp_texpr body)); assert false)

let check_noop body = ()

let check_trusted_fun_body fsym = function
  | M_Proc (loc, ret_ty, arg_tys, body, labels) ->
    check_noop body
  | _ ->
    print stdout (!^ "unexpected non-proc trusted function"); assert false

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

let process fsym ftyp = ()

let cmp_line_numbers = function
  | None, None -> 0
  | None, _ -> 1
  | _, None -> -1
  | Some (a, b), Some (c, d) ->
    let x = Int.compare a c in
    if x == 0 then Int.compare b d else x

let cmp_loc_line_numbers l1 l2 =
    cmp_line_numbers (Loc.line_numbers l1, Loc.line_numbers l2)

let generate directions mu_file =
  let (filename, kinds) = parse_directions directions in
  let channel = open_out filename in
  print channel (header filename);
  let trusted_funs = Pmap.fold (fun fsym (M_funinfo (loc, _, ftyp, trusted, _)) funs ->
    match trusted with
      | Muc.Trusted _ ->
        progress_simple "processing trusted function" (Sym.pp_string fsym);
        let result = process fsym ftyp in
        SymMap.add fsym (loc, result) funs
      | _ -> funs
    ) mu_file.mu_funinfo SymMap.empty in
  Pmap.iter (fun fsym fn ->
      if SymMap.mem fsym trusted_funs
      then
      check_trusted_fun_body fsym fn
      else ()) mu_file.mu_funs;
  let ord = SymMap.bindings trusted_funs
    |> List.sort (fun x y -> cmp_loc_line_numbers (fst (snd x)) (fst (snd y))) in
  List.iter (fun (sym, (loc, info)) ->
    progress_simple "exporting" (Sym.pp_string sym);
    print channel (Sym.pp sym)
  ) ord;
  Ok ()



