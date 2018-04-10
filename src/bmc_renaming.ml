(* DEPRECATED: replaced with bmc_ssa *)

open Core
open Bmc_utils
(*
type krename_state = {
  supply : ksym_supply ref;
  sym_map : (ksym, ksym) Pmap.map ref
}
*)

(*
let rec rename_sym (st: krename_state) (sym: ksym) =
  match Pmap.lookup sym (!(st.sym_map)) with
  | Some sym2 ->
      sym2
  | None ->
      let (new_sym, new_supply) = Sym.fresh (!(st.supply)) in
      st.supply := new_supply;
      st.sym_map := (Pmap.add sym new_sym (!(st.sym_map)));
      new_sym

let rec rename_pat (st:krename_state) (pat: pattern) =
  match pat with
  | CaseBase (Some sym, ty) ->
      CaseBase (Some (rename_sym st sym), ty)
  | CaseBase (None, _) -> 
      pat
  | CaseCtor (ctor, patList) ->
      CaseCtor(ctor, List.map (fun pat1 -> rename_pat st pat1) patList)

let rec rename_pexpr (st: krename_state)
                     (Pexpr(ty, pexpr_) as pexpr : pexpr) =
  let pexpr_' = match pexpr_ with
    | PEsym sym -> 
        PEsym (rename_sym st sym)
    | PEimpl _  -> 
        pexpr_
    | PEval _   ->
        pexpr_
    | PEconstrained _ ->
        assert false
    | PEundef _ -> 
        pexpr_
    | PEerror _ -> 
        pexpr_
    | PEctor (ctor, pelist) ->
        PEctor(ctor, List.map (fun pe -> rename_pexpr st pe) pelist)
    | PEcase (pe, caselist) ->
        PEcase(rename_pexpr st pe, 
               List.map (fun (pat1, pe1) -> 
                          (rename_pat st pat1, rename_pexpr st pe1 )) caselist)
    | PEarray_shift _
    | PEmember_shift _ ->
        assert false
    | PEnot pe ->
        PEnot (rename_pexpr st pe)
    | PEop (binop, pe1, pe2) ->
        PEop(binop, rename_pexpr st pe1, rename_pexpr st pe2)
    | PEstruct _
    | PEunion _ ->
        assert false
    | PEcall (name, pelist) -> 
        (* TODO: renaming function calls??? *)
        PEcall(name, List.map (fun pe -> rename_pexpr st pe) pelist)
    | PElet (pat, pe1, pe2) ->
        PElet(rename_pat st pat, rename_pexpr st pe1, rename_pexpr st pe2)
    | PEif (pe1, pe2, pe3) ->
        PEif(rename_pexpr st pe1, rename_pexpr st pe2, rename_pexpr st pe3)
    | PEis_scalar pe ->
        PEis_scalar(rename_pexpr st pe)
    | PEis_integer pe ->
        PEis_integer(rename_pexpr st pe)
    | PEis_signed pe ->
        PEis_signed(rename_pexpr st pe)
    | PEis_unsigned pe ->
        PEis_unsigned (rename_pexpr st pe)
    | PEstd (str, pe) ->
        PEstd(str, rename_pexpr st pe)
  in Pexpr(ty, pexpr_')
    *)
