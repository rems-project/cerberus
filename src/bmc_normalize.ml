open Core

open Bmc_utils

let sym_cmp = (Symbol.instance_Basic_classes_SetType_Symbol_sym_dict.Lem_pervasives.setElemCompare_method)
(* ========== Function inlining ========== *)


let max_inline_depth = 3

(* TODO: this is probably unnecessary *)
(* TODO: switch to monads *)
type 'a bmc_inline_state = {
  sym_supply : ksym_supply ref;
  depth      : int; (* Does not really belong here *)
  file       : 'a typed_file;
}

type krename_state = {
  supply : ksym_supply ref;
  sym_map : (ksym, ksym) Pmap.map ref
}

let rec mk_new_sym_list (supply: ksym_supply ref) (alist) =
  List.map (fun _ -> 
    let (new_sym, new_supply) = Sym.fresh (!(supply)) in
    supply := new_supply;
    new_sym) alist

let rec rename_sym (st: krename_state) (sym: ksym) =
  match Pmap.lookup sym (!(st.sym_map)) with
  | Some sym2 ->
      sym2
  | None ->
      let (new_sym, new_supply) = Sym.fresh (!(st.supply)) in
      st.supply := new_supply;
      st.sym_map := (Pmap.add sym new_sym (!(st.sym_map)));
      new_sym


let rec rename_pat (st:krename_state) (pat: typed_pattern) =
  match pat with
  | CaseBase (Some sym, ty) ->
      CaseBase (Some (rename_sym st sym), ty)
  | CaseBase (_, ty) -> 
      pat
  | CaseCtor (ctor, patList) ->
      CaseCtor(ctor, List.map (fun pat1 -> rename_pat st pat1) patList)



(* TODO: use monads *)
let rec rename_pexpr (st: krename_state)
                     (Pexpr(ty, pexpr_) as pexpr : typed_pexpr) =
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
    | PEis_scalar _
    | PEis_integer _
    | PEis_signed _->
        assert false
    | PEis_unsigned pe ->
        PEis_unsigned (rename_pexpr st pe)
    | PEstd (str, pe) ->
        PEstd(str, rename_pexpr st pe)
  in Pexpr(ty, pexpr_')

(* TODO: st doesn't properly change *)
let rec inline_pexpr (st: 'a bmc_inline_state) (Pexpr(bty, pexpr_) as pexpr :
  typed_pexpr) =
  let inlined = match pexpr_ with
    | PEsym sym -> pexpr_
    | PEimpl _  -> pexpr_
    | PEval _   -> pexpr_
    | PEconstrained _ ->
        (* TODO *)
        assert false
    | PEundef _ -> pexpr_
    | PEerror _ -> pexpr_
    | PEctor (ctor, pelist) ->
        PEctor(ctor, List.map (fun pe -> inline_pexpr st pe) pelist)
    | PEcase (pe, caselist) ->
        PEcase(inline_pexpr st pe, 
               List.map (fun (pat, pe) -> (pat, inline_pexpr st pe)) caselist)
    | PEarray_shift _
    | PEmember_shift _ ->
        pexpr_
    | PEnot pe ->
        PEnot(inline_pexpr st pe)
    | PEop (binop, pe1, pe2) ->
        PEop(binop, inline_pexpr st pe1, inline_pexpr st pe2)
    | PEstruct _
    | PEunion _ ->
        assert false
    | PEcall (Sym sym, pelist) ->
          begin
          match Pmap.lookup sym st.file.stdlib with
          | Some (Fun(ty, args, fun_exp)) -> 

              (* Make a new symbol list *)
              let fresh_sym_list = mk_new_sym_list st.sym_supply args in

              (* Rename each argument *)
              let sym_map = List.fold_left2 (
                fun pmap new_sym (arg, ty) -> Pmap.add arg new_sym pmap)
                (Pmap.empty sym_cmp) fresh_sym_list args in

              let rename_state = ({supply = st.sym_supply; 
                                   sym_map = ref (sym_map)}) in
              let renamed_fun_exp = rename_pexpr rename_state fun_exp in
              let new_pexpr = List.fold_right2 (
                fun sym (Pexpr(ty2, pe2_)) last -> 
                      let pe2 = Pexpr(ty2, pe2_) in  
                      Pexpr(ty, PElet(CaseBase(Some sym, ty2),
                                       pe2,
                                       last)) 
              ) fresh_sym_list pelist renamed_fun_exp in

              let Pexpr(ty, ret_) = (
                if st.depth < max_inline_depth then
                  inline_pexpr ({st with depth = st.depth + 1}) new_pexpr
                else
                  new_pexpr
              ) in ret_
          | Some _ -> assert false
          | None -> assert false
          end
    | PEcall _ ->
          Printf.printf "TODO: PEcall implementation constant: ";
          pp_to_stdout (Pp_core.Basic.pp_pexpr pexpr);
          Printf.printf "\n";
          pexpr_

    | PElet (pat, pe1, pe2) ->
        PElet(pat, inline_pexpr st pe1, inline_pexpr st pe2)
    | PEif (pe1, pe2, pe3) ->
        PEif(inline_pexpr st pe1, inline_pexpr st pe2, inline_pexpr st pe3)
    | PEis_scalar _
    | PEis_integer _
    | PEis_signed _ ->
        assert false
    | PEis_unsigned pe ->
        PEis_unsigned (inline_pexpr st pe)
    | PEstd (str, pe) ->
        PEstd (str, inline_pexpr st pe)
  in (Pexpr(bty, inlined))


let rec inline_expr (st: 'a bmc_inline_state) (Expr(annot, expr_) : 'a typed_expr) =
  let (inlined, st') = match expr_ with
    | Epure pe ->
        Epure (inline_pexpr st pe), st
    | Ememop (op, pelist) ->
        assert false
    | Eaction (Paction(p, Action(loc, a, Store0(pe1, pe2, pe3, mem)))) ->
        let (pe1') = inline_pexpr st pe1 in
        let (pe2') = inline_pexpr st pe2 in
        let (pe3') = inline_pexpr st pe3 in
        Eaction (Paction(p, Action(loc, a, Store0(pe1', pe2', pe3', mem)))), st
    | Eaction _ -> 
        expr_, st
    | Ecase (pe, clist) ->
        assert false;
        expr_, st
    | Elet(pat, pe1, e2) ->
        assert false;
        expr_, st
    | Eif(pe1, e2, e3) ->
        assert false;
        expr_, st
    | Eskip -> Eskip, st
    | Eccall( _, _, _) 
    | Eproc( _, _, _)  ->
        assert false;
        expr_,st
    | Eunseq eslist ->
        let new_elist = List.map 
            (fun e -> let (e', _) = inline_expr st e in e') eslist in
        Eunseq new_elist, st
    | Ewseq(pat, e1, e2) ->
        let (inlined_e1, st1) = inline_expr st e1 in
        let (inlined_e2, st2) = inline_expr st e2 in
        Ewseq(pat, inlined_e1, inlined_e2), st
    | Esseq(pat, e1, e2) ->
        let (inlined_e1, st1) = inline_expr st e1 in
        let (inlined_e2, st2) = inline_expr st e2 in
        Esseq(pat, inlined_e1, inlined_e2), st
    | Easeq(pat, e1, e2) ->
        assert false
    | Eindet( i, e) ->
        assert false
    | Ebound( i, e) ->
        let (inlined_e, _) = inline_expr st e in
        Ebound(i, inlined_e), st
    | End eslist ->
        let new_elist = List.map 
            (fun e -> let (e', _) = inline_expr st e in e') eslist in
        End new_elist, st
    | Esave( _, _, _) 
    | Erun( _, _, _) 
    | Epar _
    | Ewait _ ->
        expr_, st
  in (Expr(annot, inlined), st')


let inline_file (file: 'a typed_file) (sym_supply: ksym_supply) =
  match file.main with
  | None -> assert false
  | Some main_sym ->
      match Pmap.lookup main_sym file.funs with
      | Some (Proc(ty, params, e)) ->
          let initial_state : 'a bmc_inline_state = 
            ({sym_supply = ref sym_supply;
              depth = 0;
              file = file
              }) in
          let ret, final_state  =  inline_expr initial_state e in
          let new_fun_map = 
            Pmap.add main_sym ((Proc(ty, params,ret ))) file.funs
          in
          ({file with funs = new_fun_map}), !(final_state.sym_supply)
      | Some (Fun(ty, params, pe)) ->
          (* TODO: duplicated code *)
          let initial_state : 'a bmc_inline_state = 
            ({sym_supply = ref sym_supply;
              depth = 0;
              file = file
              }) in
          let ret =  inline_pexpr initial_state pe in
          let new_fun_map = 
            Pmap.add main_sym ((Fun(ty, params,ret ))) file.funs
          in
          ({file with funs = new_fun_map}), !(initial_state.sym_supply)

      | _ -> assert false

(* ========== Expr normalization ========== *)

(* Create a fresh symbol of type bTy, make let equal to pexpr *)
let wrap_pexpr_with_let (bTy: core_base_type) 
                        (pexpr: typed_pexpr)
                        (supply: ksym_supply ref) =
  let (new_sym, new_supply) = Sym.fresh (!supply) in
  let new_sym_expr = Pexpr(bTy, PEsym new_sym) in
  supply := new_supply;
  PElet(CaseBase (Some new_sym, bTy), 
        pexpr, 
        new_sym_expr), new_sym_expr

(* flatten let expressions *)
let rec flatten_pexpr_lets (Pexpr(bTy1, pe1) : typed_pexpr)
                           (Pexpr(bTy2, pe2) as pexpr2 : typed_pexpr) =
  match pe1 with 
    | PEsym _ -> pe2
    | PElet (pat, pe1, pe2) ->
       PElet(pat, pe1, Pexpr(bTy2, flatten_pexpr_lets pe2 pexpr2))
    | _ -> assert false

(* (normed, symbol) *)
let rec normalize_pexpr (Pexpr(annot, pexpr_) as pexpr: typed_pexpr) 
                        (supply: ksym_supply ref) 
    : (typed_pexpr * typed_pexpr) =
  let (norm_pexpr, sym) = match pexpr_ with
    | PEsym sym ->
        pexpr_, pexpr
    | PEimpl _ 
    | PEval _
    | PEconstrained _ 
    | PEundef _ 
    | PEerror _ ->
        wrap_pexpr_with_let annot pexpr supply 
    | PEctor (ctor, pelist) ->
        let norm_sym_list = 
          List.map (fun pe -> normalize_pexpr pe supply) pelist in
        let sym_list = List.map (fun (k,v) -> v) norm_sym_list in
        let new_pexpr = Pexpr(annot, PEctor(ctor, sym_list)) in
        let (new_let, sym) = wrap_pexpr_with_let annot new_pexpr supply in
        let (Pexpr(_, ret_)) = List.fold_right 
          (fun (k,v) b -> (Pexpr(annot, flatten_pexpr_lets k b))) 
                        norm_sym_list (Pexpr(annot, new_let)) in
        ret_, sym
    | PEcase (pe, caselist) ->

        (*wrap_pexpr_with_let annot pexpr supply *)
        let new_case_list = 
          List.map (fun (pat, pe) ->
             let (ret, _) = normalize_pexpr pe supply in 
             (pat, ret)) caselist in
        let new_pexpr = Pexpr(annot, PEcase(pe, new_case_list)) in
        let (new_let, sym) = wrap_pexpr_with_let annot new_pexpr supply in
        new_let, sym

    | PEarray_shift _
    | PEmember_shift _ ->
        wrap_pexpr_with_let annot pexpr supply 
    | PEnot pe ->
        (* TODO: double check *)
        let (norm_pe, sym_1) = normalize_pexpr pe supply in
        let new_pexpr = Pexpr(annot, PEnot sym_1) in
        let (new_let, sym_2) = wrap_pexpr_with_let annot new_pexpr supply in
        flatten_pexpr_lets norm_pe (Pexpr(annot, new_let)), sym_2
    | PEop (binop, pe1, pe2) ->
        let (norm_pe1, sym_1) = normalize_pexpr pe1 supply in
        let (norm_pe2, sym_2) = normalize_pexpr pe2 supply in
        let new_op = Pexpr(annot, PEop(binop, sym_1, sym_2)) in
        let (new_let, sym_binop) = wrap_pexpr_with_let annot new_op supply in
        (flatten_pexpr_lets 
            norm_pe1 
            (Pexpr(annot, (flatten_pexpr_lets norm_pe2 
                                              (Pexpr(annot, new_let))))),
         sym_binop)
    | PEstruct _
    | PEunion _
    | PEcall _ ->
        wrap_pexpr_with_let annot pexpr supply 
    | PElet (pat, pe1, pe2) ->
        let (norm_pe1, sym_1) = normalize_pexpr pe1 supply in
        let (norm_pe2, sym_2) = normalize_pexpr pe2 supply in
        let new_let = Pexpr(annot, PElet(pat, sym_1, norm_pe2)) in
        flatten_pexpr_lets norm_pe1 new_let, sym_2
    | PEif (pe1, pe2, pe3) ->
        let (norm_pe1, sym_1) = normalize_pexpr pe1 supply in
        let (norm_pe2, sym_2) = normalize_pexpr pe2 supply in
        let (norm_pe3, sym_3) = normalize_pexpr pe3 supply in
        let new_if = Pexpr(annot, PEif(sym_1, norm_pe2, norm_pe3)) in
        let (new_let, sym_if) = wrap_pexpr_with_let annot new_if supply in
        flatten_pexpr_lets norm_pe1 (Pexpr(annot, new_let)), sym_if
    | PEis_scalar _
    | PEis_integer _
    | PEis_signed _
    | PEis_unsigned _ ->
        wrap_pexpr_with_let annot pexpr supply 
    | PEstd (str, pe) ->
        wrap_pexpr_with_let annot pexpr supply 
        (*
        (* TODO: correct ?? *)
        let (norm_pe, sym_1) = normalize_pexpr pe supply in
        let new_std = (Pexpr(annot, PEstd(str, norm_pe))) in
        wrap_pexpr_with_let annot new_std supply 
        *)
  in 
  Pexpr(annot, norm_pexpr), sym

(* TODO: not done properly *)
let rec normalize_expr (Expr(annot, expr_): 'a typed_expr) 
                       (supply: ksym_supply ref) =
  let norm_expr = match expr_ with
    | Epure pe ->
        let (norm, _) = normalize_pexpr pe supply in
        Epure norm 
    | Ememop( _, _) 
    | Eaction _ -> 
        expr_
    | Ecase (pe, clist) ->
        Ecase(pe, List.map (fun (k,v) -> (k, normalize_expr v supply)) clist)
    | Elet( pat, pe1, e2) ->
        let (norm_pe1, _) = normalize_pexpr pe1 supply in
        Elet( pat, norm_pe1, normalize_expr e2 supply)
    | Eif( pe1, e2, e3) ->
        let (norm_pe1, _) = normalize_pexpr pe1 supply in
        Eif(norm_pe1, 
            normalize_expr e2 supply,
            normalize_expr e3 supply)
    | Eskip 
    | Eccall( _, _, _) 
    | Eproc( _, _, _)  ->
        expr_
    | Eunseq es ->
        Eunseq (List.map (fun e -> normalize_expr e supply) es)
    | Ewseq( pat, e1, e2) ->
        Ewseq(pat, normalize_expr e1 supply, normalize_expr e2 supply)
    | Esseq( pat, e1, e2) ->
        Esseq(pat, normalize_expr e1 supply, normalize_expr e2 supply)
    | Easeq( _, _, _)  ->
        expr_
    | Eindet( i, e) ->
        Eindet(i, normalize_expr e supply)
    | Ebound( i, e) ->
        Ebound(i, normalize_expr e supply)
    | End es ->
        End (List.map (fun e -> normalize_expr e supply) es)
    | Esave( _, _, _) 
    | Erun( _, _, _) 
    | Epar _
    | Ewait _ ->
        expr_
  in (Expr(annot, norm_expr))

let normalize_fun_map (fun_map: ('a, 'b typed_fun_map_decl) Pmap.map) 
                      (sym_supply: ksym_supply)  =
  let supply = ref (sym_supply) in
  ((Pmap.map ((function
    | Fun(ty, params, pe) ->
        let (norm, _) = normalize_pexpr pe supply in
        Fun (ty, params, norm)
    | ProcDecl(ty, params) ->
        assert false
    | Proc(ty, params, e) ->
        Proc(ty, params, normalize_expr e supply) 
   )) fun_map), !supply)



let normalize_file (file : 'a typed_file) (sym_supply: ksym_supply) =
  let (inlined_file, supply2) = inline_file file sym_supply in
  pp_file inlined_file;
  let (normed_map, supply1) = normalize_fun_map inlined_file.funs supply2 in
  ({inlined_file with funs = normed_map}), supply1
