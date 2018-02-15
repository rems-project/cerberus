open Core

open Bmc_utils


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
    | PEcase _
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
    | PEis_unsigned _
    | PEstd _ ->
        wrap_pexpr_with_let annot pexpr supply 
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
    | Eaction _ 
    | Ecase _ ->
        expr_
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
  let (normed_map, supply1) = normalize_fun_map file.funs sym_supply in
  ({file with funs = normed_map;
  }, supply1)
