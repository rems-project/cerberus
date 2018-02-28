open Core

open Bmc_utils
open Bmc_renaming
open Implementation
open Mem

open AilTypes

let max_inline_depth = 3

(* TODO: do properly *)
type 'a bmc_inline_state = {
  sym_supply : ksym_supply ref;
  depth      : int; (* Does not really belong here *)
  file       : 'a file;
}

let sym_cmp = (Symbol.instance_Basic_classes_SetType_Symbol_sym_dict.Lem_pervasives.setElemCompare_method)



  (* TODO: do rewrite in separate pass. Flag for debugging right now *)
let rec inline_pexpr (st: 'a bmc_inline_state) 
                     (Pexpr((), pexpr_) as pexpr : pexpr) =
  let inlined = match pexpr_ with
    | PEsym sym -> pexpr_
    | PEimpl _  -> pexpr_
    | PEval _   -> pexpr_
    | PEconstrained _ ->
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
        assert false
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
              let fresh_sym_list = mk_new_sym_list st.sym_supply args
              and sym_types = List.map (fun (arg, ty) -> ty) args in

              let patlist = List.map2 (fun sym ty -> CaseBase(Some sym, ty))
                                      fresh_sym_list sym_types in

              (* Map each argument to a new symbol *)
              let sym_map = List.fold_left2 (
                fun pmap new_sym (arg, ty) -> Pmap.add arg new_sym pmap)
                (Pmap.empty sym_cmp) fresh_sym_list args in

              (* State tracking symbol renames *)
              let rename_state = ({supply = st.sym_supply; 
                                   sym_map = ref (sym_map)}) in
              let renamed_fun_exp = rename_pexpr rename_state fun_exp in
            
              (* Note: forgetting type *)
              let new_pexpr = 
                Pexpr((), PElet(CaseCtor(Ctuple, patlist),
                                Pexpr((), PEctor(Ctuple, pelist)),
                                renamed_fun_exp)) in

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
    | PEis_scalar pe ->
        PEis_scalar(inline_pexpr st pe)
    | PEis_integer pe ->
        PEis_integer(inline_pexpr st pe)
    | PEis_signed pe ->
        PEis_signed(inline_pexpr st pe)
    | PEis_unsigned pe ->
        PEis_unsigned (inline_pexpr st pe)
    | PEstd (str, pe) ->
        PEstd (str, inline_pexpr st pe)
  in (Pexpr((), inlined))


let rec inline_expr (st: 'a bmc_inline_state) (Expr(annot, expr_) : 'b expr) =
  let inlined = match expr_ with
    | Epure pe ->
        Epure (inline_pexpr st pe)
    | Ememop (op, pelist) ->
        assert false
    | Eaction (Paction(p, Action(loc, a, Store0(pe1, pe2, pe3, mem)))) ->
        let pe1' = inline_pexpr st pe1 in
        let pe2' = inline_pexpr st pe2 in
        let pe3' = inline_pexpr st pe3 in
        Eaction (Paction(p, Action(loc, a, Store0(pe1', pe2', pe3', mem))))
    | Eaction _ -> 
        expr_
    | Ecase (pe, clist) ->
        Ecase(inline_pexpr st pe, 
              List.map (fun (pat, e) -> (pat, inline_expr st e)) clist)
    | Elet(pat, pe1, e2) ->
        Elet(pat, inline_pexpr st pe1, inline_expr st e2)
    | Eif(pe1, e2, e3) ->
        Eif(inline_pexpr st pe1, inline_expr st e2, inline_expr st e3)
    | Eskip -> Eskip
    | Eccall( _, _, _) 
    | Eproc( _, _, _)  ->
        assert false;
        expr_
    | Eunseq eslist ->
        Eunseq (List.map (inline_expr st) eslist) 
    | Ewseq(pat, e1, e2) ->
        Ewseq(pat, inline_expr st e1, inline_expr st e2)
    | Esseq(pat, e1, e2) ->
        Esseq(pat, inline_expr st e1, inline_expr st e2)
    | Easeq(pat, e1, e2) ->
        assert false
    | Eindet( i, e) ->
        assert false
    | Ebound( i, e) ->
        Ebound(i, inline_expr st e)
    | End eslist ->
        End (List.map (inline_expr st) eslist)
    | Esave( _, _, _) 
    | Erun( _, _, _) 
    | Epar _
    | Ewait _ ->
        expr_
  in (Expr(annot, inlined))

let inline_file (file: 'a file) (sym_supply: ksym_supply) =
  match file.main with
  | None -> 
      print_string "ERROR: file does not have a main\n";
      assert false
  | Some main_sym ->
      let initial_state : 'a bmc_inline_state = 
        ({sym_supply = ref sym_supply;
          depth = 0;
          file = file;
        }) in
      begin
      match Pmap.lookup main_sym file.funs with
      | Some (Proc(ty, params, e)) ->
          let ret = inline_expr initial_state e in
          let new_fun_map = 
            Pmap.add main_sym ((Proc(ty, params,ret ))) file.funs
          in
          ({file with funs = new_fun_map}), !(initial_state.sym_supply)
      | Some (Fun(ty, params, pe)) ->
          let ret =  inline_pexpr initial_state pe in
          let new_fun_map = 
            Pmap.add main_sym ((Fun(ty, params,ret ))) file.funs
          in
          ({file with funs = new_fun_map}), !(initial_state.sym_supply)

      | _ -> assert false
      end

(* =================== REWRITE STUFF ================= *)
(* TODO: get values from Implementation.ml *)
let core_ivminmax (v : pexpr) =
  let pe_of_ity ity = Pexpr((), PEval(Vctype (Basic0 (Integer (ity)))))
  and pe_of_sz sz = Pexpr((), PEval(Vobject (OVinteger (Ocaml_mem.integer_ival sz))))
  in

  let pe_ty_signed_int = pe_of_ity (Signed Int_) in
  let (min_signed_int, max_signed_int) = min_integer_range (Signed Int_) in
  let pe_max_signed_int = pe_of_sz (max_signed_int) in 
  let pe_min_signed_int = pe_of_sz (min_signed_int) in 

  print_string "TODO: currently using min_integer_range \n";

  let cond_signed_int = Pexpr((), PEop(OpEq, v, pe_ty_signed_int)) in
  let pe_error = Pexpr((), PEerror("TODO: IVmax/min cases", v))
  in

  PEif(cond_signed_int, pe_min_signed_int, pe_error),
  PEif(cond_signed_int, pe_max_signed_int, pe_error)

(* TODO: can't pattern match b/c signed is not a constructor in core ?*)
(* TODO: IntN_t, Int_leastN_t, Int_fastN_t not included *)
(* Maybe better to implement this in Z3? *)
let core_isunsigned_signed (v : pexpr) =
  let types = [Ichar; Short; Int_; Long; LongLong; 
               Intmax_t; Intptr_t] in
  let pe_of_ity ity = Pexpr((), PEval(Vctype (Basic0 (Integer (ity))))) in

  let signed_types = List.map (fun ty -> pe_of_ity (Signed ty)) types in
  let unsigned_types = List.map (fun ty -> pe_of_ity (Unsigned ty)) types in

  let eq_pe pe = Pexpr((), PEop(OpEq, v, pe)) in

  let is_equal tys = List.fold_left 
                     (fun pe ty_pe -> 
                        PEop(OpOr, Pexpr((), pe), eq_pe ty_pe )) 
                     (PEval(Vfalse))
                     tys in
  is_equal unsigned_types, is_equal signed_types





let rec rewrite_pexpr (st: 'a bmc_inline_state) 
                     (Pexpr((), pexpr_) as pexpr : pexpr) =
  let rewritten = match pexpr_ with
    | PEsym sym -> pexpr_
    | PEimpl _  -> pexpr_
    | PEval _   -> pexpr_
    | PEconstrained _ ->
        assert false
    | PEundef _ -> pexpr_
    | PEerror _ -> pexpr_
    | PEctor (Civmin, [v]) ->
        let (min_expr, _) = core_ivminmax (rewrite_pexpr st v) in
        min_expr

    | PEctor (Civmax, [v]) ->
        let (_, max_expr) = core_ivminmax (rewrite_pexpr st v) in
        max_expr

    | PEctor (ctor, pelist) ->
        PEctor(ctor, List.map (fun pe -> rewrite_pexpr st pe) pelist)
    | PEcase (pe, caselist) ->
        PEcase(rewrite_pexpr st pe, 
               List.map (fun (pat, pe) -> (pat, rewrite_pexpr st pe)) caselist)
    | PEarray_shift _
    | PEmember_shift _ ->
        assert false
    | PEnot pe ->
        PEnot(rewrite_pexpr st pe)
    | PEop (binop, pe1, pe2) ->
        PEop(binop, rewrite_pexpr st pe1, rewrite_pexpr st pe2)
    | PEstruct _
    | PEunion _ ->
        assert false
    | PEcall (Sym sym, pelist) ->
        assert false
    | PEcall _ ->
          Printf.printf "TODO2: PEcall implementation constant: ";
          pp_to_stdout (Pp_core.Basic.pp_pexpr pexpr);
          Printf.printf "\n";
          pexpr_

    | PElet (pat, pe1, pe2) ->
        PElet(pat, rewrite_pexpr st pe1, rewrite_pexpr st pe2)
    | PEif (pe1, pe2, pe3) ->
        PEif(rewrite_pexpr st pe1, rewrite_pexpr st pe2, rewrite_pexpr st pe3)
    | PEis_scalar pe ->
        PEis_scalar(rewrite_pexpr st pe)
    | PEis_integer pe ->
        PEis_integer(rewrite_pexpr st pe)
    | PEis_signed pe ->
        let (_, is_signed) = core_isunsigned_signed (rewrite_pexpr st pe) in
        is_signed

    | PEis_unsigned pe ->
        let (is_unsigned, _) = core_isunsigned_signed (rewrite_pexpr st pe) in
        is_unsigned
    | PEstd (str, pe) ->
        PEstd (str, rewrite_pexpr st pe)
  in (Pexpr((), rewritten))


(* TODO: massive code duplication oops :D *)
let rec rewrite_expr (st: 'a bmc_inline_state) (Expr(annot, expr_) : 'b expr) =
  let rewritten = match expr_ with
    | Epure pe ->
        Epure (rewrite_pexpr st pe)
    | Ememop (op, pelist) ->
        assert false
    | Eaction (Paction(p, Action(loc, a, Store0(pe1, pe2, pe3, mem)))) ->
        let pe1' = rewrite_pexpr st pe1 in
        let pe2' = rewrite_pexpr st pe2 in
        let pe3' = rewrite_pexpr st pe3 in
        Eaction (Paction(p, Action(loc, a, Store0(pe1', pe2', pe3', mem))))
    | Eaction _ -> 
        expr_
    | Ecase (pe, clist) ->
        Ecase(rewrite_pexpr st pe, 
              List.map (fun (pat, e) -> (pat, rewrite_expr st e)) clist)
    | Elet(pat, pe1, e2) ->
        Elet(pat, rewrite_pexpr st pe1, rewrite_expr st e2)
    | Eif(pe1, e2, e3) ->
        Eif(rewrite_pexpr st pe1, rewrite_expr st e2, rewrite_expr st e3)
    | Eskip -> Eskip
    | Eccall( _, _, _) 
    | Eproc( _, _, _)  ->
        assert false;
        expr_
    | Eunseq eslist ->
        Eunseq (List.map (rewrite_expr st) eslist) 
    | Ewseq(pat, e1, e2) ->
        Ewseq(pat, rewrite_expr st e1, rewrite_expr st e2)
    | Esseq(pat, e1, e2) ->
        Esseq(pat, rewrite_expr st e1, rewrite_expr st e2)
    | Easeq(pat, e1, e2) ->
        assert false
    | Eindet( i, e) ->
        assert false
    | Ebound( i, e) ->
        Ebound(i, rewrite_expr st e)
    | End eslist ->
        End (List.map (rewrite_expr st) eslist)
    | Esave( _, _, _) 
    | Erun( _, _, _) 
    | Epar _
    | Ewait _ ->
        expr_
  in (Expr(annot, rewritten))


let rewrite_file (file: 'a file) (sym_supply: ksym_supply) =
  match file.main with
  | None -> 
      print_string "ERROR: file does not have a main\n";
      assert false
  | Some main_sym ->
      let initial_state : 'a bmc_inline_state = 
        ({sym_supply = ref sym_supply;
          depth = 0;
          file = file;
        }) in
      begin
      match Pmap.lookup main_sym file.funs with
      | Some (Proc(ty, params, e)) ->
          let ret = rewrite_expr initial_state e in
          let new_fun_map = 
            Pmap.add main_sym ((Proc(ty, params,ret ))) file.funs
          in
          ({file with funs = new_fun_map}), !(initial_state.sym_supply)
      | Some (Fun(ty, params, pe)) ->
          let ret =  rewrite_pexpr initial_state pe in
          let new_fun_map = 
            Pmap.add main_sym ((Fun(ty, params,ret ))) file.funs
          in
          ({file with funs = new_fun_map}), !(initial_state.sym_supply)

      | _ -> assert false
      end

