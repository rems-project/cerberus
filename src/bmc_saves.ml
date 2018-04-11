open Core

open Bmc_utils

type 'a saves_map = (ksym, core_base_type * ksym list * 'a typed_expr) Pmap.map

let print_saves_map (map: 'a saves_map) = 
  print_endline "SAVES_MAP";
  Pmap.iter (fun k (cbt, sym_list, expr) -> 
    print_string (symbol_to_string k);
    print_string " -> (";
    print_string (pp_to_string (Pp_core.Basic.pp_core_base_type cbt));
    print_string " , [";
    List.iter (fun sym -> 
      print_string (symbol_to_string sym);
      print_string ", ") sym_list;
    print_string "], ";
    print_string (pp_to_string (Pp_core.Basic.pp_expr expr));
    print_endline ")";
    ) map

let rec find_save_expr (Expr(annot, expr_) : 'a typed_expr) =
  match expr_ with
    | Epure _ 
    | Ememop _ 
    | Eaction _ -> 
        Pmap.empty sym_cmp
    | Ecase(pe, elist) ->
        List.fold_left (fun map (_, e) ->
          Pmap.union map (find_save_expr e)) (Pmap.empty sym_cmp) elist
    | Elet(_, _, e) ->
        find_save_expr e
    | Eif(_, e2, e3) ->
        Pmap.union (find_save_expr e2) (find_save_expr e3)
    | Eskip ->
        Pmap.empty sym_cmp
    | Eccall _ ->
        Pmap.empty sym_cmp
    | Eproc _ ->
        assert false
    | Eunseq elist ->
        List.fold_left (fun map e ->
          Pmap.union map  (find_save_expr e)) (Pmap.empty sym_cmp) elist
    | Ewseq (_, e1, e2) (* fall through *)
    | Esseq (_, e1, e2) ->
        Pmap.union (find_save_expr e1) (find_save_expr e2)
    | Easeq _ ->
        assert false
    | Eindet _ ->
        assert false
    | Ebound (_, e) ->
        find_save_expr e
    | End elist ->
        List.fold_left (fun map e ->
          Pmap.union map (find_save_expr e)) (Pmap.empty sym_cmp) elist
    | Esave((sym, cbt), sym_pelist, elist) ->
        let sym_list = List.map (fun (sym, _) -> sym) sym_pelist in
        Pmap.add sym (cbt, sym_list, elist) (Pmap.empty sym_cmp)
    | Erun _ ->
        Pmap.empty sym_cmp
    | Epar elist ->
        List.fold_left (fun map e ->
          Pmap.union map (find_save_expr e)) (Pmap.empty sym_cmp) elist
    | Ewait _ ->
        assert false


type substitute_map = (ksym, typed_pexpr) Pmap.map

let rec substitute_pexpr (map: substitute_map)
                         (Pexpr(annot, ty, pexpr_) : typed_pexpr) =
  let ret = match pexpr_ with
    | PEsym sym ->
        begin
        match Pmap.lookup sym map with
        | Some (Pexpr(_, _, pe)) -> pe 
        | None -> assert false (* TODO: special cases for returns only *)
        end
    | PEimpl _ -> pexpr_
    | PEval _ -> pexpr_
    | PEconstrained _ -> assert false
    | PEundef _ -> pexpr_
    | PEerror _ -> pexpr_
    | PEctor (ctor, pelist) ->
        PEctor(ctor, List.map (fun pe -> substitute_pexpr map pe) pelist)
    | PEcase (pe, caselist) ->
        PEcase(substitute_pexpr map pe,
               List.map (fun (pat, pe) -> (pat, substitute_pexpr map pe)) caselist)
    | PEarray_shift _
    | PEmember_shift _ -> 
        assert false
    | PEnot pe ->
        PEnot(substitute_pexpr map pe)
    | PEop (binop, pe1, pe2) ->
        PEop(binop, substitute_pexpr map pe1, substitute_pexpr map pe2)
    | PEstruct _
    | PEunion _ -> assert false
    | PEcall _ -> assert false
    | PElet (pat, pe1, pe2) ->
        PElet (pat, substitute_pexpr map pe1, substitute_pexpr map pe2)
    | PEif(pe1, pe2, pe3) ->
        PEif(substitute_pexpr map pe1, substitute_pexpr map pe2, substitute_pexpr map pe3)
    | PEis_scalar pe ->
        PEis_scalar(substitute_pexpr map pe)
    | PEis_integer pe ->
        PEis_integer(substitute_pexpr map pe)
    | PEis_signed pe ->
        PEis_signed (substitute_pexpr map pe)
    | PEis_unsigned pe -> 
        PEis_unsigned (substitute_pexpr map pe)
  in
    Pexpr(annot, ty, ret)

let rec substitute_action (map: substitute_map)
                          (Action(loc, a, action_) : 'a typed_action) =
  let ret = match action_ with
    | Create (pe1, pe2, sym) ->
        Create(substitute_pexpr map pe1, substitute_pexpr map pe2, sym)
    | CreateReadOnly _ 
    | Alloc0 _ ->
        assert false
    | Kill pe ->
        Kill (substitute_pexpr map pe)
    | Store0 (pe1, pe2, pe3, memorder) ->
        Store0(substitute_pexpr map pe1,
               substitute_pexpr map pe2,
               substitute_pexpr map pe3,
               memorder)
    | Load0 (pe1, pe2, memorder) ->
        Load0 (substitute_pexpr map pe1, 
               substitute_pexpr map pe2,
               memorder)
    | RMW0 _
    | Fence0 _ ->
        assert false
  in
  Action(loc, a, ret)

let rec substitute_expr (map: substitute_map)
                        (Expr(annot, expr_) : 'a typed_expr) =
  let ret = match expr_ with
    | Epure pe ->
        Epure(substitute_pexpr map pe)
    | Ememop(op, pelist) ->
        Ememop(op, List.map (substitute_pexpr map) pelist)
    | Eaction(Paction(p, action)) ->
        Eaction(Paction(p, substitute_action map action))
    | Ecase (pe, clist) ->
        Ecase(substitute_pexpr map pe,
              List.map(fun(pat,e) -> (pat, substitute_expr map e)) clist)
    | Elet(pat, pe, e) ->
        Elet(pat, substitute_pexpr map pe, substitute_expr map e)
    | Eif(pe1, e2, e3) ->
        Eif(substitute_pexpr map pe1, substitute_expr map e2, substitute_expr map e3)
    | Eskip -> Eskip
    | Eccall _
    | Eproc _ ->
        assert false
    | Eunseq elist ->
        Eunseq (List.map (substitute_expr map) elist)
    | Ewseq(pat, e1, e2) ->
        Ewseq(pat, substitute_expr map e1, substitute_expr map e2)
    | Esseq(pat, e1, e2) ->
        Esseq(pat, substitute_expr map e1, substitute_expr map e2)
    | Easeq _
    | Eindet _ -> 
        assert false
    | Ebound(i, e) ->
        Ebound(i, substitute_expr map e)
    | End elist ->
        End (List.map (substitute_expr map) elist) 
    | Esave _ 
    | Erun _ 
    | Epar _
    | Ewait _ ->
        assert false
  in 
    Expr(annot, ret)

