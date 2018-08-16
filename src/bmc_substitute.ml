open Bmc_utils

open Core

type substitute_map = (sym_ty, typed_pexpr) Pmap.map

let rec substitute_pexpr (map: substitute_map)
                         (Pexpr(annot, ty, pexpr_): typed_pexpr) =
  let ret = match pexpr_ with
    | PEsym sym ->
        begin match Pmap.lookup sym map with
        | Some (Pexpr(_, _, pe)) -> pe
        | None -> PEsym sym
        end
    | PEimpl _ -> pexpr_
    | PEval _ -> pexpr_
    | PEconstrained _ -> assert false
    | PEundef _ -> pexpr_
    | PEerror (s, pe) ->
        PEerror(s, substitute_pexpr map pe)
    | PEctor (ctor, pelist) ->
        PEctor(ctor, List.map (fun pe -> substitute_pexpr map pe) pelist)
    | PEcase (pe, caselist) ->
        PEcase(substitute_pexpr map pe,
               List.map (fun (pat, pe) -> (pat, substitute_pexpr map pe))
                        caselist)
    | PEarray_shift (pe_ptr, ty, pe_index) ->
        PEarray_shift(substitute_pexpr map pe_ptr, ty,
                      substitute_pexpr map pe_index)
    | PEmember_shift (pe_ptr, sym, member) ->
        PEmember_shift(substitute_pexpr map pe_ptr, sym, member)
    | PEmemberof _ -> assert false
    | PEnot pe ->
        PEnot(substitute_pexpr map pe)
    | PEop (binop, pe1, pe2) ->
        PEop(binop, substitute_pexpr map pe1, substitute_pexpr map pe2)
    | PEstruct _
    | PEunion _ -> assert false
    | PEcall (name, pelist) ->
        PEcall(name, List.map (fun pe -> substitute_pexpr map pe) pelist)
    | PElet (pat, pe1, pe2) ->
        PElet (pat, substitute_pexpr map pe1, substitute_pexpr map pe2)
    | PEif(pe1, pe2, pe3) ->
        PEif(substitute_pexpr map pe1,
             substitute_pexpr map pe2,
             substitute_pexpr map pe3)
    | PEis_scalar pe ->
        PEis_scalar(substitute_pexpr map pe)
    | PEis_integer pe ->
        PEis_integer(substitute_pexpr map pe)
    | PEis_signed pe ->
        PEis_signed (substitute_pexpr map pe)
    | PEis_unsigned pe ->
        PEis_unsigned (substitute_pexpr map pe)
    | PEbmc_assume pe ->
        PEbmc_assume (substitute_pexpr map pe)

  in
    Pexpr(annot, ty, ret)

let rec substitute_action (map: substitute_map)
                          (Action(loc, a, action_) : 'a typed_action) =
  let ret = match action_ with
    | Create (pe1, pe2, sym) ->
        Create(substitute_pexpr map pe1, substitute_pexpr map pe2, sym)
    | CreateReadOnly _ -> assert false
    | Alloc0 (pe1,pe2,sym) ->
        Alloc0(substitute_pexpr map pe1, substitute_pexpr map pe2, sym)
    | Kill (b, pe) ->
        Kill (b, substitute_pexpr map pe)
    | Store0 (pe1, pe2, pe3, memorder) ->
        Store0(substitute_pexpr map pe1,
               substitute_pexpr map pe2,
               substitute_pexpr map pe3,
               memorder)
    | Load0 (pe1, pe2, memorder) ->
        Load0 (substitute_pexpr map pe1,
               substitute_pexpr map pe2,
               memorder)
    | RMW0 (pe1,pe2,pe3,pe4,mo1,mo2) ->
        RMW0 (substitute_pexpr map pe1,
              substitute_pexpr map pe2,
              substitute_pexpr map pe3,
              substitute_pexpr map pe4,
              mo1, mo2)
    | Fence0 mo ->
        Fence0 mo
    | CompareExchangeStrong(pe1,pe2,pe3,pe4,mo1,mo2) ->
        CompareExchangeStrong(substitute_pexpr map pe1,
                              substitute_pexpr map pe2,
                              substitute_pexpr map pe3,
                              substitute_pexpr map pe4,
                              mo1,mo2)
    | LinuxFence mo ->
        LinuxFence mo
    | LinuxStore (pe1, pe2, pe3, memorder) ->
        LinuxStore(substitute_pexpr map pe1,
                   substitute_pexpr map pe2,
                   substitute_pexpr map pe3,
                   memorder)
    | LinuxLoad (pe1, pe2, memorder) ->
        LinuxLoad (substitute_pexpr map pe1,
                   substitute_pexpr map pe2,
                   memorder)
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
    | Eccall (a, pe, pelist) ->
        Eccall(a, substitute_pexpr map pe,
                  List.map (substitute_pexpr map) pelist)
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
    | Esave(label, letlist, e) ->
        Esave(label,
              List.map (fun (sym, (ty, pe)) ->
                          (sym, (ty, substitute_pexpr map pe)))
                       letlist,
              substitute_expr map e
              )
    | Erun(a, sym, pelist) ->
        Erun(a, sym, List.map (substitute_pexpr map) pelist)
    | Epar _
    | Ewait _ ->
        assert false
  in
    Expr(annot, ret)
