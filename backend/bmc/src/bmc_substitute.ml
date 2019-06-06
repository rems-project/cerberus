open Bmc_utils

open Core

type substitute_map = (sym_ty, typed_pexpr) Pmap.map

(* WARNING: all these functions assume the symbols in the
   substitute_map doesn't clash with the binders in the Core exprs *)

let rec unsafe_substitute_pexpr (map: substitute_map)
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
        PEerror(s, unsafe_substitute_pexpr map pe)
    | PEctor (ctor, pelist) ->
        PEctor(ctor, List.map (fun pe -> unsafe_substitute_pexpr map pe) pelist)
    | PEcase (pe, caselist) ->
        PEcase(unsafe_substitute_pexpr map pe,
               List.map (fun (pat, pe) -> (pat, unsafe_substitute_pexpr map pe))
                        caselist)
    | PEarray_shift (pe_ptr, ty, pe_index) ->
        PEarray_shift(unsafe_substitute_pexpr map pe_ptr, ty,
                      unsafe_substitute_pexpr map pe_index)
    | PEmember_shift (pe_ptr, sym, member) ->
        PEmember_shift(unsafe_substitute_pexpr map pe_ptr, sym, member)
    | PEcfunction pe ->
        PEcfunction(unsafe_substitute_pexpr map pe)
    | PEmemberof _ -> assert false
    | PEnot pe ->
        PEnot(unsafe_substitute_pexpr map pe)
    | PEop (binop, pe1, pe2) ->
        PEop(binop, unsafe_substitute_pexpr map pe1, unsafe_substitute_pexpr map pe2)
    | PEstruct _
    | PEunion _ -> assert false
    | PEcall (name, pelist) ->
        PEcall(name, List.map (fun pe -> unsafe_substitute_pexpr map pe) pelist)
    | PElet (pat, pe1, pe2) ->
        PElet (pat, unsafe_substitute_pexpr map pe1, unsafe_substitute_pexpr map pe2)
    | PEif(pe1, pe2, pe3) ->
        PEif(unsafe_substitute_pexpr map pe1,
             unsafe_substitute_pexpr map pe2,
             unsafe_substitute_pexpr map pe3)
    | PEis_scalar pe ->
        PEis_scalar(unsafe_substitute_pexpr map pe)
    | PEis_integer pe ->
        PEis_integer(unsafe_substitute_pexpr map pe)
    | PEis_signed pe ->
        PEis_signed (unsafe_substitute_pexpr map pe)
    | PEis_unsigned pe ->
        PEis_unsigned (unsafe_substitute_pexpr map pe)
    | PEbmc_assume pe ->
        PEbmc_assume (unsafe_substitute_pexpr map pe)
    | PEare_compatible (pe1, pe2) ->
        PEare_compatible(unsafe_substitute_pexpr map pe1,
                         unsafe_substitute_pexpr map pe2)
  in
    Pexpr(annot, ty, ret)

let rec unsafe_substitute_action (map: substitute_map)
                          (Action(loc, a, action_) : 'a typed_action) =
  let ret = match action_ with
    | Create (pe1, pe2, sym) ->
        Create(unsafe_substitute_pexpr map pe1, unsafe_substitute_pexpr map pe2, sym)
    | CreateReadOnly _ -> assert false
    | Alloc0 (pe1,pe2,sym) ->
        Alloc0(unsafe_substitute_pexpr map pe1, unsafe_substitute_pexpr map pe2, sym)
    | Kill (b, pe) ->
        Kill (b, unsafe_substitute_pexpr map pe)
    | Store0 (is_locking, pe1, pe2, pe3, memorder) ->
        Store0(is_locking,
               unsafe_substitute_pexpr map pe1,
               unsafe_substitute_pexpr map pe2,
               unsafe_substitute_pexpr map pe3,
               memorder)
    | Load0 (pe1, pe2, memorder) ->
        Load0 (unsafe_substitute_pexpr map pe1,
               unsafe_substitute_pexpr map pe2,
               memorder)
    | RMW0 (pe1,pe2,pe3,pe4,mo1,mo2) ->
        RMW0 (unsafe_substitute_pexpr map pe1,
              unsafe_substitute_pexpr map pe2,
              unsafe_substitute_pexpr map pe3,
              unsafe_substitute_pexpr map pe4,
              mo1, mo2)
    | Fence0 mo ->
        Fence0 mo
    | CompareExchangeStrong(pe1,pe2,pe3,pe4,mo1,mo2) ->
        CompareExchangeStrong(unsafe_substitute_pexpr map pe1,
                              unsafe_substitute_pexpr map pe2,
                              unsafe_substitute_pexpr map pe3,
                              unsafe_substitute_pexpr map pe4,
                              mo1,mo2)
    | CompareExchangeWeak(pe1,pe2,pe3,pe4,mo1,mo2) ->
        CompareExchangeWeak(unsafe_substitute_pexpr map pe1,
                            unsafe_substitute_pexpr map pe2,
                            unsafe_substitute_pexpr map pe3,
                            unsafe_substitute_pexpr map pe4,
                            mo1,mo2)
    | LinuxFence mo ->
        LinuxFence mo
    | LinuxStore (pe1, pe2, pe3, memorder) ->
        LinuxStore(unsafe_substitute_pexpr map pe1,
                   unsafe_substitute_pexpr map pe2,
                   unsafe_substitute_pexpr map pe3,
                   memorder)
    | LinuxLoad (pe1, pe2, memorder) ->
        LinuxLoad (unsafe_substitute_pexpr map pe1,
                   unsafe_substitute_pexpr map pe2,
                   memorder)
    | LinuxRMW (pe1, pe2, pe3, memorder) ->
        LinuxRMW (unsafe_substitute_pexpr map pe1,
                  unsafe_substitute_pexpr map pe2,
                  unsafe_substitute_pexpr map pe3,
                  memorder)
  in
  Action(loc, a, ret)

let rec unsafe_substitute_expr (map: substitute_map)
                        (Expr(annot, expr_) : 'a typed_expr) =
  let ret = match expr_ with
    | Epure pe ->
        Epure(unsafe_substitute_pexpr map pe)
    | Ememop(op, pelist) ->
        Ememop(op, List.map (unsafe_substitute_pexpr map) pelist)
    | Eaction(Paction(p, action)) ->
        Eaction(Paction(p, unsafe_substitute_action map action))
    | Ecase (pe, clist) ->
        Ecase(unsafe_substitute_pexpr map pe,
              List.map(fun(pat,e) -> (pat, unsafe_substitute_expr map e)) clist)
    | Elet(pat, pe, e) ->
        Elet(pat, unsafe_substitute_pexpr map pe, unsafe_substitute_expr map e)
    | Eif(pe1, e2, e3) ->
        Eif(unsafe_substitute_pexpr map pe1, unsafe_substitute_expr map e2, unsafe_substitute_expr map e3)
    | Eskip -> Eskip
    | Eccall (a, pe1, pe2, pelist) ->
        Eccall(a, unsafe_substitute_pexpr map pe1,
                  unsafe_substitute_pexpr map pe2,
                  List.map (unsafe_substitute_pexpr map) pelist)
    | Eproc (a, name, pes) ->
        Eproc(a, name, List.map (unsafe_substitute_pexpr map) pes)
    | Eunseq elist ->
        Eunseq (List.map (unsafe_substitute_expr map) elist)
    | Ewseq(pat, e1, e2) ->
        Ewseq(pat, unsafe_substitute_expr map e1, unsafe_substitute_expr map e2)
    | Esseq(pat, e1, e2) ->
        Esseq(pat, unsafe_substitute_expr map e1, unsafe_substitute_expr map e2)
    | Easeq _
    | Eindet _ ->
        assert false
    | Ebound(i, e) ->
        Ebound(i, unsafe_substitute_expr map e)
    | End elist ->
        End (List.map (unsafe_substitute_expr map) elist)
    | Esave(label, letlist, e) ->
        Esave(label,
              List.map (fun (sym, (ty, pe)) ->
                          (sym, (ty, unsafe_substitute_pexpr map pe)))
                       letlist,
              unsafe_substitute_expr map e
              )
    | Erun(a, sym, pelist) ->
        Erun(a, sym, List.map (unsafe_substitute_pexpr map) pelist)
    | Epar _
    | Ewait _ ->
        assert false
  in
    Expr(annot, ret)
