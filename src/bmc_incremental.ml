open Bmc_common
open Bmc_globals
open Bmc_monad
open Bmc_sorts
open Bmc_substitute
open Bmc_utils

open Core
open Core_aux
open Ocaml_mem
open Printf
open Util
open Z3

(* CONTENTS *
 * - BmcInline
 * - BmcSSA
 * - BmcZ3
 * - BmcDropCont
 * - BmcBind
 * - BmcVC
 * - BmcSeqMem
 *)

(* ======= Do inlining ======= *)
module BmcInline = struct
  type run_depth_table = (name, int) Pmap.map
  type state_ty = {
    id_gen : int;
    run_depth_table : run_depth_table;

    file   : unit typed_file; (* unmodified *)

    inline_pexpr_map : (int, typed_pexpr) Pmap.map;
    inline_expr_map  : (int, unit typed_expr) Pmap.map;

    (* procedure-local state *)
    proc_expr : (unit typed_expr) option;
  }
  include EffMonad(struct type state = state_ty end)

  let mk_initial file : state =
    { id_gen           = 0
    ; run_depth_table  = Pmap.empty Pervasives.compare
    ; file             = file
    ; inline_pexpr_map = Pmap.empty Pervasives.compare
    ; inline_expr_map  = Pmap.empty Pervasives.compare
    ; proc_expr        = None
    }

  (* ======= Accessors ======== *)
  let get_fresh_id : int eff =
    get >>= fun st ->
    put {st with id_gen = st.id_gen + 1} >>
    return st.id_gen

  let get_run_depth_table : run_depth_table eff =
    get >>= fun st ->
    return st.run_depth_table

  let put_run_depth_table (new_table: run_depth_table)
                          : unit eff =
    get >>= fun st ->
    put {st with run_depth_table = new_table}

  let lookup_run_depth (label: name) : int eff =
    get_run_depth_table >>= fun table ->
    match Pmap.lookup label table with
    | None  -> return 0
    | Some i -> return i

  let increment_run_depth (label: name) : unit eff =
    lookup_run_depth label  >>= fun depth ->
    get_run_depth_table     >>= fun table ->
    put_run_depth_table (Pmap.add label (depth+1) table)

  let decrement_run_depth (label: name) : unit eff =
    lookup_run_depth label >>= fun depth ->
    get_run_depth_table    >>= fun table ->
    put_run_depth_table (Pmap.add label (depth-1) table)

  let get_file : (unit typed_file) eff =
    get >>= fun st ->
    return st.file

  (* proc_expr *)
  let get_proc_expr : (unit typed_expr) eff =
    get >>= fun st ->
    return (Option.get st.proc_expr)

  let update_proc_expr (proc_expr: unit typed_expr) : unit eff =
    get >>= fun st ->
    put {st with proc_expr = Some proc_expr}

  (* inline maps *)
  let add_inlined_pexpr (id: int) (pexpr: typed_pexpr) : unit eff =
    get >>= fun st ->
    put {st with inline_pexpr_map = Pmap.add id pexpr st.inline_pexpr_map}

  let add_inlined_expr (id: int) (expr: unit typed_expr) : unit eff =
    get >>= fun st ->
    put {st with inline_expr_map = Pmap.add id expr st.inline_expr_map}


  (* ======== Inline functions ======= *)
  let rec inline_pe (Pexpr(annots, bTy, pe_) as pexpr) : typed_pexpr eff =
    get_fresh_id  >>= fun id ->
    (match pe_ with
    | PEsym _  -> return pe_
    | PEimpl const ->
        get_file >>= fun file ->
        begin match Pmap.lookup const file.impl with
        | Some (Def (_, pe)) ->
            inline_pe pe >>= fun inlined_pe ->
            add_inlined_pexpr id inlined_pe >>
            return (PEimpl const)
        | _ -> assert false
        end
    | PEval _  -> return pe_
    | PEconstrained _ -> assert false
    | PEundef _ -> return pe_
    | PEerror _ -> return pe_
    | PEctor (ctor, pes) ->
        mapM inline_pe pes >>= fun inlined_pes ->
        return (PEctor(ctor, inlined_pes))
    | PEcase (pe1, cases) ->
        inline_pe pe1 >>= fun inlined_pe1 ->
        mapM (fun (pat, pe) ->
              inline_pe pe >>= fun inlined_pe ->
              return (pat, inlined_pe)) cases >>= fun inlined_cases ->
        return (PEcase(inlined_pe1, inlined_cases))
    | PEarray_shift (pe1, cty, pe2) ->
        inline_pe pe1 >>= fun inlined_pe1 ->
        inline_pe pe2 >>= fun inlined_pe2 ->
        return (PEarray_shift(inlined_pe1, cty, inlined_pe2))
    | PEmember_shift (pe, sym, cid) ->
        inline_pe pe >>= fun inlined_pe ->
        return (PEmember_shift(inlined_pe, sym, cid))
    | PEnot pe ->
        inline_pe pe >>= fun inlined_pe ->
        return (PEnot(inlined_pe))
    | PEop (bop, pe1, pe2) ->
        inline_pe pe1 >>= fun inlined_pe1 ->
        inline_pe pe2 >>= fun inlined_pe2 ->
        return (PEop(bop, inlined_pe1, inlined_pe2))
    | PEstruct _ -> assert false
    | PEunion _  -> assert false
    | PEcfunction _ -> assert false
    | PEmemberof (tag_sym, memb_ident, pe) ->
        inline_pe pe >>= fun inlined_pe ->
        return (PEmemberof(tag_sym, memb_ident, inlined_pe))
    | PEcall (name, pes)  ->
        lookup_run_depth name >>= fun depth ->
        get_file >>= fun file ->
        (* Get the function called; either from stdlib or impl consts *)
        let (ty, args, fun_expr) =
          match name with
          | Sym sym ->
              begin match Pmap.lookup sym file.stdlib with
              | Some (Fun (ty, args, fun_expr)) -> (ty, args, fun_expr)
              | _ -> assert false
              end
          | Impl impl ->
              begin match Pmap.lookup impl file.impl with
              | Some (IFun (ty, args, fun_expr)) -> (ty, args, fun_expr)
              | _ -> assert false
              end
        in
        if depth >= !!bmc_conf.max_run_depth then
          let error_msg =
            sprintf "call_depth_exceeded: %s" (name_to_string  name) in
          let new_pexpr = (Pexpr([], ty, PEerror(error_msg, pexpr))) in
          inline_pe new_pexpr >>= fun inlined_new_pexpr ->
          add_inlined_pexpr id inlined_new_pexpr >>
          return (PEcall (name, pes))
        else begin
          (* TODO: CBV/CBN semantics? *)
          (* Inline each argument *)
          mapM inline_pe pes >>= fun inlined_pes ->
          (* Substitute arguments in function call *)
          let sub_map = List.fold_right2
              (fun (sym, _) pe table -> Pmap.add sym pe table)
              args inlined_pes (Pmap.empty sym_cmp) in
          (* Get the new function body to work with *)
          let pexpr_to_call = substitute_pexpr sub_map fun_expr in
          increment_run_depth name >>
          inline_pe pexpr_to_call >>= fun inlined_pexpr_to_call ->
          decrement_run_depth name >>
          add_inlined_pexpr id inlined_pexpr_to_call >>
          return (PEcall (name, inlined_pes))
        end
    | PElet (pat, pe1, pe2) ->
        inline_pe pe1 >>= fun inlined_pe1 ->
        inline_pe pe2 >>= fun inlined_pe2 ->
        return (PElet (pat, inlined_pe1, inlined_pe2))
    | PEif (pe1, pe2, pe3) ->
        inline_pe pe1 >>= fun inlined_pe1 ->
        inline_pe pe2 >>= fun inlined_pe2 ->
        inline_pe pe3 >>= fun inlined_pe3 ->
        return (PEif(inlined_pe1, inlined_pe2, inlined_pe3))
    | PEis_scalar pe ->
        inline_pe pe >>= fun inlined_pe ->
        return (PEis_scalar(inlined_pe))
    | PEis_integer pe ->
        inline_pe pe >>= fun inlined_pe ->
        return (PEis_integer(inlined_pe))
    | PEis_signed pe ->
        inline_pe pe >>= fun inlined_pe ->
        return (PEis_signed(inlined_pe))
    | PEis_unsigned pe ->
        inline_pe pe >>= fun inlined_pe ->
        return (PEis_unsigned(inlined_pe))
    | PEare_compatible (pe1, pe2) ->
        inline_pe pe1 >>= fun inlined_pe1 ->
        inline_pe pe2 >>= fun inlined_pe2 ->
        return (PEare_compatible(pe1,pe2))
    | PEbmc_assume pe ->
        inline_pe pe >>= fun inlined_pe ->
        return (PEbmc_assume(inlined_pe))
    ) >>= fun inlined_pe ->
    return (Pexpr(Abmc (Abmc_id id)::annots, bTy, inlined_pe))

  let inline_action (Paction(p, Action(loc, a, action_))) =
    (match action_ with
    | Create (pe1, pe2, pref) ->
        inline_pe pe1 >>= fun inlined_pe1 ->
        inline_pe pe2 >>= fun inlined_pe2 ->
        return (Create(inlined_pe1, inlined_pe2, pref))
    | CreateReadOnly (pe1, pe2, pe3, pref) ->
        inline_pe pe1 >>= fun inlined_pe1 ->
        inline_pe pe2 >>= fun inlined_pe2 ->
        inline_pe pe3 >>= fun inlined_pe3 ->
        return (CreateReadOnly(inlined_pe1, inlined_pe2, inlined_pe3, pref))
    | Alloc0 (pe1, pe2, pref) ->
        inline_pe pe1 >>= fun inlined_pe1 ->
        inline_pe pe2 >>= fun inlined_pe2 ->
        return (Alloc0(inlined_pe1, inlined_pe2, pref))
    | Kill (b, pe) ->
        inline_pe pe >>= fun inlined_pe ->
        return (Kill(b, inlined_pe))
    | Store0 (b, pe1, pe2, pe3, memord) ->
        inline_pe pe1 >>= fun inlined_pe1 ->
        inline_pe pe2 >>= fun inlined_pe2 ->
        inline_pe pe3 >>= fun inlined_pe3 ->
        return (Store0(b, inlined_pe1, inlined_pe2, inlined_pe3, memord))
    | Load0 (pe1, pe2, memord) ->
        inline_pe pe1 >>= fun inlined_pe1 ->
        inline_pe pe2 >>= fun inlined_pe2 ->
        return (Load0(inlined_pe1, inlined_pe2, memord))
    | RMW0 (pe1, pe2, pe3, pe4, mo1, mo2) ->
        inline_pe pe1 >>= fun inlined_pe1 ->
        inline_pe pe2 >>= fun inlined_pe2 ->
        inline_pe pe3 >>= fun inlined_pe3 ->
        inline_pe pe4 >>= fun inlined_pe4 ->
        return (RMW0(inlined_pe1, inlined_pe2, inlined_pe3, inlined_pe4, mo1, mo2))
    | Fence0 mo ->
        return (Fence0(mo))
    | CompareExchangeStrong(pe1, pe2, pe3, pe4, mo1, mo2) ->
        inline_pe pe1 >>= fun inlined_pe1 ->
        inline_pe pe2 >>= fun inlined_pe2 ->
        inline_pe pe3 >>= fun inlined_pe3 ->
        inline_pe pe4 >>= fun inlined_pe4 ->
        return (CompareExchangeStrong(inlined_pe1, inlined_pe2, inlined_pe3, inlined_pe4, mo1, mo2))
    | LinuxFence (mo) ->
        return (LinuxFence(mo))
    | LinuxLoad (pe1, pe2, mo) ->
        inline_pe pe1 >>= fun inlined_pe1 ->
        inline_pe pe2 >>= fun inlined_pe2 ->
        return (LinuxLoad(inlined_pe1, inlined_pe2, mo))
    | LinuxStore(pe1, pe2, pe3, mo) ->
        inline_pe pe1 >>= fun inlined_pe1 ->
        inline_pe pe2 >>= fun inlined_pe2 ->
        inline_pe pe3 >>= fun inlined_pe3 ->
        return (LinuxStore(inlined_pe1, inlined_pe2, inlined_pe3, mo))
    | LinuxRMW (pe1, pe2, pe3, mo) ->
        inline_pe pe1 >>= fun inlined_pe1 ->
        inline_pe pe2 >>= fun inlined_pe2 ->
        inline_pe pe3 >>= fun inlined_pe3 ->
        return (LinuxRMW(inlined_pe1, inlined_pe2, inlined_pe3, mo))
    ) >>= fun inlined_action ->
    return (Paction(p, Action(loc, a, inlined_action)))

  let rec inline_e (Expr(annots, e_)) : (unit typed_expr) eff =
    get_fresh_id >>= fun id ->
    (match e_ with
    | Epure pe ->
        inline_pe pe >>= fun inlined_pe ->
        return (Epure(inlined_pe))
    | Ememop (memop, pes) ->
        mapM inline_pe pes >>= fun inlined_pes ->
        return (Ememop (memop, inlined_pes))
    | Eaction pact -> (* TODO: lazy assumption on structure of Core from C *)
        inline_action pact >>= fun inlined_pact ->
        return (Eaction inlined_pact)
    | Ecase (pe, cases) ->
        inline_pe pe >>= fun inlined_pe ->
        mapM (fun (pat, e) ->
              inline_e e >>= fun inlined_e ->
              return (pat, inlined_e)) cases >>= fun inlined_cases ->
        return (Ecase(inlined_pe, inlined_cases))
    | Elet (pat, pe, e) ->
        inline_pe pe  >>= fun inlined_pe ->
        inline_e e    >>= fun inlined_e  ->
        return (Elet (pat, inlined_pe, inlined_e))
    | Eif (pe, e1, e2) ->
        inline_pe pe >>= fun inlined_pe ->
        inline_e e1  >>= fun inlined_e1 ->
        inline_e e2  >>= fun inlined_e2 ->
        return (Eif (inlined_pe, inlined_e1, inlined_e2))
    | Eskip -> return Eskip
    | Eccall _ -> (* TODO: broken currently *) assert false
    | Eproc _ -> assert false
    | Eunseq es ->
        mapM inline_e es >>= fun inlined_es ->
        return (Eunseq(inlined_es))
    | Ewseq (pat, e1, e2) ->
        inline_e e1 >>= fun inlined_e1 ->
        inline_e e2 >>= fun inlined_e2 ->
        return (Ewseq(pat, inlined_e1, inlined_e2))
    | Esseq (pat, e1, e2) ->
        inline_e e1 >>= fun inlined_e1 ->
        inline_e e2 >>= fun inlined_e2 ->
        return (Esseq(pat, inlined_e1, inlined_e2))
    | Easeq _ -> assert false
    | Eindet (n, e) ->
        inline_e e >>= fun inlined_e ->
        return (Eindet(n, inlined_e))
    | Ebound (n, e) ->
        inline_e e >>= fun inlined_e ->
        return (Ebound(n, inlined_e))
    | End es ->
        mapM inline_e es >>= fun inlined_es ->
        return (End (inlined_es))
    | Esave (name, varlist, e) ->
        let sub_map = List.fold_right (fun (sym, (cbt, pe)) map ->
          Pmap.add sym pe map) varlist (Pmap.empty sym_cmp) in
        let to_check = substitute_expr sub_map e in
        inline_e to_check >>= fun inlined_to_check ->
        add_inlined_expr id inlined_to_check >>
        return (Esave(name, varlist, e))
    | Erun (a, label, pelist) ->
        lookup_run_depth (Sym label) >>= fun depth ->
        if depth >= !!bmc_conf.max_run_depth then
          let error_msg =
            sprintf "Erun_depth_exceeded: %s" (name_to_string (Sym label)) in
          (* TODO: hacky *)
          let new_expr =
            (Expr([],Epure(Pexpr([], BTy_unit,
                           PEerror(error_msg,
                                  Pexpr([], BTy_unit, PEval (Vunit))))))) in
          inline_e new_expr >>= fun inlined_new_expr ->
          add_inlined_expr id inlined_new_expr >>
          return (Erun(a, label, pelist))
        else begin
          get_proc_expr >>= fun proc_expr ->
          let (cont_syms, cont_expr) = Option.get (find_labeled_continuation
                            Sym.instance_Basic_classes_Eq_Symbol_sym_dict
                            label proc_expr) in
          assert (List.length pelist = List.length cont_syms);
          let sub_map = List.fold_right2
              (fun sym pe map -> Pmap.add sym pe map)
              cont_syms pelist (Pmap.empty sym_cmp) in
          let cont_to_check = substitute_expr sub_map cont_expr in
          increment_run_depth (Sym label) >>
          inline_e cont_to_check >>= fun inlined_cont_to_check ->
          decrement_run_depth (Sym label) >>
          add_inlined_expr id inlined_cont_to_check >>
          return (Erun(a, label, pelist))
        end
    | Epar es ->
        mapM inline_e es >>= fun inlined_es ->
        return (Epar (inlined_es))
    | Ewait _       -> assert false
    ) >>= fun inlined_e ->
    return (Expr(Abmc (Abmc_id id)::annots, inlined_e))

  let inline_globs (gname, bty, e) =
    inline_e e >>= fun inlined_e ->
    return (gname, bty, inlined_e)

  let inline (file: unit typed_file) (fn_to_check: sym_ty)
             : (unit typed_file) eff =
    mapM inline_globs file.globs >>= fun globs ->
    (match Pmap.lookup fn_to_check file.funs with
     | Some (Proc (annot, bTy, params, e)) ->
         update_proc_expr e >>= fun () ->
         inline_e e         >>= fun inlined_e ->
         return (Proc (annot, bTy, params, inlined_e))
     | Some (Fun (ty, params, pe)) ->
         inline_pe pe >>= fun inlined_pe ->
         return (Fun (ty, params, inlined_pe))
     | _ -> assert false
    ) >>= fun new_fn ->
    return {file with globs = globs;
                      funs  = Pmap.add fn_to_check new_fn file.funs}
end

(* Do SSA renaming and also get a global map from sym -> cbt
 * to construct Z3 Expr *)
module BmcSSA = struct
  type sym_table_ty = (sym_ty, sym_ty) Pmap.map
  type sym_expr_table_ty = (sym_ty, Expr.expr) Pmap.map

  type state_ty = {
    sym_supply    : sym_supply_ty;
    sym_table     : sym_table_ty;
    sym_expr_table  : sym_expr_table_ty;

    file   : unit typed_file; (* unmodified *)

    inline_pexpr_map : (int, typed_pexpr) Pmap.map;
    inline_expr_map  : (int, unit typed_expr) Pmap.map;
  }
  include EffMonad(struct type state = state_ty end)

  let mk_initial sym_supply file inline_pexpr_map inline_expr_map : state =
    { sym_supply       = sym_supply;
      sym_table        = Pmap.empty sym_cmp;
      sym_expr_table     = Pmap.empty sym_cmp;
      file             = file;
      inline_pexpr_map = inline_pexpr_map;
      inline_expr_map  = inline_expr_map;
    }

  (* accessors *)
  let get_sym_table : sym_table_ty eff =
    get >>= fun st ->
    return st.sym_table

  let put_sym_table (table: sym_table_ty) : unit eff =
    get >>= fun st ->
    put {st with sym_table = table}

  let lookup_sym (sym: sym_ty) : sym_ty eff =
    get_sym_table >>= fun sym_table ->
    match Pmap.lookup sym sym_table with
    | None -> failwith (sprintf "BmcSSA error: sym %s not found"
                                (symbol_to_string sym))
    | Some s -> return s

  let add_to_sym_table (sym1: sym_ty) (sym2: sym_ty) : unit eff =
    get_sym_table >>= fun table ->
    put_sym_table (Pmap.add sym1 sym2 table)

  let get_sym_expr_table : sym_expr_table_ty eff =
    get >>= fun st ->
    return st.sym_expr_table

  let put_sym_expr_table (table: sym_expr_table_ty) : unit eff =
    get >>= fun st ->
    put {st with sym_expr_table = table}

  let put_sym_expr (sym: sym_ty) (ty: core_base_type) : unit eff =
    get_sym_expr_table >>= fun table ->
    match Pmap.lookup sym table with
    | Some _ -> failwith (sprintf "BmcSSA error: sym %s exists in sym_expr_table"
                                  (symbol_to_string sym))
    | None ->
        let expr = mk_fresh_const (symbol_to_string sym) (cbt_to_z3 ty) in
        put_sym_expr_table (Pmap.add sym expr table)

  let get_sym_supply : sym_supply_ty eff =
    get >>= fun st ->
    return st.sym_supply

  let update_sym_supply new_supply : unit eff =
    get >>= fun st ->
    put {st with sym_supply = new_supply}

  let get_fresh_sym (str: string option) : sym_ty eff =
    get >>= fun st ->
    let (new_sym, new_supply) = Sym.fresh_fancy str st.sym_supply in
    update_sym_supply new_supply >>
    return new_sym

  (* inline maps *)
  let get_inline_pexpr (uid: int): typed_pexpr eff =
    get >>= fun st ->
    match Pmap.lookup uid st.inline_pexpr_map with
    | None -> failwith (sprintf "Error: BmcSSA inline_pexpr not found %d"
                                uid)
    | Some pe -> return pe

  let get_inline_expr (uid: int): (unit typed_expr) eff =
    get >>= fun st ->
    match Pmap.lookup uid st.inline_expr_map with
    | None -> failwith (sprintf "Error: BmcSSA inline_expr not found %d"
                                uid)
    | Some e -> return e


  let update_inline_pexpr (uid: int) (pexpr: typed_pexpr) : unit eff =
    get >>= fun st ->
    put {st with inline_pexpr_map = Pmap.add uid pexpr st.inline_pexpr_map}

  let update_inline_expr (uid: int) (expr: (unit typed_expr)) : unit eff =
    get >>= fun st ->
    put {st with inline_expr_map = Pmap.add uid expr st.inline_expr_map}


  (* Core functions*)
  let rename_sym (Symbol(n, stropt) as sym: sym_ty) : sym_ty eff =
    let str = match stropt with
              | None -> "_" ^ (string_of_int n)
              | Some s -> s ^ "_" ^ (string_of_int n) in
    get_fresh_sym (Some str) >>= fun new_sym ->
    add_to_sym_table sym new_sym >>
    return new_sym

  let rec ssa_pattern (Pattern(annots, pat) : typed_pattern) : typed_pattern eff =
    (match pat with
     | CaseBase (Some sym, typ) ->
         rename_sym sym >>= fun new_sym ->
         put_sym_expr new_sym typ >>
         return (CaseBase(Some new_sym, typ))
     | CaseBase (None, _) ->
         return pat
     | CaseCtor (ctor, patlist) ->
         mapM ssa_pattern patlist >>= fun ssad_patlist ->
         return (CaseCtor(ctor, ssad_patlist))
    ) >>= fun ssad_pat ->
    return (Pattern(annots, ssad_pat))

  let rec ssa_pe (Pexpr(annots, bTy, pe_) as pexpr) : typed_pexpr eff =
    let uid = get_id_pexpr pexpr in
    get_sym_table >>= fun original_table ->
    (match pe_ with
    | PEsym sym ->
        lookup_sym sym >>= fun ssad_sym ->
        return (PEsym ssad_sym)
    | PEimpl _ ->
        get_inline_pexpr uid >>= fun inlined_pe ->
        ssa_pe inlined_pe    >>= fun ssad_inlined_pe ->
        update_inline_pexpr uid ssad_inlined_pe >>
        return pe_
    | PEval _ -> return pe_
    | PEconstrained _ -> assert false
    | PEundef _ -> return pe_
    | PEerror _ -> return pe_
    | PEctor (ctor, pelist) ->
        mapM ssa_pe pelist >>= fun ssad_pelist ->
        return (PEctor(ctor, ssad_pelist))
    | PEcase (pe1, caselist) ->
        ssa_pe pe1 >>= fun ssad_pe1 ->
        mapM (fun (pat,pe) -> get_sym_table   >>= fun old_table ->
                              ssa_pattern pat >>= fun ssad_pat ->
                              ssa_pe pe       >>= fun ssad_pe ->
                              put_sym_table old_table >>
                              return (ssad_pat, ssad_pe))
             caselist >>= fun ssad_caselist ->
        return (PEcase(ssad_pe1, ssad_caselist))
    | PEarray_shift (pe1, ty, pe2) ->
        ssa_pe pe1 >>= fun ssad_pe1 ->
        ssa_pe pe2 >>= fun ssad_pe2 ->
        return (PEarray_shift(ssad_pe1, ty, ssad_pe2))
    | PEmember_shift (ptr, name, member) ->
        ssa_pe ptr >>= fun ssad_ptr ->
        return (PEmember_shift(ssad_ptr, name, member))
    | PEnot pe ->
        ssa_pe pe >>= fun ssad_pe ->
        return (PEnot ssad_pe)
    | PEop (binop, pe1, pe2) ->
        ssa_pe pe1 >>= fun ssad_pe1 ->
        ssa_pe pe2 >>= fun ssad_pe2 ->
        return (PEop(binop, ssad_pe1, ssad_pe2))
    | PEstruct _ -> assert false
    | PEunion _  -> assert false
    | PEcfunction _ -> assert false
    | PEmemberof (sym, id, pe) ->
        ssa_pe pe >>= fun ssad_pe ->
        return (PEmemberof(sym, id, ssad_pe))
    | PEcall (name, arglist) ->
        (* syms in arglist was just substituted into inlined_pe;
         * so nothing different needed to be done to ssa. *)
        get_inline_pexpr uid >>= fun inlined_pe ->
        ssa_pe inlined_pe    >>= fun ssad_inlined_pe ->
        update_inline_pexpr uid ssad_inlined_pe >>
        (* For debugging purposes, we update arglist *)
        get_sym_table >>= fun old_table ->
        mapM ssa_pe arglist >>= fun ssad_arglist ->
        put_sym_table old_table >>
        return (PEcall(name, ssad_arglist))
   | PElet (pat, pe1, pe2) ->
        ssa_pe pe1 >>= fun ssad_pe1 ->
        ssa_pattern pat >>= fun ssad_pat ->
        ssa_pe pe2 >>= fun ssad_pe2 ->
        return (PElet(ssad_pat, ssad_pe1, ssad_pe2))
    | PEif (pe1, pe2, pe3) ->
        ssa_pe pe1 >>= fun ssad_pe1 ->
        get_sym_table >>= fun old_table ->
        ssa_pe pe2 >>= fun ssad_pe2 ->
        put_sym_table old_table >>
        ssa_pe pe3 >>= fun ssad_pe3 ->
        put_sym_table old_table >>
        return (PEif(ssad_pe1, ssad_pe2, ssad_pe3))
    | PEis_scalar pe ->
        ssa_pe pe >>= fun ssad_pe ->
        return (PEis_scalar(ssad_pe))
    | PEis_integer pe ->
        ssa_pe pe >>= fun ssad_pe ->
        return (PEis_integer(ssad_pe))
    | PEis_signed pe ->
        ssa_pe pe >>= fun ssad_pe ->
        return (PEis_signed(ssad_pe))
    | PEis_unsigned pe ->
        ssa_pe pe >>= fun ssad_pe ->
        return (PEis_unsigned(ssad_pe))
    | PEare_compatible (pe1, pe2) ->
        ssa_pe pe1 >>= fun ssad_pe1 ->
        ssa_pe pe2 >>= fun ssad_pe2 ->
        return (PEare_compatible(ssad_pe1,ssad_pe2))
    | PEbmc_assume pe ->
        ssa_pe pe >>= fun ssad_pe ->
        return (PEbmc_assume ssad_pe)
    ) >>= fun ssad_pe ->
    put_sym_table original_table >>
    return (Pexpr(annots, bTy, ssad_pe))

  let ssa_action (Paction(p, Action(loc, a, action_))) =
    (match action_ with
    | Create (pe1, pe2, pref) ->
        ssa_pe pe1 >>= fun ssad_pe1 ->
        ssa_pe pe2 >>= fun ssad_pe2 ->
        return (Create(ssad_pe1, ssad_pe2, pref))
    | CreateReadOnly (pe1, pe2, pe3, pref) ->
        ssa_pe pe1 >>= fun ssad_pe1 ->
        ssa_pe pe2 >>= fun ssad_pe2 ->
        ssa_pe pe3 >>= fun ssad_pe3 ->
        return (CreateReadOnly(ssad_pe1, ssad_pe2, ssad_pe3, pref))
    | Alloc0 (pe1, pe2, pref) ->
        ssa_pe pe1 >>= fun ssad_pe1 ->
        ssa_pe pe2 >>= fun ssad_pe2 ->
        return (Alloc0(ssad_pe1, ssad_pe2, pref))
    | Kill (b, pe) ->
        ssa_pe pe >>= fun ssad_pe ->
        return (Kill(b, ssad_pe))
    | Store0 (b, pe1, pe2, pe3, memord) ->
        ssa_pe pe1 >>= fun ssad_pe1 ->
        ssa_pe pe2 >>= fun ssad_pe2 ->
        ssa_pe pe3 >>= fun ssad_pe3 ->
        return (Store0(b, ssad_pe1, ssad_pe2, ssad_pe3, memord))
    | Load0 (pe1, pe2, memord) ->
        ssa_pe pe1 >>= fun ssad_pe1 ->
        ssa_pe pe2 >>= fun ssad_pe2 ->
        return (Load0(ssad_pe1, ssad_pe2, memord))
    | RMW0 (pe1, pe2, pe3, pe4, mo1, mo2) ->
        ssa_pe pe1 >>= fun ssad_pe1 ->
        ssa_pe pe2 >>= fun ssad_pe2 ->
        ssa_pe pe3 >>= fun ssad_pe3 ->
        ssa_pe pe4 >>= fun ssad_pe4 ->
        return (RMW0(ssad_pe1, ssad_pe2, ssad_pe3, ssad_pe4, mo1, mo2))
    | Fence0 mo ->
        return (Fence0(mo))
    | CompareExchangeStrong(pe1, pe2, pe3, pe4, mo1, mo2) ->
        ssa_pe pe1 >>= fun ssad_pe1 ->
        ssa_pe pe2 >>= fun ssad_pe2 ->
        ssa_pe pe3 >>= fun ssad_pe3 ->
        ssa_pe pe4 >>= fun ssad_pe4 ->
        return (CompareExchangeStrong(ssad_pe1, ssad_pe2, ssad_pe3, ssad_pe4, mo1, mo2))
    | LinuxFence (mo) ->
        return (LinuxFence(mo))
    | LinuxLoad (pe1, pe2, mo) ->
        ssa_pe pe1 >>= fun ssad_pe1 ->
        ssa_pe pe2 >>= fun ssad_pe2 ->
        return (LinuxLoad(ssad_pe1, ssad_pe2, mo))
    | LinuxStore(pe1, pe2, pe3, mo) ->
        ssa_pe pe1 >>= fun ssad_pe1 ->
        ssa_pe pe2 >>= fun ssad_pe2 ->
        ssa_pe pe3 >>= fun ssad_pe3 ->
        return (LinuxStore(ssad_pe1, ssad_pe2, ssad_pe3, mo))
    | LinuxRMW (pe1, pe2, pe3, mo) ->
        ssa_pe pe1 >>= fun ssad_pe1 ->
        ssa_pe pe2 >>= fun ssad_pe2 ->
        ssa_pe pe3 >>= fun ssad_pe3 ->
        return (LinuxRMW(ssad_pe1, ssad_pe2, ssad_pe3, mo))
    ) >>= fun ssad_action ->
    return (Paction(p, Action(loc, a, ssad_action)))

  let rec ssa_e (Expr(annots, e_) as expr) : (unit typed_expr) eff =
    let uid = get_id_expr expr in
    get_sym_table >>= fun original_table ->
    (match e_ with
    | Epure pe ->
        ssa_pe pe >>= fun ssad_pe ->
        return (Epure ssad_pe)
    | Ememop (memop, pelist) ->
        mapM ssa_pe pelist >>= fun ssad_pelist ->
        return (Ememop(memop, ssad_pelist))
    | Eaction paction ->
        ssa_action paction >>= fun ssad_paction ->
        return (Eaction ssad_paction)
    | Ecase (pe, caselist) ->
        ssa_pe pe >>= fun ssad_pe ->
        mapM (fun (pat,e) -> get_sym_table   >>= fun old_table ->
                             ssa_pattern pat >>= fun ssad_pat ->
                             ssa_e e         >>= fun ssad_e ->
                             put_sym_table old_table >>
                             return (ssad_pat, ssad_e))
             caselist >>= fun ssad_caselist ->
        return (Ecase(ssad_pe, ssad_caselist))
    | Elet (pat, pe1, e2) ->
        ssa_pe pe1      >>= fun ssad_pe1 ->
        ssa_pattern pat >>= fun ssad_pat ->
        ssa_e e2        >>= fun ssad_e2 ->
        return (Elet(ssad_pat, ssad_pe1, ssad_e2))
    | Eif (pe, e1, e2) ->
        ssa_pe pe       >>= fun ssad_pe ->
        get_sym_table   >>= fun old_table ->
        ssa_e e1        >>= fun ssad_e1 ->
        put_sym_table old_table >>
        ssa_e e2        >>= fun ssad_e2 ->
        put_sym_table old_table >>
        return (Eif(ssad_pe, ssad_e1, ssad_e2))
    | Eskip ->
        return Eskip
    | Eccall _ -> assert false
    | Eproc _  -> assert false
    | Eunseq es ->
        mapM ssa_e es >>= fun ssad_es ->
        return (Eunseq ssad_es)
    | Ewseq (pat, e1, e2) ->
        ssa_e e1        >>= fun ssad_e1 ->
        ssa_pattern pat >>= fun ssad_pat ->
        ssa_e e2        >>= fun ssad_e2 ->
        return (Ewseq(ssad_pat, ssad_e1, ssad_e2))
    | Esseq (pat, e1, e2) ->
        ssa_e e1        >>= fun ssad_e1 ->
        ssa_pattern pat >>= fun ssad_pat ->
        ssa_e e2        >>= fun ssad_e2 ->
        return (Esseq(ssad_pat, ssad_e1, ssad_e2))
    | Easeq _ -> assert false
    | Eindet _ -> assert false
    | Ebound (n, e1) ->
        ssa_e e1 >>= fun ssad_e1 ->
        return (Ebound(n, ssad_e1))
    | End elist ->
        mapM ssa_e elist >>= fun ssad_elist ->
        return (End elist)
    | Esave (name, varlist, e) ->
        (* Just update inline_expr_map *)
        get_inline_expr uid >>= fun inlined_e ->
        ssa_e inlined_e >>= fun ssad_inlined_e ->
        update_inline_expr uid ssad_inlined_e >>
        (* NOT ANYMORE; For debugging purposes, we update varlist *)
        (*mapM (fun (sym, (cbt, pe)) ->
                ssa_pe pe >>= fun ssad_pe ->
                return (sym, (cbt, ssad_pe)))
             varlist >>= fun ssad_varlist ->*)
        return (Esave(name, varlist, e))
    | Erun (a, sym, pelist) ->
        get_inline_expr uid >>= fun inline_e ->
        ssa_e inline_e      >>= fun ssad_inlined_e ->
        update_inline_expr uid ssad_inlined_e >>
        (* NOT ANYMORE; For debugging purposes, we update pelist *)
        (*mapM ssa_pe pelist  >>= fun ssad_pelist ->*)
        return (Erun(a, sym, pelist))
    | Epar _
    | Ewait _       ->
        assert false
    ) >>= fun ssad_e ->
      put_sym_table original_table >>
      return (Expr(annots, ssad_e))

    let ssa_globs (gname, bty, e) =
      (* Globals are not given fresh names for no arbitrary reason... *)
      add_to_sym_table gname gname >>
      put_sym_expr gname bty >>
      ssa_e e >>= fun ssad_e ->
      return (gname, bty, ssad_e)

    let ssa_param ((sym, cbt): (sym_ty * core_base_type)) =
      rename_sym sym >>= fun new_sym ->
      put_sym_expr new_sym cbt >>
      return (new_sym, cbt)

    let ssa (file: unit typed_file) (fn_to_check: sym_ty)
            : (unit typed_file) eff =
      mapM ssa_globs file.globs >>= fun ssad_globs ->
      (match Pmap.lookup fn_to_check file.funs with
       | Some (Proc(annot, bTy, params, e)) ->
          ssa_e e                >>= fun ssad_e ->
          mapM ssa_param params  >>= fun ssad_params ->
          return (Proc (annot, bTy, ssad_params, ssad_e))
       | Some (Fun (ty, params, pe)) ->
          ssa_pe pe             >>= fun ssad_pe ->
          mapM ssa_param params >>= fun ssad_params ->
          return (Fun (ty, ssad_params, ssad_pe))
       | _ -> assert false
      ) >>= fun new_fn ->
      return {file with globs = ssad_globs;
                        funs  = Pmap.add fn_to_check new_fn file.funs}

end
(* ======= Convert to Z3 exprs ======= *)
module BmcZ3 = struct
  type alloc = int
  type aid = int

  type ctype_sort = ctype * Sort.sort

  (* Massive TODO *)
  type intermediate_action =
    | ICreate of aid * (* TODO: align *) ctype_sort list * alloc
    | IKill of aid
    | ILoad of aid * (* TODO: list *) ctype_sort * (* ptr *) Expr.expr * (* rval *) Expr.expr * Cmm_csem.memory_order
    | IStore of aid * ctype_sort * (* ptr *) Expr.expr * (* wval *) Expr.expr * Cmm_csem.memory_order
    | ICompareExchangeStrong of aid * ctype_sort * (* object *) Expr.expr * (*expected *) Expr.expr * (* desired *) Expr.expr * (* rval_expected *) Expr.expr * (* rval_object *) Expr.expr * Cmm_csem.memory_order * Cmm_csem.memory_order
    | IFence of aid * Cmm_csem.memory_order
    | ILinuxLoad of aid * ctype_sort * (* ptr *) Expr.expr * (* rval *) Expr.expr * Linux.memory_order0
    | ILinuxStore of aid * ctype_sort * (* ptr *) Expr.expr * (* wval *) Expr.expr * Linux.memory_order0
    | ILinuxFence of aid * Linux.memory_order0

  type z3_state = {
    (* Builds expr_map, case_guard_map, and action_map *)
    expr_map      : (int, Expr.expr) Pmap.map;
    case_guard_map: (int, Expr.expr list) Pmap.map;
    action_map    : (int, intermediate_action) Pmap.map;

    file          : unit typed_file;

    (* Internal state *)
    alloc_supply  : alloc;
    aid_supply    : aid;

    inline_pexpr_map: (int, typed_pexpr) Pmap.map;
    inline_expr_map : (int, unit typed_expr) Pmap.map;
    sym_table       : (sym_ty, Expr.expr) Pmap.map;
  }

  let mk_initial file inline_pexpr_map inline_expr_map sym_table: z3_state = {
    expr_map       = Pmap.empty Pervasives.compare;
    case_guard_map = Pmap.empty Pervasives.compare;
    action_map     = Pmap.empty Pervasives.compare;

    file = file;

    alloc_supply = 0;
    aid_supply   = 0;

    inline_pexpr_map = inline_pexpr_map;
    inline_expr_map  = inline_expr_map;
    sym_table        = sym_table;
  }

  include EffMonad(struct type state = z3_state end)

  let add_expr (uid: int) (expr: Expr.expr) : unit eff =
    get >>= fun st ->
    put {st with expr_map = Pmap.add uid expr st.expr_map}

  let add_guards (uid: int) (guards: Expr.expr list) : unit eff =
    get >>= fun st ->
    put {st with case_guard_map = Pmap.add uid guards st.case_guard_map}

  let add_action (uid: int) (action: intermediate_action) : unit eff =
    get >>= fun st ->
    put {st with action_map = Pmap.add uid action st.action_map}

  let get_file : (unit typed_file) eff =
    get >>= fun st ->
    return st.file

  let lookup_sym (sym: sym_ty) : Expr.expr eff =
    get >>= fun st ->
    match Pmap.lookup sym st.sym_table with
    | None -> failwith (sprintf "Error: BmcZ3 %s not found in sym_table"
                                (symbol_to_string sym))
    | Some expr -> return expr

  (* internal state *)

  (* get new alloc and update supply *)
  let get_fresh_alloc : alloc eff =
    get                    >>= fun st ->
    return st.alloc_supply >>= fun alloc ->
    put {st with alloc_supply = alloc + 1} >>= fun () ->
    return alloc

  let get_fresh_aid : aid eff =
    get                  >>= fun st ->
    return st.aid_supply >>= fun aid ->
    put {st with aid_supply = aid + 1} >>
    return aid

  (* inline expr maps *)
  let get_inline_pexpr (uid: int): typed_pexpr eff =
    get >>= fun st ->
    match Pmap.lookup uid st.inline_pexpr_map with
    | None -> failwith (sprintf "Error: BmcZ3 inline_pexpr not found %d" uid)
    | Some pe -> return pe

  let get_inline_expr (uid: int): (unit typed_expr) eff =
    get >>= fun st ->
    match Pmap.lookup uid st.inline_expr_map with
    | None -> failwith (sprintf "Error: BmcZ3 inline_expr not found %d" uid)
    | Some e -> return e

  (* HELPERS *)
  let compute_case_guards (patterns: typed_pattern list)
                          (to_match: Expr.expr)
                          : Expr.expr * Expr.expr list =
    let pattern_guards =
      List.map (fun pat -> pattern_match pat to_match) patterns in
    let case_guards = List.mapi (
        fun i expr ->
          mk_and [ mk_not (mk_or (list_take i pattern_guards))
                 ; expr]) pattern_guards in
    let vc = mk_or pattern_guards in
    (vc, case_guards)

  (* SMT stuff *)
  let rec z3_pe (Pexpr(annots, bTy, pe_) as pexpr) : Expr.expr eff =
    let uid = get_id_pexpr pexpr in
    (match pe_ with
    | PEsym sym ->
        lookup_sym sym
    | PEimpl _ ->
        get_inline_pexpr uid >>= fun inline_pe ->
        z3_pe inline_pe
    | PEval cval ->
       return (value_to_z3 cval)
    | PEconstrained _ -> assert false
    | PEundef _ ->
        let sort = cbt_to_z3 bTy in
        return (mk_fresh_const (sprintf "undef_%d" uid) sort)
    | PEerror _ ->
        let sort = cbt_to_z3 bTy in
        return (mk_fresh_const (sprintf "error_%d" uid) sort)
    | PEctor (Civmin, [Pexpr(_, BTy_ctype, PEval (Vctype ctype))]) ->
        assert (is_integer_type ctype);
        return (Pmap.find ctype ImplFunctions.ivmin_map)
    | PEctor(Civmax, [Pexpr(_, BTy_ctype, PEval (Vctype ctype))]) ->
        assert (is_integer_type ctype);
        return (Pmap.find ctype ImplFunctions.ivmax_map)
    | PEctor(Civsizeof, [Pexpr(_, BTy_ctype, PEval (Vctype ctype))]) ->
        assert (is_integer_type ctype);
        return (Pmap.find ctype ImplFunctions.sizeof_map)
    | PEctor (ctor, pes) ->
        mapM z3_pe pes >>= fun z3d_pes ->
        return (ctor_to_z3 ctor z3d_pes (Some bTy))
    | PEcase (pe, cases) ->
        assert (List.length cases > 0);
        z3_pe pe                              >>= fun z3d_pe ->
        mapM z3_pe (List.map snd cases)       >>= fun z3d_cases_pe ->
        let (_,guards) = compute_case_guards (List.map fst cases) z3d_pe in
        add_guards uid guards >>
        return (mk_guarded_ite z3d_cases_pe guards)
    | PEarray_shift (ptr, ty, index) ->
        (* TODO: do properly *)
        z3_pe ptr      >>= fun z3d_ptr ->
        z3_pe index    >>= fun z3d_index ->
        get_file >>= fun file ->
        let ty_size = bmcz3sort_size (ctype_to_bmcz3sort ty file) in
        let shift_size = binop_to_z3 OpMul z3d_index (int_to_z3 ty_size) in
        let addr = PointerSort.get_addr z3d_ptr in
        return (PointerSort.mk_ptr (AddressSort.shift_index_by_n addr shift_size))
    | PEmember_shift (ptr, sym, member) ->
        z3_pe ptr >>= fun z3d_ptr ->
        get_file  >>= fun file ->
        begin match Pmap.lookup sym file.tagDefs with
        | Some (StructDef memlist) ->
            let memsizes = List.map (fun (cid, cbt) ->
                (cid, bmcz3sort_size (ctype_to_bmcz3sort cbt file))
              ) memlist in
            let (shift_size, _) = List.fold_left (
                fun (acc, skip) (cid, n) ->
                  if cabsid_cmp cid member = 0 || skip then (acc, true)
                  else (acc + n, false)
            ) (0, false) memsizes in
            let addr = PointerSort.get_addr z3d_ptr in
            let new_addr =
              AddressSort.shift_index_by_n addr (int_to_z3 shift_size) in
            return (PointerSort.mk_ptr new_addr)
        | _ -> assert false
        end
    | PEnot pe ->
        z3_pe pe >>= fun z3d_pe ->
        return (mk_not z3d_pe)
    | PEop (binop, pe1, pe2) ->
        z3_pe pe1 >>= fun z3d_pe1 ->
        z3_pe pe2 >>= fun z3d_pe2 ->
        return (binop_to_z3 binop z3d_pe1 z3d_pe2)
    | PEstruct _    -> assert false
    | PEunion _     -> assert false
    | PEcfunction _ -> assert false
    | PEmemberof _  -> assert false
    | PEcall _ ->
        get_inline_pexpr uid >>= fun inline_pe ->
        z3_pe inline_pe
    | PElet (_, pe1, pe2) ->
        z3_pe pe1 >>= fun _ ->
        z3_pe pe2
    | PEif (cond, pe1, pe2) ->
        z3_pe cond >>= fun z3d_cond ->
        z3_pe pe1  >>= fun z3d_pe1 ->
        z3_pe pe2  >>= fun z3d_pe2 ->
        return (mk_ite z3d_cond z3d_pe1 z3d_pe2)
    | PEis_scalar _  -> assert false
    | PEis_integer _ -> assert false
    | PEis_signed _  -> assert false
    | PEis_unsigned (Pexpr(_, BTy_ctype, PEval (Vctype ctype))) ->
        return (Pmap.find ctype ImplFunctions.is_unsigned_map)
    | PEis_unsigned _    -> assert false
    | PEare_compatible _ -> assert false
    | PEbmc_assume pe ->
        z3_pe pe >>= fun _ ->
        return UnitSort.mk_unit
    ) >>= fun z3d_pexpr ->
    add_expr uid z3d_pexpr >>
    return z3d_pexpr

  let z3_action (Paction(p, Action(loc, a, action_))) uid =
    get_fresh_aid >>= fun aid ->
    (match action_ with
    | Create (align, Pexpr(_, BTy_ctype, PEval (Vctype ctype)), prefix) ->
        get_file >>= fun file ->
        get_fresh_alloc >>= fun alloc_id ->
        (* TODO: we probably don't actually want to flatten the sort list *)
        let flat_sortlist = flatten_bmcz3sort (ctype_to_bmcz3sort ctype file) in

        return (PointerSort.mk_ptr (AddressSort.mk_from_addr (alloc_id, 0)),
                ICreate (aid, flat_sortlist, alloc_id))
    | Create _ ->
        assert false
    | CreateReadOnly _ ->
        assert false
    | Alloc0 _ ->
        assert false
    | Kill (b, pe) ->
        bmc_debug_print 7 "TODO: kill ignored";
        z3_pe pe >>= fun z3d_pe ->
        return (UnitSort.mk_unit, IKill aid)
    | Store0 (b, Pexpr(_,_,PEval (Vctype ty)), Pexpr(_,_,PEsym sym), wval, mo) ->
        lookup_sym sym >>= fun sym_expr ->
        z3_pe wval     >>= fun z3d_wval ->
        get_file       >>= fun file ->
        let flat_sortlist = flatten_bmcz3sort (ctype_to_bmcz3sort ty file) in
        assert (List.length flat_sortlist = 1);

        return (UnitSort.mk_unit,
                IStore (aid, List.hd flat_sortlist, sym_expr, z3d_wval, mo))
    | Store0 _ ->
        assert false
    | Load0 (Pexpr(_,_,PEval (Vctype ty)), Pexpr(_,_,PEsym sym), mo) ->
        get_file >>= fun file ->
        let flat_sortlist = flatten_bmcz3sort (ctype_to_bmcz3sort ty file) in
        (* TODO: can't load multiple memory locations... *)
        assert (List.length flat_sortlist = 1);
        let (_, sort) = List.hd flat_sortlist in
        lookup_sym sym >>= fun sym_expr ->
        let rval_expr = mk_fresh_const ("load_" ^ (symbol_to_string sym)) sort in
        return (rval_expr, ILoad (aid, List.hd flat_sortlist,
                sym_expr, rval_expr, mo))
    | Load0 _ ->
        assert false
    | RMW0 (pe1, pe2, pe3, pe4, mo1, mo2) ->
        assert false
    | CompareExchangeStrong(Pexpr(_,_,PEval (Vctype ty)),
                            Pexpr(_,_,PEsym obj),
                            Pexpr(_,_,PEsym expected),
                            desired, mo_success, mo_failure) ->
        get_file >>= fun file ->
        let flat_sortlist = flatten_bmcz3sort (ctype_to_bmcz3sort ty file) in
        assert (List.length flat_sortlist = 1);
        let (ctype, sort) = List.hd flat_sortlist in

        let rval_expected =
          mk_fresh_const ("load_" ^ (symbol_to_string expected)) sort in
        let rval_object =
          mk_fresh_const ("load_" ^ (symbol_to_string obj)) sort in

        lookup_sym obj      >>= fun obj_expr ->
        lookup_sym expected >>= fun expected_expr ->
        z3_pe desired       >>= fun z3d_desired ->

        let success_guard = mk_eq rval_expected rval_object in
        (* TODO *)
        return (mk_ite success_guard (LoadedInteger.mk_specified (int_to_z3 1))
                                     (LoadedInteger.mk_specified (int_to_z3 0)),
                ICompareExchangeStrong (aid, (ctype,sort), obj_expr, expected_expr,
                                        z3d_desired, rval_expected, rval_object,
                                        mo_success, mo_failure))
    | CompareExchangeStrong _ ->
        assert false
    | Fence0 mo ->
        return (UnitSort.mk_unit, IFence (aid, mo))
    | LinuxFence mo ->
        return (UnitSort.mk_unit, ILinuxFence (aid, mo))
    | LinuxLoad (Pexpr(_,_,PEval (Vctype ty)), Pexpr(_,_,PEsym sym), mo) ->
        assert (g_memory_mode = MemoryMode_Linux);
        assert (!!bmc_conf.concurrent_mode);
        get_file >>= fun file ->
        let flat_sortlist = flatten_bmcz3sort (ctype_to_bmcz3sort ty file) in
        let (ctype, sort) = List.hd flat_sortlist in
        (* TODO: can't load multiple memory locations... *)
        assert (List.length flat_sortlist = 1);
        lookup_sym sym >>= fun sym_expr ->
        let rval_expr = mk_fresh_const ("load_" ^ (symbol_to_string sym)) sort in
        return (rval_expr, ILinuxLoad (aid, (ctype,sort),
                sym_expr, rval_expr, mo))
    | LinuxLoad _ ->
        assert false
    | LinuxStore (Pexpr(_,_,PEval (Vctype ty)), Pexpr(_,_,PEsym sym), wval, mo) ->
        lookup_sym sym >>= fun sym_expr ->
        z3_pe wval     >>= fun z3d_wval ->
        get_file       >>= fun file ->
        let flat_sortlist = flatten_bmcz3sort (ctype_to_bmcz3sort ty file) in
        assert (List.length flat_sortlist = 1);
        return (UnitSort.mk_unit,
                ILinuxStore (aid, List.hd flat_sortlist,
                             sym_expr, z3d_wval, mo))
    | LinuxStore _ ->
        assert false
    | LinuxRMW (pe1, pe2, pe3, mo) ->
        assert false
    ) >>= fun (z3d_action, intermediate_action) ->
    add_action uid intermediate_action >>
    return z3d_action

  let rec z3_e (Expr(annots, expr_) as expr: unit typed_expr) : Expr.expr eff =
    let uid = get_id_expr expr in
    (match expr_ with
    | Epure pe ->
        z3_pe pe
    | Ememop (PtrValidForDeref, [ptr]) ->
        z3_pe ptr >>= fun z3d_ptr ->
        let addr = PointerSort.get_addr z3d_ptr in
        let range_assert = AddressSort.valid_index_range addr in
        return (mk_and [mk_not (PointerSort.is_null z3d_ptr); range_assert])
    | Ememop (PtrEq, [p1;p2]) ->
        z3_pe p1 >>= fun z3d_p1 ->
        z3_pe p2 >>= fun z3d_p2 ->
        return (mk_eq z3d_p1 z3d_p2)
    | Ememop _ -> assert false
    | Eaction action ->
        z3_action action uid
    | Ecase (pe, cases) ->
        z3_pe pe                       >>= fun z3d_pe ->
        mapM z3_e (List.map snd cases) >>= fun z3d_cases_e ->
        let (_, guards) = compute_case_guards (List.map fst cases) z3d_pe in
        add_guards uid guards >>
        return (mk_guarded_ite z3d_cases_e guards)
    | Elet _ -> assert false
    | Eif (pe, e1, e2) ->
        z3_pe pe >>= fun z3d_pe ->
        z3_e e1  >>= fun z3d_e1 ->
        z3_e e2  >>= fun z3d_e2 ->
        let (guard1, guard2) = (z3d_pe, mk_not z3d_pe) in
        add_guards uid [guard1; guard2] >>
        return (mk_ite guard1 z3d_e1 z3d_e2)
    | Eskip ->
        return UnitSort.mk_unit
    | Eccall _ -> assert false
    | Eproc _  -> assert false
    | Eunseq elist ->
        assert (not !!bmc_conf.sequentialise);
        assert (!!bmc_conf.concurrent_mode);
        mapM z3_e elist >>= fun z3d_elist ->
        return (ctor_to_z3 Ctuple z3d_elist None)
    | Ewseq (_, e1, e2) (* fall through *)
    | Esseq (_, e1, e2) ->
        z3_e e1 >>= fun _ ->
        z3_e e2
    | Easeq _  -> assert false
    | Eindet _ -> assert false
    | Ebound (_, e) ->
        z3_e e
    | End elist ->
        mapM z3_e elist >>= fun z3d_elist ->
        let choice_vars = List.mapi (
          fun i _ -> mk_fresh_const ("seq_" ^ (string_of_int i))
                                    boolean_sort) elist in
        add_guards uid choice_vars >>
        let ret_expr = List.fold_left2
          (fun acc choice res -> mk_ite choice res acc)
          (List.hd z3d_elist)
          (List.tl choice_vars)
          (List.tl z3d_elist) in
        return ret_expr
    | Esave _  ->
        get_inline_expr uid >>= fun inlined_expr ->
        z3_e inlined_expr
    | Erun _   ->
        get_inline_expr uid >>= fun inlined_expr ->
        z3_e inlined_expr   >>= fun _ ->
        return (UnitSort.mk_unit)
    | Epar _   -> assert false
    | Ewait _  -> assert false
    ) >>= fun ret ->
    add_expr uid ret >>
    return ret

    let z3_globs (gname, bty, e) =
      z3_e e >>= fun z3d_e ->
      return (gname, bty, z3d_e)

    let z3_file (file: unit typed_file) (fn_to_check: sym_ty)
                : (unit typed_file) eff =
      mapM z3_globs file.globs >>= fun _ ->
      (match Pmap.lookup fn_to_check file.funs with
      | Some (Proc(annot, bTy, params, e)) ->
          z3_e e
      | Some (Fun(ty, params, pe)) ->
          z3_pe pe
      | _ -> assert false
      ) >>= fun _ ->
      return file
end

(* ======= Compute drop continuation; only matters for Esseq/Ewseq? *)
module BmcDropCont = struct
  type internal_state = {
    inline_pexpr_map : (int, typed_pexpr) Pmap.map;
    inline_expr_map  : (int, unit typed_expr) Pmap.map;
    case_guard_map   : (int, Expr.expr list) Pmap.map;

    drop_cont_map : (int, Expr.expr) Pmap.map;
  }

  include EffMonad(struct type state = internal_state end)

  let mk_initial inline_pexpr_map
                 inline_expr_map
                 case_guard_map : state =
  { inline_pexpr_map = inline_pexpr_map;
    inline_expr_map  = inline_expr_map;
    case_guard_map   = case_guard_map;
    drop_cont_map    = Pmap.empty Pervasives.compare;
  }

  let get_inline_pexpr (uid: int): typed_pexpr eff =
    get >>= fun st ->
    match Pmap.lookup uid st.inline_pexpr_map with
    | None -> failwith (sprintf "Error: BmcDropCont inline_pexpr not found %d"
                                uid)
    | Some pe -> return pe

  let get_inline_expr (uid: int): (unit typed_expr) eff =
    get >>= fun st ->
    match Pmap.lookup uid st.inline_expr_map with
    | None -> failwith (sprintf "Error: BmcDropCont inline_expr not found %d"
                                uid)
    | Some e -> return e

  let get_case_guards (uid: int): (Expr.expr list) eff =
    get >>= fun st ->
    match Pmap.lookup uid st.case_guard_map with
    | None -> failwith (sprintf "Error: BmcDropCont case guard not found %d" uid)
    | Some es -> return es

  let add_to_drop_cont_map (uid: int) (drop_cont: Expr.expr) : unit eff =
    get >>= fun st ->
    put {st with drop_cont_map = Pmap.add uid drop_cont st.drop_cont_map}

  (* Z3 stuff *)
  let rec drop_cont_e (Expr(annots, expr_) as expr)
                  : Expr.expr eff =
    let uid = get_id_expr expr in
    (match expr_ with
    | Epure _   -> return mk_false
    | Ememop _  -> return mk_false
    | Eaction _ -> return mk_false
    | Ecase (_, cases) ->
        get_case_guards uid    >>= fun guards ->
        mapM (fun (_, e) -> drop_cont_e e) cases >>= fun drop_cases ->
        return (mk_or (List.map2 (
          fun guard drop_case -> mk_and [guard; drop_case])
          guards drop_cases))
    | Elet _ -> assert false
    | Eif (_, e1, e2) ->
        get_case_guards uid >>= fun guards ->
        let (guard1, guard2) = (
          match guards with
          | [g1;g2] -> (g1, g2)
          | _ -> assert false) in
        drop_cont_e e1 >>= fun drop_e1 ->
        drop_cont_e e2 >>= fun drop_e2 ->
        return (mk_or [mk_and [guard1; drop_e1]
                      ;mk_and [guard2; drop_e2]])
    | Eskip ->
        return mk_false
    | Eccall _ -> assert false
    | Eproc _  -> assert false
    | Eunseq elist ->
        mapM drop_cont_e elist >>= fun drop_cont_elist ->
        return (mk_or drop_cont_elist)
    | Ewseq (pat, e1, e2) (* fall through *)
    | Esseq (pat, e1, e2) ->
        drop_cont_e e1 >>= fun drop_e1 ->
        drop_cont_e e2 >>= fun drop_e2 ->
        return (mk_or [drop_e1; drop_e2])
    | Easeq _  -> assert false
    | Eindet _ -> assert false
    | Ebound (_, e) ->
        drop_cont_e e
    | End elist ->
        mapM drop_cont_e elist >>= fun drop_elist ->
        get_case_guards uid    >>= fun guards ->
        return (mk_or (List.map2
          (fun choice drop_e -> mk_and [choice; drop_e])
          guards drop_elist))
    | Esave _ ->
        get_inline_expr uid >>= fun inlined_expr ->
        drop_cont_e inlined_expr
    | Erun _ ->
        get_inline_expr uid      >>= fun inlined_expr ->
        drop_cont_e inlined_expr >>= fun _ ->
        return mk_true
    | Epar _
    | Ewait _       -> assert false
    ) >>= fun drop_expr ->
    add_to_drop_cont_map uid drop_expr >>
    return drop_expr

  let drop_cont_globs (_, _, e) : Expr.expr eff =
    drop_cont_e e

  let drop_cont_file (file: unit typed_file) (fn_to_check: sym_ty)
                     : Expr.expr eff =
    mapM drop_cont_globs file.globs >>= fun _ ->
    (match Pmap.lookup fn_to_check file.funs with
    | Some (Proc(annot, bTy, params, e)) ->
        drop_cont_e e
    | Some (Fun(ty, params, pe)) ->
        return mk_false
    | _ -> assert false
    )
end

(* ======= Compute syntactic let bindings ====== *)
module BmcBind = struct
  type binding_state = {
    inline_pexpr_map : (int, typed_pexpr) Pmap.map;
    inline_expr_map  : (int, unit typed_expr) Pmap.map;
    sym_table        : (sym_ty, Expr.expr) Pmap.map;
    case_guard_map   : (int, Expr.expr list) Pmap.map;
    expr_map         : (int, Expr.expr) Pmap.map;
    action_map       : (int, BmcZ3.intermediate_action) Pmap.map;
  }

  include EffMonad(struct type state = binding_state end)

  let mk_initial inline_pexpr_map
                 inline_expr_map
                 sym_table
                 case_guard_map
                 expr_map
                 action_map
                 : state =
  { inline_pexpr_map = inline_pexpr_map;
    inline_expr_map  = inline_expr_map;
    sym_table        = sym_table;
    case_guard_map   = case_guard_map;
    expr_map         = expr_map;
    action_map       = action_map;
  }

  let get_inline_pexpr (uid: int): typed_pexpr eff =
    get >>= fun st ->
    match Pmap.lookup uid st.inline_pexpr_map with
    | None -> failwith (sprintf "Error: BmcBind inline_pexpr not found %d" uid)
    | Some pe -> return pe

  let get_inline_expr (uid: int): (unit typed_expr) eff =
    get >>= fun st ->
    match Pmap.lookup uid st.inline_expr_map with
    | None -> failwith (sprintf "Error: BmcBind inline_expr not found %d" uid)
    | Some e -> return e

  let lookup_sym (sym: sym_ty) : Expr.expr eff =
    get >>= fun st ->
    match Pmap.lookup sym st.sym_table with
    | None -> failwith (sprintf "Error: BmcBind %s not found in sym_table"
                                (symbol_to_string sym))
    | Some expr -> return expr

  let get_case_guards (uid: int): (Expr.expr list) eff =
    get >>= fun st ->
    match Pmap.lookup uid st.case_guard_map with
    | None -> failwith (sprintf "Error: BmcBind case guard not found %d" uid)
    | Some es -> return es

  let get_expr (uid: int): Expr.expr eff =
    get >>= fun st ->
    match Pmap.lookup uid st.expr_map with
    | None -> failwith (sprintf "Error: BmcBind expr not found %d" uid)
    | Some e -> return e

  let get_action (uid: int) : BmcZ3.intermediate_action eff =
    get >>= fun st ->
    match Pmap.lookup uid st.action_map with
    | None -> failwith (sprintf "Error: BmcBind action not found %d" uid)
    | Some a -> return a

  (* let bindings *)
  let mk_let_binding (maybe_sym: sym_ty option)
                     (expr: Expr.expr)
                     : Expr.expr eff =
    match maybe_sym with
    | None -> return mk_true
    | Some sym ->
        lookup_sym sym >>= fun sym_expr ->
        return (mk_eq sym_expr expr)

        (* TODO: hack for C functions... *)
        (*if (Sort.equal CFunctionSort.mk_sort (Expr.get_sort expr)) then
          BmcM.add_sym_to_sym_table sym expr >>= fun () ->
          return (mk_eq sym_expr expr)
        else
          return (mk_eq sym_expr expr) *)

  let rec mk_let_bindings (Pattern(_,pat): typed_pattern) (expr: Expr.expr)
                          : Expr.expr eff =
    match pat with
    | CaseBase(sym, _) ->
        mk_let_binding sym expr
    | CaseCtor (Ctuple, patlist) ->
        assert (Expr.get_num_args expr = List.length patlist);
        mapM (fun (pat, e) -> mk_let_bindings pat e)
             (List.combine patlist (Expr.get_args expr)) >>= fun bindings ->
        return (mk_and bindings)
  | CaseCtor(Cspecified, [Pattern(_,CaseBase(sym, BTy_object OTy_integer))]) ->
      let is_specified = LoadedInteger.is_specified expr in
      let specified_value = LoadedInteger.get_specified_value expr in
      mk_let_binding sym specified_value >>= fun is_eq_value ->
      return (mk_and [is_specified; is_eq_value])
  | CaseCtor(Cspecified, [Pattern(_,CaseBase(sym, BTy_object OTy_pointer))]) ->
      let is_specified = LoadedPointer.is_specified expr in
      let specified_value = LoadedPointer.get_specified_value expr in
      mk_let_binding sym specified_value >>= fun is_eq_value ->
      return (mk_and [is_specified; is_eq_value])
  | CaseCtor(Cspecified, _) ->
      assert false
  | CaseCtor(Cunspecified, [Pattern(_,CaseBase(sym, BTy_ctype))]) ->
      let (is_unspecified, unspecified_value) =
        if (Sort.equal (Expr.get_sort expr) (LoadedInteger.mk_sort)) then
          let is_unspecified = LoadedInteger.is_unspecified expr in
          let unspecified_value = LoadedInteger.get_unspecified_value expr in
          (is_unspecified, unspecified_value)
        else if (Sort.equal (Expr.get_sort expr) (LoadedPointer.mk_sort)) then
          let is_unspecified = LoadedPointer.is_unspecified expr in
          let unspecified_value = LoadedPointer.get_unspecified_value expr in
          (is_unspecified, unspecified_value)
        else
          assert false
      in
      mk_let_binding sym unspecified_value >>= fun is_eq_value ->
      return (mk_and [is_unspecified; is_eq_value])
  | CaseCtor(Cunspecified, _) ->
      assert false
  | CaseCtor(_, _) ->
      assert false

  (* TODO: check if removing guard here is significantly faster *)
  let guard_assert (guard: Expr.expr) =
    mk_implies guard

  (* SMT stuff *)
  let rec bind_pe (Pexpr(annots, bTy, pe_) as pexpr) : (Expr.expr list) eff =
    let uid = get_id_pexpr pexpr in
    (match pe_ with
    | PEsym _ ->
        return []
    | PEimpl _ ->
        get_inline_pexpr uid >>= fun inline_pe ->
        bind_pe inline_pe
    | PEval _ ->
        return []
    | PEconstrained _ ->
        assert false
    | PEundef _ ->
        return []
    | PEerror _ ->
        return []
    | PEctor (ctor, pes) ->
        mapM bind_pe pes >>= fun bound_pes ->
        return (List.concat bound_pes)
    | PEcase (pe, cases) ->
        bind_pe pe                        >>= fun bound_pe ->
        mapM bind_pe (List.map snd cases) >>= fun bound_cases ->

        (* Make let binding for each pattern with z3_pe *)
        get_expr (get_id_pexpr pe) >>= fun z3_pe ->
        mapM (fun (pat, _) -> mk_let_bindings pat z3_pe) cases
             >>= fun bindings ->

        (* Guard the bindings *)
        get_case_guards uid               >>= fun guards ->
        let case_bindings = List.map2 mk_implies guards bindings in
        let guarded_bound_cases = List.concat (List.map2
          (fun guard case_binds -> List.map (guard_assert guard) case_binds)
          guards bound_cases) in
        return (bound_pe @ case_bindings @ guarded_bound_cases)
    | PEarray_shift (ptr, _, index) ->
        bind_pe ptr   >>= fun bound_ptr ->
        bind_pe index >>= fun bound_index ->
        return (bound_ptr @ bound_index)
    | PEmember_shift (ptr, _, _) ->
        bind_pe ptr
    | PEnot pe ->
        bind_pe pe
    | PEop (_, pe1, pe2) ->
        bind_pe pe1 >>= fun bound_pe1 ->
        bind_pe pe2 >>= fun bound_pe2 ->
        return (bound_pe1 @ bound_pe2)
    | PEstruct _    -> assert false
    | PEunion _     -> assert false
    | PEcfunction _ -> assert false
    | PEmemberof _  -> assert false
    | PEcall _ ->
        get_inline_pexpr uid >>= fun inline_pe ->
        bind_pe inline_pe
    | PElet (pat, pe1, pe2) ->
        get_expr (get_id_pexpr pe1) >>= fun z3_pe1 ->
        mk_let_bindings pat z3_pe1  >>= fun let_binding ->
        bind_pe pe1                 >>= fun bound_pe1 ->
        bind_pe pe2                 >>= fun bound_pe2 ->
        return (let_binding :: bound_pe1 @ bound_pe2)
    | PEif (cond, pe1, pe2) ->
        bind_pe cond >>= fun bound_cond ->
        bind_pe pe1  >>= fun bound_pe1 ->
        bind_pe pe2  >>= fun bound_pe2 ->
        get_expr (get_id_pexpr cond) >>= fun guard ->
        return (bound_cond @
                (* Guarded asserts is unnecessary *)
                (List.map (guard_assert guard) bound_pe1) @
                (List.map (guard_assert (mk_not guard)) bound_pe2))
    | PEis_scalar _
    | PEis_integer _ ->
        assert false
    | PEis_signed _ ->
        assert false
    | PEis_unsigned (Pexpr (_, BTy_ctype, PEval (Vctype ctype))) ->
        return []
    | PEis_unsigned _ ->
        assert false
    | PEare_compatible _ ->
        assert false
    | PEbmc_assume pe ->
        bind_pe pe
    )

  (* TODO TODO TODO TODO *)
  let bind_action (Paction(p, Action(loc, a, action_))) uid
                  : (Expr.expr list) eff =
    match action_ with
    | Create (pe1, pe2, pref) ->
        get_action uid >>= fun action ->

        let (alloc_size, alloc_id) =
          (match action with
           | ICreate(_, sortlist, alloc_id) -> (List.length sortlist, alloc_id)
           | _ -> assert false
          ) in

        (* Assert alloc_size(alloc_id) = allocation_size *)
        return [mk_eq (Expr.mk_app g_ctx AddressSort.alloc_size_decl
                                         [int_to_z3 alloc_id])
                      (int_to_z3 alloc_size)]
    | CreateReadOnly _ -> assert false
    | Alloc0 _ -> assert false
    | Kill (_, pe) ->
        bind_pe pe
    | Store0 (b, Pexpr(_,_,PEval (Vctype ty)), Pexpr(_,_,PEsym sym), wval, mo) ->
        bind_pe wval
    | Store0 _ ->
        assert false
    | Load0 (Pexpr(_,_,PEval (Vctype ty)), Pexpr(_,_,PEsym sym), mo) ->
        return []
    | Load0 _ ->
        assert false
    | RMW0 (pe1, pe2, pe3, pe4, mo1, mo2) ->
        return []
    | Fence0 mo ->
        return []
    | CompareExchangeStrong(pe1, pe2, pe3, pe4, mo1, mo2) ->
        return []
    | LinuxFence mo ->
        return []
    | LinuxLoad (pe1, pe2, mo) ->
        return []
    | LinuxStore(pe1, pe2, pe3, mo) ->
        return []
    | LinuxRMW (pe1, pe2, pe3, mo) ->
        return []

  let rec bind_e (Expr(annots, expr_) as expr: unit typed_expr)
                 : (Expr.expr list) eff =
    let uid = get_id_expr expr in
    (match expr_ with
    | Epure pe ->
        bind_pe pe
    | Ememop (PtrValidForDeref, [ptr]) ->
        bind_pe ptr
    | Ememop (PtrEq, [p1;p2]) ->
        bind_pe p1 >>= fun bound_p1 ->
        bind_pe p2 >>= fun bound_p2 ->
        return (bound_p1 @ bound_p2)
    | Ememop _ -> assert false
    | Eaction action ->
        bind_action action uid
    | Ecase (pe, cases) ->
        bind_pe pe                       >>= fun bound_pe ->
        mapM bind_e (List.map snd cases) >>= fun bound_cases ->

        (* Make let binding for each pattern with z3_pe *)
        get_expr (get_id_pexpr pe)       >>= fun z3_pe ->
        mapM (fun (pat, _) -> mk_let_bindings pat z3_pe) cases
             >>= fun bindings ->

        (* Guard the bindings *)
        get_case_guards uid               >>= fun guards ->
        let case_bindings = List.map2 mk_implies guards bindings in
        let guarded_bound_cases = List.concat (List.map2
          (fun guard case_binds -> List.map (guard_assert guard) case_binds)
          guards bound_cases) in
        return (bound_pe @ case_bindings @ guarded_bound_cases)
    | Elet _ -> assert false
    | Eif (cond, e1, e2) ->
        bind_pe cond >>= fun bound_cond ->
        bind_e  e1   >>= fun bound_e1 ->
        bind_e  e2   >>= fun bound_e2 ->
        get_expr (get_id_pexpr cond) >>= fun guard ->
        return (bound_cond @
                (* Guarded asserts is unnecessary *)
                (List.map (guard_assert guard) bound_e1) @
                (List.map (guard_assert (mk_not guard)) bound_e2))
    | Eskip ->
        return []
    | Eccall _ -> assert false
    | Eproc _  -> assert false
    | Eunseq elist ->
        mapM bind_e elist >>= fun bound_elist ->
        return (List.concat bound_elist)
    | Ewseq (pat, e1, e2) (* fall through *)
    | Esseq (pat, e1, e2) ->
        bind_e e1 >>= fun bound_e1 ->
        bind_e e2 >>= fun bound_e2 ->
        get_expr (get_id_expr e1) >>= fun z3_e1 ->
        mk_let_bindings pat z3_e1 >>= fun let_binding ->
        (* TODO: drop_cont guard *)
        return (let_binding :: bound_e1 @ bound_e2)
    | Easeq _ -> assert false
    | Eindet _ -> assert false
    | Ebound (_, e) ->
        bind_e e
    | End elist ->
        mapM bind_e elist   >>= fun bound_elist ->
        get_case_guards uid >>= fun guards ->
        (* Also assert xor guards here *)
        let guarded_asserts = List.concat (List.map2
          (fun guard bindings -> List.map (guard_assert guard) bindings)
          guards bound_elist) in
        return ((List.fold_left mk_xor mk_false guards) :: guarded_asserts)
    | Esave _ ->
        get_inline_expr uid >>= fun inlined_expr ->
        bind_e inlined_expr
    | Erun _ ->
        get_inline_expr uid >>= fun inlined_expr ->
        bind_e inlined_expr
    | Epar _        -> assert false
    | Ewait _       -> assert false
    )

    let bind_globs (gname, _, e) : (Expr.expr list) eff =
      bind_e e                 >>= fun bound_e ->
      get_expr (get_id_expr e) >>= fun z3d_e ->
      mk_let_binding (Some gname) z3d_e >>= fun let_binding ->
      return (let_binding :: bound_e)

    let bind_file (file: unit typed_file) (fn_to_check: sym_ty)
                  : (Expr.expr list) eff =
      mapM bind_globs file.globs >>= fun bound_globs ->
        print_endline "GLOBS";
      List.iter print_expr (List.concat(bound_globs));
      (match Pmap.lookup fn_to_check file.funs with
      | Some (Proc(annot, bTy, params, e)) ->
          bind_e e
      | Some (Fun(ty, params, pe)) ->
          bind_pe pe
      | _ -> assert false
      ) >>= fun bound_expr ->
      return ((List.concat bound_globs) @ bound_expr)
end

(* ======= Compute verification conditions ======= *)

module BmcVC = struct
  type vc_state = {
    inline_pexpr_map : (int, typed_pexpr) Pmap.map;
    inline_expr_map  : (int, unit typed_expr) Pmap.map;
    sym_table        : (sym_ty, Expr.expr) Pmap.map;
    case_guard_map   : (int, Expr.expr list) Pmap.map;
    expr_map         : (int, Expr.expr) Pmap.map;
    action_map       : (int, BmcZ3.intermediate_action) Pmap.map;
    drop_cont_map    : (int, Expr.expr) Pmap.map;
  }

  include EffMonad(struct type state = vc_state end)

  let mk_initial inline_pexpr_map
                 inline_expr_map
                 sym_table
                 case_guard_map
                 expr_map
                 action_map
                 drop_cont_map
                 : state =
  { inline_pexpr_map = inline_pexpr_map;
    inline_expr_map  = inline_expr_map;
    sym_table        = sym_table;
    case_guard_map   = case_guard_map;
    expr_map         = expr_map;
    action_map       = action_map;
    drop_cont_map    = drop_cont_map;
  }

  let get_inline_pexpr (uid: int): typed_pexpr eff =
    get >>= fun st ->
    match Pmap.lookup uid st.inline_pexpr_map with
    | None -> failwith (sprintf "Error: BmcVC inline_pexpr not found %d" uid)
    | Some pe -> return pe

  let get_inline_expr (uid: int): (unit typed_expr) eff =
    get >>= fun st ->
    match Pmap.lookup uid st.inline_expr_map with
    | None -> failwith (sprintf "Error: BmcVC inline_expr not found %d" uid)
    | Some e -> return e

  let lookup_sym (sym: sym_ty) : Expr.expr eff =
    get >>= fun st ->
    match Pmap.lookup sym st.sym_table with
    | None -> failwith (sprintf "Error: BmcVC %s not found in sym_table"
                                (symbol_to_string sym))
    | Some expr -> return expr

  let get_case_guards (uid: int): (Expr.expr list) eff =
    get >>= fun st ->
    match Pmap.lookup uid st.case_guard_map with
    | None -> failwith (sprintf "Error: BmcVC case guard not found %d" uid)
    | Some es -> return es

  let get_expr (uid: int): Expr.expr eff =
    get >>= fun st ->
    match Pmap.lookup uid st.expr_map with
    | None -> failwith (sprintf "Error: BmcVC expr not found %d" uid)
    | Some e -> return e

  let get_action (uid: int) : BmcZ3.intermediate_action eff =
    get >>= fun st ->
    match Pmap.lookup uid st.action_map with
    | None -> failwith (sprintf "Error: BmcVC action not found %d" uid)
    | Some a -> return a

  let get_drop_cont (uid: int) : Expr.expr eff =
    get >>= fun st ->
    match Pmap.lookup uid st.drop_cont_map with
    | None -> failwith (sprintf "BmcVC: Uid %d not found in drop_cont_map" uid)
    | Some expr -> return expr

  (* ==== VC definitions ==== *)
  type vc_debug =
  | VcDebugUndef of Location_ocaml.t * Undefined.undefined_behaviour
  | VcDebugStr of string

  let vc_debug_to_str (dbg: vc_debug) =
    match dbg with
    | VcDebugUndef (loc, ub) ->
        sprintf "(%s,%s)" (Location_ocaml.location_to_string loc)
                          (Undefined.stringFromUndefined_behaviour ub)
    | VcDebugStr str -> str


  type vc = Expr.expr * vc_debug

  let guard_vc (guard: Expr.expr) ((vc_expr, dbg): vc) : vc =
    (mk_implies guard vc_expr, dbg)

  let map2_inner (f: 'x->'y->'z) (xs: 'x list) (yss: ('y list) list) : 'z list =
    List.concat (List.map2 (fun x ys -> List.map (f x) ys) xs yss)

  let rec vcs_pe (Pexpr (annots, bTy, pe_) as pexpr)
                 : (vc list) eff =
    let uid = get_id_pexpr pexpr in
    match pe_ with
    | PEsym _           -> return []
    | PEimpl _          ->
       get_inline_pexpr uid >>= fun inline_pe ->
       vcs_pe inline_pe
    | PEval _           -> return []
    | PEconstrained _   -> assert false
    | PEundef (loc, ub) -> return [(mk_false, VcDebugUndef (loc,ub))]
    | PEerror (str, _)  -> return [(mk_false, VcDebugStr (string_of_int uid ^ "_" ^ str))]
    | PEctor (ctor, pelist) ->
        mapM vcs_pe pelist >>= fun vcss ->
        return (List.concat vcss)
    | PEcase (pe0, cases) ->
        (* TODO: double check this *)
        mapM (fun (_, pe) -> vcs_pe pe) cases >>= fun vcss_cases ->
        get_case_guards uid                   >>= fun guards ->
        vcs_pe pe0                            >>= fun vcs_pe0 ->
        assert (List.length vcss_cases == List.length guards);
        let dbg = VcDebugStr (string_of_int uid ^ "_PEcase_caseMatch") in
        return ((mk_or guards, dbg) ::
                vcs_pe0 @ (map2_inner guard_vc guards vcss_cases))
    | PEarray_shift (ptr, ty, index) ->
        get_expr (get_id_pexpr ptr) >>= fun ptr_z3 ->
        vcs_pe ptr                  >>= fun vcs_ptr ->
        vcs_pe index                >>= fun vcs_index ->
        let dbg = VcDebugStr (string_of_int uid ^ "_PEarray_shift_notNull") in
        return ((mk_not (PointerSort.is_null ptr_z3), dbg)
                :: (vcs_ptr @ vcs_index))
    | PEmember_shift (ptr, sym, member) ->
        get_expr (get_id_pexpr ptr) >>= fun ptr_z3 ->
        vcs_pe ptr                  >>= fun vcs_ptr ->
        let dbg = VcDebugStr (string_of_int uid ^ "_PEmember_shift_notNull") in
        return ((mk_not (PointerSort.is_null ptr_z3), dbg) :: vcs_ptr)
    | PEnot pe         -> vcs_pe pe
    | PEop (_, pe1, pe2) ->
        vcs_pe    pe1 >>= fun vc1s ->
        vcs_pe    pe2 >>= fun vc2s ->
        return (vc1s @ vc2s)
    | PEstruct _       -> assert false
    | PEunion _        -> assert false
    | PEcfunction _    -> assert false
    | PEmemberof _     -> assert false
    | PEcall _ ->
        get_inline_pexpr uid >>= fun inline_pe ->
        vcs_pe inline_pe
    | PElet (pat, pe1, pe2) ->
        vcs_pe pe1 >>= fun vc1s ->
        vcs_pe pe2 >>= fun vc2s ->
        return (vc1s @ vc2s)
    | PEif (cond, pe1, pe2) ->
        get_expr (get_id_pexpr cond)          >>= fun guard_z3 ->
        vcs_pe pe1                            >>= fun vc1s ->
        vcs_pe pe2                            >>= fun vc2s ->
        return ((List.map (guard_vc guard_z3) vc1s) @
                (List.map (guard_vc (mk_not guard_z3)) vc2s))
    | PEis_scalar pe   -> vcs_pe pe
    | PEis_integer pe  -> vcs_pe pe
    | PEis_signed pe   -> vcs_pe pe
    | PEis_unsigned pe -> vcs_pe pe
    | PEare_compatible (pe1,pe2) ->
        vcs_pe pe1 >>= fun vc1s ->
        vcs_pe pe2 >>= fun vc2s ->
        return (vc1s @ vc2s)
    | PEbmc_assume pe -> vcs_pe pe

  (* TODO!!! *)
  let vcs_paction (Paction (p, Action(loc, a, action_)) : unit typed_paction)
                      uid
                      : (vc list) eff =
    match action_ with
    | Create (align, Pexpr(_, BTy_ctype, PEval (Vctype ctype)), prefix) ->
        return []
    | Create _ -> assert false
    | CreateReadOnly _  -> assert false
    | Alloc0 _          -> assert false
    | Kill (_, pe) ->
        (* TODO: Kill ignored *)
        vcs_pe pe
    | Store0 (_, Pexpr(_,_,PEval (Vctype ty)),
                 (Pexpr(_,_,PEsym sym)), wval, memorder) ->
        (* TODO: Where should we check whether the ptr is valid? *)
        let valid_memorder =
          mk_bool (not (memorder = Acquire || memorder = Acq_rel)) in
        vcs_pe wval                     >>= fun vcs_wval ->
        lookup_sym sym                  >>= fun ptr_z3 ->
        return (  (valid_memorder, VcDebugStr (string_of_int uid ^ "_Store_memorder"))
                ::(mk_not (PointerSort.is_null ptr_z3),
                   VcDebugStr (string_of_int uid ^ "_Store_null"))
                :: vcs_wval)
    | Store0 _          -> assert false
    | Load0 (Pexpr(_,_,PEval (Vctype ty)),
             (Pexpr(_,_,PEsym sym)), memorder) ->
        let valid_memorder =
              mk_bool (not (memorder = Release || memorder = Acq_rel)) in
        lookup_sym sym >>= fun ptr_z3 ->
        return [(valid_memorder, VcDebugStr (string_of_int uid ^ "_Load_memorder"))
               ;(mk_not (PointerSort.is_null ptr_z3),
                   VcDebugStr (string_of_int uid ^ "_Load_null"))
               ]
    | Load0 _ -> assert false
    | RMW0 _  -> assert false
    | Fence0 _ -> return []
    | CompareExchangeStrong _ -> assert false
    | LinuxFence _ -> return []
    | LinuxStore _ -> assert false
    | LinuxLoad _  -> assert false
    | LinuxRMW _ -> assert false

  let rec vcs_e (Expr(annots, expr_) as expr)
                   : (vc list) eff =
    let uid = get_id_expr expr in
    match expr_ with
    | Epure pe      -> vcs_pe pe
    | Ememop (memop, pes) ->
        mapM vcs_pe pes >>= fun vcss_pes ->
        begin match memop with
        | PtrValidForDeref | PtrEq -> return (List.concat vcss_pes)
        | _ -> assert false (* Unimplemented *)
        end
    | Eaction paction ->
        vcs_paction paction uid
    | Ecase (pe, cases) ->
        mapM (fun (_, e) -> vcs_e e) cases >>= fun vcss_cases ->
        get_case_guards uid                >>= fun guards ->
        vcs_pe pe                          >>= fun vcs_pe ->
        let dbg = VcDebugStr (string_of_int uid ^ "_Ecase_caseMatch") in
        return ((mk_or guards, dbg) ::
                vcs_pe @ (map2_inner guard_vc guards vcss_cases))
    | Elet _        -> assert false
    | Eif (cond, e1, e2) ->
        vcs_pe cond >>= fun vcs_cond ->
        vcs_e e1    >>= fun vcs_e1 ->
        vcs_e e2    >>= fun vcs_e2 ->
        get_expr (get_id_pexpr cond) >>= fun cond_z3 ->
        return (vcs_cond @ (List.map (guard_vc cond_z3) vcs_e1)
                         @ (List.map (guard_vc (mk_not cond_z3)) vcs_e2))
    | Eskip         -> return []
    | Eccall _      -> assert false
    | Eproc _       -> assert false
    | Eunseq es ->
        mapM vcs_e es >>= fun vcss_es ->
        return (List.concat vcss_es)
    | Ewseq (pat, e1, e2)
    | Esseq (pat, e1, e2) ->
        vcs_e e1 >>= fun vcs_e1 ->
        vcs_e e2 >>= fun vcs_e2 ->
        get_drop_cont (get_id_expr e1) >>= fun e1_drop_cont ->
        return (vcs_e1 @ (List.map (guard_vc (mk_not e1_drop_cont)) vcs_e2))
    | Easeq _       -> assert false
    | Eindet _      -> assert false
    | Ebound (_, e) -> vcs_e e
    | End es ->
        get_case_guards uid >>= fun guards ->
        mapM vcs_e es    >>= fun vcss_es ->
        return (map2_inner guard_vc guards vcss_es)
    | Esave _       (* fall through *)
    | Erun _        ->
        get_inline_expr uid >>= fun inline_expr ->
        vcs_e inline_expr
    | Epar es -> assert false
        (*BmcVC.mapM vcs_e es >>= fun vcss_es ->
        return (List.concat vcss_es)*)
    | Ewait _       -> assert false

    let vcs_globs (_, _, e) : (vc list) eff =
      vcs_e e

    let vcs_file (file: unit typed_file) (fn_to_check: sym_ty)
                  : (vc list) eff =
      mapM vcs_globs file.globs >>= fun vcs_globs ->
      (match Pmap.lookup fn_to_check file.funs with
      | Some (Proc(annot, bTy, params, e)) ->
          vcs_e e
      | Some (Fun(ty, params, pe)) ->
          vcs_pe pe
      | _ -> assert false
      ) >>= fun vcs_expr ->
      return ((List.concat vcs_globs) @ vcs_expr)
end

(* Sequential memory model; read from most recent write *)
module BmcSeqMem = struct
  type memory_table = (addr_ty, Expr.expr) Pmap.map
  type seq_state = {
    inline_expr_map  : (int, unit typed_expr) Pmap.map;
    expr_map         : (int, Expr.expr) Pmap.map;
    action_map       : (int, BmcZ3.intermediate_action) Pmap.map;
    case_guard_map   : (int, Expr.expr list) Pmap.map;
    drop_cont_map    : (int, Expr.expr) Pmap.map;

    memory           : memory_table;
  }

  include EffMonad(struct type state = seq_state end)

  let mk_initial inline_expr_map
                 expr_map
                 action_map
                 case_guard_map
                 drop_cont_map
                 : state =
  { inline_expr_map  = inline_expr_map;
    expr_map         = expr_map;
    action_map       = action_map;
    case_guard_map   = case_guard_map;
    drop_cont_map    = drop_cont_map;
    memory           = Pmap.empty Pervasives.compare
  }

  (* TODO: use Set.Make *)
  module AddrSet = struct
      type t = addr_ty Pset.set

      let cmp = Pervasives.compare
      let empty = Pset.empty cmp
      let of_list = Pset.from_list cmp
      let union s1 s2 = Pset.union s1 s2
      let fold = Pset.fold

      let pp s = Pset.fold (fun (x,y) acc ->
        sprintf "(%d,%d) %s" x y acc) s ""
  end

  let get_inline_expr (uid: int): (unit typed_expr) eff =
    get >>= fun st ->
    match Pmap.lookup uid st.inline_expr_map with
    | None -> failwith (sprintf "Error: BmcSeqMem inline_expr not found %d"
                                uid)
    | Some e -> return e


  let get_expr (uid: int): Expr.expr eff =
    get >>= fun st ->
    match Pmap.lookup uid st.expr_map with
    | None -> failwith (sprintf "Error: BmcSeqMem expr not found %d" uid)
    | Some e -> return e


  let get_action (uid: int) : BmcZ3.intermediate_action eff =
    get >>= fun st ->
    match Pmap.lookup uid st.action_map with
    | None -> failwith (sprintf "Error: BmcSeqMem action not found %d" uid)
    | Some a -> return a

  let get_case_guards (uid: int): (Expr.expr list) eff =
    get >>= fun st ->
    match Pmap.lookup uid st.case_guard_map with
    | None -> failwith (sprintf "Error: BmcSeqMem case guard not found %d" uid)
    | Some es -> return es

  let get_drop_cont (uid: int) : Expr.expr eff =
    get >>= fun st ->
    match Pmap.lookup uid st.drop_cont_map with
    | None -> failwith (sprintf "BmcSeqMem: Uid %d not found in drop_cont_map" uid)
    | Some expr -> return expr

  let get_memory : memory_table eff =
   get >>= fun st ->
   return st.memory

  let update_memory (addr: addr_ty) (expr: Expr.expr) : unit eff =
    get >>= fun st ->
    put {st with memory = Pmap.add addr expr st.memory}

  let update_memory_table (memory: memory_table) : unit eff =
    get >>= fun st ->
    put {st with memory = memory}

  type ret_ty = {
    bindings : Expr.expr list;
    mod_addr : AddrSet.t;
  }

  let get_bindings (ret: ret_ty) : Expr.expr list =
    ret.bindings

  let empty_ret = { bindings = []; mod_addr = AddrSet.empty }
  let mk_ret bindings mod_addr =
    { bindings = bindings
    ; mod_addr = mod_addr
    }

  (* For each modified address, update base memory using tables
   * guarded by guards. *)
  let merge_memory (base     : memory_table)
                   (mod_addr : AddrSet.t)
                   (tables   : memory_table list)
                   (guards   : Expr.expr list) =
    let guarded_tables : (memory_table * Expr.expr) list =
      List.combine tables guards in
    AddrSet.fold (fun addr acc ->
      match Pmap.lookup addr acc with
      | None -> acc
      | Some expr_base ->
        let new_expr =
          List.fold_right (fun (table, guard) acc_expr ->
            match Pmap.lookup addr table with
            | None      -> acc_expr
            | Some expr -> mk_ite guard expr acc_expr
         ) guarded_tables expr_base in
        (* TODO: create new seq variable? *)
        Pmap.add addr new_expr acc
    ) mod_addr base

  (* TODO: move to separate file *)
  let mk_unspecified_expr (sort: Sort.sort) (ctype: Expr.expr)
                          : Expr.expr =
    if (Sort.equal (LoadedInteger.mk_sort) sort) then
      LoadedInteger.mk_unspecified ctype
    else if (Sort.equal (LoadedPointer.mk_sort) sort) then
      LoadedPointer.mk_unspecified ctype
    else
      assert false

  let mk_initial_value (ctype: ctype) (name: string) =
    match ctype with
    | Void0 ->
        (UnitSort.mk_unit, [])
    | Basic0 (Integer ity) ->
        let const = mk_fresh_const name integer_sort in
        let ge_ivmin =
            binop_to_z3 OpGe const (Pmap.find ctype ImplFunctions.ivmin_map) in
        let le_ivmax =
            binop_to_z3 OpLe const (Pmap.find ctype ImplFunctions.ivmax_map) in
        (const, [ge_ivmin;le_ivmax])
    | _ -> assert false


  let mk_initial_loaded_value (sort: Sort.sort) (name: string)
                              (ctype: ctype) (specified: bool)
                              : Expr.expr * (Expr.expr list) =
    if specified then begin
      let (initial_value, assertions) = mk_initial_value ctype name in
      assert (Sort.equal (LoadedInteger.mk_sort) sort);
      (LoadedInteger.mk_specified initial_value, assertions)
    end else
      (mk_unspecified_expr sort (CtypeSort.mk_nonatomic_expr ctype), [])

  (* TODO: mod_addr *)
  let do_paction (Paction(p, Action(loc, a, action_)) : unit typed_paction)
                 uid
                 : ret_ty eff =
    get_action uid >>= fun action ->
    match action with
    | ICreate(aid, sortlist, alloc_id) ->
        mapMi (fun i (ctype,sort) ->
          let addr = (alloc_id, i) in
          let seq_var =
            mk_fresh_const (sprintf "store_(%d %d)" alloc_id i) sort in
          update_memory addr seq_var >>
          let (initial_value, assumptions) =
            mk_initial_loaded_value sort (sprintf "init_%d,%d" alloc_id i)
                                    ctype false in
          let binding = mk_eq seq_var initial_value in
          return (addr, binding::assumptions)
        ) sortlist >>= fun retlist ->
        return { bindings = List.concat (List.map snd retlist)
               ; mod_addr = AddrSet.of_list (List.map fst retlist)
               }
    | IKill(aid) ->
        return empty_ret
    | ILoad(aid, (ctype,sort), ptr, rval, mo) ->
        (* TODO: alias analysis *)
        get_memory >>= fun possible_addresses ->
        mapM (fun (addr, expr_in_memory) ->
          let addr_sort = Expr.get_sort expr_in_memory in
          if (Sort.equal sort addr_sort) then
            let addr_expr = AddressSort.mk_from_addr addr in
            let addr_eq =
              mk_and [mk_not (PointerSort.is_null ptr)
                     ; mk_eq addr_expr (PointerSort.get_addr ptr)] in
            let impl_expr =
              mk_implies addr_eq (mk_eq rval expr_in_memory) in
            return (Some (impl_expr, addr_eq))
          else
            return None
        ) (Pmap.bindings_list possible_addresses) >>= fun retlist ->
        let filtered = List.map Option.get (List.filter is_some retlist) in
        (* TODO: should mk_or (List.map snd filtered be a vc? *)
        return { bindings = (mk_or (List.map snd filtered))
                            :: (List.map fst filtered)
               ; mod_addr = AddrSet.empty
               }
    | IStore(aid, (ctype,sort), ptr, wval, mo) ->
        (* TODO: alias analysis *)
        get_memory >>= fun possible_addresses ->
        mapM (fun (addr, expr_in_memory) ->
          let addr_sort = Expr.get_sort expr_in_memory in
          if (Sort.equal sort addr_sort) then
            let addr_expr = AddressSort.mk_from_addr addr in

            let new_seq_var =
              mk_fresh_const (sprintf "store_%s" (Expr.to_string addr_expr)) sort
            in
            (* new_seq_var is equal to to_store if addr_eq, else old value *)
            let addr_eq =
              mk_and [ mk_not (PointerSort.is_null ptr)
                     ; mk_eq (PointerSort.get_addr ptr) addr_expr] in
            let new_val = mk_eq new_seq_var wval in
            let old_val = mk_eq new_seq_var expr_in_memory in
            update_memory addr new_seq_var >>
            return (Some (addr, mk_ite addr_eq new_val old_val))
          else
            return None
        ) (Pmap.bindings_list possible_addresses) >>= fun update_list ->
        let filtered = List.map Option.get (List.filter is_some update_list) in
        assert (List.length filtered > 0);
        return { bindings = List.map snd filtered
               ; mod_addr = AddrSet.of_list (List.map fst filtered)
               }
    | ICompareExchangeStrong _ ->
        failwith "Error: CompareExchangeStrong only supported with --bmc_conc"
    | IFence (aid, mo) ->
       assert false
    | ILinuxLoad(aid, (ctype,sort), ptr, rval, mo) ->
       assert false
    | ILinuxStore(aid, (ctype,sort), ptr, wval, mo) ->
       assert false
    | ILinuxFence(aid, mo) ->
       assert false

  (* TODO: check if removing guard here is significantly faster *)
  let guard_assert (guard: Expr.expr) =
    mk_implies guard

  let rec do_e (Expr(annots, expr_) as expr)
               : ret_ty eff =
    let uid = get_id_expr expr in
    match expr_ with
    | Epure pe      ->
        return empty_ret
    | Ememop (memop, pes) ->
        return empty_ret
    | Eaction paction ->
        do_paction paction uid
    | Ecase (pe, cases) ->
        get_memory >>= fun old_memory ->
        mapM (fun (_, case_e) ->
          do_e case_e >>= fun ret_case ->
          get_memory  >>= fun mem ->
          update_memory_table old_memory >>
          return (mem, ret_case)
        ) cases >>= fun res_cases ->
        get_case_guards uid >>= fun guards ->

        let retlist = List.map snd res_cases in
        (* Update memory *)
        let mod_addr = List.fold_right (fun res acc ->
          AddrSet.union acc res.mod_addr) retlist AddrSet.empty in
        let new_memory =
          merge_memory old_memory mod_addr
                       (List.map fst res_cases) guards in
        update_memory_table new_memory >>

        let guarded_asserts = List.concat (List.map2
          (fun guard res -> List.map (guard_assert guard) res.bindings)
          guards retlist) in
        return { bindings = guarded_asserts
               ; mod_addr = mod_addr}
    | Elet _        -> assert false
    | Eif (cond, e1, e2) ->
        get_memory                     >>= fun old_memory ->
        do_e e1                        >>= fun res_e1 ->
        get_memory                     >>= fun mem_e1 ->
        update_memory_table old_memory >>
        do_e e2                        >>= fun res_e2 ->
        get_memory                     >>= fun mem_e2 ->

        get_expr (get_id_pexpr cond)   >>= fun cond_z3 ->
        let (guard1, guard2) = (cond_z3, mk_not cond_z3) in

        let mod_addr = AddrSet.union res_e1.mod_addr res_e2.mod_addr in
        let new_memory = merge_memory old_memory mod_addr
                                      [mem_e1; mem_e2] [guard1; guard2] in
        update_memory_table new_memory >>
        return { bindings = (List.map (guard_assert guard1) res_e1.bindings)
                           @(List.map (guard_assert guard2) res_e2.bindings)
               ; mod_addr = mod_addr
               }
    | Eskip         -> return empty_ret
    | Eccall _      -> assert false
    | Eproc _       -> assert false
    | Eunseq _ ->
        failwith "Error: Eunseq in sequentialised, concurrent mode only"
    | Ewseq (pat, e1, e2)
    | Esseq (pat, e1, e2) ->
        do_e e1 >>= fun res_e1 ->
        do_e e2 >>= fun res_e2 ->

        get_drop_cont (get_id_expr e1) >>= fun e1_drop_cont ->

        return {bindings = res_e1.bindings
                          @(List.map (guard_assert (mk_not e1_drop_cont))
                                     res_e2.bindings)
               ;mod_addr = AddrSet.union res_e1.mod_addr res_e2.mod_addr
              }
    | Easeq _       -> assert false
    | Eindet _      -> assert false
    | Ebound (_, e) ->
        do_e e
    | End es ->
        get_memory >>= fun old_memory ->
        mapM (fun expr ->
          do_e expr                      >>= fun res_expr ->
          get_memory                     >>= fun mem ->
          update_memory_table old_memory >>
          return (mem, res_expr)
        ) es >>= fun res_elist ->
        get_case_guards uid >>= fun guards ->
        let mem_tables = List.map fst res_elist in
        let ress       = List.map snd res_elist in
        let mod_addr = List.fold_right
          (fun res acc -> AddrSet.union acc res.mod_addr)
          ress AddrSet.empty in
        let new_memory = merge_memory old_memory mod_addr
                                      mem_tables guards in
        update_memory_table new_memory >>
        let guarded_asserts = List.concat (List.map2
          (fun guard res -> List.map (guard_assert guard) res.bindings)
          guards ress) in
        return {bindings = guarded_asserts
               ;mod_addr = mod_addr}
    | Esave _       (* fall through *)
    | Erun _        ->
        get_inline_expr uid >>= fun inline_expr ->
        do_e inline_expr
    | Epar es -> assert false
        (*BmcVC.mapM vcs_e es >>= fun vcss_es ->
        return (List.concat vcss_es)*)
    | Ewait _       -> assert false

  let do_globs (gname, bty, e) =
    do_e e

  let do_file (file: unit typed_file) (fn_to_check: sym_ty)
              : (Expr.expr list) eff =
    mapM do_globs file.globs >>= fun globs ->
    (match Pmap.lookup fn_to_check file.funs with
     | Some (Proc (annot, bTy, params, e)) ->
        do_e e
     | Some (Fun(ty, params, pe)) ->
        return empty_ret
     | _ -> assert false
    ) >>= fun ret ->
    return (ret.bindings @ (List.concat (List.map get_bindings globs)))
end
