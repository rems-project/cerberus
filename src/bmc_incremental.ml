open Bmc_common
open Bmc_conc
open Bmc_globals
open Bmc_monad
open Bmc_sorts
open Bmc_substitute
open Bmc_types
open Bmc_utils

open Core
open Core_aux
open Ocaml_mem
open Printf
open Util
open Z3
open Z3.Arithmetic

module Caux = Core_aux

(* CONTENTS
 * - BmcInline
 * - BmcSSA
 * - BmcZ3
 * - BmcDropCont
 * - BmcBind
 * - BmcVC
 * - BmcRet
 * - BmcSeqMem
 * - BmcConcActions
 *)

(* TODO: factor out all the repeated state *)
(* TODO: inline does some bad rewrites:
 *  - function calls
 *  - core type compatibility
 *  PEare_compatible is currently just equality
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

    fn_call_map : (int, sym_ty) Pmap.map;

    (* Return type for Erun *)
    fn_type : core_base_type option;

    (* procedure-local state *)
    proc_expr : (unit typed_expr) option;

    (* function call map: map from Core symbol -> function ptr*)
    fn_ptr_map : (sym_ty, sym_ty) Pmap.map;

  }

  include EffMonad(struct type state = state_ty end)

  let mk_initial file : state =
    { id_gen           = 0
    ; run_depth_table  = Pmap.empty Pervasives.compare
    ; file             = file
    ; inline_pexpr_map = Pmap.empty Pervasives.compare
    ; inline_expr_map  = Pmap.empty Pervasives.compare
    ; fn_call_map      = Pmap.empty Pervasives.compare
    ; fn_type          = None
    ; proc_expr        = None
    ; fn_ptr_map       = Pmap.empty Pervasives.compare
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

  let get_fn_type : core_base_type eff =
    get >>= fun st ->
    assert (is_some st.fn_type);
    return (Option.get st.fn_type)

  let put_fn_type (cbt : core_base_type) : unit eff =
    get >>= fun st ->
    put {st with fn_type = Some cbt}

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

  let add_fn_call (id: int) (fn_sym: sym_ty) : unit eff =
    get >>= fun st ->
    put {st with fn_call_map = Pmap.add id fn_sym st.fn_call_map}

  (* fn_ptr_map *)
  let add_to_fn_ptr_map (sym: sym_ty) (fn_sym: sym_ty) : unit eff =
    get >>= fun st ->
    put {st with fn_ptr_map = Pmap.add sym fn_sym st.fn_ptr_map}

  let get_fn_ptr_sym (sym : sym_ty) : sym_ty eff =
    get >>= fun st ->
    match Pmap.lookup sym st.fn_ptr_map with
    | None -> failwith (sprintf "BmcInline: fn_sym %s not found"
                        (symbol_to_string sym))
    | Some fn_sym -> return fn_sym

  (* TODO: hack to compute function from pointer *)
  let get_function_from_ptr (ptr: Ocaml_mem.pointer_value): sym_ty eff =
    get_file >>= fun file ->
    let ptr_str = pp_to_string (Ocaml_mem.pp_pointer_value ptr) in
    let (fn_sym, _) = List.find (fun (sym, _) ->
      ptr_str = (sprintf "Cfunction(%s)"
                         (Pp_symbol.to_string_pretty sym))
    ) (Pmap.bindings_list file.funinfo) in
    return fn_sym

  (* TODO: move this; really same as core_aux except typed. *)

  let mk_sym_pat sym_opt bTy: typed_pattern =
    (Pattern( [], (CaseBase (sym_opt, bTy))))

  let mk_ctype_pe ty: typed_pexpr =
    (Pexpr( [], BTy_ctype, (PEval (Vctype ty))))

  let mk_boolean_pe b: typed_pexpr =
    (Pexpr( [], BTy_boolean, (PEval (if b then Vtrue else Vfalse))))

  let rec mk_list_pe pes : typed_pexpr =
    (Pexpr( [], BTy_list BTy_ctype, (match pes with
      | [] ->
          PEctor( (Cnil BTy_ctype), [])
      | pe :: pes' ->
          PEctor( Ccons, [pe; mk_list_pe pes'])
    )))

  let mk_tuple_pe pes: typed_pexpr =
    let cbts = List.map (fun (Pexpr(_, cbt, _)) -> cbt) pes in
    (Pexpr( [], BTy_tuple cbts, (PEctor( Ctuple, pes))))

  let mk_ewseq pat e1 e2 : unit typed_expr =
    Expr([], Ewseq(pat, e1, e2))

  (* ======== Inline functions ======= *)
  let rec inline_pe (Pexpr(annots, bTy, pe_)) : typed_pexpr eff =
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
    | PEstruct (sym, pexprs) ->
        mapM (fun (cab_id, pe) ->
          inline_pe pe >>= fun inlined_pe ->
          return (cab_id, inlined_pe)) pexprs >>= fun inlined_pexprs ->
        return (PEstruct(sym, inlined_pexprs))
    | PEunion _  -> assert false
    | PEcfunction (Pexpr(_,_,PEsym sym)) ->
        get_fn_ptr_sym sym >>= fun fn_sym ->
        get_file >>= fun file ->
        (* Rewrite as tuple *)
        begin match Pmap.lookup fn_sym file.funinfo with
        | Some (ret_ty, args_ty, b1, b2) ->
            let pes =
              [mk_ctype_pe ret_ty
              ;mk_list_pe (List.map mk_ctype_pe @@ List.map snd args_ty)
              ;mk_boolean_pe b1
              ;mk_boolean_pe b2] in
            mapM inline_pe pes >>= fun inlined_pes ->
            return (PEctor(Ctuple, inlined_pes))
        | _ -> failwith "TODO: support generic core C functions"
        end
    | PEcfunction _ ->
        failwith "TODO: implement generic core C function call pattern"
    | PEmemberof (tag_sym, memb_ident, pe) ->
        inline_pe pe >>= fun inlined_pe ->
        return (PEmemberof(tag_sym, memb_ident, inlined_pe))
    | PEcall (name, pes)  ->
        mapM inline_pe pes >>= fun inlined_pes ->
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
        if depth >= !!bmc_conf.max_core_call_depth then
          let error_msg =
            sprintf "call_depth_exceeded: %s" (name_to_string  name) in
          let new_pexpr =
            (Pexpr([], ty, PEerror(error_msg, Pexpr([], BTy_unit,PEval(Vunit))))) in
          inline_pe new_pexpr >>= fun inlined_new_pexpr ->
          add_inlined_pexpr id inlined_new_pexpr >>
          return (PEcall (name, inlined_pes))
        else begin
          (* TODO: CBV/CBN semantics? *)
          (* Inline each argument *)
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
        return (PEare_compatible(inlined_pe1,inlined_pe2))
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
    | CompareExchangeWeak(pe1, pe2, pe3, pe4, mo1, mo2) ->
        inline_pe pe1 >>= fun inlined_pe1 ->
        inline_pe pe2 >>= fun inlined_pe2 ->
        inline_pe pe3 >>= fun inlined_pe3 ->
        inline_pe pe4 >>= fun inlined_pe4 ->
        return (CompareExchangeWeak(inlined_pe1, inlined_pe2, inlined_pe3, inlined_pe4, mo1, mo2))
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
    | Elet((Pattern(_, CaseBase(Some cty_sym, BTy_ctype))) as pat,
           pe,
           (Expr(_,Eif(
             Pexpr(_,_,PEnot(Pexpr(_,_,PEare_compatible(pe_ty, Pexpr(_,_,PEsym sym2))))),
                       Expr(_, Epure(Pexpr(_,_,PEundef _))),
                       _)) as e)) ->
        assert (sym_cmp cty_sym sym2 = 0);
        (* TODO: ugly hack. This changes the semantics and is just wrong. *)
        bmc_debug_print 7 "TODO: Elet hack for function calls";
        let sub_map = Pmap.add cty_sym pe_ty (Pmap.empty sym_cmp) in
        let hacky_expr = substitute_expr sub_map e in

        inline_pe pe >>= fun inlined_pe ->
        inline_e hacky_expr >>= fun inlined_hacky_expr ->
        return (Elet(pat, inlined_pe, inlined_hacky_expr))
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
    | Eccall (a, pe_ty, (Pexpr(_,_,PEsym fn_ptr) as pe_fn), pe_args) ->
        inline_pe pe_ty >>= fun inlined_pe_ty ->
        inline_pe pe_fn >>= fun inlined_pe_fn ->
        mapM inline_pe pe_args >>= fun inlined_pe_args ->

        get_fn_ptr_sym fn_ptr >>= fun fn_ptr_sym ->
        add_fn_call id fn_ptr_sym >>
        get_file >>= fun file ->

        (* Check if it is in file.stdlib (e.g. memcmp_proxy) or in file.funs *)
        let (fun_ty, fun_args, fun_expr) =
          match Pmap.lookup fn_ptr_sym file.stdlib with
          | Some (Proc(_, fun_ty, fun_args, fun_expr)) ->
             (fun_ty, fun_args, fun_expr)
          | Some _ -> assert false
          | None ->
              begin match Pmap.lookup fn_ptr_sym file.funs with
              | Some (Proc (_, fun_ty, fun_args, fun_expr)) ->
                  (fun_ty, fun_args, fun_expr)
              | Some (ProcDecl(_,_,_)) ->
                  failwith (sprintf "Function %s not defined"
                                    (name_to_string (Sym fn_ptr_sym)))
              | Some _ ->
                  failwith (sprintf "TODO: Eccall %s"
                                    (name_to_string (Sym fn_ptr_sym)))
              | None -> assert false
              end
        in
        lookup_run_depth (Sym fn_ptr_sym) >>= fun depth ->
        if depth >= !!bmc_conf.max_run_depth then
          begin
          let error_msg =
            sprintf "Eccall_depth_exceeded: %s" (name_to_string (Sym fn_ptr_sym)) in
          let new_expr =
            (Expr([],Epure(Pexpr([], fun_ty,
                           PEerror(error_msg,
                                   Pexpr([], BTy_unit, PEval(Vunit))))))) in
          inline_e new_expr >>= fun inlined_new_expr ->
          add_inlined_expr id inlined_new_expr >>
          return (Eccall(a, pe_ty, pe_fn, pe_args))
          end
        else
          begin
            (* TODO: not true for variadic *)
            assert (List.length pe_args = List.length fun_args);
            let sub_map = List.fold_right2
              (fun (sym,_) pe map -> Pmap.add sym pe map)
              fun_args inlined_pe_args (Pmap.empty sym_cmp) in
            let expr_to_check = substitute_expr sub_map fun_expr in

            get_proc_expr >>= fun old_proc_expr ->
            get_fn_type  >>= fun old_fn_type ->

            (* TODO: fn_ptr_map should be saved... *)
            update_proc_expr expr_to_check >>
            put_fn_type fun_ty >>
            increment_run_depth (Sym fn_ptr_sym) >>
            inline_e expr_to_check >>= fun inlined_expr_to_check ->
            decrement_run_depth (Sym fn_ptr_sym) >>
            put_fn_type old_fn_type >>
            update_proc_expr old_proc_expr >>

            add_inlined_expr id inlined_expr_to_check >>

            return (Eccall(a, pe_ty, pe_fn, pe_args))
          end
    | Eccall _ ->
        assert false
    | Eproc (a,name, pes) ->
        (* TODO: code duplication with PEcall/Eccall *)
        mapM inline_pe pes >>= fun inlined_pes ->
        lookup_run_depth name >>= fun depth ->
        get_file >>= fun file ->
        let (ty, args, fun_expr) =
          match name with
          | Sym sym ->
              begin match Pmap.lookup sym file.stdlib with
              | Some (Proc(_,ty, args, fun_expr)) -> (ty, args, fun_expr)
              | _ -> assert false
              end
          | Impl impl ->
                failwith (sprintf "EProc: %s not found" (name_to_string name))
        in
        if depth >= !!bmc_conf.max_core_call_depth then
          let error_msg =
            sprintf "call_depth_exceeded: %s" (name_to_string name) in
          let new_expr =
            (Expr([],Epure(Pexpr([], ty,
                           PEerror(error_msg,
                                   Pexpr([], BTy_unit, PEval(Vunit))))))) in
          inline_e new_expr >>= fun inlined_new_expr ->
          add_inlined_expr id inlined_new_expr >>
          return (Eproc(a, name, pes))
        else begin
          bmc_debug_print 7 "Eproc: Check this";
          let sub_map = List.fold_right2
            (fun (sym, _) pe table -> Pmap.add sym pe table)
            args inlined_pes (Pmap.empty sym_cmp) in
          let expr_to_check = substitute_expr sub_map fun_expr in
          increment_run_depth name >>
          inline_e expr_to_check >>= fun inlined_expr_to_check ->
          decrement_run_depth name >>
          add_inlined_expr id inlined_expr_to_check >>
          return (Eproc(a, name, pes))
        end
    | Eunseq es ->
        mapM inline_e es >>= fun inlined_es ->
        return (Eunseq(inlined_es))
    | Ewseq (pat, e1, e2) (* fall through *)
    | Esseq (pat, e1, e2) ->
        let cfun_opt = extract_cfun_if_cfun_call pat e1 e2 in
        (if is_some cfun_opt then
          let cfun_info = Option.get cfun_opt in
          get_function_from_ptr cfun_info.ptr >>= fun fn_sym ->
          add_to_fn_ptr_map cfun_info.fn_ptr fn_sym >>
          (if is_some cfun_info.fn_ptr_inner then
             add_to_fn_ptr_map (Option.get cfun_info.fn_ptr_inner) fn_sym
           else
             return ()
          )
        else
          return ()
        ) >>
        inline_e e1 >>= fun inlined_e1 ->
        inline_e e2 >>= fun inlined_e2 ->
        begin match e_ with
        | Ewseq _ -> return (Ewseq(pat, inlined_e1, inlined_e2))
        | Esseq _ -> return (Esseq(pat, inlined_e1, inlined_e2))
        | _ -> assert false
        end
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
          (* TODO: hacky; type is wrong. *)
          (* This should also be error but then would need to make expression...
           *)
          get_fn_type >>= fun ret_type ->
          let new_expr =
            (Expr([],Epure(Pexpr([], ret_type,
                           PEerror(error_msg,
                                   Pexpr([], BTy_unit, PEval(Vunit)))))))
                           (*error(error_msg,
                                  Pexpr([], BTy_unit, PEval (Vunit))))))) *)in
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
        return (Epar inlined_es)
    | Ewait _       -> assert false
    ) >>= fun inlined_e ->
    return (Expr(Abmc (Abmc_id id)::annots, inlined_e))

  let inline_globs (gname, glb) =
    match glb with
    | GlobalDef (bty, e) ->
      inline_e e >>= fun inlined_e ->
      return (gname, GlobalDef (bty, inlined_e))
    | GlobalDecl bty ->
      return (gname, GlobalDecl bty)

  let inline (file: unit typed_file) (fn_to_check: sym_ty)
             : (unit typed_file) eff =
    mapM inline_globs file.globs >>= fun globs ->
    (match Pmap.lookup fn_to_check file.funs with
     | Some (Proc (annot, bTy, params, e)) ->
         update_proc_expr e >>
         put_fn_type bTy    >>
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
    sym_table     : sym_table_ty;
    sym_expr_table  : sym_expr_table_ty;

    file   : unit typed_file; (* unmodified *)

    inline_pexpr_map : (int, typed_pexpr) Pmap.map;
    inline_expr_map  : (int, unit typed_expr) Pmap.map;
  }
  include EffMonad(struct type state = state_ty end)

  let mk_initial file inline_pexpr_map inline_expr_map : state =
    { sym_table        = Pmap.empty sym_cmp;
      sym_expr_table   = Pmap.empty sym_cmp;
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
    get >>= fun st ->
    match Pmap.lookup sym table with
    | Some _ -> failwith (sprintf "BmcSSA error: sym %s exists in sym_expr_table"
                                  (symbol_to_string sym))
    | None ->
        let expr = mk_fresh_const (symbol_to_string sym)
                                  (cbt_to_z3 ty st.file) in
        put_sym_expr_table (Pmap.add sym expr table)

  let get_fresh_sym (str: string option) : sym_ty eff =
    get >>= fun st ->
    return @@ Sym.fresh_fancy str

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
  let rename_sym (Symbol(_, n, stropt) as sym: sym_ty) : sym_ty eff =
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
    | PEstruct (sym, pexprs) ->
       mapM (fun (cab_id, pe) ->
          ssa_pe pe >>= fun ssad_pe ->
          return (cab_id, ssad_pe)) pexprs >>= fun ssad_pexprs ->
        return (PEstruct(sym, ssad_pexprs))
    | PEunion _  -> assert false
    | PEcfunction _ ->
        assert false

        (*get_inline_pexpr uid >>= fun inlined_pe ->
        ssa_pe inlined_pe >>= fun ssad_inlined_pe ->
        update_inline_pexpr uid ssad_inlined_pe >>
        return (PEcfunction pe) *)
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
    | CompareExchangeWeak(pe1, pe2, pe3, pe4, mo1, mo2) ->
        ssa_pe pe1 >>= fun ssad_pe1 ->
        ssa_pe pe2 >>= fun ssad_pe2 ->
        ssa_pe pe3 >>= fun ssad_pe3 ->
        ssa_pe pe4 >>= fun ssad_pe4 ->
        return (CompareExchangeWeak(ssad_pe1, ssad_pe2, ssad_pe3, ssad_pe4, mo1, mo2))
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
    | Eccall (a,pe_ty, pe_ptr, pe_args) ->
        get_inline_expr uid >>= fun inline_e ->
        ssa_e inline_e      >>= fun ssad_inlined_e ->
        update_inline_expr uid ssad_inlined_e >>
        return (Eccall (a,pe_ty, pe_ptr, pe_args))
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
    | Epar elist ->
        mapM ssa_e elist >>= fun ssad_elist ->
        return (Epar ssad_elist)
    | Ewait _       ->
        assert false
    ) >>= fun ssad_e ->
      put_sym_table original_table >>
      return (Expr(annots, ssad_e))

    let ssa_globs (gname, glb) =
      match glb with
      | GlobalDef (bty, e) ->
        (* Globals are not given fresh names for no arbitrary reason... *)
        add_to_sym_table gname gname >>
        put_sym_expr gname bty >>
        ssa_e e >>= fun ssad_e ->
        return (gname, GlobalDef (bty, ssad_e))
      | GlobalDecl bty ->
        add_to_sym_table gname gname >>
        put_sym_expr gname bty >>
        return (gname, GlobalDecl bty)

    let ssa_param ((sym, cbt): (sym_ty * core_base_type)) =
      rename_sym sym >>= fun new_sym ->
      put_sym_expr new_sym cbt >>
      return (new_sym, cbt)

    let ssa (file: unit typed_file) (fn_to_check: sym_ty)
            : (unit typed_file) eff =
      mapM ssa_globs file.globs >>= fun ssad_globs ->
      (match Pmap.lookup fn_to_check file.funs with
       | Some (Proc(annot, bTy, params, e)) ->
          mapM ssa_param params  >>= fun ssad_params ->
          ssa_e e                >>= fun ssad_e ->
          return (Proc (annot, bTy, ssad_params, ssad_e))
       | Some (Fun (ty, params, pe)) ->
          mapM ssa_param params >>= fun ssad_params ->
          ssa_pe pe             >>= fun ssad_pe ->
          return (Fun (ty, ssad_params, ssad_pe))
       | _ -> assert false
      ) >>= fun new_fn ->
      return {file with globs = ssad_globs;
                        funs  = Pmap.add fn_to_check new_fn file.funs}

end
(* ======= Convert to Z3 exprs ======= *)
module BmcZ3 = struct
  type alloc = int

  type ctype_sort = ctype * Sort.sort

  (* Massive TODO *)
  type intermediate_action =
    (* TODO: aid list for ICreate as a hack for structs *)
    | ICreate of aid list * ctype  (* align ty *) * ctype * ctype_sort list * alloc
    | ICreateReadOnly of aid list * ctype  (* align ty *) * ctype * ctype_sort list * alloc * Expr.expr (* initial_value *)
    | IKill of aid * Expr.expr (* ptr *) * bool (* is dynamic *)
    | ILoad of aid * ctype * (* TODO: list *) ctype_sort list * (* ptr *) Expr.expr * (* rval *) Expr.expr * Cmm_csem.memory_order
    | IStore of aid * ctype * ctype_sort list * (* ptr *) Expr.expr * (* wval *) Expr.expr * Cmm_csem.memory_order
    | ICompareExchangeStrong of
        (* Load expected value *) aid *
        (* If fail, do a load of obj then a store *) aid * aid *
        (* If succeed, do a rmw *) aid * ctype *
        ctype_sort list * (* object *) Expr.expr * (*expected *) Expr.expr * (* desired *) Expr.expr * (* rval_expected *) Expr.expr * (* rval_object *) Expr.expr * Cmm_csem.memory_order * Cmm_csem.memory_order
    | ICompareExchangeWeak of
        (* Loaded expected *) aid *
        (* If fail, do a load of obj and then a store *) aid * aid *
        (* If succeed, do a rmw *) aid * ctype *
        ctype_sort list * (* object *) Expr.expr * (*expected *) Expr.expr * (* desired *) Expr.expr * (* rval_expected *) Expr.expr * (* rval_object *) Expr.expr * Cmm_csem.memory_order * Cmm_csem.memory_order
    | IFence of aid * Cmm_csem.memory_order
    | IMemop of aid * Mem_common.memop * Expr.expr list (* arguments *) * Expr.expr list (* values bound by Z3; only relevant for PtrValidForDeref *)
    | ILinuxLoad of aid * ctype * ctype_sort list * (* ptr *) Expr.expr * (* rval *) Expr.expr * Linux.linux_memory_order
    | ILinuxStore of aid * ctype * ctype_sort list * (* ptr *) Expr.expr * (* wval *) Expr.expr * Linux.linux_memory_order
    | ILinuxRmw of aid * ctype * ctype_sort list * (* ptr *) Expr.expr * (* wval *) Expr.expr * (* rval *) Expr.expr * Linux.linux_memory_order
    | ILinuxFence of aid * Linux.linux_memory_order

  (*type permission_flag =
    | ReadWrite
    | ReadOnly*)

  (* TODO: kind in {object, region} *)

  (*type allocation_metadata =
    (* size *) int * ctype option * (* alignment *) int * (* base address *) Expr.expr * permission_flag *
    (* C prefix *) Sym.prefix
    *)
  (*
  let get_metadata_size (sz,_,_,_,_,_) : int = sz
  let get_metadata_base (_,_,_,base,_,_) : Expr.expr = base
  let get_metadata_ctype (_,ctype,_,_,_,_) : ctype option = ctype
  let get_metadata_align (_,_,align,_,_,_) : int = align
  let get_metadata_prefix (_,_,_,_,_,pref) : Sym.prefix = pref
  let print_metadata (size, cty, align, expr, _, pref) =
    sprintf "Size: %d, Base: %s, Align %d, prefix: %s"
                size (Expr.to_string expr) align
                (prefix_to_string pref)
  *)

  type z3_state = {
    (* Builds the following *)
    expr_map      : (int, Expr.expr) Pmap.map;
    case_guard_map: (int, Expr.expr list) Pmap.map;
    action_map    : (int, intermediate_action) Pmap.map;
    param_actions : (intermediate_action option) list;
    (* TODO: extend this to include type *)

    (* Provenance symbols and types that need to be constrained *)
    alloc_meta_map: (alloc, allocation_metadata) Pmap.map;
    prov_syms       : (Expr.expr * (Expr.expr * ctype)) list;

    file          : unit typed_file;

    (* Internal state *)
    alloc_supply  : alloc;
    aid_supply    : aid;

    inline_pexpr_map: (int, typed_pexpr) Pmap.map;
    inline_expr_map : (int, unit typed_expr) Pmap.map;
    sym_table       : (sym_ty, Expr.expr) Pmap.map;
    fn_call_map     : (int, sym_ty) Pmap.map;
  }

  let mk_initial file
                 inline_pexpr_map
                 inline_expr_map
                 sym_table
                 fn_call_map
                 : z3_state = {
    expr_map       = Pmap.empty Pervasives.compare;
    case_guard_map = Pmap.empty Pervasives.compare;
    action_map     = Pmap.empty Pervasives.compare;
    param_actions  = [];
    alloc_meta_map = Pmap.empty Pervasives.compare;
    prov_syms      = [];

    file = file;

    alloc_supply = 1; (* 0 is empty provenance *)
    aid_supply   = 0;

    inline_pexpr_map = inline_pexpr_map;
    inline_expr_map  = inline_expr_map;
    sym_table        = sym_table;
    fn_call_map      = fn_call_map;
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

  let get_fn_call (uid: int) : sym_ty eff =
    get >>= fun st ->
    match Pmap.lookup uid st.fn_call_map with
    | None -> failwith (sprintf "Error: BmcZ3 fn_call not found %d"
                                uid)
    | Some sym -> return sym

  let set_param_actions (actions: (intermediate_action option) list)
                        : unit eff =
    get >>= fun st ->
    put {st with param_actions = actions}

  let add_metadata (alloc_id: alloc) (meta: allocation_metadata) : unit eff =
    get >>= fun st ->
    put {st with alloc_meta_map = Pmap.add alloc_id meta st.alloc_meta_map}

  let add_prov_sym (sym: Expr.expr) ((ival,ty): Expr.expr * ctype) : unit eff =
    get >>= fun st ->
    put {st with prov_syms = (sym,(ival,ty)) :: st.prov_syms}

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
       get_file >>= fun file ->
       return (value_to_z3 cval file)
    | PEconstrained _ -> assert false
    | PEundef _ ->
        get_file >>= fun file ->
        let sort = cbt_to_z3 bTy file in
        return (mk_fresh_const (sprintf "undef_%d" uid) sort)
    | PEerror _ ->
        get_file >>= fun file ->
        let sort = cbt_to_z3 bTy file in
        return (mk_fresh_const (sprintf "error_%d" uid) sort)
    | PEctor (Civmin, [Pexpr(_, BTy_ctype, PEval (Vctype ctype))]) ->
        (* TODO: Get rid of ImplFunctions *)
        let raw_ctype = strip_atomic ctype in
        assert (is_integer_type raw_ctype);
        begin match Pmap.lookup raw_ctype ImplFunctions.ivmin_map with
        | Some expr -> return expr
        | None ->
           failwith (sprintf "Unsupported ctype: %s"
                             (pp_to_string (Pp_core_ctype.pp_ctype raw_ctype)))
        end
    | PEctor(Civmax, [Pexpr(_, BTy_ctype, PEval (Vctype ctype))]) ->
        let raw_ctype = strip_atomic ctype in
        assert (is_integer_type raw_ctype);
        begin match Pmap.lookup raw_ctype ImplFunctions.ivmax_map with
        | Some expr -> return expr
        | None ->
           failwith (sprintf "Unsupported ctype: %s"
                             (pp_to_string (Pp_core_ctype.pp_ctype raw_ctype)))
        end
    | PEctor(Civsizeof, [Pexpr(_, BTy_ctype, PEval (Vctype ctype))]) ->
        let raw_ctype = strip_atomic ctype in
        if is_pointer_type raw_ctype then
          return (int_to_z3 (Option.get(ImplFunctions.sizeof_ptr)))
        else begin
          (if not (is_integer_type raw_ctype) then
            failwith "TODO: sizeof non-integer types"
          );
          begin match Pmap.lookup raw_ctype ImplFunctions.sizeof_map with
          | Some expr -> return expr
          | None ->
             failwith (sprintf "Unsupported ctype: %s"
                               (pp_to_string (Pp_core_ctype.pp_ctype raw_ctype)))
          end
        end
    | PEctor(Civalignof, [Pexpr(_, BTy_ctype, PEval (Vctype ctype))]) ->
        (* We can just directly compute the values rather than do it in the
         * roundabout way as in the above *)
        let raw_ctype = strip_atomic ctype in
        assert (is_integer_type raw_ctype);
        get_file >>= fun file ->
        return (int_to_z3 (alignof_type raw_ctype file));
    | PEctor (ctor, pes) ->
        get_file >>= fun file ->
        mapM z3_pe pes >>= fun z3d_pes ->
        return (ctor_to_z3 ctor z3d_pes (Some bTy) uid file)
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
        (* TODO: different w/ address type *)
        let ty_size = PointerSort.type_size ty file in
          (*bmcz3sort_size (ctype_to_bmcz3sort ty file) in*)
        let shift_size = binop_to_z3 OpMul z3d_index (int_to_z3 ty_size) in

        (*let addr = PointerSort.get_addr z3d_ptr in

        return (PointerSort.mk_ptr (AddressSort.shift_index_by_n addr shift_size))
        *)
        return (PointerSort.shift_by_n z3d_ptr shift_size)
    | PEmember_shift (ptr, sym, member) ->
        (* TODO: padding/alignment *)
        z3_pe ptr >>= fun z3d_ptr ->
        get_file  >>= fun file ->
        begin match Pmap.lookup sym file.tagDefs with
        | Some (StructDef memlist) ->
            let (size, (index_list, _)) =
              PointerSort.struct_member_index_list sym file in
            let member_indices = zip index_list memlist in
            let shift_opt = List.find_opt (fun (shift, (mem, _)) ->
              if cabsid_cmp mem member = 0 then true
              else false
            ) member_indices in
            (match shift_opt with
            | Some (shift, _) ->
                return (PointerSort.shift_by_n z3d_ptr (int_to_z3 shift))
            | None -> assert false
            )
        | _ -> assert false
        end
    | PEnot pe ->
        z3_pe pe >>= fun z3d_pe ->
        return (mk_not z3d_pe)
    | PEop (binop, pe1, pe2) ->
        z3_pe pe1 >>= fun z3d_pe1 ->
        z3_pe pe2 >>= fun z3d_pe2 ->
        return (binop_to_z3 binop z3d_pe1 z3d_pe2)
    | PEstruct (sym, pes) ->
        get_file >>= fun file ->
        let struct_sort = CtypeToZ3.struct_sym_to_z3_sort sym file in
        (* TODO: assume pes are in order *)
        mapM (fun (_, pe) -> z3_pe pe) pes >>= fun z3d_pes ->
        return (CustomTuple.mk_tuple struct_sort z3d_pes)
    | PEunion _     -> assert false
    | PEcfunction _ ->
        (*get_inline_pexpr uid >>= fun inline_pe ->
        z3_pe inline_pe *)
        assert false
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
        let raw_ctype = strip_atomic ctype in
        begin match Pmap.lookup raw_ctype ImplFunctions.is_unsigned_map with
        | Some expr -> return expr
        | None ->
           failwith (sprintf "Unsupported ctype: %s"
                             (pp_to_string (Pp_core_ctype.pp_ctype raw_ctype)))
        end
    | PEis_unsigned _    -> assert false
    | PEare_compatible (pe1, pe2) ->
        bmc_debug_print 7 "TODO: PEare_compatible";
        z3_pe pe1 >>= fun z3d_pe1 ->
        z3_pe pe2 >>= fun z3d_pe2 ->
        (* TODO: Currently just assert they are the same type *)
        return (mk_eq z3d_pe1 z3d_pe2)
    | PEbmc_assume pe ->
        z3_pe pe >>= fun _ ->
        return UnitSort.mk_unit
    ) >>= fun z3d_pexpr ->
    add_expr uid z3d_pexpr >>
    return z3d_pexpr

  let mk_create_aux ctype align_ty (pref: Sym.prefix)
                    (permission: permission_flag) =
    get_file >>= fun file ->
    get_fresh_alloc >>= fun alloc_id ->
    (* TODO: we probably don't actually want to flatten the sort list *)
    let flat_sortlist = flatten_bmcz3sort (ctype_to_bmcz3sort ctype file) in
    (* TODO: replace aid list -> single aid *)
    get_fresh_aid >>= fun aid ->
    let aids = [aid] in
    (*(match ctype with
     | Struct0 _ -> mapMi (fun i _ -> get_fresh_aid) flat_sortlist
     | _         -> get_fresh_aid >>= fun aid -> return [aid]
    ) >>= fun aids ->*)
    let base_addr = PointerSort.mk_nd_addr alloc_id in
    add_metadata alloc_id (PointerSort.type_size ctype file,
                           Some ctype,
                           alignof_type align_ty file,
                           base_addr,
                           permission, pref) >>

    return (alloc_id,flat_sortlist, aids, base_addr)


  let mk_create_read_only ctype align_ty (pref: Sym.prefix)
                          (initial_value: Expr.expr) =
    get_file >>= fun file ->
    mk_create_aux ctype align_ty pref ReadOnly
        >>= fun (alloc_id, flat_sortlist, aids, base_addr) ->
    return (PointerSort.mk_ptr (int_to_z3 alloc_id) base_addr,
            ICreateReadOnly (aids, ctype, align_ty, flat_sortlist,
                             alloc_id, initial_value))

  let mk_create ctype align_ty (pref: Sym.prefix) =
    get_file >>= fun file ->
    mk_create_aux ctype align_ty pref ReadWrite
        >>= fun (alloc_id, flat_sortlist, aids, base_addr) ->
    return (PointerSort.mk_ptr (int_to_z3 alloc_id) base_addr,
            ICreate (aids, ctype, align_ty, flat_sortlist, alloc_id))

  let z3_action (Paction(p, Action(loc, a, action_)) ) uid =
    (match action_ with
    | Create (Pexpr(_, _, PEctor(Civalignof, [Pexpr(_, BTy_ctype, PEval (Vctype align))])),
              Pexpr(_, BTy_ctype, PEval (Vctype ctype)), prefix) ->
        mk_create ctype align prefix
    | Create _ ->
        assert false
    | CreateReadOnly (Pexpr(_, _, PEctor(Civalignof, [Pexpr(_, BTy_ctype, PEval (Vctype align))])),
              Pexpr(_, BTy_ctype, PEval (Vctype ctype)),
              initial_value, prefix) ->
        z3_pe initial_value >>= fun z3d_initial_value ->
        mk_create_read_only ctype align prefix z3d_initial_value
    | Alloc0 _ ->
        failwith "TODO: dynamic allocation"
    | Kill (b, pe) ->
        get_fresh_aid >>= fun aid ->
        (* TODO: bool for free dynamic ignored *)
        bmc_debug_print 7 "TODO: kill ignored";
        z3_pe pe >>= fun z3d_pe ->
        return (UnitSort.mk_unit, IKill (aid, z3d_pe,b))
    | Store0 (b, Pexpr(_,_,PEval (Vctype ty)), Pexpr(_,_,PEsym sym), wval, mo) ->
        get_fresh_aid  >>= fun aid ->
        lookup_sym sym >>= fun sym_expr ->
        z3_pe wval     >>= fun z3d_wval ->
        get_file       >>= fun file ->
        let flat_sortlist = flatten_bmcz3sort (ctype_to_bmcz3sort ty file) in

        return (UnitSort.mk_unit,
                IStore (aid, ty, flat_sortlist, sym_expr, z3d_wval, mo))
    | Store0 _ ->
        assert false
    | Load0 (Pexpr(_,_,PEval (Vctype ty)), Pexpr(_,_,PEsym sym), mo) ->
        get_fresh_aid  >>= fun aid ->
        get_file >>= fun file ->
        let flat_sortlist = flatten_bmcz3sort (ctype_to_bmcz3sort ty file) in
        (* TODO: can't load multiple memory locations... *)
        assert (List.length flat_sortlist = 1);
        let (_, sort) = List.hd flat_sortlist in
        lookup_sym sym >>= fun sym_expr ->
        let rval_expr = mk_fresh_const ("load_" ^ (symbol_to_string sym)) sort in
        return (rval_expr, ILoad (aid, ty, flat_sortlist, sym_expr, rval_expr, mo))
    | Load0 _ ->
        assert false
    | RMW0 (pe1, pe2, pe3, pe4, mo1, mo2) ->
        assert false
    | CompareExchangeStrong(Pexpr(_,_,PEval (Vctype ty)),
                            Pexpr(_,_,PEsym obj),
                            Pexpr(_,_,PEsym expected),
                            desired, mo_success, mo_failure) (* fall through *)
    | CompareExchangeWeak  (Pexpr(_,_,PEval (Vctype ty)),
                            Pexpr(_,_,PEsym obj),
                            Pexpr(_,_,PEsym expected),
                            desired, mo_success, mo_failure) ->

        get_fresh_aid  >>= fun aid_load ->
        get_fresh_aid  >>= fun aid_fail_load ->
        get_fresh_aid  >>= fun aid_fail_store ->
        get_fresh_aid  >>= fun aid_succeed_rmw ->
        get_file >>= fun file ->
        let flat_sortlist = flatten_bmcz3sort (ctype_to_bmcz3sort ty file) in
        assert (List.length flat_sortlist = 1); (* TODO *)
        let (ctype, sort) = List.hd flat_sortlist in

        let rval_expected =
          mk_fresh_const ("load_" ^ (symbol_to_string expected)) sort in
        let rval_object =
          mk_fresh_const ("load_" ^ (symbol_to_string obj)) sort in

        lookup_sym obj      >>= fun obj_expr ->
        lookup_sym expected >>= fun expected_expr ->
        z3_pe desired       >>= fun z3d_desired ->

        begin match action_ with
        | CompareExchangeStrong _ ->
          let success_guard = mk_eq rval_expected rval_object in
          add_guards uid [success_guard] >>
          (* TODO *)
          return (mk_ite success_guard (LoadedInteger.mk_specified (int_to_z3 1))
                                       (LoadedInteger.mk_specified (int_to_z3 0)),
                  ICompareExchangeStrong (
                    aid_load, aid_fail_load, aid_fail_store, aid_succeed_rmw, ty,
                    flat_sortlist, obj_expr, expected_expr,
                    z3d_desired, rval_expected, rval_object,
                    mo_success, mo_failure))
        | CompareExchangeWeak _ ->
            (* ComparExchangeWeak may fail spuriously; we implement this by
             * creating a fresh Boolean constant representing spuriuos failure
             *)
          let spurious_fail =
            mk_fresh_const "cmpxcgweak_spurious_fail" boolean_sort in
          let success_guard = mk_and [mk_eq rval_expected rval_object
                                     ;mk_not spurious_fail] in
          add_guards uid [success_guard] >>
          return (mk_ite success_guard (LoadedInteger.mk_specified (int_to_z3 1))
                                       (LoadedInteger.mk_specified (int_to_z3 0)),
                  ICompareExchangeWeak (
                    aid_load, aid_fail_load, aid_fail_store, aid_succeed_rmw, ty,
                    flat_sortlist, obj_expr, expected_expr,
                    z3d_desired, rval_expected, rval_object,
                    mo_success, mo_failure))
        | _ -> assert false
        end

    | CompareExchangeStrong _ ->
        assert false
    | CompareExchangeWeak _ ->
        assert false
    | Fence0 mo ->
        get_fresh_aid  >>= fun aid ->
        return (UnitSort.mk_unit, IFence (aid, mo))
    | LinuxFence mo ->
        assert_memory_mode_linux ();
        get_fresh_aid  >>= fun aid ->
        return (UnitSort.mk_unit, ILinuxFence (aid, mo))
    | LinuxLoad (Pexpr(_,_,PEval (Vctype ty)), Pexpr(_,_,PEsym sym), mo) ->
        assert_memory_mode_linux ();
        assert (!!bmc_conf.concurrent_mode);
        get_fresh_aid  >>= fun aid ->
        get_file >>= fun file ->
        let flat_sortlist = flatten_bmcz3sort (ctype_to_bmcz3sort ty file) in
        let (ctype, sort) = List.hd flat_sortlist in
        (* TODO: can't load multiple memory locations... *)
        assert (List.length flat_sortlist = 1); (* TODO *)
        lookup_sym sym >>= fun sym_expr ->
        let rval_expr = mk_fresh_const ("load_" ^ (symbol_to_string sym)) sort in
        return (rval_expr, ILinuxLoad (aid, ty, flat_sortlist,
                sym_expr, rval_expr, mo))
    | LinuxLoad _ ->
        assert false
    | LinuxStore (Pexpr(_,_,PEval (Vctype ty)), Pexpr(_,_,PEsym sym), wval, mo) ->
        assert_memory_mode_linux ();
        get_fresh_aid  >>= fun aid ->
        lookup_sym sym >>= fun sym_expr ->
        z3_pe wval     >>= fun z3d_wval ->
        get_file       >>= fun file ->
        let flat_sortlist = flatten_bmcz3sort (ctype_to_bmcz3sort ty file) in
        assert (List.length flat_sortlist = 1); (* TODO *)
        return (UnitSort.mk_unit,
                ILinuxStore (aid, ty, flat_sortlist, sym_expr, z3d_wval, mo))
    | LinuxStore _ ->
        assert false
    | LinuxRMW (Pexpr(_,_,PEval (Vctype ty)), Pexpr(_,_,PEsym sym), wval, mo) ->
        assert_memory_mode_linux ();
        get_fresh_aid  >>= fun aid ->
        lookup_sym sym >>= fun sym_expr ->
        z3_pe wval     >>= fun z3d_wval ->
        get_file       >>= fun file ->
        let flat_sortlist = flatten_bmcz3sort (ctype_to_bmcz3sort ty file) in
        assert (List.length flat_sortlist = 1);
        let (ctype, sort) = List.hd flat_sortlist in
        let rval_expr = mk_fresh_const ("load_" ^ (symbol_to_string sym)) sort in
        return (rval_expr,
                ILinuxRmw (aid, ty, flat_sortlist, sym_expr, z3d_wval, rval_expr, mo))
    | _ -> assert false
    ) >>= fun (z3d_action, intermediate_action) ->
    add_action uid intermediate_action >>
    return z3d_action

  let rec z3_e (Expr(annots, expr_) as expr: unit typed_expr) : Expr.expr eff =
    let uid = get_id_expr expr in

    (match expr_ with
    | Epure pe ->
        z3_pe pe
    | Ememop (PtrValidForDeref, [ctype;ptr]) ->
        (* TODO: includes type *)
        bmc_debug_print 7 "TODO: PtrValidForDeref: check type";
        bmc_debug_print 7 "TODO: PtrValidForDeref: check object lifetime";
        z3_pe ctype >>= fun _ ->
        z3_pe ptr >>= fun z3d_ptr ->

        get_fresh_aid >>= fun aid ->

        let is_hb_before_kill =
          mk_fresh_const ("ptrValidForDeref_" ^ (Expr.to_string z3d_ptr)) boolean_sort in
        let intermediate_action =
          (IMemop(aid, PtrValidForDeref, [z3d_ptr], [is_hb_before_kill])) in

        (* PtrValidForDeref in Core isn't supposed to check range.
         * However bad things happen right now if we generate memory
         * bindings that are not satisfiable (e.g. there is nothing to
         * read from; so we leave this in for now *)
        add_action uid intermediate_action >>
        return (mk_and [is_hb_before_kill
                       ;PointerSort.valid_ptr z3d_ptr
                       ;PointerSort.ptr_in_range z3d_ptr])
    | Ememop (PtrEq, [p1;p2]) ->
        z3_pe p1 >>= fun z3d_p1 ->
        z3_pe p2 >>= fun z3d_p2 ->
        return (PointerSort.ptr_eq z3d_p1 z3d_p2)
    | Ememop (PtrNe, [p1;p2]) ->
        z3_pe p1 >>= fun z3d_p1 ->
        z3_pe p2 >>= fun z3d_p2 ->
        return (mk_not (PointerSort.ptr_eq z3d_p1 z3d_p2))
    | Ememop (PtrLt, [p1;p2]) ->
        z3_pe p1 >>= fun z3d_p1 ->
        z3_pe p2 >>= fun z3d_p2 ->
        (* TODO: Get rid of this code duplication *)
        return (binop_to_z3 OpLt (PointerSort.get_addr_index z3d_p1)
                                 (PointerSort.get_addr_index z3d_p2))
    | Ememop (PtrGt, [p1;p2]) ->
        z3_pe p1 >>= fun z3d_p1 ->
        z3_pe p2 >>= fun z3d_p2 ->
        return (binop_to_z3 OpGt (PointerSort.get_addr_index z3d_p1)
                                 (PointerSort.get_addr_index z3d_p2))
    | Ememop (PtrLe, [p1;p2]) ->
        z3_pe p1 >>= fun z3d_p1 ->
        z3_pe p2 >>= fun z3d_p2 ->
        return (binop_to_z3 OpLe (PointerSort.get_addr_index z3d_p1)
                                 (PointerSort.get_addr_index z3d_p2))
    | Ememop (PtrGe, [p1;p2]) ->
        z3_pe p1 >>= fun z3d_p1 ->
        z3_pe p2 >>= fun z3d_p2 ->
        return (binop_to_z3 OpGe (PointerSort.get_addr_index z3d_p1)
                                 (PointerSort.get_addr_index z3d_p2))
    | Ememop (Ptrdiff, [((Pexpr(_,BTy_ctype, (PEval (Vctype ctype)))) as ty);p1;p2]) ->
        assert (g_pnvi);
        z3_pe ty >>= fun _ ->
        z3_pe p1 >>= fun z3d_p1 ->
        z3_pe p2 >>= fun z3d_p2 ->
        get_file >>= fun file ->

        get_fresh_aid >>= fun aid ->
        let intermediate_action =
          (IMemop(aid, Ptrdiff, [z3d_p1;z3d_p2], [])) in
        add_action uid intermediate_action >>

        (* TODO: assert PNVI model *)
        let raw_ptr_diff = PointerSort.ptr_diff_raw z3d_p1 z3d_p2 in
        let type_size = PointerSort.type_size ctype file in
        (* TODO *)
        return (binop_to_z3 OpDiv raw_ptr_diff (int_to_z3 type_size))
    | Ememop(IntFromPtr, [ctype_src; ctype_dst; ptr]) ->
        assert (g_pnvi);
        z3_pe ctype_src >>= fun _ ->
        z3_pe ctype_dst >>= fun _ ->
        z3_pe ptr       >>= fun z3d_ptr ->

        (* 0 if p = null;
         * a if p = (prov,a) and a is in value_range(ctype_int),
         * UB otherwise
         *
         * We leave UB to BmcVCs*)
        return (mk_ite (PointerSort.is_null z3d_ptr) (int_to_z3 0)
                       (PointerSort.get_addr_index z3d_ptr)
               )
    | Ememop(PtrFromInt, [ctype_src;ctype_dst;ival]) ->
        assert (g_pnvi);
        z3_pe ctype_src >>= fun _ ->
        z3_pe ctype_dst >>= fun _ ->
        z3_pe ival      >>= fun z3d_ival ->

        let ctype = ctype_from_pexpr ctype_dst in

        let new_prov_sym =
          mk_fresh_const (sprintf "Prov_PtrFromInt_%d" uid) integer_sort in
        add_prov_sym new_prov_sym (z3d_ival,ctype) >>= fun _ ->

        (* null if x = 0
         * (@i,x) if @i is the allocation corresponding to x
         * (@empty, x) if there is no such allocation *)
        (* TODO: stuff breaks right now if the ival does not correspond to
         * the larger addresses (e.g. char* casts...) *)
        bmc_debug_print 7 "TODO: PtrFromInt allows casts to unsupported addresses";
        return (mk_ite (mk_eq z3d_ival (int_to_z3 0))
                       PointerSort.mk_null
                       (PointerSort.mk_ptr_from_int_addr new_prov_sym z3d_ival)
               )
    | Ememop (Memcmp, [p;q;size]) ->
        assert false
    | Ememop (PtrWellAligned,[ctype_pe;ptr]) ->
        assert (g_pnvi);
        (* We only support this with byte-wise mode *)
        failwith "Ptr type-casting not supported"
        (* address of ptr % align of ctype is 0 *)
        (* TODO: what if NULL? *)
        (*let ctype = ctype_from_pexpr ctype_pe in
        z3_pe ctype_pe >>= fun _ ->
        z3_pe ptr      >>= fun z3d_ptr ->
        get_file       >>= fun file ->
        let addr_of_ptr = PointerSort.get_addr_index z3d_ptr in
        let alignment = int_to_z3 (alignof_type ctype file) in
        return (mk_eq (Integer.mk_mod g_ctx addr_of_ptr alignment)
                      (int_to_z3 0)
               )*)
    | Ememop (PtrArrayShift,
              [ptr;Pexpr(_, BTy_ctype, PEval (Vctype ctype));index]) ->
        (* We treat this like a PEarray_shift;
         * except in the memory model we add a check for pointer
         * validity/lifetime
         *)
        assert (g_pnvi);
        z3_pe ptr      >>= fun z3d_ptr ->
        z3_pe index    >>= fun z3d_index ->
        get_file >>= fun file ->
        (* TODO: different w/ address type *)
        let ty_size = PointerSort.type_size ctype file in
        let shift_size = binop_to_z3 OpMul z3d_index (int_to_z3 ty_size) in
        let ret_ptr = PointerSort.shift_by_n z3d_ptr shift_size in

        (* Add intermediate action *)
        (* ty and index not needed for lifetime check *)
        get_fresh_aid >>= fun aid ->
        let intermediate_action =
          (IMemop(aid, PtrArrayShift, [z3d_ptr;ret_ptr], [])) in
        add_action uid intermediate_action >>

        return ret_ptr
    | Ememop (memop,_ ) ->
        failwith (sprintf "TODO: support %s"
                          (pp_to_string (Pp_mem.pp_memop memop)))
    | Eaction action ->
        z3_action action uid
    | Ecase (pe, cases) ->
        z3_pe pe                       >>= fun z3d_pe ->
        mapM z3_e (List.map snd cases) >>= fun z3d_cases_e ->
        let (_, guards) = compute_case_guards (List.map fst cases) z3d_pe in
        add_guards uid guards >>
        return (mk_guarded_ite z3d_cases_e guards)
    | Elet (pat, pe, e) ->
        z3_pe pe >>= fun _ ->
        z3_e e
    | Eif (pe, e1, e2) ->
        z3_pe pe >>= fun z3d_pe ->
        z3_e e1  >>= fun z3d_e1 ->
        z3_e e2  >>= fun z3d_e2 ->
        let (guard1, guard2) = (z3d_pe, mk_not z3d_pe) in
        add_guards uid [guard1; guard2] >>
        return (mk_ite guard1 z3d_e1 z3d_e2)
    | Eskip ->
        return UnitSort.mk_unit
    | Eccall _ ->
        get_inline_expr uid >>= fun inlined_expr ->
        get_fn_call uid >>= fun fn_sym ->
        get_file >>= fun file ->

        let ret_ty =
          begin match Pmap.lookup fn_sym file.funs with
          | Some Proc(_, ret_ty, _, _) -> ret_ty
          | _ ->
              begin match Pmap.lookup fn_sym file.stdlib with
              | Some Proc(_, ret_ty, _,_) -> ret_ty
              | _ ->
                failwith (sprintf "Unknown ccall: %s" (symbol_to_string fn_sym))
              end
          end in
        let new_ret_const =
            mk_fresh_const (sprintf "ret_%s_%s"
                                    (Pp_symbol.to_string fn_sym)
                                    (string_of_int uid))
                           (cbt_to_z3 ret_ty file) in
        z3_e inlined_expr >>= fun _ ->
        return new_ret_const
    | Eproc _  -> assert false
    | Eunseq elist ->
        get_file >>= fun file ->
        assert (not !!bmc_conf.sequentialise);
        assert (!!bmc_conf.concurrent_mode);
        mapM z3_e elist >>= fun z3d_elist ->
        return (ctor_to_z3 Ctuple z3d_elist None uid file)
    | Ewseq (pat, e1, e2) ->
        z3_e e1 >>= fun _ ->
        z3_e e2
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
        (* Need to save return value *)
        return (UnitSort.mk_unit)
    | Epar elist ->
        get_file >>= fun file ->
        assert (!!bmc_conf.concurrent_mode);
        mapM z3_e elist >>= fun z3d_elist ->
        return (ctor_to_z3 Ctuple z3d_elist None uid file)
    | Ewait _  -> assert false
    ) >>= fun ret ->
    add_expr uid ret >>
    return ret

    let z3_globs (gname, glb) =
      match glb with
      | GlobalDef (bty, e) ->
        z3_e e >>= fun z3d_e ->
(*        return (gname, bty, z3d_e)*)
        return ()
      | GlobalDecl ty ->
        return ()

    let z3_param ((sym, cbt): (sym_ty * core_base_type))
                 (ctype: ctype)
                 (fn_to_check: sym_ty)
                 : (intermediate_action option) eff =
      if not (is_core_ptr_bty cbt) then
        return None
      else begin
        mk_create ctype ctype (* TODO: alignment *)
            (PrefSource(Location_ocaml.other "param", [fn_to_check; sym]))
            >>= fun (_,action) ->
        return (Some action)
      end

    let z3_params (params : (sym_ty * core_base_type) list)
                  (fn_to_check : sym_ty)
                  : (intermediate_action option) list eff =
      get_file >>= fun file ->
      match Pmap.lookup fn_to_check file.funinfo with
      | None -> failwith (sprintf "BmcZ3 z3_params: %s not found"
                                  (symbol_to_string fn_to_check))
      | Some (_, param_tys, _, _) ->
          mapM2 (fun p ty -> z3_param p ty fn_to_check) params @@ List.map snd param_tys

    let z3_file (file: unit typed_file) (fn_to_check: sym_ty)
                : (unit typed_file) eff =
      mapM z3_globs file.globs >>
      (match Pmap.lookup fn_to_check file.funs with
      | Some (Proc(annot, bTy, params, e)) ->
          z3_params params fn_to_check >>= fun param_actions ->
          set_param_actions param_actions >>
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
    | Elet (pat, pe, e) ->
        drop_cont_e e
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
    | Eccall _ ->
        get_inline_expr uid      >>= fun inlined_expr ->
        drop_cont_e inlined_expr >>= fun _ ->
        return mk_false
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
    | Epar elist ->
        mapM drop_cont_e elist >>= fun drop_cont_elist ->
        (* TODO: Erun within Epar? *)
        return mk_false
    | Ewait _       -> assert false
    ) >>= fun drop_expr ->
    add_to_drop_cont_map uid drop_expr >>
    return drop_expr

  let drop_cont_globs(gname, glb) =
    match glb with
    | GlobalDef(_, e) ->
        drop_cont_e e >>= fun _ ->
        return ()
    | GlobalDecl _ ->
        return ()

  let drop_cont_file (file: unit typed_file) (fn_to_check: sym_ty)
                     : Expr.expr eff =
    mapM drop_cont_globs file.globs >>
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
    alloc_meta_map   : (int, allocation_metadata) Pmap.map;
  }

  include EffMonad(struct type state = binding_state end)

  let mk_initial inline_pexpr_map
                 inline_expr_map
                 sym_table
                 case_guard_map
                 expr_map
                 action_map
                 alloc_meta
                 : state =
  { inline_pexpr_map = inline_pexpr_map;
    inline_expr_map  = inline_expr_map;
    sym_table        = sym_table;
    case_guard_map   = case_guard_map;
    expr_map         = expr_map;
    action_map       = action_map;
    alloc_meta_map   = alloc_meta;
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

  let get_meta (alloc_id: int) : allocation_metadata eff =
    get >>= fun st ->
    match Pmap.lookup alloc_id st.alloc_meta_map with
    | None -> failwith (sprintf "BmcBind: alloc id %d not found in alloc_meta"
                                alloc_id)
    | Some data -> return data

  type binding =
  | BindLet of Expr.expr (* Normal let binding *)
  | BindAssume of Location_ocaml.t option * Expr.expr

  (*let is_bind_let = function
    | BindLet _ -> true
    | _ -> false

  let is_bind_assume = function
    | BindAssume _ -> true
    | _ -> false
  *)

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

  let rec mk_let_bindings_raw (Pattern(_,pat): typed_pattern) (expr: Expr.expr)
                              : Expr.expr eff =
    (match pat with
    | CaseBase(sym, _) ->
        mk_let_binding sym expr
    | CaseCtor (Ctuple, patlist) ->
        assert (Expr.get_num_args expr = List.length patlist);
        mapM (fun (pat, e) -> mk_let_bindings_raw pat e)
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
    | CaseCtor(Cnil BTy_ctype, []) ->
        assert (Sort.equal (Expr.get_sort expr) (CtypeListSort.mk_sort));
        return mk_true
    | CaseCtor(Ccons, [hd;tl]) ->
        assert (Sort.equal (Expr.get_sort expr) (CtypeListSort.mk_sort));
        let is_cons = CtypeListSort.is_cons expr in
        mk_let_bindings_raw hd (CtypeListSort.get_head expr) >>= fun eq_head ->
        mk_let_bindings_raw tl (CtypeListSort.get_tail expr) >>= fun eq_tail ->
        return (mk_and [is_cons; eq_head; eq_tail])
    | CaseCtor(_, _) ->
        assert false
    )

  let mk_let_bindings (pat: typed_pattern) (expr: Expr.expr)
                      : binding eff =
    mk_let_bindings_raw pat expr >>= fun binding ->
    return (BindLet binding)

  (* TODO: check if removing guard here is significantly faster *)
  let guard_assert (guard: Expr.expr) binding =
    match binding with
    | BindLet expr  ->
        BindLet (mk_implies guard expr)
    | BindAssume (loc, expr) ->
        BindAssume(loc, mk_implies guard expr)

  (* Quick hack to distinguish BMC_ASSUME *)

  (* SMT stuff *)
  let rec bind_pe (Pexpr(annots, bTy, pe_) as pexpr) : (binding list) eff =
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
    | PEctor (Carray, pes) ->
        (* Need to bind array values to constant symbol *)
        get_expr uid >>= fun z3_array_expr ->
        mapM (fun pe -> get_expr (get_id_pexpr pe)) pes >>= fun z3_pes ->

        assert (Z3Array.is_array z3_array_expr);
        let array_bindings = List.mapi (fun i expr ->
            BindLet (mk_eq (Z3Array.mk_select g_ctx z3_array_expr (int_to_z3 i)) expr)) z3_pes in
        mapM bind_pe pes >>= fun bound_pes ->
        return (array_bindings @ (List.concat bound_pes))
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
        let case_bindings = List.map2 guard_assert guards bindings in
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
    | PEstruct (_, pes) ->
        mapM bind_pe @@ List.map snd pes >>= fun bound_pes ->
        return (List.concat bound_pes)
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
    | PEare_compatible (pe1, pe2) ->
        bind_pe pe1 >>= fun bound_pe1 ->
        bind_pe pe2 >>= fun bound_pe2 ->
        return (bound_pe1 @ bound_pe2)
    | PEbmc_assume pe ->
        let loc = Annot.get_loc annots in
        (*assert (is_some loc);
        print_endline ((Location_ocaml.location_to_string (Option.get loc)));*)

        bind_pe pe >>= fun bound_pe ->
        (* TODO: move this to a separate phase for easier debugging *)
        get_expr (get_id_pexpr pe) >>= fun z3_pe ->
        return (BindAssume (loc, z3_pe) :: bound_pe)
    )

  let bind_create_helper uid =
      get_action uid >>= fun action ->
      let alloc_id = (
        match action with
        | ICreate(_,_,_,_, alloc_id) -> alloc_id
        | ICreateReadOnly(_,_,_,_, alloc_id,_) -> alloc_id
        | _ -> assert false
        ) in
      get_meta alloc_id >>= fun metadata ->
      let base_addr = get_metadata_base metadata in
      let max_addr =
        binop_to_z3 OpAdd (PointerSort.get_index_from_addr base_addr)
                          (int_to_z3 (get_metadata_size metadata)) in

      (* Assert alloc_size(alloc_id) = allocation_size *)
      (* TODO: why is this here and not later when dealing with memory?... *)
      return [BindLet (mk_eq (Expr.mk_app g_ctx PointerSort.alloc_min_decl
                                               [int_to_z3 alloc_id])
                      (PointerSort.get_index_from_addr base_addr))
             ;BindLet (mk_eq (Expr.mk_app g_ctx PointerSort.alloc_max_decl
                                       [int_to_z3 alloc_id])
                       max_addr)
             ]

  (* TODO TODO TODO TODO *)
  let bind_action (Paction(p, Action(loc, a, action_))) uid
                  : (binding list) eff =
   (match action_ with
    | Create (pe1, pe2, pref) ->
        bind_create_helper uid
    | CreateReadOnly _ ->
        bind_create_helper uid
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
        bind_pe pe1 >>= fun bound_pe1 ->
        bind_pe pe2 >>= fun bound_pe2 ->
        bind_pe pe3 >>= fun bound_pe3 ->
        bind_pe pe4 >>= fun bound_pe4 ->
        return (bound_pe1 @ bound_pe2 @ bound_pe3 @ bound_pe4)
    | Fence0 mo ->
        return []
    | CompareExchangeStrong(pe1, pe2, pe3, pe4, mo1, mo2) ->
        bind_pe pe1 >>= fun bound_pe1 ->
        bind_pe pe2 >>= fun bound_pe2 ->
        bind_pe pe3 >>= fun bound_pe3 ->
        bind_pe pe4 >>= fun bound_pe4 ->
        return (bound_pe1 @ bound_pe2 @ bound_pe3 @ bound_pe4)
    | CompareExchangeWeak(pe1, pe2, pe3, pe4, mo1, mo2) ->
        bind_pe pe1 >>= fun bound_pe1 ->
        bind_pe pe2 >>= fun bound_pe2 ->
        bind_pe pe3 >>= fun bound_pe3 ->
        bind_pe pe4 >>= fun bound_pe4 ->
        return (bound_pe1 @ bound_pe2 @ bound_pe3 @ bound_pe4)
    | LinuxFence mo ->
        return []
    | LinuxLoad (pe1, pe2, mo) ->
        bind_pe pe1 >>= fun bound_pe1 ->
        bind_pe pe2 >>= fun bound_pe2 ->
        return (bound_pe1 @ bound_pe2)
    | LinuxStore(pe1, pe2, pe3, mo) ->
        bind_pe pe1 >>= fun bound_pe1 ->
        bind_pe pe2 >>= fun bound_pe2 ->
        bind_pe pe3 >>= fun bound_pe3 ->
        return (bound_pe1 @ bound_pe2 @ bound_pe3)
    | LinuxRMW (pe1, pe2, pe3, mo) ->
        bind_pe pe1 >>= fun bound_pe1 ->
        bind_pe pe2 >>= fun bound_pe2 ->
        bind_pe pe3 >>= fun bound_pe3 ->
        return (bound_pe1 @ bound_pe2 @ bound_pe3)
    )

  let rec bind_e (Expr(annots, expr_) as expr: unit typed_expr)
                 : (binding list) eff =
    let uid = get_id_expr expr in
    (match expr_ with
    | Epure pe ->
        bind_pe pe
    | Ememop(PtrValidForDeref, args) (* fall through *)
    | Ememop(PtrEq, args)            (* fall through *)
    | Ememop(PtrNe, args)            (* fall through *)
    | Ememop(PtrLt, args)            (* fall through *)
    | Ememop(PtrGt, args)            (* fall through *)
    | Ememop(PtrLe, args)            (* fall through *)
    | Ememop(PtrGe, args)            (* fall through *)
    | Ememop(Ptrdiff, args)          (* fall through *)
    | Ememop(IntFromPtr, args)       (* fall through *)
    | Ememop(PtrFromInt, args)       (* fall through *)
    | Ememop(PtrWellAligned, args)   (* fall through *)
    | Ememop(PtrArrayShift,args) ->  (* fall through *)
        mapM bind_pe args >>= fun bound_args ->
        return (List.concat bound_args)
    | Ememop _ ->
        assert false
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
        let case_bindings = List.map2 guard_assert guards bindings in
        let guarded_bound_cases = List.concat (List.map2
          (fun guard case_binds -> List.map (guard_assert guard) case_binds)
          guards bound_cases) in
        return (bound_pe @ case_bindings @ guarded_bound_cases)
    | Elet (pat, pe, e) ->
        bind_pe pe >>= fun bound_pe ->
        bind_e   e >>= fun bound_e  ->

        get_expr (get_id_pexpr pe) >>= fun z3_pe ->
        mk_let_bindings pat z3_pe >>= fun let_binding ->
        return (let_binding :: bound_pe @ bound_e)
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
    | Eccall _ ->
        get_inline_expr uid >>= fun inlined_expr ->
        bind_e inlined_expr
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
        return (BindLet (List.fold_left mk_xor mk_false guards) :: guarded_asserts)
    | Esave _ ->
        get_inline_expr uid >>= fun inlined_expr ->
        bind_e inlined_expr
    | Erun _ ->
        get_inline_expr uid >>= fun inlined_expr ->
        bind_e inlined_expr
    | Epar es ->
        mapM bind_e es >>= fun bound_es ->
        return (List.concat bound_es)
    | Ewait _       -> assert false
    )

    let bind_globs(gname, glb) : (binding list) eff =
      match glb with
      | GlobalDef (_, e) ->
          bind_e e                 >>= fun bound_e ->
          get_expr (get_id_expr e) >>= fun z3d_e ->
          mk_let_binding (Some gname) z3d_e >>= fun let_binding ->
          return (BindLet let_binding :: bound_e)
      | GlobalDecl _ ->
          return []

    let bind_file (file: unit typed_file) (fn_to_check: sym_ty)
                  : (Expr.expr list * (Location_ocaml.t option * Expr.expr) list) eff =
      mapM bind_globs file.globs >>= fun bound_globs ->
      (match Pmap.lookup fn_to_check file.funs with
      | Some (Proc(annot, bTy, params, e)) ->
          bind_e e
      | Some (Fun(ty, params, pe)) ->
          bind_pe pe
      | _ -> assert false
      ) >>= fun bound_expr ->
      let all = List.concat bound_globs @ bound_expr in
      return (List.fold_left (fun (lets, assumes) binding ->
        match binding with
        | BindLet expr -> (expr::lets, assumes)
        | BindAssume (loc, expr) -> (lets, (loc,expr)::assumes)
      ) ([],[]) all)
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

  let guard_vc (guard: Expr.expr) ((vc_expr, dbg): bmc_vc) : bmc_vc =
    (mk_implies guard vc_expr, dbg)

  let map2_inner (f: 'x->'y->'z) (xs: 'x list) (yss: ('y list) list) : 'z list =
    List.concat (List.map2 (fun x ys -> List.map (f x) ys) xs yss)

  let rec vcs_pe (Pexpr (annots, bTy, pe_) as pexpr)
                 : (bmc_vc list) eff =
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
    | PEstruct (_, pes) ->
        mapM vcs_pe @@ List.map snd pes >>= fun vcs ->
        return (List.concat vcs)
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
                      : (bmc_vc list) eff =
    match action_ with
    | Create (align, Pexpr(_, BTy_ctype, PEval (Vctype ctype)), prefix) ->
        return []
    | Create _ -> assert false
    | CreateReadOnly (align, Pexpr(_, BTy_ctype, PEval (Vctype ctype)), initial_value, prefix) ->
        vcs_pe initial_value >>= fun vcs_initial_value ->
        return vcs_initial_value
    | CreateReadOnly _  -> assert false
    | Alloc0 _          -> assert false
    | Kill (_, pe) ->
        vcs_pe pe
    | Store0 (_, Pexpr(_,_,PEval (Vctype ty)),
                 (Pexpr(_,_,PEsym sym)), wval, memorder) ->
        (* TODO: Where should we check whether the ptr is valid? *)
        let valid_memorder =
          mk_bool (not (memorder = Acquire || memorder = Acq_rel)) in
        vcs_pe wval                     >>= fun vcs_wval ->
        lookup_sym sym                  >>= fun ptr_z3 ->
        return (  (valid_memorder, VcDebugStr (string_of_int uid ^ "_Store_memorder"))
                ::(PointerSort.valid_ptr ptr_z3,
                   VcDebugStr (string_of_int uid ^ "_Store_invalid_ptr"))
                ::(PointerSort.ptr_in_range ptr_z3,
                   VcDebugStr ("out of bounds pointer at memory store"))
                :: vcs_wval)
    | Store0 _          -> assert false
    | Load0 (Pexpr(_,_,PEval (Vctype ty)),
             (Pexpr(_,_,PEsym sym)), memorder) ->
        let valid_memorder =
              mk_bool (not (memorder = Release || memorder = Acq_rel)) in
        lookup_sym sym >>= fun ptr_z3 ->
        return [(valid_memorder, VcDebugStr (string_of_int uid ^ "_Load_memorder"))
               ;(PointerSort.valid_ptr ptr_z3,
                 VcDebugStr (string_of_int uid ^ "_Load_valid_ptr"))
               ;(PointerSort.ptr_in_range ptr_z3,
                   VcDebugStr ("out of bounds pointer at memory load"))
               ]
    | Load0 _ -> assert false
    | RMW0 _  -> assert false
    | Fence0 _ -> return []
    | CompareExchangeStrong (Pexpr(_,_,PEval (Vctype ty)),
                             Pexpr(_,_,PEsym obj),
                             Pexpr(_,_,PEsym expected),
                             desired, mo_success, mo_failure)  (* fall through *)
    | CompareExchangeWeak   (Pexpr(_,_,PEval (Vctype ty)),
                             Pexpr(_,_,PEsym obj),
                             Pexpr(_,_,PEsym expected),
                             desired, mo_success, mo_failure) ->
        assert (!!bmc_conf.concurrent_mode);
        assert_memory_mode_c ();
        (* Check valid memory orders:
         * mo_failure must not be RELEASE or ACQ_REL
         * mo_failure must be no stronger than mo_success
         *)
        let invalid_mo_failure =
          (mo_failure = Release || mo_failure = Acq_rel) in
        let mo_failure_stronger =
          (mo_failure = Seq_cst && mo_success <> Seq_cst) ||
          (mo_failure = Acquire && mo_success = Relaxed) in
        let valid_memorder =
          mk_bool (not (invalid_mo_failure || mo_failure_stronger)) in
        if invalid_mo_failure then
          bmc_debug_print 3
            "`failure' memory order of CompareExchange` must not be
             release or acq_rel"
        else if mo_failure_stronger then
          bmc_debug_print 3
            "'failure' memory order of CompareExchange' must not be
             stronger than the success argument"
        ;
        bmc_debug_print 7 "TODO: assert ptr validity for CompareXchg";
        return [(valid_memorder,
                 VcDebugStr(string_of_int uid ^ "_CompareExchange_memorder"))]
    | CompareExchangeStrong _ -> assert false
    | CompareExchangeWeak _ -> assert false
    | LinuxFence _ -> return []
    | LinuxStore (Pexpr(_,_,PEval (Vctype ty)),
                  (Pexpr(_,_,PEsym sym)), wval, memorder) ->
        assert_memory_mode_linux ();
        vcs_pe wval                     >>= fun vcs_wval ->
        lookup_sym sym                  >>= fun ptr_z3 ->

        bmc_debug_print 7 "TODO: VCs of LinuxStore. Check memory order";
        return ((PointerSort.valid_ptr ptr_z3,
                 VcDebugStr (string_of_int uid ^ "_Store_invalid_ptr"))
                ::(PointerSort.ptr_in_range ptr_z3,
                   VcDebugStr ("out of bounds pointer at memory store"))
                :: vcs_wval)
    | LinuxStore _ -> assert false
    | LinuxLoad (Pexpr(_,_,PEval (Vctype ty)),
                 (Pexpr(_,_,PEsym sym)), memorder) ->
        assert_memory_mode_linux ();
        lookup_sym sym >>= fun ptr_z3 ->
        return [(PointerSort.valid_ptr ptr_z3,
                 VcDebugStr (string_of_int uid ^ "_Load_valid_ptr"))
               ;PointerSort.ptr_in_range ptr_z3,
                   VcDebugStr ("out of bounds pointer at memory load")
               ]
    | LinuxLoad _  -> assert false
    | LinuxRMW (Pexpr(_,_,PEval (Vctype ty)), Pexpr(_,_,PEsym sym), wval, mo) ->
        assert (!!bmc_conf.concurrent_mode);
        assert_memory_mode_linux ();
        vcs_pe wval >>= fun vcs_wval ->
        lookup_sym sym >>= fun ptr_z3 ->
          return ((mk_and [PointerSort.valid_ptr ptr_z3;PointerSort.ptr_in_range ptr_z3],
                 VcDebugStr (string_of_int uid ^ "_RMW_invalid_ptr"))
                 :: vcs_wval)
    | LinuxRMW _ -> assert false

  let rec vcs_e (Expr(annots, expr_) as expr)
                   : (bmc_vc list) eff =
    let uid = get_id_expr expr in
    match expr_ with
    | Epure pe      -> vcs_pe pe
    | Ememop (Ptrdiff, [ctype;pe1;pe2]) ->
        assert (g_pnvi);
        vcs_pe pe1 >>= fun vcs_pe1 ->
        vcs_pe pe2 >>= fun vcs_pe2 ->

        get_expr (get_id_pexpr pe1) >>= fun z3_pe1 ->
        get_expr (get_id_pexpr pe2) >>= fun z3_pe2 ->

        let dbg_valid_ptr = VcDebugStr(string_of_int uid ^ "_Ptrdiff validity") in
        let valid_assert =
          mk_and [PointerSort.valid_ptr z3_pe1
                 ;PointerSort.valid_ptr z3_pe2
                 ;PointerSort.ptr_in_range_plus_one z3_pe1
                 ;PointerSort.ptr_in_range_plus_one z3_pe2
                 ;PointerSort.ptr_comparable z3_pe1 z3_pe2
                 ] in
        return ((valid_assert, dbg_valid_ptr)
                :: (vcs_pe1 @ vcs_pe2))
    | Ememop (PtrArrayShift,[ptr;ty;index]) ->
        assert (g_pnvi);
        (* TODO: do we need to check the resulting value? *)
        vcs_pe ptr >>= fun vcs_ptr ->
        vcs_pe ty  >>= fun vcs_ty ->
        vcs_pe index >>= fun vcs_index ->

        get_expr (get_id_pexpr ptr) >>= fun z3_ptr ->

        let dbg_valid_ptr = VcDebugStr(string_of_int uid ^ "_PtrArrayShift validity") in
        let valid_assert =
          mk_and [PointerSort.valid_ptr z3_ptr
                 ;PointerSort.ptr_in_range_plus_one z3_ptr
                 ] in

        get_expr uid >>= fun shifted_ptr ->
        let dbg_arith_in_range =
          VcDebugStr("the result of some pointer arithmetic operator was out of bound") in
        let in_range_assert =
          mk_and [PointerSort.valid_ptr shifted_ptr
                 ;PointerSort.ptr_in_range_plus_one shifted_ptr
                 ] in
        return ((valid_assert, dbg_valid_ptr)
                :: (in_range_assert, dbg_arith_in_range)
                :: (vcs_ptr @ vcs_ty @ vcs_index))
    | Ememop(IntFromPtr, [ctype_src;ctype_dst;ptr]) ->
        (* assert ptr is null or ptr is (prov,a) and
         * a is in value_range (ctype_int) *)
        vcs_pe ctype_src >>= fun vcs_ctype_src ->
        vcs_pe ctype_dst >>= fun vcs_ctype_dst ->
        vcs_pe ptr       >>= fun vcs_ptr ->

        let ctype = (match ctype_dst with
          | Pexpr(_, BTy_ctype, PEval (Vctype ctype)) -> ctype
          | _ -> assert false
          ) in
        get_expr (get_id_pexpr ptr) >>= fun z3d_ptr ->
        let ptr_addr = PointerSort.get_addr_index z3d_ptr in
        let min_value = Pmap.find ctype ImplFunctions.ivmin_map in
        let max_value = Pmap.find ctype ImplFunctions.ivmax_map in

        let dbg = VcDebugStr (string_of_int uid ^ "_IntFromPtr_invalid_cast") in
        return ((mk_or [PointerSort.is_null z3d_ptr
                      ;binop_to_z3 OpGe ptr_addr min_value
                      ;binop_to_z3 OpLe ptr_addr max_value
                      ], dbg) ::(vcs_ctype_src @ vcs_ctype_dst @ vcs_ptr))
    | Ememop (memop, pes) ->
        mapM vcs_pe pes >>= fun vcss_pes ->
        begin match memop with
        | PtrValidForDeref | PtrEq | PtrNe | PtrLt | PtrGt | PtrLe | PtrGe
        | PtrFromInt | PtrWellAligned -> return (List.concat vcss_pes)
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
    | Elet (pat, pe, e) ->
        vcs_pe pe >>= fun vcs_pe ->
        vcs_e   e >>= fun vcs_e  ->
        return (vcs_pe @ vcs_e)
    | Eif (cond, e1, e2) ->
        vcs_pe cond >>= fun vcs_cond ->
        vcs_e e1    >>= fun vcs_e1 ->
        vcs_e e2    >>= fun vcs_e2 ->
        get_expr (get_id_pexpr cond) >>= fun cond_z3 ->
        return (vcs_cond @ (List.map (guard_vc cond_z3) vcs_e1)
                         @ (List.map (guard_vc (mk_not cond_z3)) vcs_e2))
    | Eskip         -> return []
    | Eccall _      ->
        get_inline_expr uid >>= fun inline_expr ->
        vcs_e inline_expr
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
    | Epar es ->
        mapM vcs_e es >>= fun vcss_es ->
        return (List.concat vcss_es)
    | Ewait _       -> assert false

    let vcs_globs(_, glb) : (bmc_vc list) eff =
      match glb with
      | GlobalDef(_, e) -> vcs_e e
      | GlobalDecl _ -> return []

    let vcs_file (file: unit typed_file) (fn_to_check: sym_ty)
                  : (bmc_vc list) eff =
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

(* Return value *)
module BmcRet = struct

  type internal_state = {
    file            : unit typed_file;
    inline_expr_map : (int, unit typed_expr) Pmap.map;
    expr_map        : (int, Expr.expr) Pmap.map;
    case_guard_map  : (int, Expr.expr list) Pmap.map;
    drop_cont_map   : (int, Expr.expr) Pmap.map;

    (*ret_map  : (int, Expr.expr) Pmap.map;*)
    ret_val  : Expr.expr option;
  }

  include EffMonad(struct type state = internal_state end)

  let mk_initial file
                 inline_expr_map
                 expr_map
                 case_guard_map
                 drop_cont_map
                 : state =
  { file             = file;
    inline_expr_map  = inline_expr_map;
    expr_map         = expr_map;
    case_guard_map   = case_guard_map;
    drop_cont_map    = drop_cont_map;

    ret_val          = None;
  }

  (* Getters/setters *)
  let get_file : (unit typed_file) eff =
    get >>= fun st ->
    return st.file

  let get_inline_expr (uid: int): (unit typed_expr) eff =
    get >>= fun st ->
    match Pmap.lookup uid st.inline_expr_map with
    | None -> failwith (sprintf "Error: BmcRet inline_expr not found %d"
                                uid)
    | Some e -> return e

  let get_expr (uid: int): Expr.expr eff =
    get >>= fun st ->
    match Pmap.lookup uid st.expr_map with
    | None   -> failwith (sprintf "Error: BmcRet expr not found %d" uid)
    | Some e -> return e

  let get_case_guards (uid: int): (Expr.expr list) eff =
    get >>= fun st ->
    match Pmap.lookup uid st.case_guard_map with
    | None -> failwith (sprintf "Error: BmcRet case guard not found %d" uid)
    | Some es -> return es

  let get_drop_cont (uid: int) : Expr.expr eff =
    get >>= fun st ->
    match Pmap.lookup uid st.drop_cont_map with
    | None -> failwith (sprintf "Error BmcRet: uid %d not found in drop_cont_map" uid)
    | Some expr -> return expr

  let get_ret_const : Expr.expr eff =
    get >>= fun st ->
    assert (is_some st.ret_val);
    return (Option.get st.ret_val)

  let set_ret_const (expr: Expr.expr) : unit eff =
    get >>= fun st ->
    put {st with ret_val = Some expr}

  (* z3 stuff *)
  let rec do_e (Expr(annots, expr_) as expr)
              : (Expr.expr list) eff =
    let uid = get_id_expr expr in
    match expr_ with
    | Epure pe ->
        return []
    | Ememop (memop, pes) ->
        return []
    | Eaction paction ->
        return []
    | Ecase (pe, cases) ->
        mapM do_e (List.map snd cases) >>= fun ret_cases ->
        get_case_guards uid >>= fun guards ->
        let guard_cases guard = List.map (mk_implies guard) in
        return (List.concat (List.map2 guard_cases guards ret_cases))
    | Elet (pat, pe, e) ->
        do_e e
    | Eif (cond, e1, e2) ->
        do_e e1 >>= fun ret_e1 ->
        do_e e2 >>= fun ret_e2 ->

        get_case_guards uid >>= fun guards ->
        let (guard1, guard2) = (
          match guards with
          | [g1;g2] -> (g1,g2)
          | _ -> assert false) in

        return  ((List.map (mk_implies guard1) ret_e1)
                @(List.map (mk_implies guard2) ret_e2))
    | Eskip         ->
        return []
    | Eccall _ ->
        get_ret_const >>= fun old_ret ->

        get_expr uid  >>= fun ccall_ret_const ->
        set_ret_const ccall_ret_const >>

        get_inline_expr uid >>= fun inline_expr ->
        do_e inline_expr    >>= fun ret_expr ->

        set_ret_const old_ret >>
        return ret_expr
    | Eproc _       -> assert false
    | Eunseq elist ->
        mapM do_e elist >>= fun ret_elist ->
        return (List.concat ret_elist)
    | Ewseq (pat, e1, e2) (* fall through *)
    | Esseq (pat, e1, e2) ->
        do_e e1 >>= fun ret_e1 ->
        do_e e2 >>= fun ret_e2 ->

        get_drop_cont (get_id_expr e1) >>= fun e1_drop_cont ->
        let e2_guard = mk_not e1_drop_cont in
        return (ret_e1 @ (List.map (mk_implies e2_guard) ret_e2))
    | Easeq _       -> assert false
    | Eindet _      -> assert false
    | Ebound (_, e) ->
        do_e e
    | End es ->
        mapM do_e es >>= fun ret_es ->
        get_case_guards uid >>= fun guards ->
        let guard_cases guard = List.map (mk_implies guard) in
        return (List.concat (List.map2 guard_cases guards ret_es))
    | Esave _ ->
        get_inline_expr uid >>= fun inline_expr ->
        do_e inline_expr
    | Erun _ ->
        get_inline_expr uid >>= fun inline_expr ->
        do_e inline_expr    >>= fun ret_expr ->
        get_expr (get_id_expr inline_expr) >>= fun z3_expr ->
        get_ret_const       >>= fun ret_const ->
        return ((mk_eq ret_const z3_expr) :: ret_expr)
    | Epar es ->
        mapM do_e es >>= fun ret_es ->
        (* TODO: check this. Really want to assert can't jump out of par... *)
        return [mk_or (List.map mk_and ret_es)]
    | Ewait _       -> assert false

  let do_file (file: unit typed_file) (fn_to_check: sym_ty)
              : (Expr.expr * Expr.expr list) eff =
    (match Pmap.lookup fn_to_check file.funs with
    | Some (Proc(annot, bTy, params, e)) ->
        let uid = get_id_expr e in
        let expr = mk_fresh_const
            (sprintf "ret_%s{%d}" (symbol_to_string fn_to_check) uid)
            (cbt_to_z3 bTy file) in
        set_ret_const expr >>
        do_e e >>= fun bindings ->

        get_expr (get_id_expr e) >>= fun z3_e ->
        get_drop_cont (get_id_expr e) >>= fun e_drop_cont ->
        let guard = mk_not e_drop_cont in

        return (expr, (mk_implies guard (mk_eq expr z3_e)) :: bindings)
    | Some (Fun(ty, params, pe)) ->
        get_expr (get_id_pexpr pe) >>= fun z3_pe ->
        return (z3_pe, [])
    | _ -> assert false
    )

end

(* Common functions *)
module BmcMemCommon = struct
  (* TODO: move to separate file *)
  let mk_unspecified_expr (sort: Sort.sort)
                          (raw_ctype: ctype)
                          (file: unit typed_file)
                          : Expr.expr =
    let ctype = CtypeSort.mk_nonatomic_expr raw_ctype in
    let rec aux raw_ctype =
      match raw_ctype with
      | Core_ctype.Basic0 (Integer _) (* fall through *)
      | Pointer0 _ (* fall through *)
      | Array0 _ (* fall through *)
      | Struct0 _ ->
          let obj_sort = TODO_LoadedSort.extract_obj_sort sort in
          TODO_LoadedSort.mk_unspecified obj_sort ctype
      | Atomic0 ty' -> aux ty'
      | ty -> failwith
                (sprintf "TODO: ctype %s"
                         (pp_to_string (Pp_core_ctype.pp_ctype ty)))
    in aux raw_ctype
    (*if (Sort.equal (LoadedInteger.mk_sort) sort) then
      LoadedInteger.mk_unspecified ctype
    else if (Sort.equal (LoadedPointer.mk_sort) sort) then
      LoadedPointer.mk_unspecified ctype
    else if (Sort.equal (LoadedIntArray.mk_sort) sort) then
      LoadedIntArray.mk_unspecified ctype

    else if (Sort.equal (LoadedIntArrayArray.mk_sort) sort) then
      LoadedIntArrayArray.mk_unspecified ctype
    else begin
      *)
      (*
      begin
      (* TODO: Pretty bad... *)
      let ret = List.fold_left (fun acc (sym, memlist) ->
        if is_some acc then acc
        else begin
          let struct_sort = (struct_to_sort (sym, memlist) file) in
          let module LoadedStructSort = (val struct_sort : LoadedSortTy) in
          if (Sort.equal (LoadedStructSort.mk_sort) sort) then
            Some (LoadedStructSort.mk_unspecified ctype)
          else
            None
        end
      ) None (Pmap.bindings_list file.tagDefs) in
      assert (is_some ret);
      Option.get ret
    end*)

  let mk_initial_value (ctype: ctype) (const: string) =
    match ctype with
    | Void0 ->
        (UnitSort.mk_unit, [])
    | Basic0 (Integer ity) ->
        let const = mk_fresh_const name integer_sort in
        (const, assert_initial_range ctype const)
    | _ -> assert false

  let mk_initial_loaded_value (sort: Sort.sort) (name: string)
                              (ctype: ctype) (specified: bool)
                              (file: unit typed_file)
                              : Expr.expr * (Expr.expr list) =
    if specified then begin
      let (initial_value, assertions) = mk_initial_value ctype name in
      if Sort.equal (LoadedInteger.mk_sort) sort then
        (LoadedInteger.mk_specified initial_value, assertions)
      else
        failwith "TODO: initial values of non-basic types"
    end else
      (mk_unspecified_expr sort ctype file, [])

  (* ==== PNVI STUFF ==== *)
  let provenance_constraint (sym: Expr.expr)
                            ((ival,ctype) : Expr.expr * ctype)
                            : Expr.expr list =
    assert false

  (* Base address aligned: assert address is a multiple of alignment > 0*)
  let alignment_assertions ((alloc,metadata) )
                           : Expr.expr list =
      let base_addr = get_metadata_base metadata in
      let alignment = get_metadata_align metadata in
      let fresh_int = mk_fresh_const (sprintf "align_multiplier: %d" alloc)
                                     integer_sort in
      let align_assert =
        mk_eq (PointerSort.get_index_from_addr base_addr)
              (binop_to_z3 OpMul (int_to_z3 alignment) fresh_int) in
      [align_assert
      ;binop_to_z3 OpGt fresh_int (int_to_z3 0)] (* > 0 *)

    (* Address isn't too large *)
    let addr_lt_max_assertions ((alloc,metadata)) : Expr.expr =
      let base_addr = get_metadata_base metadata in
      let size = get_metadata_size metadata in
      let max_address =
        binop_to_z3 OpAdd (PointerSort.get_index_from_addr base_addr) (int_to_z3 size) in
      binop_to_z3 OpLt max_address (int_to_z3 g_max_addr)

    (* TODO: Ew quadratic *)
    (* [start_1, end_1), [start_2, end_2)
     *
     * Assert that
     * start_2 >= end_1 or
     * start_1 >= end_2
     *)
    let disjoint_assertions ((id1, meta1) : int * allocation_metadata)
                            ((id2, meta2) : int * allocation_metadata)
                            : Expr.expr list =
      if id1 = id2 then []
      else begin
        let start_1 = PointerSort.get_index_from_addr (get_metadata_base meta1) in
        let end_1   = binop_to_z3 OpAdd start_1
                                        (int_to_z3 (get_metadata_size meta1)) in
        let start_2 = PointerSort.get_index_from_addr (get_metadata_base meta2) in
        let end_2   = binop_to_z3 OpAdd start_2
                                        (int_to_z3 (get_metadata_size meta2)) in
        [mk_or [binop_to_z3 OpGe start_2 end_1
               ;binop_to_z3 OpGe start_1 end_2]
        ]
      end

    (* TODO: add provenance somewhere *)
    (* For each allocation, we need to assert
     * - The base addresses are correctly aligned
     * - Addresses < some max value
     * - the allocations are disjoint
     * - Somehow create a function expressing whether an address is valid for pointers
     * - TODO: track permission
     * - Eventually the provenance
     *)
    let metadata_assertions (data: (int * allocation_metadata) list)
                            : Expr.expr list =
      let alignment_asserts =
        List.concat (List.map alignment_assertions data) in
      let addr_lt_max_asserts = List.map addr_lt_max_assertions data in
      let disjoint_asserts = List.concat
        (List.map (fun (d1,d2) -> disjoint_assertions d1 d2)
                  (cartesian_product data data)) in
        (alignment_asserts @
         addr_lt_max_asserts @
         disjoint_asserts)


    (*TODO: this is probably the wrong place to do it *)
    (* Constrain provenances from cast_ival_to_ptrval *)
    let provenance_assertions ((sym,(ival, ctype)) : Expr.expr * (Expr.expr * ctype))
                              (data: (int, allocation_metadata) Pmap.map)
                              (file: unit typed_file)
                              : Expr.expr list =
      let ival_max =
        binop_to_z3 OpAdd ival (int_to_z3 ((PointerSort.type_size ctype file) - 1)) in
      let prov = PointerSort.get_provenance ival ival_max data in
      assert (is_some prov);
      [mk_eq sym (Option.get prov)]

    (* ===== REPR from PNVI ===== *)

    (*let int_exp x y =
      (float_of_int x) ** (float_of_int y) |> int_of_float
    (* Return an Ocaml list of expressions.
     *
     * Byte 0 refers to the lowest byte (little endian)
     *)
    let unsigned_repr (value: Expr.expr) (num_bytes: int)
                      : Expr.expr list =
      let mask = int_to_z3 256 in
      List.init num_bytes (fun i ->
        let shifted_right =
          binop_to_z3 OpDiv value (int_to_z3 (int_exp 2 (8*i))) in
        binop_to_z3 OpRem_f shifted_right mask
      )
    (*
     * If > 0 then just value
     * 2 ^ N - (-value)
     *)
    let twos_complement_repr (value: Expr.expr) (num_bytes: int)
                             : Expr.expr list =
      let max_value = int_exp 2 (8 * num_bytes) in
      let sub_value = binop_to_z3 OpAdd (int_to_z3 max_value) value in
      unsigned_repr sub_value num_bytes

    (* Return representation + Z3 assertions *)
    let repr_ity (value: Expr.expr) (ity: AilTypes.integerType)
                 (aid: int)
                 : Expr.expr * Expr.expr list =
      assert (Sort.equal (Expr.get_sort value) (LoadedInteger.mk_sort));
      let spec_value = LoadedInteger.get_specified_value value in
      let num_bytes = Option.get (ImplFunctions.sizeof_ity ity) in

      let bytes =
        if ImplFunctions.impl.impl_signed ity then
          twos_complement_repr spec_value num_bytes
        else
          unsigned_repr spec_value num_bytes in
      let new_array =
        PNVIByteArray.mk_const_s (sprintf "repr_int_%d_%d" aid num_bytes) in

      let spec_asserts = mk_and
        (List.mapi (fun i byte ->
          mk_eq (PNVIByteArray.mk_select new_array (int_to_z3 i))
                (PNVIByte.mk_byte (int_to_z3 0)
                                  (LoadedInteger.mk_specified byte )
                                  (IntOption.mk_none))
        ) bytes) in
      let unspec_asserts = mk_and
        (List.init num_bytes (fun i ->
            mk_eq (PNVIByteArray.mk_select new_array (int_to_z3 i))
                  PNVIByte.unspec_byte
        )) in

      (new_array,
       [mk_ite (LoadedInteger.is_specified value)
               spec_asserts
               unspec_asserts
       ])

    let repr_ptr (value: Expr.expr) (aid: int) =
      assert (Sort.equal (Expr.get_sort value) LoadedPointer.mk_sort);
      let ptr = LoadedPointer.get_specified_value value in
      let num_bytes = g_ptr_size in

      let ptr_addr = AddressSort.get_index (PointerSort.get_addr ptr) in

      let bytes = unsigned_repr ptr_addr num_bytes in
      let new_array =
        PNVIByteArray.mk_const_s (sprintf "repr_ptr_%d_%d" aid num_bytes) in
      let spec_asserts = mk_and
        (List.mapi (fun i byte ->
          mk_eq (PNVIByteArray.mk_select new_array (int_to_z3 i))
                (PNVIByte.mk_byte (PointerSort.get_prov ptr)
                                  (LoadedInteger.mk_specified byte)
                                  (IntOption.mk_some (int_to_z3 i))
                )
        ) bytes) in
      let null_asserts = mk_and
        (List.init num_bytes (fun i ->
          mk_eq (PNVIByteArray.mk_select new_array (int_to_z3 i))
                (PNVIByte.mk_byte (int_to_z3 0)
                                  (LoadedInteger.mk_specified (int_to_z3 0))
                                  (IntOption.mk_none)
                )
        )) in
      let unspec_asserts = mk_and
        (List.init num_bytes (fun i ->
            mk_eq (PNVIByteArray.mk_select new_array (int_to_z3 i))
                  PNVIByte.unspec_byte
        )) in
      (new_array,
       [mk_ite (LoadedPointer.is_specified value)
               (mk_ite (PointerSort.is_null ptr)
                       null_asserts
                       spec_asserts)
               unspec_asserts
       ])

    (* Value of sort loaded _*)
    let repr (value: Expr.expr) (ctype: ctype)
             (aid: int)
             : Expr.expr * Expr.expr list =
      match ctype with
      | Void0 -> assert false
      | Basic0 (Integer ity) ->
          repr_ity value ity aid
      | Pointer0 (_, _) ->
          repr_ptr value aid
      | Array0(cty, Some n) ->
          assert false
      | Atomic0 _ ->
          assert false (* Deal with this later *)
      | _ -> assert false


    let interpret_unsigned_ity (bytes: Expr.expr list) : Expr.expr =
      Arithmetic.mk_add g_ctx
        (List.mapi (fun i byte ->
          let factor = int_to_z3 (int_exp 2 (8*i)) in
          binop_to_z3 OpMul (PNVIByte.get_spec_value byte) factor
        ) bytes)

    let interpret_signed_ity (bytes: Expr.expr list) : Expr.expr =
      Arithmetic.mk_add g_ctx
        (List.mapi (fun i byte ->
          let factor = int_to_z3 (int_exp 2 (8*i)) in
          let spec_value = PNVIByte.get_spec_value byte in
          (* Special case for the last byte *)
          if i = List.length bytes - 1 then begin
            (* if byte >= 128 then it's negative; else it's just the value *)
            mk_ite (binop_to_z3 OpGe spec_value (int_to_z3 128))
                   (binop_to_z3 OpMul (binop_to_z3 OpSub spec_value (int_to_z3 256))
                                      factor)
                   (binop_to_z3 OpMul spec_value factor)
          end else begin
            binop_to_z3 OpMul spec_value factor
          end
        ) bytes)

    let abst (ctype: ctype) (bytes: Expr.expr list)
             : Expr.expr =
      match ctype with
      | Void0 -> assert false
      | Basic0 (Integer ity) ->
          assert (List.length bytes = Option.get (ImplFunctions.sizeof_ity ity));
          let interp =
            if ImplFunctions.impl.impl_signed ity then
              (* Interpret as two's complement *)
              interpret_signed_ity bytes
            else interpret_unsigned_ity bytes in
          (* If any byte is unspec then unspec; else interp *)
          mk_ite (mk_or (List.map PNVIByte.is_unspec bytes))
                 (LoadedInteger.mk_unspecified (CtypeSort.mk_expr ctype))
                 (LoadedInteger.mk_specified interp)
      | Pointer0 _ ->
          assert (List.length bytes = g_ptr_size);
          let interp_addr = interpret_unsigned_ity bytes in
          let interp_provenance =
            let appropriate_index =
              mk_and (List.mapi (fun i byte ->
                mk_eq (IntOption.mk_some (int_to_z3 i)) (PNVIByte.get_index byte)
              ) bytes) in
            let prov_candidate = PNVIByte.get_provenance (List.hd bytes) in
            (bmc_debug_print 7 "TODO: look up allocation";
             mk_ite appropriate_index
                    prov_candidate
                    (int_to_z3 0) (* TODO *)
            ) in
          mk_ite (mk_or (List.map PNVIByte.is_unspec bytes))
                 (LoadedPointer.mk_unspecified (CtypeSort.mk_expr ctype))
                 (LoadedPointer.mk_specified
                    (PointerSort.mk_ptr_from_int_addr interp_provenance interp_addr))
      | Array0 _ -> assert false
      | Atomic0 _ -> assert false
      | _ -> assert false
      *)

end

(* Sequential memory model; read from most recent write *)
module BmcSeqMem = struct

  module type SEQMEM = sig
    type addr
    type alloc_id = int
    type index = int
    type memory_table = (addr, Expr.expr) Pmap.map
    type addr_set = addr Pset.set

    val addr_cmp : addr -> addr -> int
    (*val mk_addr : alloc_id -> index -> addr*)

    val empty_memory : memory_table
    val print_memory : memory_table -> unit
    val print_addr : addr -> string

    val update_memory : addr -> Expr.expr -> memory_table -> memory_table

    val merge_memory : memory_table -> addr_set ->
                       memory_table list -> Expr.expr list -> memory_table

    val mk_addr_expr : addr -> Expr.expr
    (* TODO: gross hack *)
    val mk_shift : alloc_id -> index -> Expr.expr -> addr

    val metadata_assertions :
          (int * allocation_metadata) list -> Expr.expr list

    val provenance_assertions :
          (Expr.expr * (Expr.expr * ctype)) list ->
          (int, allocation_metadata) Pmap.map ->
          unit typed_file ->
          Expr.expr list
  end

  module MemConcrete : SEQMEM = struct
    type addr = addr_ty
    type alloc_id = int
    type index = int
    type memory_table = (addr, Expr.expr) Pmap.map
    type addr_set = addr Pset.set

    let addr_cmp = Pervasives.compare

    let mk_addr (alloc: alloc_id) (index: index) =
      (alloc, index)

    let empty_memory = Pmap.empty addr_cmp

    let print_memory (table: memory_table): unit =
      Pmap.iter (fun (x,y) expr ->
          printf "(%d,%d) %s\n" x y (Expr.to_string expr)
      ) table

    let print_addr ((x,y): addr) =
      sprintf "(%d,%d)" x y

    let update_memory (addr: addr) (expr: Expr.expr) (table: memory_table)
                      : memory_table =
      Pmap.add addr expr table

    (* For each modified address, update base memory using tables
     * guarded by guards. *)
    let merge_memory (base     : memory_table)
                     (mod_addr : addr_set)
                     (tables   : memory_table list)
                     (guards   : Expr.expr list) =
      let guarded_tables : (memory_table * Expr.expr) list =
        List.combine tables guards in
      Pset.fold (fun ((alloc_id, i) as addr) acc ->
        let expr_base =
          match Pmap.lookup addr acc with
          | None ->
              let (table, guard) = List.find
                  (fun (table, _) -> is_some (Pmap.lookup addr table))
                  guarded_tables in
              let sort =
                match Pmap.lookup addr table with
                | None -> assert false
                | Some expr -> Expr.get_sort expr
              in
              mk_fresh_const (sprintf "merge_(%d %d)" alloc_id i) sort
          | Some expr_base ->
              expr_base
          in
        let new_expr =
          List.fold_right (fun (table, guard) acc_expr ->
              match Pmap.lookup addr table with
              | None      -> acc_expr
              | Some expr -> mk_ite guard expr acc_expr
          ) guarded_tables expr_base in
          (* TODO: create new seq variable? *)
          Pmap.add addr new_expr acc
      ) mod_addr base

    (* TODO: concrete only *)
    let mk_addr_expr (addr: addr) =
      PointerSort.mk_from_alloc_index addr

    let mk_shift (alloc: alloc_id) (index: index) (_: Expr.expr) =
      (alloc, index)

    let metadata_assertions = fun _ -> []

    let provenance_assertions = fun _ _ _ -> []
  end

  module MemPNVI : SEQMEM = struct
    type alloc_id = int
    type addr = Expr.expr (* addr is really just a range of addresses *)
    type index = int
    (* memory_table as an alloc_id/address range? alloc_id
     * associated with address range *)
    type memory_table = (addr, Expr.expr) Pmap.map
    type addr_set = addr Pset.set

    let addr_cmp = Pervasives.compare (*Expr.compare*)

    (*let mk_addr (alloc: alloc_id) (index: index) =
      AddressSort.mk_from_addr (alloc, index)*)

    let empty_memory = Pmap.empty addr_cmp

    let print_addr (addr: addr) =
      Expr.to_string addr

    let print_memory (table: memory_table): unit =
      Pmap.iter (fun addr expr ->
          printf "%s %s\n" (print_addr addr) (Expr.to_string expr)
      ) table

    let update_memory (addr: addr) (expr: Expr.expr) (table: memory_table)
                      : memory_table =
      Pmap.add addr expr table

    (* For each modified address, update base memory using tables
     * guarded by guards. *)
    let merge_memory (base     : memory_table)
                     (mod_addr : addr_set)
                     (tables   : memory_table list)
                     (guards   : Expr.expr list) =
      let guarded_tables : (memory_table * Expr.expr) list =
        List.combine tables guards in
      Pset.fold (fun addr acc ->
        let expr_base =
          match Pmap.lookup addr acc with
          | None ->
              let (table, guard) = List.find
                  (fun (table, _) -> is_some (Pmap.lookup addr table))
                  guarded_tables in
              let sort =
                match Pmap.lookup addr table with
                | None -> assert false
                | Some expr -> Expr.get_sort expr
              in
              mk_fresh_const (sprintf "merge_%s" (print_addr addr)) sort
          | Some expr_base ->
              expr_base
          in
        let new_expr =
          List.fold_right (fun (table, guard) acc_expr ->
              match Pmap.lookup addr table with
              | None      -> acc_expr
              | Some expr -> mk_ite guard expr acc_expr
          ) guarded_tables expr_base in
          (* TODO: create new seq variable? *)
          Pmap.add addr new_expr acc
      ) mod_addr base

    let mk_addr_expr (addr: addr) =
      addr

    let mk_shift (_: alloc_id) (index: index) (addr: Expr.expr) =
      PointerSort.shift_index_by_n addr (int_to_z3 index)

    let metadata_assertions (data: (int * allocation_metadata) list)
                            : Expr.expr list =
      BmcMemCommon.metadata_assertions data

    let provenance_assertions (provsyms : (Expr.expr * (Expr.expr * ctype)) list)
                              (data: (int , allocation_metadata) Pmap.map)
                              (file: unit typed_file)
                              : Expr.expr list =
      List.concat (List.map
          (fun x -> BmcMemCommon.provenance_assertions x data file)
          provsyms)
  end

  (*module MemPNVIBytes = struct
    type alloc_id = int
    type addr = Expr.expr (* addr is really just a range of addresses *)
    type mem_domain  = alloc_id
    type index = int

    (* allocation id -> array of btyes *)
    type memory_table = (mem_domain, Expr.expr) Pmap.map
    type addr_set = alloc_id Pset.set

    let addr_cmp = Pervasives.compare (*Expr.compare*)

    (*let mk_addr (alloc: alloc_id) (index: index) =
      AddressSort.mk_from_addr (alloc, index)*)

    let empty_memory = Pmap.empty addr_cmp

    (* TODO: misnomer *)
    let print_addr (alloc: alloc_id) =
      string_of_int alloc
      (*Expr.to_string addr*)

    let print_memory (table: memory_table): unit =
      Pmap.iter (fun alloc expr ->
          printf "%d %s\n" alloc (Expr.to_string expr)
      ) table

    let update_memory (alloc: alloc_id) (expr: Expr.expr) (table: memory_table)
                      : memory_table =
      Pmap.add alloc expr table

    (* For each modified address, update base memory using tables
     * guarded by guards. *)
    let merge_memory (base     : memory_table)
                     (mod_alloc : addr_set)
                     (tables   : memory_table list)
                     (guards   : Expr.expr list) =
      let guarded_tables : (memory_table * Expr.expr) list =
        List.combine tables guards in
      Pset.fold (fun alloc acc ->
        let expr_base =
          match Pmap.lookup alloc acc with
          | None ->
              let (table, guard) = List.find
                  (fun (table, _) -> is_some (Pmap.lookup alloc table))
                  guarded_tables in
              let sort =
                match Pmap.lookup alloc table with
                | None -> assert false
                | Some expr -> Expr.get_sort expr
              in
              mk_fresh_const (sprintf "merge_%d" alloc) sort
          | Some expr_base ->
              expr_base
          in
        let new_expr =
          List.fold_right (fun (table, guard) acc_expr ->
              match Pmap.lookup alloc table with
              | None      -> acc_expr
              | Some expr -> mk_ite guard expr acc_expr
          ) guarded_tables expr_base in
          (* TODO: create new seq variable? *)
          Pmap.add alloc new_expr acc
      ) mod_alloc base

    (* TODO: concrete only *)
    let mk_addr_expr (addr: addr) =
      assert false
      (*addr*)

    let mk_shift (_: alloc_id) (index: index) (addr: Expr.expr) =
      AddressSort.shift_index_by_n addr (int_to_z3 index)

    let metadata_assertions (data: (int * allocation_metadata) list)
                            : Expr.expr list =
      BmcMemCommon.metadata_assertions data

    let provenance_assertions (provsyms : (Expr.expr * (Expr.expr * ctype)) list)
                              (data: (int , allocation_metadata) Pmap.map)
                              : Expr.expr list =
      List.concat (List.map
          (fun x -> BmcMemCommon.provenance_assertions x data)
          provsyms)
  end
  *)

  (*module SeqMem = MemConcrete*)
  module SeqMem = MemConcrete

  type seq_state = {
    file             : unit typed_file;
    inline_expr_map  : (int, unit typed_expr) Pmap.map;
    sym_expr_table   : (sym_ty, Expr.expr) Pmap.map;
    expr_map         : (int, Expr.expr) Pmap.map;
    action_map       : (int, BmcZ3.intermediate_action) Pmap.map;
    param_actions    : (BmcZ3.intermediate_action option) list;
    case_guard_map   : (int, Expr.expr list) Pmap.map;
    drop_cont_map    : (int, Expr.expr) Pmap.map;
    alloc_meta_map   : (int, allocation_metadata) Pmap.map;
    prov_syms        : (Expr.expr * (Expr.expr * ctype)) list;

    memory           : SeqMem.memory_table;
  }

  include EffMonad(struct type state = seq_state end)

  let mk_initial file
                 inline_expr_map
                 sym_expr_table
                 expr_map
                 action_map
                 param_actions
                 case_guard_map
                 drop_cont_map
                 alloc_meta
                 prov_syms
                 : state =
  { file             = file;
    inline_expr_map  = inline_expr_map;
    sym_expr_table   = sym_expr_table;
    expr_map         = expr_map;
    action_map       = action_map;
    param_actions    = param_actions;
    case_guard_map   = case_guard_map;
    drop_cont_map    = drop_cont_map;
    alloc_meta_map   = alloc_meta;
    prov_syms        = prov_syms;

    memory           = SeqMem.empty_memory;
  }

  (* TODO: use Set.Make *)
  module AddrSet = struct
      type t = SeqMem.addr_set

      let cmp = SeqMem.addr_cmp
      let empty = Pset.empty cmp
      let of_list = Pset.from_list cmp
      let union s1 s2 = Pset.union s1 s2
      let fold = Pset.fold

      let pp s = Pset.fold (fun addr acc ->
        sprintf "%s %s" (SeqMem.print_addr addr) acc) s ""
  end

  let get_file : (unit typed_file) eff =
    get >>= fun st ->
    return st.file

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

  let get_sym_expr (sym: sym_ty) : Expr.expr eff =
    get >>= fun st ->
    match Pmap.lookup sym st.sym_expr_table with
    | None -> failwith (sprintf "Error: BmcSeqMem sym_expr %s not found"
                                (symbol_to_string sym))
    | Some e -> return e

  let get_action (uid: int) : BmcZ3.intermediate_action eff =
    get >>= fun st ->
    match Pmap.lookup uid st.action_map with
    | None -> failwith (sprintf "Error: BmcSeqMem action not found %d" uid)
    | Some a -> return a

  let get_param_actions : (BmcZ3.intermediate_action option) list eff =
    get >>= fun st ->
    return st.param_actions

  let get_case_guards (uid: int): (Expr.expr list) eff =
    get >>= fun st ->
    match Pmap.lookup uid st.case_guard_map with
    | None -> failwith (sprintf "Error: BmcSeqMem case guard not found %d" uid)
    | Some es -> return es

  let get_drop_cont (uid: int) : Expr.expr eff =
    get >>= fun st ->
    match Pmap.lookup uid st.drop_cont_map with
    | None -> failwith (sprintf "BmcSeqMem: Uid %d not found in drop_cont_map"                                 uid)
    | Some expr -> return expr

  let get_meta (alloc_id: int) : allocation_metadata eff =
    get >>= fun st ->
    match Pmap.lookup alloc_id st.alloc_meta_map with
    | None -> failwith (sprintf "BmcSeqMem: alloc id %d not found in alloc_meta"
                                alloc_id)
    | Some data -> return data

  let get_meta_map : (int, allocation_metadata) Pmap.map eff =
    get >>= fun st ->
    return st.alloc_meta_map

  let get_prov_syms : (Expr.expr * (Expr.expr * ctype)) list eff =
    get >>= fun st ->
    return st.prov_syms

  let get_memory : SeqMem.memory_table eff =
   get >>= fun st ->
   return st.memory

  let update_memory (addr: SeqMem.addr) (expr: Expr.expr) : unit eff =
    get >>= fun st ->
    put {st with memory = SeqMem.update_memory addr expr st.memory}

  let update_memory_table (memory: SeqMem.memory_table) : unit eff =
    get >>= fun st ->
    put {st with memory = memory}

  let print_memory : unit eff =
    get_memory >>= fun memory ->
    return (SeqMem.print_memory memory)

  type ret_ty = {
    bindings : Expr.expr list;
    mod_addr : SeqMem.addr_set;
  }

  let get_bindings (ret: ret_ty) : Expr.expr list =
    ret.bindings

  let empty_ret = { bindings = []; mod_addr = Pset.empty SeqMem.addr_cmp }
  let mk_ret bindings mod_addr =
    { bindings = bindings
    ; mod_addr = mod_addr
    }

  (* Address ranges of the base type? *)
  (*let do_create_pnvi_bytes
                (aid: aid)
                (ctype: ctype)
                (*(sortlist: BmcZ3.ctype_sort list)*)
                (alloc_id: BmcZ3.alloc)
                (initialise: bool)
                : ret_ty eff =
    (* Get metadata *)
    get_meta alloc_id >>= fun metadata ->
    (*let base_addr = get_metadata_base metadata in*)
    let (initial_value, assumptions) =
      BmcMemCommon.mk_initial_loaded_value
        (ctype_to_z3_sort ctype) (sprintf "init_%d" alloc_id)
        ctype initialise in
    (* TODO: Do this directly *)
    let (expr, assertions) =
      BmcMemCommon.repr initial_value ctype aid in

    update_memory alloc_id expr >>
    return { bindings = assertions @ assumptions
           ; mod_addr = AddrSet.of_list [alloc_id]
           }
  *)

  let do_create (*(aid: aid)*)
                (ctype: ctype)
                (sortlist: BmcZ3.ctype_sort list)
                (alloc_id: BmcZ3.alloc)
                (initialise: bool)
                : ret_ty eff =
    (* Get base address, shift by size of ctype *)

    get_meta alloc_id >>= fun metadata ->
    get_file >>= fun file ->
    let base_addr = get_metadata_base metadata in
    mapMi (fun i (ctype,sort) ->
      let index = List.fold_left
          (fun acc (ty, _) -> acc + (PointerSort.type_size ty file))
          0 (list_take i sortlist) in
      let addr = SeqMem.mk_shift alloc_id index base_addr in

      (*let addr = SeqMem.mk_addr alloc_id index in*)
      let seq_var =
        mk_fresh_const (sprintf "store_(%d %d)" alloc_id index) sort in
      update_memory addr seq_var >>
      let (initial_value, assumptions) =
        BmcMemCommon.mk_initial_loaded_value
            sort (sprintf "init_%d,%d" alloc_id i)
            ctype initialise file in
      let binding = mk_eq seq_var initial_value in
      return (addr, binding::assumptions)
    ) sortlist >>= fun retlist ->
    return { bindings = (List.concat (List.map snd retlist))
           ; mod_addr = AddrSet.of_list (List.map fst retlist)
           }

  (* TODO: mod_addr *)
  let do_paction (Paction(p, Action(loc, a, action_)) : unit typed_paction)
                 uid
                 : ret_ty eff =
    get_action uid >>= fun action ->
    match action with
    | ICreate(_, ctype, _, sortlist, alloc_id) ->
        do_create ctype sortlist alloc_id false
    | ICreateReadOnly _ ->
        failwith "TODO: CreateReadOnly in sequential mode"
    | IKill(_) ->
        failwith "TODO: implement Kills in sequential mode"
        (*return empty_ret*)
    | ILoad(_, ctype, type_list, ptr, rval, mo) ->
        assert (List.length type_list = 1);

        (*get_memory >>= fun memory ->

        let ptr_addr = PointerSort.get_addr ptr in
        let ptr_not_null = mk_not (PointerSort.is_null ptr) in
        let size = AddressSort.type_size ctype in
        bmc_debug_print 7 "TODO: Check addr range ";

        mapM (fun (alloc_id, expr_in_memory) ->
          get_meta alloc_id >>= fun metadata ->
          let base_addr = get_metadata_base metadata in

          let diff =
            binop_to_z3 OpSub (AddressSort.get_index ptr_addr)
                              (AddressSort.get_index base_addr) in
          let bytes = List.init size (fun i ->
              let index = binop_to_z3 OpAdd diff (int_to_z3 i) in
              PNVIByteArray.mk_select expr_in_memory index
            ) in
          let value = BmcMemCommon.abst ctype bytes in
          bmc_debug_print 7 "TODO: Check addr range ";
          let addr_guard =
            mk_and [ ptr_not_null
                   ; AddressSort.valid_index_range (int_to_z3 alloc_id)
                                                   ptr_addr
                     (* TODO: check max is in range *)
                   ] in
          let impl_expr = mk_implies addr_guard (mk_eq rval value) in
          return (Some (impl_expr, addr_guard))
        ) (Pmap.bindings_list memory) >>= fun retlist ->
        let filtered = List.map Option.get (List.filter is_some retlist) in
        (* TODO: should mk_or (List.map snd filtered be a vc? *)
        return { bindings = (mk_or (List.map snd filtered))::
                            (List.map fst filtered)
               ; mod_addr = AddrSet.empty
               }
        *)

        let (_, sort) = List.hd type_list in
        get_memory >>= fun possible_addresses ->
        mapM (fun (addr, expr_in_memory) ->
          let addr_sort = Expr.get_sort expr_in_memory in
          if (Sort.equal sort addr_sort) then
            let addr_expr = SeqMem.mk_addr_expr addr in
            let addr_eq =
              mk_and [mk_not (PointerSort.is_null ptr)
                     ;mk_eq addr_expr (PointerSort.get_addr ptr)] in
            let impl_expr = mk_implies addr_eq (mk_eq rval expr_in_memory) in
            return (Some (impl_expr, addr_eq))
          else
            return None
        ) (Pmap.bindings_list possible_addresses) >>= fun retlist ->
        let filtered = List.map Option.get (List.filter is_some retlist) in
        (* TODO: should mk_or (List.map snd filtered be a vc? *)
        return { bindings = (mk_or (List.map snd filtered))::
                            (List.map fst filtered)
               ; mod_addr = AddrSet.empty
               }
    | IStore(aid, ctype, type_list, ptr, wval, mo) ->
        failwith "TODO: sequential mode"
        (*get_memory >>= fun memory ->
        let ptr_addr = PointerSort.get_addr ptr in
        let ptr_not_null = mk_not (PointerSort.is_null ptr) in
        let size = AddressSort.type_size ctype in

        (* Get representation of wval *)
        let (wval_repr, assertions) = BmcMemCommon.repr wval ctype aid in

        bmc_debug_print 7 "TODO: Check addr range ";
        mapM (fun (alloc_id, expr_in_memory) ->
          get_meta alloc_id >>= fun metadata ->
          let base_addr = get_metadata_base metadata in
          let diff =
            binop_to_z3 OpSub (AddressSort.get_index ptr_addr)
                              (AddressSort.get_index base_addr) in
          (* The new value is the old value except with indexed bytes set *)
          let addr_guard =
            mk_and [ptr_not_null
                   ;AddressSort.valid_index_range (int_to_z3 alloc_id)
                                                  ptr_addr
                   ] in
          (* TODO TODO *)
          let new_seq_var =
            mk_fresh_const (sprintf "store_%s" (Expr.to_string ptr_addr))
                           (PNVIByteArray.mk_sort) in
          let new_val = mk_eq new_seq_var wval_repr in
          let old_val = mk_eq new_seq_var expr_in_memory in
          update_memory alloc_id new_seq_var >>
          return (Some (alloc_id, mk_ite addr_guard new_val old_val))
        ) (Pmap.bindings_list memory) >>= fun update_list ->
        let filtered = List.map Option.get (List.filter is_some update_list) in
        assert (List.length filtered > 0);
        return { bindings = assertions @(List.map snd filtered)
               ; mod_addr = AddrSet.of_list (List.map fst filtered)
               }
        *)
          (*mapMi (fun i (ctype, sort) ->
          let indexed_wval = get_ith_in_loaded i wval in
          get_memory >>= fun possible_addresses ->
          get_file >>= fun file ->

          let index = List.fold_left
              (fun acc (ty, _) -> acc + (PointerSort.type_size ctype file))
              0 (list_take i type_list) in
          let target_addr =
            PointerSort.shift_index_by_n (PointerSort.get_addr ptr)
                                         (int_to_z3 index) in
          (*let target_addr =
              AddressSort.shift_index_by_n
                        (PointerSort.get_addr ptr) (int_to_z3 i) in*)
          mapM (fun (addr, expr_in_memory) ->
            let addr_sort = Expr.get_sort expr_in_memory in
            if (Sort.equal sort addr_sort) then
              let addr_expr = SeqMem.mk_addr_expr addr in

              let new_seq_var =
                mk_fresh_const (sprintf "store_%s" (Expr.to_string addr_expr)) sort
              in
              (* new_seq_var is equal to to_store if addr_eq, else old value *)
                        let addr_eq =
                mk_and [ mk_not (PointerSort.is_null ptr)
                       ; mk_eq target_addr addr_expr] in
              (* Write ith element of wval *)
              let new_val = mk_eq new_seq_var indexed_wval in
              let old_val = mk_eq new_seq_var expr_in_memory in
              update_memory addr new_seq_var >>
              return (Some (addr, mk_ite addr_eq new_val old_val))
            else
              return None
          ) (Pmap.bindings_list possible_addresses)
        ) type_list >>= fun update_list_list ->
        let update_list = List.concat update_list_list in
        let filtered = List.map Option.get (List.filter is_some update_list) in
        assert (List.length filtered > 0);
        return { bindings = List.map snd filtered
               ; mod_addr = AddrSet.of_list (List.map fst filtered)
               }
        *)
    | ICompareExchangeStrong _ ->
        failwith "Error: CompareExchangeStrong only supported with --bmc_conc"
    | ICompareExchangeWeak _ ->
        failwith "Error: CompareExchangeWeak only supported with --bmc_conc"
    | IMemop(_) ->
        failwith "TODO: implement Memop in sequential mode"
    | IFence (aid, mo) ->
       assert false
    | ILinuxLoad(aid, _, type_list, ptr, rval, mo) ->
       assert false
    | ILinuxStore(aid, _, type_list, ptr, wval, mo) ->
       assert false
    | ILinuxRmw _->
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
          SeqMem.merge_memory old_memory mod_addr
                              (List.map fst res_cases) guards in
        update_memory_table new_memory >>

        let guarded_asserts = List.concat (List.map2
          (fun guard res -> List.map (guard_assert guard) res.bindings)
          guards retlist) in
        return { bindings = guarded_asserts
               ; mod_addr = mod_addr}
    | Elet (pat, pe, e) ->
        do_e e
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
        let new_memory =
          SeqMem.merge_memory old_memory mod_addr
                              [mem_e1; mem_e2] [guard1; guard2] in
        update_memory_table new_memory >>
        return { bindings = (List.map (guard_assert guard1) res_e1.bindings)
                           @(List.map (guard_assert guard2) res_e2.bindings)
               ; mod_addr = mod_addr
               }
    | Eskip         -> return empty_ret
    | Eccall _      ->
        get_inline_expr uid >>= fun inline_expr ->
        do_e inline_expr
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
        let new_memory =
          SeqMem.merge_memory old_memory mod_addr
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
    | Epar es ->
        failwith "Error: Epar in sequentialised; concurrent mode only"
    | Ewait _       -> assert false

  let do_globs (gname, glb) =
    match glb with
    | GlobalDef(bty, e) -> do_e e
    | GlobalDecl _ -> return empty_ret

  (* Initialize value of argument to something specified in valid range *)
  let initialise_param ((sym,cbt): (sym_ty * core_base_type))
                       (action_opt: BmcZ3.intermediate_action option)
                       : ret_ty eff =
    match action_opt with
    | None ->
        (* Param is not a pointer; nothing to be done *)
        assert (not (is_core_ptr_bty cbt));
        return empty_ret
    | Some (ICreate(_, ctype, _, sortlist, alloc_id)) ->
        do_create (*aid*) ctype sortlist alloc_id true >>= fun ret ->
        (* Make let binding *)
        get_sym_expr sym >>= fun sym_expr ->
        let eq_expr =
          mk_eq sym_expr
                (PointerSort.mk_ptr (int_to_z3 alloc_id)
                                    (PointerSort.mk_from_alloc_index (alloc_id, 0))) in
        (* TODO: need extra assertions for arrays/pointers *)
        return { bindings = eq_expr :: ret.bindings
               ; mod_addr = ret.mod_addr
               }
    | _ ->
        assert false

  let initialise_params (params: ((sym_ty * core_base_type) list))
                        (fn_to_check: sym_ty)
                        : ret_ty eff =
    get_param_actions >>= fun param_actions ->
    mapM2 initialise_param params param_actions >>= fun rets ->
    return (List.fold_left (fun acc ret ->
      { bindings = ret.bindings @ acc.bindings
      ; mod_addr = AddrSet.union ret.mod_addr acc.mod_addr
      }) empty_ret rets)

  let do_file (file: unit typed_file) (fn_to_check: sym_ty)
              : (Expr.expr list) eff =
    mapM do_globs file.globs >>= fun globs ->
    (match Pmap.lookup fn_to_check file.funs with
     | Some (Proc (annot, bTy, params, e)) ->
        initialise_params params fn_to_check >>= fun ret_params ->
        do_e e >>= fun ret_e ->
        return { bindings = ret_params.bindings @ ret_e.bindings
               ; mod_addr = AddrSet.union ret_params.mod_addr ret_e.mod_addr
               }
     | Some (Fun(ty, params, pe)) ->
        return empty_ret
     | _ -> assert false
    ) >>= fun ret ->
    get_meta_map >>= fun metadata ->
    get_prov_syms >>= fun prov_syms ->
    let metadata_list = Pmap.bindings_list metadata in
    let meta_asserts = SeqMem.metadata_assertions metadata_list in
    let provenance_asserts =
      SeqMem.provenance_assertions prov_syms metadata file in
    return (provenance_asserts @ meta_asserts @ ret.bindings @ (List.concat (List.map get_bindings globs)))
end

(* Concurrency
 *
 * Compute all actions
 *
 * Preexecution:
 * - sb/po
 * - asw
 * - dd
 *)
module BmcConcActions = struct

  type internal_state = {
    file             : unit typed_file;
    inline_pexpr_map : (int, typed_pexpr) Pmap.map;
    inline_expr_map  : (int, unit typed_expr) Pmap.map;
    sym_expr_table   : (sym_ty, Expr.expr) Pmap.map;
    action_map       : (int, BmcZ3.intermediate_action) Pmap.map;
    param_actions    : (BmcZ3.intermediate_action option) list;
    case_guard_map   : (int, Expr.expr list) Pmap.map;
    drop_cont_map    : (int, Expr.expr) Pmap.map;

    alloc_meta_map  : (int, allocation_metadata) Pmap.map;
    prov_syms       : (Expr.expr * (Expr.expr * ctype)) list;

    bmc_actions    : (int, aid list) Pmap.map;
    bmc_action_map : (aid, bmc_action) Pmap.map;
    tid            : tid;
    tid_supply     : tid;
    parent_tids    : (tid, tid) Pmap.map;
    assertions     : Expr.expr list;
    read_only_allocs : int list;

    mem_module     : (module MemoryModel);

    taint_table    : (sym_ty, aid Pset.set) Pmap.map;
  }

  include EffMonad(struct type state = internal_state end)

  (* TODO: the sort of Loaded needs to include struct stuff *)
  let mk_memory_module (file: unit typed_file) =
    if !!bmc_conf.parse_from_model then
      let cat_model = Bmc_cat.CatParser.load_file !!bmc_conf.model_file in
      (module GenericModel (val cat_model) : MemoryModel)
    else
      (module RC11MemoryModel : MemoryModel)

  let get_memory_module =
    get >>= fun st ->
    return st.mem_module

  let mk_initial file
                 inline_pexpr_map
                 inline_expr_map
                 sym_expr_table
                 action_map
                 param_actions
                 case_guard_map
                 drop_cont_map
                 alloc_meta_map
                 prov_syms
                 : internal_state =

  { file             = file;
    inline_pexpr_map = inline_pexpr_map;
    inline_expr_map  = inline_expr_map;
    sym_expr_table   = sym_expr_table;
    action_map       = action_map;
    param_actions    = param_actions;
    case_guard_map   = case_guard_map;
    drop_cont_map    = drop_cont_map;
    alloc_meta_map   = alloc_meta_map;
    prov_syms        = prov_syms;

    bmc_actions      = Pmap.empty Pervasives.compare;
    bmc_action_map   = Pmap.empty Pervasives.compare;
    tid              = 0;
    tid_supply       = 1;
    parent_tids      = Pmap.empty Pervasives.compare;
    assertions       = [];
    read_only_allocs = [];

    taint_table      = Pmap.empty Pervasives.compare;
    mem_module       = mk_memory_module file;
  }

  let get_file : unit typed_file eff =
    get >>= fun st ->
    return st.file

  let get_inline_pexpr (uid: int): typed_pexpr eff =
    get >>= fun st ->
    match Pmap.lookup uid st.inline_pexpr_map with
    | None -> failwith (sprintf "Error: BmcConcActions inline_pexpr not found %d"
                                uid)
    | Some pe -> return pe

  let get_inline_expr (uid: int): (unit typed_expr) eff =
    get >>= fun st ->
    match Pmap.lookup uid st.inline_expr_map with
    | None -> failwith (sprintf "Error: BmcConcActions inline_expr not found %d"
                                uid)
    | Some e -> return e

  let get_sym_expr (sym: sym_ty) : Expr.expr eff =
    get >>= fun st ->
    match Pmap.lookup sym st.sym_expr_table with
    | None -> failwith (sprintf "Error: BmcConcActions sym_expr %s not found"
                                (symbol_to_string sym))
    | Some e -> return e

  let get_action (uid: int) : BmcZ3.intermediate_action eff =
    get >>= fun st ->
    match Pmap.lookup uid st.action_map with
    | None -> failwith (sprintf "Error: BmcConcActions action not found %d" uid)
    | Some a -> return a

  let get_param_actions : (BmcZ3.intermediate_action option) list eff =
    get >>= fun st ->
    return st.param_actions

  let get_case_guards (uid: int): (Expr.expr list) eff =
    get >>= fun st ->
    match Pmap.lookup uid st.case_guard_map with
    | None -> failwith (sprintf "Error: BmcConcActions case guard not found %d" uid)
    | Some es -> return es

  let get_drop_cont (uid: int) : Expr.expr eff =
    get >>= fun st ->
    match Pmap.lookup uid st.drop_cont_map with
    | None -> failwith (sprintf "BmcConcActions: Uid %d not found in drop_cont_map" uid)
    | Some expr -> return expr

  let get_meta (alloc_id: int) : allocation_metadata eff =
    get >>= fun st ->
    match Pmap.lookup alloc_id st.alloc_meta_map with
    | None -> failwith (sprintf "BmcConcActions: alloc id %d not found in alloc_meta"
                                alloc_id)
    | Some data -> return data

  let get_meta_map : (int, allocation_metadata) Pmap.map eff =
    get >>= fun st ->
    return st.alloc_meta_map

  let get_tid : int eff =
    get >>= fun st ->
    return st.tid

  let get_fresh_tid : int eff =
    get                                >>= fun st ->
    return st.tid_supply               >>= fun ret ->
    put {st with tid_supply = ret + 1} >>
    return ret

  let put_tid (tid: tid) : unit eff =
    get >>= fun st ->
    put {st with tid = tid}

  let add_aids_to_bmc_actions (uid: int) (actions: aid list)
                                 : unit eff =
    get >>= fun st ->
    put {st with bmc_actions = Pmap.add uid actions st.bmc_actions}

  let get_actions_from_uid (uid: int) : (bmc_action list) eff =
    get >>= fun st ->
    let aids = Pmap.find uid st.bmc_actions in
    return (List.map (fun aid -> Pmap.find aid st.bmc_action_map) aids)

  let add_action_to_bmc_action_map (aid: aid) (action: bmc_action)
                                   : unit eff =
    get >>= fun st ->
    put {st with bmc_action_map = Pmap.add aid action st.bmc_action_map}

  let get_bmc_action_map : ((aid, bmc_action) Pmap.map) eff =
    get >>= fun st ->
    return st.bmc_action_map

  let get_parent_tids : ((tid, tid) Pmap.map) eff =
    get >>= fun st ->
    return st.parent_tids

  let add_parent_tid (child_tid: tid) (parent_tid: tid) : unit eff =
    get >>= fun st ->
    put {st with parent_tids = Pmap.add child_tid parent_tid st.parent_tids}

  let add_assertion (assertion: Expr.expr) : unit eff =
    get >>= fun st ->
    put {st with assertions = assertion :: st.assertions}

  let get_assertions : Expr.expr list eff =
    get >>= fun st ->
    return st.assertions

  let get_prov_syms : (Expr.expr * (Expr.expr * ctype)) list eff =
    get >>= fun st ->
    return st.prov_syms

  (* Helpers *)
  let guard_action (guard: Expr.expr) (BmcAction(pol, g, action): bmc_action) =
    BmcAction(pol, mk_and [guard;g], action)

  let add_read_only_alloc (alloc_id: int) : unit eff =
    get >>= fun st ->
    put {st with read_only_allocs = alloc_id :: st.read_only_allocs}

  let get_read_only_allocs : int list eff =
    get >>= fun st ->
    return st.read_only_allocs

  (* Given a ctype and a wval with sort corresponding to ctype_to_z3_sort ctype:
   * if the ctype is a multidimensional array, we create a new wval' with sort
   * LoadedIntArray.mk_sort and size corresponding to the flattened ctype. We
   * then generate the relevant equalities for wval' to wval.
   * If the ctype is not a multidimensional array, do nothing.
   *
   * Note: this is essentially a hack to simplify indexing into complex types in Z3.
   * TODO: make this work nicely with unspecified subarrays too. Currently we assume   * array types are specified.
   *)
  let flatten_multid_arrays (ctype: Core_ctype.ctype0)
                            (file: unit typed_file)
                            (value: Expr.expr)
                            (initial: bool)
                            : Expr.expr * (Expr.expr list) =
    assert (Sort.equal (Expr.get_sort value) (CtypeToZ3.ctype_to_z3_sort ctype file));

    let rec aux (global_array: Expr.expr)
                (ctype: Core_ctype.ctype0)
                (value: Expr.expr)
                (base_index: int)
                : Expr.expr list =
      match ctype with
      | Basic0 (Integer _) ->
          [mk_eq (Z3Array.mk_select g_ctx global_array (int_to_z3 base_index))
                 (Loaded.mk_base_expr value)
          ]
      | Basic0 _ ->
          failwith "TODO: multid-arrays of non-integer ctype"
      | Pointer0 _ ->
          [mk_eq (Z3Array.mk_select g_ctx global_array (int_to_z3 base_index))
                 (Loaded.mk_base_expr value)
          ]
      | Array0 (ctype', Some n) ->
          (*let size_of_bmcz3sort_ctype' : int =
            bmcz3sort_size (ctype_to_bmcz3sort ctype' file) in*)
          let size_of_ctype' : int = PointerSort.type_size ctype' file in
          (* TODO: Need to rewrite loaded sorts.
           * No guarantee value was created in this manner.
           *)
          let loaded_value = TODO_LoadedSort.get_specified_value value in

          let assertions =
            List.init (Nat_big_num.to_int n) (fun i ->
              (*let new_base = base_index + (i * size_of_bmcz3sort_ctype') in*)
              let new_base = base_index + (i * size_of_ctype') in
              let subobj = Z3Array.mk_select g_ctx loaded_value (int_to_z3 i) in
              aux global_array ctype' subobj new_base
            ) in
          List.concat assertions
      | _ ->
          failwith (sprintf "TODO: multid arrays with ctype %s"
                            (pp_to_string (Pp_core_ctype.pp_ctype ctype)))
   in
    match ctype with
    | Array0(_, _) ->
        let new_array =
            Z3Array.mk_const_s g_ctx (sprintf "flattened_%s" (Expr.to_string value))
                               integer_sort (Loaded.base_sort) in
        let loaded_new_array = TODO_LoadedSort.mk_specified new_array in
        let assertions =
          if initial then []
          else aux new_array ctype value 0 in
        (loaded_new_array, assertions)
    | Struct0 _ ->
        (TODO_LoadedSort.mk_unspecified Loaded.raw_array_sort
             (CtypeSort.mk_expr ctype), [])
    | _ ->
        (value, [])


  (*let mk_store (pol: polarity)
               (guard: Expr.expr)
               (aid: aid)
               (tid: tid)
               (memorder: memory_order)
               (ptr: Expr.expr)
               (wval: Expr.expr)
               (ctype: ctype)
               : bmc_action =
    BmcAction(pol, guard, Store(aid, tid, memorder, ptr, wval, ctype))
  *)

  let mk_store_and_flatten_multid_arrays (pol: polarity)
                                         (guard: Expr.expr)
                                         (aid: aid)
                                         (tid: tid)
                                         (memorder: memory_order)
                                         (ptr: Expr.expr)
                                         (wval: Expr.expr)
                                         (ctype: ctype)
                                         (initial: bool)
                                         : bmc_action eff =
    get_file >>= fun file ->
    let (new_wval, assertions) = flatten_multid_arrays ctype file wval initial in
    mapM_ add_assertion assertions >>
    return (BmcAction(pol, guard, Store(aid, tid, memorder, ptr, new_wval, ctype)))

  type create_mode =
    | CreateMode_Specified
    | CreateMode_Unspecified
    | CreateMode_InitialValue of Expr.expr


  (* TODO: allocation size assertions *)
  (* Make a single create *)
  let do_create (aids: aid list)
                (ctype: ctype)
                (sortlist: BmcZ3.ctype_sort list)
                (alloc_id: BmcZ3.alloc)
                (pol: polarity)
                (create_mode: create_mode)
                : bmc_action list eff =
    get_file >>= fun file ->
    let sort = CtypeToZ3.ctype_to_z3_sort ctype file in
    let is_atomic_fn = (function ctype -> match ctype with
                       | Core_ctype.Atomic0 _ -> mk_true
                       | _ -> mk_false) in
    get_meta alloc_id >>= fun metadata ->
    let base_addr = get_metadata_base metadata in

    let is_dynamic_assert =
      mk_eq (Expr.mk_app g_ctx PointerSort.is_dynamic_alloc_decl
                               [int_to_z3 alloc_id])
            mk_false in
    add_assertion is_dynamic_assert >>

    mapMi_ (fun i (ctype,sort) ->
      let index = List.fold_left
          (fun acc (ty, _) -> acc + (PointerSort.type_size ctype file))
          0 (list_take i sortlist) in
      let target_addr =
        PointerSort.shift_index_by_n base_addr (int_to_z3 index) in
      let is_atomic =
        PointerSort.assert_is_atomic target_addr (is_atomic_fn ctype) in
      add_assertion is_atomic
    ) sortlist >>= fun _ ->
    begin match ctype with
    | Struct0 tag ->
        begin match create_mode with
        | CreateMode_Specified ->
            failwith "TODO: initializing structs as values"
        | CreateMode_Unspecified ->
            ()
        | CreateMode_InitialValue _ ->
            failwith "TODO: Read only structs"
        end
    | _ -> ()
    end;
    assert (List.length aids = 1);
    let aid = List.hd aids in
    let ptr_0 = PointerSort.mk_ptr (int_to_z3 alloc_id) base_addr in

    let (initial_value, assumptions) =
      begin
      match create_mode with
      | CreateMode_Specified ->
          BmcMemCommon.mk_initial_loaded_value sort
              (sprintf "init_%d[0...%d]" alloc_id (List.length sortlist))
              ctype true file
      | CreateMode_Unspecified ->
          BmcMemCommon.mk_initial_loaded_value sort
              (sprintf "init_%d[0...%d]" alloc_id (List.length sortlist))
              ctype false file
      | CreateMode_InitialValue iv ->
          (iv, [])
      end in
    let is_initial = (CreateMode_Unspecified = create_mode) in
    mapM add_assertion assumptions >>= fun _ ->
    mk_store_and_flatten_multid_arrays
              pol mk_true aid initial_tid
              (C_mem_order Cmm_csem.NA) ptr_0 initial_value ctype
              is_initial
        >>= fun store ->
    return [store]


        (* Unspecified structs only; convert to array const *)
        (*
        begin
        assert (List.length aids = List.length sortlist);
        let (size, (_,flat_list)) = PointerSort.struct_member_index_list tag file in

        if (List.length flat_list <> List.length sortlist) then
          failwith (sprintf "Complex struct %s not supported"
                            (pp_to_string (Pp_core_ctype.pp_ctype ctype)))
        else begin
          let indexed_sorts = zip flat_list sortlist in
          mapMi (fun i (index, (ty, sort)) ->
            let target_addr =
              PointerSort.shift_index_by_n base_addr (int_to_z3 index) in
            let aid = List.nth aids i in
            let initialise =
              begin match create_mode with
              | CreateMode_Specified ->
                  failwith "TODO: initializing structs"
              | CreateMode_Unspecified -> false
              | CreateMode_InitialValue _ ->
                  failwith "TODO: Read only structs"
              end in
            let (initial_value, assumptions) =
              BmcMemCommon.mk_initial_loaded_value sort
                (sprintf "init_%d[struct.%d]" alloc_id i)
                ctype initialise file in
            mapM_ add_assertion assumptions >>
            let ptr = PointerSort.mk_ptr (int_to_z3 alloc_id) target_addr in
            (mk_store_and_flatten_multid_arrays
                             pol mk_true aid initial_tid
                             (C_mem_order Cmm_csem.NA) ptr initial_value ty)
          ) indexed_sorts
          end
        end
        *)


  let intermediate_to_bmc_actions (action: BmcZ3.intermediate_action)
                                  (pol : polarity)
                                  (uid : int)
                                  : (bmc_action list) eff =
    (match action with
    | ICreate(aids, ctype, _, sortlist, alloc_id) ->
        do_create aids ctype sortlist alloc_id pol CreateMode_Unspecified
    | ICreateReadOnly(aids, ctype, _, sortlist, alloc_id, initial_value) ->
        add_read_only_alloc alloc_id >>
        do_create aids ctype sortlist alloc_id pol
          (CreateMode_InitialValue initial_value)
    | IKill (aid,ptr, b) ->
        get_tid >>= fun tid ->
        let dynamic_kill_assertion =
          mk_eq (Expr.mk_app g_ctx is_dynamic_kill_decl [int_to_z3 aid])
                (Boolean.mk_val g_ctx b) in
        add_assertion dynamic_kill_assertion >>
        return [BmcAction(pol, mk_true, Kill(aid, tid, ptr))]
    (*| ILoad (aid, (ctype, sort), ptr, rval, mo) ->*)
    | ILoad (aid, ctype, _, ptr, rval, mo) ->
        get_tid >>= fun tid ->
        return [BmcAction(pol, mk_true, Load(aid, tid, C_mem_order mo, ptr, rval, ctype))]
    (*| IStore(aid, (ctype, sort), ptr, wval, mo) ->*)
    | IStore (aid,ctype,_,ptr,wval,mo) ->
        get_tid >>= fun tid ->
        mk_store_and_flatten_multid_arrays
                pol mk_true aid tid (C_mem_order mo) ptr wval ctype false
            >>= fun store ->
        return [store]

    | ICompareExchangeStrong (aid_load, aid_fail_load, aid_fail_store, aid_succeed_rmw,
                              ctype,_, ptr_obj, ptr_exp,
                              desired, rval_expected, rval_object,
                              mo_success, mo_failure) (* fall through *)
    | ICompareExchangeWeak   (aid_load, aid_fail_load, aid_fail_store, aid_succeed_rmw,
                              ctype,_, ptr_obj, ptr_exp,
                              desired, rval_expected, rval_object,
                              mo_success, mo_failure) ->

        get_tid >>= fun tid ->
        get_case_guards uid >>= fun guards ->
        assert (List.length guards = 1);

        (*let success_guard = mk_eq rval_expected rval_object in*)
        let success_guard = List.hd guards in
        (* TODO: need to change this type *)
        return [
          (* NA load of ptr_exp -> rval_expected *)
          BmcAction(pol, mk_true,
                    Load(aid_load, tid, C_mem_order NA, ptr_exp, rval_expected,ctype));
          (* if fail: do a load of object and then a store *)
          BmcAction(pol, mk_not success_guard,
                    Load(aid_fail_load, tid, C_mem_order mo_failure, ptr_obj, rval_object,ctype));
          BmcAction(pol, mk_not success_guard,
                    Store(aid_fail_store, tid, C_mem_order NA, ptr_exp, rval_object,ctype));
          (* if succeed, do a rmw *)
          BmcAction(pol, success_guard,
                    RMW(aid_succeed_rmw, tid, (C_mem_order mo_success), ptr_obj, rval_object, desired,ctype))
        ]

    | IFence (aid, mo) ->
        get_tid >>= fun tid ->
        return [BmcAction(pol, mk_true, Fence(aid,tid,C_mem_order mo))]
    | IMemop(aid, memop, args, rets) ->
       get_tid >>= fun tid ->
       begin match memop, args, rets with
       | PtrValidForDeref, [ptr], [ret] ->
          return [BmcAction(pol, mk_true,
                            Memop(aid, tid, (Memop_PtrValidForDeref(ptr, ret))))]
       | PtrValidForDeref, _, _ ->
           assert false
       | Ptrdiff, [p1;p2],[] ->
          return [BmcAction(pol, mk_true,
                            Memop(aid, tid, (Memop_PtrDiff(p1, p2))))]
       | Ptrdiff, _, _ ->
           assert false
       | PtrArrayShift, [p1;p2],[] ->
          return [BmcAction(pol, mk_true,
                            Memop(aid, tid, (Memop_PtrArrayShift(p1, p2))))]
       | PtrArrayShift, _, _ ->
          assert false
       | _,_,_ -> failwith
            (sprintf "TODO: Do concurrency model implementation of %s"
                       (pp_to_string (Pp_mem.pp_memop memop)))
       end
    | ILinuxLoad(aid, ctype, _, ptr, rval, mo) ->
        get_tid >>= fun tid ->
        return [BmcAction(pol, mk_true, Load(aid, tid, Linux_mem_order mo, ptr, rval, ctype))]
    | ILinuxStore(aid, ctype, _, ptr, wval, mo) ->
        get_tid >>= fun tid ->
        return [BmcAction(pol, mk_true, Store(aid, tid, Linux_mem_order mo, ptr, wval, ctype))]
    | ILinuxRmw(aid, ctype, _, ptr, wval, rval, mo) ->
        get_tid >>= fun tid ->
        return [BmcAction(pol, mk_true, RMW(aid, tid, Linux_mem_order mo, ptr, rval, wval, ctype))]
    | ILinuxFence(aid, mo) ->
        get_tid >>= fun tid ->
        return [BmcAction(pol, mk_true, Fence(aid, tid, Linux_mem_order mo))]
    ) >>= fun actions ->
    (* Just for convenience *)
    mapM (fun action -> add_action_to_bmc_action_map
                            (aid_of_bmcaction action) action) actions >>
    return actions

  let rec do_actions_e (Expr(annots, expr_) as expr)
                       : (bmc_action list) eff =
    let uid = get_id_expr expr in
    (match expr_ with
    | Epure pe ->
        return []
    | Ememop(PtrValidForDeref, _)  (* fall through *)
    | Ememop(Ptrdiff, _)  (* fall through *)
    | Ememop(PtrArrayShift, _) ->
        get_action uid >>= fun interm_action ->
        intermediate_to_bmc_actions interm_action Pos uid
    | Ememop(PtrEq, args)            (* fall through *)
    | Ememop(PtrNe, args)            (* fall through *)
    | Ememop(PtrLt, args)            (* fall through *)
    | Ememop(PtrGt, args)            (* fall through *)
    | Ememop(PtrLe, args)            (* fall through *)
    | Ememop(PtrGe, args)            (* fall through *)
    | Ememop(IntFromPtr, args)       (* fall through *)
    | Ememop(PtrFromInt, args)       (* fall through *)
    | Ememop(PtrWellAligned, args) ->
        return []
    | Ememop (memop, _) ->
        failwith (sprintf "TODO: support %s"
                          (pp_to_string (Pp_mem.pp_memop memop)))
    | Eaction (Paction(pol, action)) ->
        get_action uid >>= fun interm_action ->
        intermediate_to_bmc_actions interm_action pol uid
    | Ecase (pe, cases) ->
        mapM do_actions_e (List.map snd cases) >>= fun case_actions ->
        get_case_guards uid            >>= fun case_guards ->
        return (List.concat (
          List.map2 (fun guard actions -> List.map (guard_action guard) actions)
                    case_guards case_actions))
    | Elet (pat, pe, e) ->
        do_actions_e e
    | Eif (cond, e1, e2) ->
        do_actions_e e1 >>= fun e1_actions ->
        do_actions_e e2 >>= fun e2_actions ->
        (* TODO: do this more nicely *)
        get_case_guards uid >>= fun guards ->
        let (guard1, guard2) = (
          match guards with
          | [g1;g2] -> (g1,g2)
          | _ -> assert false) in
        return ((List.map (guard_action guard1) e1_actions) @
                (List.map (guard_action guard2) e2_actions))
    | Eskip         -> return []
    | Eccall _ ->
        get_inline_expr uid >>= fun inline_expr ->
        do_actions_e inline_expr
    | Eproc _       -> assert false
    | Eunseq es ->
        mapM do_actions_e es >>= fun es_actions ->
        return (List.concat es_actions)
    | Ewseq (pat, e1, e2) (* fall through *)
    | Esseq (pat, e1, e2) ->
        do_actions_e e1 >>= fun e1_actions ->
        do_actions_e e2 >>= fun e2_actions ->
        get_drop_cont (get_id_expr e1) >>= fun e1_drop_cont ->
        let e2_guard = mk_not e1_drop_cont in
        return (e1_actions @ (List.map (guard_action e2_guard) e2_actions))
    | Easeq _       -> assert false
    | Eindet _      -> assert false
    | Ebound (_, e) ->
        do_actions_e e
    | End es ->
        mapM do_actions_e es        >>= fun es_actions ->
        get_case_guards uid >>= fun es_guards ->
        return (List.concat (
          List.map2 (fun guard actions -> List.map (guard_action guard) actions)
                    es_guards es_actions))
    | Esave _       (* fall through *)
    | Erun _        ->
        get_inline_expr uid >>= fun inline_expr ->
        do_actions_e inline_expr
    | Epar elist ->
        get_tid >>= fun old_tid ->
        mapM (fun e ->
          get_fresh_tid >>= fun tid ->
          put_tid tid   >>
          add_parent_tid tid old_tid >>
          do_actions_e e) elist >>= fun elist_actions ->
        put_tid old_tid >>
        return (List.concat elist_actions)
    | Ewait _       ->
        assert false
    ) >>= fun actions ->
    let aids = List.map aid_of_bmcaction actions in
    add_aids_to_bmc_actions uid aids >>
    return actions

  let do_actions_globs(gname, glb) =
    match glb with
    | GlobalDef(_, e) -> do_actions_e e
    | GlobalDecl _ -> return []

  let do_actions_param ((sym,cbt): (sym_ty * core_base_type))
                       (action_opt : BmcZ3.intermediate_action option)
                       : bmc_action list eff =
    match action_opt with
    | None ->
        (* Param is not a pointer; nothing to be done *)
        assert (not (is_core_ptr_bty cbt));
        return []
    | Some (ICreate(aids, ctype, _, sortlist, alloc_id)) ->
        (* Polarity is irrelevant? *)
        do_create aids ctype sortlist alloc_id Pos CreateMode_Specified >>= fun actions ->
        (* Make let binding *)
        get_sym_expr sym >>= fun sym_expr ->
        get_meta alloc_id >>= fun metadata ->
        let base_addr = get_metadata_base metadata in


        let eq_expr =
          mk_eq sym_expr
                (PointerSort.mk_ptr (int_to_z3 alloc_id) base_addr) in
        add_assertion eq_expr >>
        return actions
    | _ -> assert false

  let do_actions_params (params: ((sym_ty * core_base_type) list))
                        (fn_to_check: sym_ty)
                        : bmc_action list eff =
    get_param_actions >>= fun param_actions ->
    mapM2 do_actions_param params param_actions >>= fun actionss ->
    let actions = List.concat actionss in
    mapM (fun action -> add_action_to_bmc_action_map
                            (aid_of_bmcaction action) action) actions >>
    return actions

  (* TODO: this is currently not po, but ignores thread ids and computes
   * cartesian product!!! *)
  let rec do_po_e (Expr(annots, expr_) as expr)
                  : aid_rel list eff =
    let uid = get_id_expr expr in
    (match expr_ with
    | Epure pe ->
        return []
    | Ememop (memop, pes) ->
        return []
    | Eaction (Paction(pol, action)) ->
        (* Only need to do something for RMW *)
        get_action uid >>= fun interm_action ->
        begin match interm_action with
        | ICompareExchangeStrong
              (aid_load, aid_fail_load, aid_fail_store, aid_success_rmw,
               _,_, _, _, _, _, _, _, _) (* fall through *)
        | ICompareExchangeWeak
              (aid_load, aid_fail_load, aid_fail_store, aid_success_rmw,
               _,_, _, _, _, _, _, _, _) ->
            return [(aid_load, aid_fail_load)
                   ;(aid_load, aid_fail_store)
                   ;(aid_load, aid_success_rmw)
                   ;(aid_fail_load, aid_fail_store)]
        | _ ->
            return []
        end
    | Ecase (pe, cases) ->
        mapM do_po_e (List.map snd cases) >>= fun po_cases ->
        return (List.concat po_cases)
    | Elet (pat, pe, e) ->
        do_po_e e
    | Eif (cond, e1, e2) ->
        do_po_e e1 >>= fun po_e1 ->
        do_po_e e2 >>= fun po_e2 ->
        return (po_e1 @ po_e2)
    | Eskip         -> return []
    | Eccall _ ->
        get_inline_expr uid >>= fun inline_expr ->
        do_po_e inline_expr
    | Eproc _       -> assert false
    | Eunseq es ->
        mapM do_po_e es >>= fun po_es ->
        return (List.concat po_es)
    | Ewseq (pat, e1, e2) ->
        do_po_e e1 >>= fun po_e1 ->
        do_po_e e2 >>= fun po_e2 ->
        get_actions_from_uid (get_id_expr e1) >>= fun actions_e1 ->
        get_actions_from_uid (get_id_expr e2) >>= fun actions_e2 ->
        let to_sequence = List.filter is_pos_action actions_e1 in
        return ((List.map aid_of_bmcaction_rel (cartesian_product to_sequence actions_e2))
                @ po_e1 @ po_e2)
    | Esseq (pat, e1, e2) ->
        do_po_e e1 >>= fun po_e1 ->
        do_po_e e2 >>= fun po_e2 ->
        get_actions_from_uid (get_id_expr e1) >>= fun actions_e1 ->
        get_actions_from_uid (get_id_expr e2) >>= fun actions_e2 ->

        (* TODO (hacky):
         * For all actions in e1, make them have positive polarity from now on.
         * This is hacky/bad b/c we're modifying bmc_action_map in the wrong phase.
         * Polarity is not a static property of bmc_action and should be tracked
         * elsewhere.
         *)
        let pos_actions_e1 =
          List.map (fun (BmcAction(_, guard, action)) -> BmcAction(Pos, guard, action))
                   actions_e1 in
        mapM_ (fun action -> add_action_to_bmc_action_map
                                  (aid_of_bmcaction action) action)
              pos_actions_e1 >>

        return ((List.map aid_of_bmcaction_rel (cartesian_product actions_e1 actions_e2))
                @ po_e1 @ po_e2)
    | Easeq _       -> assert false
    | Eindet _      -> assert false
    | Ebound (_, e) ->
        do_po_e e
    | End es ->
        mapM do_po_e es >>= fun po_es ->
        return (List.concat po_es)
    | Esave _       (* fall through *)
    | Erun _        ->
        get_inline_expr uid >>= fun inline_expr ->
        do_po_e inline_expr
    | Epar es ->
        mapM do_po_e es >>= fun po_es ->
        return (List.concat po_es)
    | Ewait _       ->
        assert false
    )

  (* TODO: create/store in global can be replaced by single store *)
  let do_po_globs(gname, glb) =
    match glb with
    | GlobalDef(_, e) -> do_po_e e
    | GlobalDecl _ -> return []

  (* ==== Taint analysis ===== *)
  let get_taint (sym: sym_ty) : aid Pset.set eff =
    get >>= fun st ->
    match Pmap.lookup sym st.taint_table with
    | None -> failwith (sprintf "BmcConcActions: taint %s not found"
                                (symbol_to_string sym))
    | Some ret -> return ret

  let add_taint (sym: sym_ty) (taint: aid Pset.set) : unit eff =
    get >>= fun st ->
    put {st with taint_table = Pmap.add sym taint st.taint_table}

  let print_taint_table : unit eff =
    get >>= fun st ->
    return (Pmap.iter (fun sym taints ->
      printf "%s: [" (symbol_to_string sym);
      Pset.iter (fun taint -> printf "%d," taint) taints;
      print_endline "]";
    ) st.taint_table)

  let rec do_taint_pat (Pattern(_,pat): typed_pattern) (aids: aid Pset.set)
                       : unit eff =
    match pat with
    | CaseBase(Some sym, _) ->
        add_taint sym aids
    | CaseBase(None, _) ->
        return ()
    | CaseCtor(_, patlist) ->
        mapM_ (fun pat -> do_taint_pat pat aids) patlist

  let union_taints (taints: (aid Pset.set) list) : aid Pset.set =
    List.fold_left (fun x y -> Pset.union x y)
                   (Pset.empty Pervasives.compare)
                   taints

  type deps = {
    addr : aid_rel list;
    data : aid_rel list;
    ctrl : aid_rel list;
  }

  let empty_deps : deps =
    { addr = []; data = []; ctrl = []}

  let union_deps (deps: deps list) : deps =
    List.fold_left (fun acc dep ->
      {addr = acc.addr @ dep.addr
      ;data = acc.data @ dep.data
      ;ctrl = acc.ctrl @ dep.ctrl}
    ) empty_deps deps

  let pp_deps (deps: deps) =
    printf "===Addr:\n%s\n===Data:\n%s\n====Ctrl:\n%s\n"
          (String.concat "\n" (List.map (fun (x,y) -> sprintf "(%d,%d)" x y) deps.addr))
          (String.concat "\n" (List.map (fun (x,y) -> sprintf "(%d,%d)" x y) deps.data))
          (String.concat "\n" (List.map (fun (x,y) -> sprintf "(%d,%d)" x y) deps.ctrl))

  let rec do_taint_pe (Pexpr(annots, bTy, pe_) as pexpr)
                      : aid Pset.set eff =
  let uid = get_id_pexpr pexpr in
  (match pe_ with
    | PEsym sym ->
        get_taint sym
    | PEimpl const ->
        get_inline_pexpr uid >>= fun inline_pe ->
        do_taint_pe inline_pe
    | PEval cval ->
        return (Pset.empty Pervasives.compare)
    | PEconstrained _ -> assert false
    | PEundef _ ->
        return (Pset.empty Pervasives.compare)
    | PEerror _ ->
        return (Pset.empty Pervasives.compare)
    | PEctor (_, pes) ->
        mapM do_taint_pe pes >>= fun taint_pes ->
        return (union_taints taint_pes)
    | PEcase (pe, cases) ->
        do_taint_pe pe >>= fun taint_pe ->
        (* Add taint to each symbol in pattern *)
        mapM (fun (pat, _) -> do_taint_pat pat taint_pe) cases >>
        mapM (fun (_, case_pe) -> do_taint_pe case_pe) cases
              >>= fun case_taints ->
        return (union_taints case_taints)
    | PEarray_shift (ptr, _, index) ->
        do_taint_pe ptr >>= fun taint_ptr ->
        do_taint_pe index >>= fun taint_index ->
        return (Pset.union taint_ptr taint_index)
    | PEmember_shift (ptr, _, _) ->
        do_taint_pe ptr
    | PEnot pe ->
        do_taint_pe pe
    | PEop (_, pe1, pe2) ->
        do_taint_pe pe1 >>= fun taint_pe1 ->
        do_taint_pe pe2 >>= fun taint_pe2 ->
        return (Pset.union taint_pe1 taint_pe2)
    | PEstruct (_,pes) ->
        mapM do_taint_pe @@ List.map snd pes >>= fun taint_pes ->
        return (union_taints taint_pes)
    | PEunion _     -> assert false
    | PEcfunction _ -> assert false
    | PEmemberof _  -> assert false
    | PEcall _ ->
        get_inline_pexpr uid >>= fun inline_pe ->
        do_taint_pe inline_pe
    | PElet (pat, pe1, pe2) ->
        do_taint_pe pe1 >>= fun taint_pe1 ->
        do_taint_pat pat taint_pe1 >>
        do_taint_pe pe2
    | PEif (cond, pe1, pe2) ->
        do_taint_pe cond >>= fun taint_cond ->
        do_taint_pe pe1 >>= fun taint_pe1 ->
        do_taint_pe pe2 >>= fun taint_pe2 ->
        return (union_taints [taint_cond; taint_pe1; taint_pe2])
          (*Pset.union taint_pe1 taint_pe2)*)
    | PEis_scalar pe   (* fall through *)
    | PEis_integer pe  (* fall through *)
    | PEis_signed pe   (* fall through *)
    | PEis_unsigned pe ->
        do_taint_pe pe
    | PEare_compatible (pe1, pe2) ->
        do_taint_pe pe1 >>= fun taint_pe1 ->
        do_taint_pe pe2 >>= fun taint_pe2 ->
        return (Pset.union taint_pe1 taint_pe2)
    | PEbmc_assume pe ->
        do_taint_pe pe
    )

  let do_taint_action (Paction(p, Action(loc, a, action_))) (uid: int)
                      : (aid Pset.set * deps) eff =
    match action_ with
    | Create(pe1, pe2, pref) ->
        do_taint_pe pe1 >>= fun _ ->
        do_taint_pe pe2 >>= fun _ ->
        return (Pset.empty Pervasives.compare, empty_deps)
    | CreateReadOnly _ -> assert false
    | Alloc0 _ -> assert false
    | Kill(_, pe) ->
        do_taint_pe pe >>= fun taint_pe ->
        (* TODO: ignored *)
        return (taint_pe, empty_deps)
    | Store0 (b, Pexpr(_,_,PEval (Vctype ty)), Pexpr(_,_,PEsym sym), wval, mo) ->
        get_action uid >>= fun interm_action ->
        do_taint_pe wval >>= fun taint_wval ->
        get_taint sym >>= fun taint_ptr ->
        begin match interm_action with
        | IStore(aid, _,_,_,_,_) ->
          return (Pset.empty Pervasives.compare,
                 { addr = cartesian_product (Pset.elements taint_ptr) [aid]
                 ; data = cartesian_product (Pset.elements taint_wval) [aid]
                 ; ctrl = []
                 })
        | _ -> assert false
        end
    | Store0 _ ->
        assert false
    | Load0 (Pexpr(_,_,PEval (Vctype ty)), Pexpr(_,_,PEsym sym), mo) ->
        get_action uid >>= fun interm_action ->
        get_taint sym >>= fun taint_ptr ->
        begin match interm_action with
        | ILoad(aid, _,_,_,_,_) ->
            return (Pset.add aid (Pset.empty Pervasives.compare),
                    { addr = cartesian_product (Pset.elements taint_ptr) [aid]
                    ; data = []
                    ; ctrl = []
                    })
        | _ -> assert false
        end

    | Load0 _ ->
        assert false
    | RMW0 (pe1, pe2, pe3, pe4, mo1, mo2) ->
        bmc_debug_print 7 "TODO: Taint RMW0";
        (* TODO *)
        return (Pset.empty Pervasives.compare, empty_deps)
    | Fence0 mo ->
        return (Pset.empty Pervasives.compare, empty_deps)
    | CompareExchangeStrong(pe1, pe2, pe3, pe4, mo1, mo2) ->
        (* TODO: We only do taint analysis for linux at the moment;
         * CompareExchangeStrong for C only*)
        bmc_debug_print 7 "TODO: Taint CompareExchangeStrong";
        return (Pset.empty Pervasives.compare, empty_deps)
    | CompareExchangeWeak(pe1, pe2, pe3, pe4, mo1, mo2) ->
        bmc_debug_print 7 "TODO: Taint CompareExchangeWeak";
        return (Pset.empty Pervasives.compare, empty_deps)
    | LinuxFence mo ->
        return (Pset.empty Pervasives.compare, empty_deps)

    | LinuxLoad (Pexpr(_,_,PEval (Vctype ty)), Pexpr(_,_,PEsym sym), mo) ->
        get_action uid >>= fun interm_action ->
        get_taint sym >>= fun taint_ptr ->
        begin match interm_action with
        | ILinuxLoad(aid, _,_,_,_,_) ->
            return (Pset.add aid (Pset.empty Pervasives.compare),
                    { addr = cartesian_product (Pset.elements taint_ptr) [aid]
                    ; data = []
                    ; ctrl = []
                    }
                   )
        | _ -> assert false
        end
    | LinuxStore (Pexpr(_,_,PEval (Vctype ty)), Pexpr(_,_,PEsym sym), wval, mo) ->
        get_action uid >>= fun interm_action ->
        do_taint_pe wval >>= fun taint_wval ->
        get_taint sym >>= fun taint_ptr ->
        begin match interm_action with
        | ILinuxStore(aid, _,_,_,_,_) ->
          return (Pset.empty Pervasives.compare,
                 { addr = cartesian_product (Pset.elements taint_ptr) [aid]
                 ; data = cartesian_product (Pset.elements taint_wval) [aid]
                 ; ctrl = []
                 })
        | _ -> assert false
        end
    | LinuxRMW (Pexpr(_,_,PEval (Vctype ty)), Pexpr(_,_,PEsym sym), wval, mo) ->
        get_action uid   >>= fun interm_action ->
        do_taint_pe wval >>= fun taint_wval ->
        get_taint sym >>= fun taint_ptr ->
        (* TODO: Check if this is correct *)
        begin match interm_action with
        | ILinuxRmw(aid, _, _, _, _,_,_) ->
            return (Pset.add aid (Pset.empty Pervasives.compare),
                   { addr = cartesian_product (Pset.elements taint_ptr) [aid]
                   ; data = cartesian_product (Pset.elements taint_wval) [aid]
                   ; ctrl = []
                   })
        | _ -> assert false
        end
    | _ -> assert false

  let rec do_taint_e (Expr(annots, expr_) as expr)
                     : (aid Pset.set * deps) eff =
    let uid = get_id_expr expr in
    (match expr_ with
    | Epure pe ->
        do_taint_pe pe >>= fun taints ->
        return (taints, empty_deps)
    | Ememop (memop, pes) ->
        mapM do_taint_pe pes >>= fun taints ->
        return (union_taints taints, empty_deps)
    | Eaction paction ->
        do_taint_action paction uid
    | Ecase (pe, cases) ->
        do_taint_pe pe >>= fun taint_pe ->
        (* Add taint to each symbol in pattern *)
        mapM (fun (pat, _) -> do_taint_pat pat taint_pe) cases >>
        mapM (fun (_, case_e) -> do_taint_e case_e) cases
              >>= fun case_taints_and_deps ->

        let case_taints = union_taints (List.map fst case_taints_and_deps) in
        let case_deps = union_deps (List.map snd case_taints_and_deps) in
        (* Add control dependencies between taint_pe and actions in cases *)
        mapM (fun (_, case_e) ->
          get_actions_from_uid (get_id_expr case_e)) cases
          >>= fun case_actionss ->
        let case_action_ids =
          List.map aid_of_bmcaction (List.concat case_actionss) in
        let ctrl_deps =
          cartesian_product (Pset.elements taint_pe) case_action_ids in

        return (case_taints,
                {case_deps with ctrl = ctrl_deps @ case_deps.ctrl})
    | Elet (pat, pe, e) ->
        do_taint_pe pe >>= fun taint_pe ->
        do_taint_pat pat taint_pe >>
        do_taint_e e
    | Eif (cond, e1, e2) ->
        do_taint_pe cond >>= fun taint_pe ->
        do_taint_e e1 >>= fun (taint_e1, deps_e1) ->
        do_taint_e e2 >>= fun (taint_e2, deps_e2) ->
        (* ctrl dep *)
        get_actions_from_uid (get_id_expr e1) >>= fun actions_e1 ->
        get_actions_from_uid (get_id_expr e2) >>= fun actions_e2 ->
        let branch_actions =
          List.map aid_of_bmcaction (actions_e1 @ actions_e2) in

        let ctrl_deps =
          cartesian_product (Pset.elements taint_pe) branch_actions in
        let deps = union_deps [deps_e1; deps_e2] in
        return (Pset.union taint_e1 taint_e2,
                {deps with ctrl = ctrl_deps @ deps.ctrl})
    | Eskip ->
        return (Pset.empty Pervasives.compare, empty_deps)
    | Eccall _ ->
        get_inline_expr uid >>= fun inline_expr ->
        do_taint_e inline_expr
    | Eproc _       -> assert false
    | Eunseq es ->
        mapM do_taint_e es >>= fun taint_es ->
        return (union_taints (List.map fst taint_es),
                union_deps (List.map snd taint_es))
    | Ewseq (pat, e1, e2) (* fall through *)
      (* TODO: need to check they are subset of po;
       * positive actions? *)
    | Esseq (pat, e1, e2) ->
        do_taint_e e1 >>= fun (taint_e1, deps_e1) ->
        do_taint_pat pat taint_e1 >>
        do_taint_e e2 >>= fun (taint_e2, deps_e2) ->
        return (taint_e2, union_deps [deps_e1; deps_e2])
    | Easeq _       -> assert false
    | Eindet _      -> assert false
    | Ebound (_, e) ->
        do_taint_e e
    | End es ->
        mapM do_taint_e es >>= fun taint_es ->
        return (union_taints (List.map fst taint_es),
                union_deps (List.map snd taint_es))
    | Esave _       (* fall through *)
    | Erun _        ->
        get_inline_expr uid >>= fun inline_expr ->
        do_taint_e inline_expr
    | Epar es ->
        mapM do_taint_e es >>= fun taint_es ->
        return (union_taints (List.map fst taint_es),
                union_deps (List.map snd taint_es))
    | Ewait _       ->
        assert false
    )

  (* Just add empty taint *)
  let do_taint_globs (gname, glb) =
    add_taint gname (Pset.empty Pervasives.compare)

  let mk_preexec (actions: bmc_action list)
                 (prod: aid_rel list)
                 (deps: deps)
                 : preexec eff =
    get_bmc_action_map >>= fun action_map ->
    get_parent_tids    >>= fun parent_tids ->

    let is_related tid1 tid2 =
      let p1 = (match Pmap.lookup tid1 parent_tids with (* (x,y) *)
                | Some a -> tid2 = a | _ -> false) in
      let p2 = (match Pmap.lookup tid2 parent_tids with (* (y,x) *)
                | Some a -> tid1 = a | _ -> false) in
      p1 || p2
    in

    let aid_rel_to_bmcaction (a,b) =
      (Pmap.find a action_map, Pmap.find b action_map) in

    let po_actions = List.map aid_rel_to_bmcaction prod in
    let po = List.filter (fun (a,b) -> tid_of_bmcaction a = tid_of_bmcaction b)
                         po_actions in

    let in_po (a,b) =
      is_some (List.find_opt
      (fun (x,y) -> aid_of_bmcaction a = aid_of_bmcaction x &&
                    aid_of_bmcaction b = aid_of_bmcaction y) po) in

    let addr = List.map aid_rel_to_bmcaction deps.addr in
    let data = List.map aid_rel_to_bmcaction deps.data in
    let ctrl = List.map aid_rel_to_bmcaction deps.ctrl in

    return
    { actions = List.filter (fun a -> tid_of_bmcaction a <> initial_tid) actions
    ; initial_actions = List.filter (fun a -> tid_of_bmcaction a = initial_tid) actions
    ; po = List.filter (fun (a,b) -> tid_of_bmcaction a = tid_of_bmcaction b)
                       po_actions
    ; asw = List.filter
              (fun (a,b) -> is_related (tid_of_bmcaction a) (tid_of_bmcaction b))
              po_actions
    (*; rmw = []*)
    ; addr = List.filter in_po addr
    ; data = List.filter in_po data
    ; ctrl = List.filter in_po ctrl
    }

  let compute_po (xs: bmc_action list)
                 (ys: bmc_action list)
                 : aid_rel list =
    List.map aid_of_bmcaction_rel (cartesian_product xs ys)

  let do_read_only_vcs () : bmc_vc list eff =
    get_read_only_allocs >>= fun read_only_allocs ->
    get_bmc_action_map   >>= fun bmc_action_map ->

    let vcs = Pmap.fold (fun _ (BmcAction(_, guard, action)) acc ->
      match action with
      | Store (_, tid, _, loc, _, _) (* fall through *)
      | RMW (_,tid,_,loc,_,_,_) ->
          if tid = initial_tid then
            (* Initial action; do nothing *)
            acc
          else begin
            let index = PointerSort.get_addr_index loc in

            let inner_vcs = List.map (fun alloc ->
              let alloc_min = Expr.mk_app g_ctx
                  PointerSort.alloc_min_decl [int_to_z3 alloc] in
              let alloc_max = Expr.mk_app g_ctx
                  PointerSort.alloc_max_decl [int_to_z3 alloc] in
              let vc_expr =
                mk_not (mk_and [binop_to_z3 OpGe index alloc_min
                               ;binop_to_z3 OpLt index alloc_max]) in
              let guarded_vc = mk_implies guard vc_expr in
              (guarded_vc, VcDebugStr "writing read only memory")
            ) read_only_allocs in
            inner_vcs @ acc
          end
      | _ -> acc
    ) bmc_action_map [] in

    return vcs

  let do_file (file: unit typed_file) (fn_to_check: sym_ty)
              : (preexec * Expr.expr list * bmc_vc list * 't option) eff =
    mapM do_actions_globs file.globs >>= fun globs_actions ->
    mapM do_po_globs file.globs      >>= fun globs_po ->
    mapM do_taint_globs file.globs   >>

    (match Pmap.lookup fn_to_check file.funs with
     | Some (Proc(annot, bTy, params, e)) ->
         do_actions_params params fn_to_check >>= fun actions_params ->
         do_actions_e e >>= fun actions ->
         do_taint_e e   >>= fun (_, deps) ->
         do_po_e e      >>= fun po ->
         return (actions @ actions_params,
                 (compute_po actions_params actions) @ po, deps)
     | Some (Fun(ty, params, pe)) ->
         return ([], [], empty_deps)
     | _ -> assert false
    ) >>= fun (fn_actions, fn_po, fn_deps) ->

    let actions = (List.concat globs_actions) @ fn_actions in
    let po = ((compute_po (List.concat globs_actions) fn_actions))
              @ (List.concat globs_po) @ fn_po in
    get_assertions >>= fun assertions ->
    mk_preexec actions po fn_deps >>= fun preexec ->
    bmc_debug_print 6 (pp_preexec preexec);

    (* TODO *)
    (*compute_crit preexec.po;*)
    (* Debug: iterate through taint map *)
    (*print_taint_table >>*)

    (*pp_deps filtered_deps;*)

    (* TODO *)
    get_memory_module >>= fun memory_module ->
    let module BmcMem = (val memory_module : MemoryModel) in

    let (mem_assertions, mem_vcs, memory_model) =
      if (List.length actions > 0) then
         let model = BmcMem.compute_executions preexec file in
         (BmcMem.get_assertions model, BmcMem.get_vcs model, Some model)
      else
        ([], [], None) in

    get_meta_map >>= fun metadata ->
    get_prov_syms >>= fun prov_syms ->

    let pnvi_asserts =
      if (g_pnvi) then begin
        let metadata_list = Pmap.bindings_list metadata in
        let meta_asserts = BmcMemCommon.metadata_assertions metadata_list in
        let provenance_asserts =
          List.concat (List.map (fun x ->
                BmcMemCommon.provenance_assertions x metadata file) prov_syms) in
        meta_asserts @ provenance_asserts
      end else
        []
    in

    do_read_only_vcs () >>= fun read_only_vcs ->

    return (preexec,
            assertions @ mem_assertions @  pnvi_asserts,
            (* TODO: should races be here instead? *)
            read_only_vcs @ mem_vcs,
            if is_some memory_model then
              Some (BmcMem.extract_executions g_solver (Option.get memory_model))
            else None
            )
end
