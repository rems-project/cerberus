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
    get_fresh_id >>= fun id ->
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
          add_inlined_pexpr id (Pexpr([], ty, PEerror(error_msg, pexpr))) >>
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
    return (Pexpr(Abmc (Abmc_inline_pexpr_id id)::annots, bTy, inlined_pe))

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
        return (Eaction pact)
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
          add_inlined_expr id 
            (Expr([],Epure(Pexpr([], BTy_unit, 
                                 PEerror(error_msg, Pexpr([], BTy_unit, PEval (Vunit))))))) >>
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
    return (Expr(Abmc (Abmc_inline_expr_id id)::annots, inlined_e))

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
  type sym_ty_table_ty = (sym_ty, core_base_type) Pmap.map

  type state_ty = {
    sym_supply    : sym_supply_ty;
    sym_table     : sym_table_ty;
    sym_ty_table  : sym_ty_table_ty;
    
    file   : unit typed_file; (* unmodified *)

    inline_pexpr_map : (int, typed_pexpr) Pmap.map;
    inline_expr_map  : (int, unit typed_expr) Pmap.map;
  }
  include EffMonad(struct type state = state_ty end)

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

  let get_sym_ty_table : sym_ty_table_ty eff =
    get >>= fun st ->
    return st.sym_ty_table

  let put_sym_ty_table (table: sym_ty_table_ty) : unit eff =
    get >>= fun st ->
    put {st with sym_ty_table = table}

  let put_sym_ty (sym: sym_ty) (ty: core_base_type) : unit eff =
    get_sym_ty_table >>= fun table ->
    match Pmap.lookup sym table with
    | Some _ -> failwith (sprintf "BmcSSA error: sym %s exists in sym_ty_table"
                                  (symbol_to_string sym))
    | None -> put_sym_ty_table (Pmap.add sym ty table)

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
         put_sym_ty new_sym typ >>
         return (CaseBase(Some new_sym, typ))       
     | CaseBase (None, _) ->
         return pat
     | CaseCtor (ctor, patlist) ->
         mapM ssa_pattern patlist >>= fun ssad_patlist ->
         return (CaseCtor(ctor, ssad_patlist))
    ) >>= fun ssad_pat ->
    return (Pattern(annots, ssad_pat))

  let rec ssa_pe (Pexpr(annots, bTy, pe_) as pexpr) : typed_pexpr eff =
    (match pe_ with
    | PEsym sym ->
        lookup_sym sym >>= fun ssad_sym ->
        return (PEsym ssad_sym)
    | PEimpl _ -> return pe_        
    | PEval _ -> return pe_          
    | PEconstrained _ -> assert false
    | PEundef _ -> return pe_
    | PEerror _ -> return pe_
    | PEctor (ctor, pelist) ->
        mapM ssa_pe pelist >>= fun ssad_pelist ->
        return (PEctor(ctor, ssad_pelist))
    | PEcase (pe1, caselist) ->
        ssa_pe pe1 >>= fun ssad_pe1 ->
        mapM (fun (pat,pe) -> ssa_pattern pat >>= fun ssad_pat ->
                              ssa_pe pe       >>= fun ssad_pe ->
                              return (ssad_pat, ssad_pe))
             caselist >>= fun ssad_caselist ->
        return (PEcase(ssad_pe1, ssad_caselist))      
    | PEarray_shift _
    | PEmember_shift _
    | PEnot _
    | PEop _
    | PEstruct _
    | PEunion _ 
    | PEcfunction _
    | PEmemberof _     
    | PEcall _ 
    | PElet _ 
    | PEif _ 
    | PEis_scalar _
    | PEis_integer _
    | PEis_signed _
    | PEis_unsigned _
    | PEare_compatible _
    | PEbmc_assume _ -> assert false
    ) >>= fun ssad_pe ->
    return (Pexpr(annots, bTy, ssad_pe))
end

(* ======= Convert to Z3 exprs ======= *)
module BmcZ3 = struct
  type z3_state = {
    (* Builds expr_map and case_guard_map *)
    expr_map : (string, Expr.expr) Pmap.map;
    case_guard_map: (string, Expr.expr list) Pmap.map;

    file              : unit typed_file;

    (* REQUIRED *)
    sym_table_map : (string, (sym_ty, Expr.expr) Pmap.map) Pmap.map;

    (* PEcall; PEimpl; *)
    inline_pexpr_map: (string, typed_pexpr) Pmap.map;

    (* Esave; Erun *)
    inline_expr_map : (string, unit typed_expr) Pmap.map;
  }

  include EffMonad(struct type state = z3_state end)

  let add_expr (uid: string) (expr: Expr.expr) : unit eff =
    get >>= fun st ->
    put {st with expr_map = Pmap.add uid expr st.expr_map}

  let add_guards (uid: string) (guards: Expr.expr list) : unit eff =
    get >>= fun st ->
    put {st with case_guard_map = Pmap.add uid guards st.case_guard_map}

  let get_file : (unit typed_file) eff =
    get >>= fun st ->
    return st.file

  let lookup_sym (uid: string) (sym: sym_ty) : Expr.expr eff =
    get >>= fun st ->
    match Pmap.lookup uid st.sym_table_map with
    | None -> failwith (sprintf "BmcZ3: Uid %s not found in sym_table_map" uid)
    | Some table ->
        begin
        match Pmap.lookup sym table with
        | None -> failwith (sprintf "BmcZ3: Sym %s not found in table"
                                    (symbol_to_string sym))
        | Some expr -> return expr
        end

  let get_inline_pexpr (uid: string) : typed_pexpr eff =
    get >>= fun st ->
    match Pmap.lookup uid st.inline_pexpr_map with
    | None ->
        failwith (sprintf "BmcZ3: Uid %s not found in inline_pexpr_map" uid)
    | Some pe ->  return pe

  let get_inline_expr (uid: string) : (unit typed_expr) eff =
    get >>= fun st ->
    match Pmap.lookup uid st.inline_expr_map with
    | None ->
        failwith (sprintf "BmcZ3: Uid %s not found in inline_expr_map" uid)
    | Some pe ->  return pe
end

let rec pexpr_to_z3 (Pexpr (annots, bTy, pe): typed_pexpr)
                    : Expr.expr BmcZ3.eff =
  let (>>=) = BmcZ3.bind in
  let (>>) = BmcZ3.(>>) in
  let return = BmcZ3.return in
  let uid = get_uid_or_fail annots in
  (match pe with
  | PEsym sym ->
      BmcZ3.lookup_sym uid sym
  | PEimpl _ ->
      BmcZ3.get_inline_pexpr uid >>= fun inline_pe ->
      pexpr_to_z3 inline_pe
  | PEval cval ->
      return (value_to_z3 cval)
  | PEconstrained _ -> assert false
  | PEundef _ ->
      let sort = cbt_to_z3 bTy in
      return (mk_fresh_const "undef" sort)
  | PEerror _ ->
      let sort = cbt_to_z3 bTy in
      return (mk_fresh_const "error" sort)
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
      BmcZ3.mapM pexpr_to_z3 pes >>= fun z3s_pe ->
      return (ctor_to_z3 ctor z3s_pe (Some bTy))
  | PEcase (pe, cases) ->
      assert (List.length cases > 0);
      pexpr_to_z3 pe                              >>= fun z3_pe ->
      BmcZ3.mapM pexpr_to_z3 (List.map snd cases) >>= fun z3s_cases_pe ->
      let (_,guards) = compute_case_guards (List.map fst cases) z3_pe in
      BmcZ3.add_guards uid guards >>
      return (mk_guarded_ite z3s_cases_pe guards)
  | PEarray_shift (ptr, ty, index) ->
      (* TODO: do properly *)
      pexpr_to_z3 ptr   >>= fun z3_ptr ->
      pexpr_to_z3 index >>= fun z3_index ->
      BmcZ3.get_file    >>= fun file ->
      let ty_size = bmcz3sort_size (ctype_to_bmcz3sort ty file) in
      let shift_size = binop_to_z3 OpMul z3_index (int_to_z3 ty_size) in
      let addr = PointerSort.get_addr z3_ptr in
      return (PointerSort.mk_ptr (AddressSort.shift_index_by_n addr shift_size))
  | PEmember_shift (ptr, sym, member) ->
      pexpr_to_z3 ptr >>= fun z3_ptr ->
      BmcZ3.get_file  >>= fun file ->
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
          let addr = PointerSort.get_addr z3_ptr in
          let new_addr =
            AddressSort.shift_index_by_n addr (int_to_z3 shift_size) in
          return (PointerSort.mk_ptr new_addr)
      | _ -> assert false
      end
  | PEnot pe ->
      pexpr_to_z3 pe >>= fun z3_pe ->
      return (mk_not z3_pe)
  | PEop (binop, pe1, pe2) ->
      pexpr_to_z3 pe1 >>= fun z3_pe1 ->
      pexpr_to_z3 pe2 >>= fun z3_pe2 ->
      return (binop_to_z3 binop z3_pe1 z3_pe2)
  | PEstruct _    -> assert false
  | PEunion _     -> assert false
  | PEcfunction _ -> assert false
  | PEmemberof _  -> assert false
  | PEcall (name, pes) ->
      BmcZ3.mapM pexpr_to_z3 pes >>= fun _ ->
      BmcZ3.get_inline_pexpr uid >>= fun inline_pe ->
      pexpr_to_z3 inline_pe
  | PElet (_, pe1, pe2) ->
      pexpr_to_z3 pe1 >>= fun _ ->
      pexpr_to_z3 pe2
  | PEif (cond, pe1, pe2) ->
      pexpr_to_z3 cond >>= fun z3_cond ->
      pexpr_to_z3 pe1  >>= fun z3_pe1 ->
      pexpr_to_z3 pe2  >>= fun z3_pe2 ->
      return (mk_ite z3_cond z3_pe1 z3_pe2)
  | PEis_scalar _  -> assert false
  | PEis_integer _ -> assert false
  | PEis_signed _  -> assert false
  | PEis_unsigned (Pexpr(_, BTy_ctype, PEval (Vctype ctype))) ->
      return (Pmap.find ctype ImplFunctions.is_unsigned_map)
  | PEis_unsigned _    -> assert false
  | PEare_compatible _ -> assert false
  | PEbmc_assume pe ->
      pexpr_to_z3 pe >>= fun _ ->
      return UnitSort.mk_unit
  ) >>= fun ret ->
  BmcZ3.add_expr uid ret >>
  return ret

let rec expr_to_z3 (Expr(annots, expr_) : unit typed_expr)
                   : Expr.expr BmcZ3.eff =
  let (>>=) = BmcZ3.bind in
  let (>>) = BmcZ3.(>>) in
  let return = BmcZ3.return in
  let uid = get_uid_or_fail annots in
  (match expr_ with
  | Epure pe ->
      pexpr_to_z3 pe
  | Ememop (PtrValidForDeref, [ptr]) ->
      pexpr_to_z3 ptr >>= fun z3_ptr ->
      let addr = PointerSort.get_addr z3_ptr in
      let range_assert = AddressSort.valid_index_range addr in
      return (mk_and [mk_not (PointerSort.is_null z3_ptr); range_assert])
  | Ememop (PtrEq, [p1;p2]) ->
      pexpr_to_z3 p1 >>= fun z3_p1 ->
      pexpr_to_z3 p2 >>= fun z3_p2 ->
      return (mk_eq z3_p1 z3_p2)
  | Ememop _ -> assert false
  | Eaction _ ->
      assert false
  | Ecase (pe, cases) ->
      assert false
      (*
      pexpr_to_z3 pe >>= fun z3_pe ->
      let guards = compute_case_guards (List.map fst cases) z3_pe in
      *)
  | Elet _ -> assert false
  | Eif _  -> assert false
  | Eskip ->
      return UnitSort.mk_unit
  | Eccall _ -> assert false
  | Eproc _  -> assert false
  | Eunseq _ -> assert false
  | Ewseq _  -> assert false
  | Esseq _  -> assert false
  | Easeq _  -> assert false
  | Eindet _ -> assert false
  | Ebound _ -> assert false
  | End _    -> assert false
  | Esave _  -> assert false
  | Erun _   -> assert false
  | Epar _   -> assert false
  | Ewait _  -> assert false
  ) >>= fun ret ->
  BmcZ3.add_expr uid ret >>
  return ret

(* ======= Compute verification conditions ======= *)

module BmcVC = struct
  type vc_state = {
    (* Map from uid to guard expr *)
    expr_map: (string, Expr.expr) Pmap.map;

    (* PEcase, Ecase, End *)
    case_guard_map: (string, Expr.expr list) Pmap.map;

    drop_cont_map: (string, Expr.expr) Pmap.map;

    (* PEcall; PEimpl; *)
    inline_pexpr_map: (string, typed_pexpr) Pmap.map;

    (* Esave; Erun *)
    inline_expr_map : (string, unit typed_expr) Pmap.map;
  }
  include EffMonad(struct type state = vc_state end)

  let get_expr (uid: string): (Expr.expr) eff =
    get >>= fun st ->
    match Pmap.lookup uid st.expr_map with
    | None -> failwith (sprintf "BmcVC: Uid %s not found in expr_map" uid)
    | Some expr -> return expr

  let get_case_guards (uid: string) : (Expr.expr list) eff =
    get >>= fun st ->
    match Pmap.lookup uid st.case_guard_map with
    | None -> failwith (sprintf "BmcVC: Uid %s not found in case_guard_map" uid)
    | Some exprs -> return exprs

  let get_drop_cont (uid: string) : Expr.expr eff =
    get >>= fun st ->
    match Pmap.lookup uid st.drop_cont_map with
    | None -> failwith (sprintf "BmcVC: Uid %s not found in drop_cont_map" uid)
    | Some expr -> return expr

  let get_inline_pexpr (uid: string) : typed_pexpr eff =
    get >>= fun st ->
    match Pmap.lookup uid st.inline_pexpr_map with
    | None ->
        failwith (sprintf "BmcVC: Uid %s not found in inline_pexpr_map" uid)
    | Some pe ->  return pe

  let get_inline_expr (uid: string) : (unit typed_expr) eff =
    get >>= fun st ->
    match Pmap.lookup uid st.inline_expr_map with
    | None ->
        failwith (sprintf "BmcVC: Uid %s not found in inline_expr_map" uid)
    | Some pe ->  return pe


end

type vc_debug =
  | VCDebugUndef of Location_ocaml.t * Undefined.undefined_behaviour
  | VcDebugStr of string

type vc = Expr.expr * vc_debug

let guard_vc (guard: Expr.expr) ((vc_expr, dbg): vc) : vc =
  (mk_implies guard vc_expr, dbg)

let map2_inner (f: 'x->'y->'z) (xs: 'x list) (yss: ('y list) list) : 'z list =
  List.concat (List.map2 (fun x ys -> List.map (f x) ys) xs yss)


let rec vcs_pexpr (Pexpr (annots, bTy, pe): typed_pexpr) :
                  (vc list) BmcVC.eff =
  let (>>=) = BmcVC.bind in
  let return = BmcVC.return in
  let uid = get_uid_or_fail annots in
  match pe with
  | PEsym _           -> return []
  | PEimpl _          ->
     BmcVC.get_inline_pexpr uid >>= fun inline_pe ->
     vcs_pexpr inline_pe
  | PEval _           -> return []
  | PEconstrained _   -> assert false
  | PEundef (loc, ub) -> return [(mk_false, VCDebugUndef (loc,ub))]
  | PEerror (str, _)  -> return [(mk_false, VcDebugStr (uid ^ "_" ^ str))]
  | PEctor (ctor, pelist) ->
      BmcVC.mapM vcs_pexpr pelist >>= fun vcss ->
      return (List.concat vcss)
  | PEcase (pe0, cases) ->
      (* TODO: double check this *)
      BmcVC.mapM (fun (_, pe) -> vcs_pexpr pe) cases >>= fun vcss_cases ->
      BmcVC.get_case_guards uid                      >>= fun guards ->
      vcs_pexpr pe0                                  >>= fun vcs_pe0 ->
      assert (List.length vcss_cases == List.length guards);
      let dbg = VcDebugStr (uid ^ "_PEcase_caseMatch") in
      return ((mk_or guards, dbg) ::
              vcs_pe0 @ (map2_inner guard_vc guards vcss_cases))
  | PEarray_shift (ptr, ty, index) ->
      BmcVC.get_expr (get_uid_pexpr ptr) >>= fun ptr_z3 ->
      vcs_pexpr ptr                      >>= fun vcs_ptr ->
      vcs_pexpr index                    >>= fun vcs_index ->
      let dbg = VcDebugStr (uid ^ "_PEarray_shift_notNull") in
      return ((mk_not (PointerSort.is_null ptr_z3), dbg)
              :: (vcs_ptr @ vcs_index))
  | PEmember_shift (ptr, sym, member) ->
      BmcVC.get_expr (get_uid_pexpr ptr) >>= fun ptr_z3 ->
      vcs_pexpr ptr                      >>= fun vcs_ptr ->
      let dbg = VcDebugStr (uid ^ "_PEmember_shift_notNull") in
      return ((mk_not (PointerSort.is_null ptr_z3), dbg) :: vcs_ptr)
  | PEnot pe         -> vcs_pexpr pe
  | PEop (_, pe1, pe2) ->
      vcs_pexpr pe1 >>= fun vc1s ->
      vcs_pexpr pe2 >>= fun vc2s ->
      return (vc1s @ vc2s)
  | PEstruct _       -> assert false
  | PEunion _        -> assert false
  | PEcfunction pe   -> vcs_pexpr pe
  | PEmemberof _     -> assert false
  | PEcall (_, pes) ->
      BmcVC.mapM vcs_pexpr pes    >>= fun vcss_pes ->
      BmcVC.get_inline_pexpr uid  >>= fun inline_pe ->
      vcs_pexpr inline_pe         >>= fun vcs_inline ->
      return (vcs_inline @ (List.concat vcss_pes))
  | PElet (pat, pe1, pe2) ->
      vcs_pexpr pe1 >>= fun vc1s ->
      vcs_pexpr pe2 >>= fun vc2s ->
      return (vc1s @ vc2s)
  | PEif (cond, pe1, pe2) ->
      BmcVC.get_expr (get_uid_pexpr cond)  >>= fun guard_z3 ->
      vcs_pexpr pe1                        >>= fun vc1s ->
      vcs_pexpr pe2                        >>= fun vc2s ->
      return ((List.map (guard_vc guard_z3) vc1s) @
              (List.map (guard_vc (mk_not guard_z3)) vc2s))
  | PEis_scalar pe   -> vcs_pexpr pe
  | PEis_integer pe  -> vcs_pexpr pe
  | PEis_signed pe   -> vcs_pexpr pe
  | PEis_unsigned pe -> vcs_pexpr pe
  | PEare_compatible (pe1,pe2) ->
      vcs_pexpr pe1 >>= fun vc1s ->
      vcs_pexpr pe2 >>= fun vc2s ->
      return (vc1s @ vc2s)
  | PEbmc_assume pe -> vcs_pexpr pe

let rec vcs_paction uid (Paction (_, Action(_, _, action_)) : unit typed_paction)
                    : (vc list) BmcVC.eff =
  let (>>=) = BmcVC.bind in
  let return = BmcVC.return in

  match action_ with
  | Create (pe1, pe2, _) ->
      vcs_pexpr pe1 >>= fun vc1s ->
      vcs_pexpr pe2 >>= fun vc2s ->
      return (vc1s @ vc2s)
  | CreateReadOnly _  -> assert false
  | Alloc0 _          -> assert false
  | Kill (_, pe) ->
      (* TODO: Kill ignored *)
      vcs_pexpr pe
  | Store0 (_, ty, (Pexpr(_,_, PEsym sym) as ptr), wval, memorder) ->
      (* TODO: Where should we check whether the ptr is valid? *)
      let valid_memorder =
        mk_bool (not (memorder = Acquire || memorder = Acq_rel)) in
      vcs_pexpr ty                       >>= fun vcs_ty ->
      vcs_pexpr wval                     >>= fun vcs_wval ->
      BmcVC.get_expr (get_uid_pexpr ptr) >>= fun ptr_z3 ->
      return (  (valid_memorder, VcDebugStr (uid ^ "_Store_memorder"))
              ::(mk_not (PointerSort.is_null ptr_z3),
                 VcDebugStr (uid ^ "_Store_null"))
              ::vcs_ty @ vcs_wval)
  | Store0 _          -> assert false
  | Load0 (ty, (Pexpr(_,_, PEsym _) as ptr), memorder) ->
      let valid_memorder =
            mk_bool (not (memorder = Release || memorder = Acq_rel)) in
      vcs_pexpr ty                       >>= fun vcs_ty ->
      BmcVC.get_expr (get_uid_pexpr ptr) >>= fun ptr_z3 ->
      return ((valid_memorder, VcDebugStr (uid ^ "_Load_memorder"))
              ::(mk_not (PointerSort.is_null ptr_z3),
                 VcDebugStr (uid ^ "_Load_null"))
              :: vcs_ty)
  | Load0 _ -> assert false
  | RMW0 _  -> assert false
  | Fence0 _ -> return []
  | CompareExchangeStrong _ -> assert false
  | LinuxFence _ -> return []
  | LinuxStore _ -> assert false
  | LinuxLoad _  -> assert false
  | LinuxRMW _ -> assert false

let rec vcs_expr (Expr(annots, expr_) : unit typed_expr)
                 : (vc list) BmcVC.eff =
  let (>>=) = BmcVC.bind in
  let return = BmcVC.return in
  let uid = get_uid_or_fail annots in
  match expr_ with
  | Epure pe      -> vcs_pexpr pe
  | Ememop (memop, pes) ->
      BmcVC.mapM vcs_pexpr pes >>= fun vcss_pes ->
      begin match memop with
      | PtrValidForDeref | PtrEq -> return (List.concat vcss_pes)
      | _ -> assert false (* Unimplemented *)
      end
  | Eaction paction ->
      vcs_paction uid paction
  | Ecase (pe, cases) ->
      BmcVC.mapM (fun (_, e) -> vcs_expr e) cases >>= fun vcss_cases ->
      BmcVC.get_case_guards uid                   >>= fun guards ->
      vcs_pexpr pe                                >>= fun vcs_pe ->
      let dbg = VcDebugStr (uid ^ "_Ecase_caseMatch") in
      return ((mk_or guards, dbg) ::
              vcs_pe @ (map2_inner guard_vc guards vcss_cases))
  | Elet _        -> assert false
  | Eif (cond, e1, e2) ->
      vcs_pexpr cond >>= fun vcs_cond ->
      vcs_expr e1    >>= fun vcs_e1 ->
      vcs_expr e2    >>= fun vcs_e2 ->
      BmcVC.get_expr (get_uid_pexpr cond) >>= fun cond_z3 ->
      return (vcs_cond @ (List.map (guard_vc cond_z3) vcs_e1)
                       @ (List.map (guard_vc (mk_not cond_z3)) vcs_e2))
  | Eskip         -> return []
  | Eccall _      -> assert false
  | Eproc _       -> assert false
  | Eunseq es ->
      BmcVC.mapM vcs_expr es >>= fun vcss_es ->
      return (List.concat vcss_es)
  | Ewseq (pat, e1, e2)
  | Esseq (pat, e1, e2) ->
      vcs_expr e1 >>= fun vcs_e1 ->
      vcs_expr e2 >>= fun vcs_e2 ->
      BmcVC.get_drop_cont (get_uid_expr e1) >>= fun e1_drop_cont ->
      return (vcs_e1 @ (List.map (guard_vc e1_drop_cont) vcs_e2))
  | Easeq _       -> assert false
  | Eindet _      -> assert false
  | Ebound (_, e) -> vcs_expr e
  | End es ->
      BmcVC.get_case_guards uid >>= fun guards ->
      BmcVC.mapM vcs_expr es    >>= fun vcss_es ->
      return (map2_inner guard_vc guards vcss_es)
  | Esave _       (* fall through *)
  | Erun _        ->
      BmcVC.get_inline_expr uid >>= fun inline_expr ->
      vcs_expr inline_expr
  | Epar es ->
      BmcVC.mapM vcs_expr es >>= fun vcss_es ->
      return (List.concat vcss_es)
  | Ewait _       -> assert false
