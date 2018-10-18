open Bmc_common
open Bmc_sorts
open Bmc_utils

open Core
open Ocaml_mem
open Printf
open Z3

module type State = sig type state end

module EffMonad (M: State) = struct
  type state = M.state

  type 'a eff = Eff of (state -> 'a * state)

  let return (a: 't) : 't eff = Eff (fun st -> (a,st))

  let bind ((Eff ma): 'a eff) (f: 'a -> 'b eff) : 'b eff =
    Eff begin
      fun st ->
        let (a, st') = ma st in
        let Eff mb = f a in
        mb st'
    end

  let (>>=) = bind

  let (>>) m m' = m >>= fun _ -> m'

  let run : state -> 'a eff -> 'a * state =
    fun st (Eff ma) -> ma st

  let sequence ms =
    List.fold_right (
      fun m m' ->
      m  >>= fun x  ->
      m' >>= fun xs ->
      return (x :: xs)
    ) ms (return [])

  let sequence_ ms = List.fold_right (>>) ms (return ())
  let mapM  f ms = sequence (List.map f ms)
  let mapMi f ms = sequence (List.mapi f ms)
  let mapM2 f ms1 ms2  = sequence (List.map2 f ms1 ms2)
  let mapM_ f ms = sequence_ (List.map f ms)
  let mapM2_ f ms1 ms2 = sequence_ (List.map2 f ms1 ms2)

  let get : state eff =
    Eff (fun st -> (st, st))

  let put (st' : state) : unit eff =
    Eff (fun _ -> ((), st'))
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
