(* monad fun *)
(* TODO: badly named *)
(* TODO: parametrize on monad *)
open Core
open Bmc_utils

module SSA = struct
  type kssa_state = {
    supply      : ksym_supply;
    sym_table   : (ksym, ksym) Pmap.map
  }

  type 'a eff = 
    Eff of (kssa_state -> 'a * kssa_state)
    
  let return (a : 't) : 't eff = Eff (fun st -> (a, st))

  let bind ((Eff ma) : 'a eff) (f : 'a -> 'b eff) : 'b eff =
    Eff begin
      fun st -> 
        let (a, st') = ma st in
        let Eff mb = f a in
        mb st' 
    end

  let (>>=) = bind

  let (>>) m m' = bind m (fun _ -> bind m' (fun x' -> return x'))

  let run : kssa_state -> 'a eff -> 'a * kssa_state  = 
    fun st (Eff(ma)) -> ma st

  let sequence ms =
    List.fold_right 
      ( fun m m' ->
        m  >>= fun x ->
        m' >>= fun xs ->
        return (x :: xs)
     ) ms (return [])

  let sequence_ ms = List.fold_right (>>) ms (return ())
  let mapM f ms = sequence (List.map f ms)
  let mapM_ f ms = sequence_ (List.map f ms)

  let get : kssa_state eff =
    Eff (fun st -> (st, st))

  let put (st' : kssa_state) : unit eff =
    Eff (fun _ -> ((), st'))

  let lookup_sym sym : (ksym option) eff = 
    get >>= fun st -> return (Pmap.lookup sym st.sym_table)

  let add_to_sym_table sym1 sym2 : unit eff =
    get >>= fun st -> 
      put ({st with sym_table = Pmap.add sym1 sym2 st.sym_table})

  let get_supply : ksym_supply eff =
    get >>= fun st -> return st.supply

  let update_supply new_supply : unit eff =
    get >>= fun st ->
      put ({st with supply = new_supply})

  let get_fresh_sym (str: string option) : ksym eff =
    get >>= fun st -> 
    return (Sym.fresh_fancy str st.supply) >>= fun (new_sym, new_supply) ->
    update_supply new_supply >>= fun () ->
    return new_sym
end

let rename_sym (Symbol(_, stropt) as sym: ksym) : ksym SSA.eff =
  let (>>=) = SSA.bind in
  SSA.get_fresh_sym stropt >>= fun new_sym ->
  SSA.add_to_sym_table sym new_sym >>= fun () ->
  SSA.return new_sym

let rec ssa_pattern (pat : ('bTy, Symbol.sym) generic_pattern ) 
        : (('bTy, Symbol.sym) generic_pattern) SSA.eff =
  let (>>=) = SSA.bind in
  match pat with
  | CaseBase(Some sym, typ) ->
      rename_sym sym >>= fun new_sym ->
      SSA.return (CaseBase(Some new_sym, typ))
  | CaseBase(None, _) -> 
      SSA.return pat
  | CaseCtor(ctor, patList) -> 
      SSA.mapM ssa_pattern patList >>= fun retList ->
      SSA.return (CaseCtor(ctor, retList)) 

let rec ssa_pexpr (Pexpr(annot, ty, pexpr_))
      : (('bTy, Symbol.sym) generic_pexpr) SSA.eff = 
  let (>>=) = SSA.bind in
  (match pexpr_ with
  | PEsym sym -> 
      SSA.lookup_sym sym >>= fun ret_sym ->
        begin
      match ret_sym with
      | None -> assert false
      | Some x -> 
          SSA.return (PEsym x)
        end
  | PEimpl _  -> assert false
  | PEval _   -> 
      SSA.return pexpr_ 
  | PEconstrained _ -> assert false
  | PEundef _ -> 
      SSA.return pexpr_
  | PEerror _ -> 
      SSA.return pexpr_
  | PEctor (ctor, pelist) ->
      SSA.mapM (fun pe -> ssa_pexpr pe) pelist >>= fun retlist ->
      SSA.return (PEctor(ctor, retlist))
  | PEcase (pe, caselist) ->
      ssa_pexpr pe >>= fun ret_pe ->
      (* TODO: this is not really correct. 
       * we actually want different sym tables but we can get away
       * with this for renaming only...
       *)
      SSA.mapM (fun (pat, pe) -> 
                  ssa_pattern pat >>= fun pat' ->
                  ssa_pexpr pe >>= fun pe' ->
                  SSA.return (pat', pe')) caselist  >>= fun retlist ->
      SSA.return (PEcase(ret_pe, retlist))
  | PEarray_shift _
  | PEmember_shift _ ->
      assert false
  | PEnot pe ->
      ssa_pexpr pe >>= fun ret ->
      SSA.return (PEnot(ret))
  | PEop (binop, pe1, pe2) ->
      ssa_pexpr pe1 >>= fun ret_pe1 ->
      ssa_pexpr pe2 >>= fun ret_pe2 ->
      SSA.return (PEop(binop, ret_pe1, ret_pe2))
  | PEstruct _
  | PEunion _ ->
      assert false
  | PEcall (name, arglist) ->
      SSA.mapM ssa_pexpr arglist >>= fun retList ->
      SSA.return (PEcall(name, retList))
  | PElet (pat, pe1, pe2) ->
      ssa_pattern pat >>= fun ret_pat ->
      ssa_pexpr pe1 >>= fun ret_pe1 ->
      ssa_pexpr pe2 >>= fun ret_pe2 ->
      SSA.return (PElet(ret_pat, ret_pe1, ret_pe2))
  | PEif (pe1, pe2, pe3) ->
      (* TODO: not correct. state needs to branch somehow *)
      ssa_pexpr pe1 >>= fun ret_pe1 ->
      ssa_pexpr pe2 >>= fun ret_pe2 ->
      ssa_pexpr pe3 >>= fun ret_pe3 ->
      SSA.return (PEif(ret_pe1, ret_pe2, ret_pe3))
  | PEis_scalar pe ->
      ssa_pexpr pe >>= fun ret_pe ->
      SSA.return (PEis_scalar ret_pe)
  | PEis_integer pe ->
      ssa_pexpr pe >>= fun ret_pe ->
      SSA.return (PEis_integer ret_pe)
  | PEis_signed pe -> 
      ssa_pexpr pe >>= fun ret_pe ->
      SSA.return (PEis_signed ret_pe)
  | PEis_unsigned pe ->
      ssa_pexpr pe >>= fun ret_pe ->
      SSA.return (PEis_unsigned ret_pe)
  (*
  | PEstd (str, pe) ->
      ssa_pexpr pe >>= fun ret_pe ->
      SSA.return (PEstd(str, ret_pe))
  *)
  ) >>= fun ret_ -> SSA.return (Pexpr(annot,ty, ret_))
  
(* NOTE: Lots of assumptions about what core generated from C looks like *)  
let rec ssa_expr (Expr(annot, expr_)) 
                  : (('a, 'bTy, Symbol.sym) generic_expr) SSA.eff =
  let (>>=) = SSA.bind in
  (match expr_ with
  | Epure pe ->
      ssa_pexpr pe >>= fun ret ->
      SSA.return (Epure ret)
  | Ememop (PtrValidForDeref, pelist) ->
      SSA.mapM ssa_pexpr pelist >>= fun retlist ->
      SSA.return (Ememop(PtrValidForDeref, retlist))
  | Ememop _ ->
      assert false
  | Eaction (Paction(p, Action(loc, a, Create _))) ->
      SSA.return expr_
  | Eaction (Paction(p, Action(loc, a, Store0 (pe1, ptr, value, mem)))) ->
      ssa_pexpr ptr >>= fun ret_ptr ->
      ssa_pexpr value >>= fun ret_value ->
      SSA.return (Eaction(Paction(p, Action(loc, a, 
                      Store0(pe1, ret_ptr, ret_value, mem)))))
  | Eaction (Paction(p, Action(loc, a, Load0 (ty, ptr, b)))) ->
      ssa_pexpr ptr >>= fun ret ->
      (* TODO... move paction into separate function *)
      SSA.return (Eaction(Paction(p, Action(loc, a, Load0 (ty, ret, b)))))
  | Eaction (Paction(p, Action(loc, a, Kill pe))) ->
      ssa_pexpr pe >>= fun ret ->
      SSA.return (Eaction (Paction(p, Action(loc, a, Kill ret))))
  | Eaction _ ->
      assert false
  | Ecase (pe, patlist) ->  
      ssa_pexpr pe >>= fun ret_pe ->
      (* TODO: this is not really correct. Branching state
       *)
      SSA.mapM (fun (pat, e) -> 
                  ssa_pattern pat >>= fun pat' ->
                  ssa_expr e >>= fun e' ->
                  SSA.return (pat', e')) patlist  >>= fun retlist ->
      SSA.return (Ecase(ret_pe, retlist))
  | Eskip -> 
      SSA.return expr_
  | Eproc (a, name, pelist) -> 
      SSA.mapM (fun p -> ssa_pexpr p) pelist >>= fun retList ->
      SSA.return (Eproc(a,name, retList))
  | Eccall (a, pe, arglist) ->
      ssa_pexpr pe >>= fun ret_pe ->
      SSA.mapM ssa_pexpr arglist >>= fun retlist ->
      SSA.return (Eccall(a, ret_pe, retlist))
  | Eunseq elist -> 
      SSA.mapM (fun e -> ssa_expr e) elist >>= fun retlist ->
      SSA.return (Eunseq retlist) 
  | Eindet _ -> assert false
  | Ebound (n, e1) ->
      ssa_expr e1 >>= fun ret_e1 ->
      SSA.return (Ebound(n, ret_e1))
  | End elist ->
      SSA.mapM ssa_expr elist >>= fun retlist ->
      SSA.return (End retlist) 
  | Erun (a,sym, pelist) ->
      SSA.mapM ssa_pexpr pelist >>= fun retlist ->
      SSA.return (Erun(a,sym, retlist)) 
  | Epar (elist) ->
      SSA.mapM ssa_expr elist >>= fun retlist ->
      SSA.return (Epar(retlist))
  | Ewait _ -> assert false
  | Eif (pe, e1, e2) ->
      ssa_pexpr pe >>= fun ret_pe ->
      ssa_expr e1 >>= fun ret_e1 ->
      ssa_expr e2 >>= fun ret_e2 ->
      SSA.return (Eif(ret_pe, ret_e1, ret_e2))
  | Elet _  -> 
      assert false
  | Easeq _ -> assert false
  | Ewseq (pat, e1, e2) ->
      ssa_pattern pat >>= fun ret_pat ->
      ssa_expr e1 >>= fun ret_e1 ->
      ssa_expr e2 >>= fun ret_e2 ->
      SSA.return (Ewseq (ret_pat, ret_e1, ret_e2))

  | Esseq (pat, e1, e2) ->
      ssa_pattern pat >>= fun ret_pat ->
      ssa_expr e1 >>= fun ret_e1 ->
      ssa_expr e2 >>= fun ret_e2 ->
      SSA.return (Esseq (ret_pat, ret_e1, ret_e2))
  | Esave (label, letlist, e)  ->
      SSA.mapM (fun (sym, (ty, pe)) -> 
        match sym with
        | Sym.Symbol(_, stropt) ->
          SSA.get_fresh_sym stropt >>= fun new_sym ->
          SSA.add_to_sym_table sym new_sym >>= fun () ->
          ssa_pexpr pe >>= fun ret_pe ->
          SSA.return (new_sym, (ty, ret_pe))) letlist >>= fun retlist ->
      ssa_expr e >>= fun ret_e ->
      SSA.return (Esave(label, retlist, ret_e))
  ) >>= fun ret_ -> SSA.return (Expr(annot,ret_))

let ssa_fn (fn) 
           : (('bTy, 'a) generic_fun_map_decl) SSA.eff =
  let (>>=) = SSA.bind in
  match fn with
  | Proc(ty, params, e) ->
      SSA.mapM (fun (sym, ty) ->
        rename_sym sym >>= fun ret_sym ->
        SSA.return (ret_sym, ty)) params >>= fun ret_params ->
      ssa_expr e >>= fun ret_e ->
      SSA.get >>= fun st ->
      (
      print_endline "--RENAME STUFF--";
      Pmap.iter (fun k v -> 
        Printf.printf "%s -> %s\n" (symbol_to_string k) (symbol_to_string v)) 
        st.sym_table;
      SSA.return (Proc(ty, ret_params, ret_e))
      )
  | Fun(ty, params, pe) -> 
      SSA.mapM (fun (sym, ty) -> 
        rename_sym sym >>= fun ret_sym ->
        SSA.return (ret_sym, ty)) params >>= fun ret_params -> 
      ssa_pexpr pe >>= fun ret_pe ->
      SSA.return (Fun(ty, ret_params, ret_pe))
  | _ ->
      assert false


let ssa_file (file) (sym_supply: ksym_supply) =
  let (>>=) = SSA.bind in
  let table_with_globals = List.fold_left (fun table (sym, _, _) ->
    Pmap.add sym sym table) (Pmap.empty sym_cmp) file.globs in

  let initial_state : SSA.kssa_state =  
    ({supply = sym_supply;
      sym_table = table_with_globals
    }) in

  let to_run = SSA.mapM (fun (sym, fn) ->
    ssa_fn fn >>= fun ret_fn ->
    SSA.return (sym, ret_fn)) (Pmap.bindings_list file.funs) in

  let (retMap, st) = SSA.run initial_state to_run in
  let new_fun_map = List.fold_left (fun pmap (sym, fn) ->
    Pmap.add sym fn pmap) (Pmap.empty sym_cmp) retMap in
  {file with funs = new_fun_map}, st.supply


  (*
  match file.main with
  | None -> 
      print_string "ERROR: file does not have a main\n";
      assert false
  | Some main_sym ->
        (*
      let (new_globals, st) = SSA.run initial_state 
        (SSA.mapM (fun (sym, typ, expr) ->
          rename_sym sym >>= fun ret_sym ->
          ssa_expr expr >>= fun ret ->
          SSA.return (ret_sym , typ, ret)) file.globs) in
      *)

      begin
      match Pmap.lookup main_sym file.funs with
      | Some f ->
          let (ret, st) =
            SSA.run initial_state (ssa_fn f) in
          let new_fun_map = 
            Pmap.add main_sym ret file.funs in
          {file with funs = new_fun_map}, st.supply
            
          (*
          let to_run = 
            SSA.mapM_ (fun (sym, ty) -> 
              SSA.add_to_sym_table sym sym) params 
            >>= fun () -> ssa_expr e in

          let (ret, st) = SSA.run st to_run in
          print_endline "--RENAME STUFF--";
          Pmap.iter (fun k v -> Printf.printf "%s -> %s\n" (symbol_to_string k) (symbol_to_string v)) st.sym_table;
          let new_fun_map = 
            Pmap.add main_sym ((Proc(ty, params, ret))) file.funs
          in
            {file with funs = new_fun_map;
                       globs = new_globals}, st.supply
                       *)
      (*
      | Some (Fun(ty, params, pe)) ->
          print_endline "TODO: switch to ssa_fn";
          let to_run = 
            SSA.mapM_ (fun (sym, ty) -> 
              SSA.add_to_sym_table sym sym) params 
            >>= fun () -> ssa_pexpr pe in

          let (ret, st) = SSA.run initial_state to_run in
          let new_fun_map = 
            Pmap.add main_sym ((Fun(ty, params, ret))) file.funs
          in
            {file with funs = new_fun_map
                       (*globs = new_globals *)}, st.supply
      *)
      | _ -> assert false
      end
  *)
