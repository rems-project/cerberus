open Bmc_utils
open Core

(* Context-insensitive analysis... 
 * Assumes variables in SSA form
 * Could easily be smarter if done at same time as conversion to Z3
 *)

type k_address = int

module AddressSet = Set.Make( 
  struct
    let compare = Pervasives.compare
    type t = k_address
  end)

type kptr_map = (ksym, AddressSet.t) Pmap.map

(* TODO: stop using references... :D *)
type kanalysis_state = {
  (* Map from ptr symbol to set of addresses it may alias with *)
  ptr_map : kptr_map ref;

  (* ctr to generate unique address *)
  addr_gen : k_address ref;

  (* set of all addresses: not used really *)
  addr_set : AddressSet.t ref;

  (* Map from addresses (that store C pointers) to
   * addresses that can be stored *)
  addr_map : ((k_address, AddressSet.t) Pmap.map) ref
}

let string_of_address_set set =
  AddressSet.fold (fun v s -> (string_of_int v) ^ " " ^ s) set ""

let print_ptr_map (ptr_map : (ksym, AddressSet.t) Pmap.map) =
  Printf.printf "PtrMap:\n";
  Pmap.iter (fun k v -> 
    Printf.printf "%s -> [ %s]\n" 
        (symbol_to_string k) 
        (string_of_address_set v)
  ) ptr_map

let print_addr_map (addr_map : (k_address, AddressSet.t) Pmap.map) =
  Printf.printf "AddrMap:\n";
  Pmap.iter (fun k v -> 
    Printf.printf "@%s -> [ %s]\n" 
        (string_of_int k) 
        (string_of_address_set v)
  ) addr_map

let is_ptr_type (bTy: core_base_type) =
  match bTy with
  | BTy_object OTy_pointer -> true 
  | BTy_loaded OTy_pointer -> true
  | _ -> false

let is_ptr_ctype (pe : typed_pexpr) = 
  match pe with
  | Pexpr(BTy_ctype, PEval (Vctype (Pointer0 _))) -> true
  | _ -> false
      
let add_set (state: kanalysis_state)
            (sym : ksym)
            (set: AddressSet.t) =
  let new_set = (
    match Pmap.lookup sym (!(state.ptr_map)) with
    | None -> set
    | Some s -> AddressSet.union s set
  ) in
  state.ptr_map := Pmap.add sym new_set !(state.ptr_map)

(* TODO: very stupid right now with tuples... but easy to fix... *)
let rec alias_pattern (state: kanalysis_state)
                      (pat: typed_pattern)
                      (set: AddressSet.t) =
  match pat with
  | CaseBase(Some sym, typ) ->
      if is_ptr_type typ then
        add_set state sym set
      else ()
  | CaseBase(None, _) -> ()
  | CaseCtor(ctor, patList) ->
      List.iter (fun p -> alias_pattern state p set) patList



let rec analyse_pexpr (state: kanalysis_state)
                      (Pexpr(bTy, pexpr_) : typed_pexpr) =
  let ret = match pexpr_ with
    | PEsym sym -> 
        begin
          match Pmap.lookup sym (!(state.ptr_map)) with
          | None -> AddressSet.empty 
          | Some s -> s
        end 
    | PEimpl _  -> assert false
    | PEval _   -> AddressSet.empty
    | PEconstrained _ -> assert false
    | PEundef _ -> AddressSet.empty
    | PEerror _ -> AddressSet.empty
    | PEctor (_, pelist) ->
        List.fold_left (fun s pe -> 
          AddressSet.union s (analyse_pexpr state pe)) AddressSet.empty pelist 
    | PEcase (pe, caselist) ->
        let pe_set = analyse_pexpr state pe in
        List.iter (fun (pat1, _) -> alias_pattern state pat1 pe_set) caselist;
        List.fold_left (fun s (pat1, pe1) -> 
          let set1 = analyse_pexpr state pe1 in
          AddressSet.union s set1) AddressSet.empty caselist 
    | PEarray_shift _
    | PEmember_shift _ ->
        assert false
    | PEnot pe ->
        analyse_pexpr state pe
    | PEop (binop, pe1, pe2) ->
        AddressSet.union (analyse_pexpr state pe1) (analyse_pexpr state pe2)
    | PEstruct _
    | PEunion _ ->
        assert false
    | PEcall (Sym _, _) ->
        assert false
    | PEcall (_, arglist) ->
        List.fold_left (fun s pe -> 
          AddressSet.union s (analyse_pexpr state pe)) 
          AddressSet.empty arglist
    | PElet (pat, pe1, pe2) ->
        alias_pattern state pat (analyse_pexpr state pe1);
        analyse_pexpr state pe2
    | PEif (pe1, pe2, pe3) ->
        let _ = analyse_pexpr state pe1 in
        AddressSet.union (analyse_pexpr state pe2) (analyse_pexpr state pe3)
    | PEis_scalar pe (* fall through *)
    | PEis_integer pe (* fall through *)
    | PEis_signed pe (* fall through *)
    | PEis_unsigned pe (* fall through *)
    | PEstd (_, pe) ->
        analyse_pexpr state pe
  in ret 

let mk_new_addr (state: kanalysis_state) = 
  state.addr_gen := succ (!(state.addr_gen));
  !(state.addr_gen)

let rec analyse_expr (state: kanalysis_state)
                     (Expr(annot, expr_) : 'a typed_expr) =
  let ret = match expr_ with
  | Epure pe ->
      analyse_pexpr state pe
  | Ememop (PtrValidForDeref, _) ->
      AddressSet.empty
  | Ememop _ ->
      assert false
  | Eaction (Paction(_, Action(_, _, Create (_, ty, _)))) ->
      let new_addr = mk_new_addr state in
      state.addr_set := AddressSet.add new_addr !(state.addr_set);
      (if is_ptr_ctype ty then
        state.addr_map := Pmap.add new_addr AddressSet.empty !(state.addr_map)
      );

      AddressSet.singleton new_addr

  | Eaction (Paction(_, Action(_, _, Create _))) ->
      assert false
  | Eaction (Paction(_, Action(_, _, Store0 (ty, ptr, value, _)))) ->
      (if is_ptr_ctype ty then
        let locs = analyse_pexpr state ptr in
        let to_store = analyse_pexpr state value in

        assert (not (AddressSet.is_empty locs));
        assert (not (AddressSet.is_empty to_store));

        (* For each potential store location, add to_store to addr_map *)
        AddressSet.iter (fun loc -> 
          let old = (match Pmap.lookup loc !(state.addr_map) with
          | None -> assert false 
          | Some s -> s) in

          state.addr_map := Pmap.add loc (AddressSet.union old to_store) !(state.addr_map);
        ) locs
      ); 

      AddressSet.empty

  | Eaction (Paction(_, Action(_, _, Load0 (ty, ptr, _)))) ->
      if is_ptr_ctype ty then
        begin
          let locs = analyse_pexpr state ptr in
          assert (not (AddressSet.is_empty locs));

          (* Union all addr_map[loc] for loc in locs *)
          AddressSet.fold (fun loc ret ->
            match Pmap.lookup loc !(state.addr_map) with
            | None -> assert false
            | Some s -> AddressSet.union s ret
          ) locs AddressSet.empty
        end
      else
        AddressSet.empty

  | Eaction (Paction(_, Action(_, _, Kill _))) ->
      AddressSet.empty
  | Eaction _ ->
      assert false
  | Ecase (pe, patlist) ->  
      let pe_set = analyse_pexpr state pe in
      List.iter (fun (pat1, _) -> alias_pattern state pat1 pe_set) patlist;
      List.fold_left (fun s (pat1, e1) ->
        let set1 = analyse_expr state e1 in
        AddressSet.union s set1) AddressSet.empty patlist
  | Eskip -> 
      AddressSet.empty
  | Eproc _ -> assert false
  | Eccall _  -> assert false
  | Eunseq _ -> assert false
  | Eindet _ -> assert false
  | Ebound (_, e1) ->
      analyse_expr state e1
  | End elist ->
      List.fold_left (fun s e -> 
        AddressSet.union s (analyse_expr state e)) AddressSet.empty elist
  | Erun _ ->
      Printf.printf "TODO: Erun ignored\n";
      AddressSet.empty
  | Epar _
  | Ewait _ -> assert false
  | Eif (pe, e1, e2) ->
      let _ = analyse_pexpr state pe in
      AddressSet.union (analyse_expr state e1) (analyse_expr state e2)
  | Elet _  -> 
      assert false
  | Easeq _ -> assert false
  | Ewseq (pat, e1, e2)  (* fall through *)
  | Esseq (pat, e1, e2) ->
      alias_pattern state pat (analyse_expr state e1);
      analyse_expr state e2
  | Esave _  ->
      Printf.printf "TODO: Esave ignored\n";
      AddressSet.empty
  in 
    ret
