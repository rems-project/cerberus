module CF = Cerb_frontend
module IT = IndexTerms
module BT = BaseTypes
module LRT = LogicalReturnTypes
module Req = Request
module RT = ReturnTypes
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module IdSet = Set.Make (Id)
module Loc = Locations
module RI = ResourceInference
open IT
open TypeErrors
open Pp
module Mu = Mucore
module LC = LogicalConstraints
open Typing

open Effectful.Make (Typing)

(* some of this is informed by impl_mem *)

type mem_value = CF.Impl_mem.mem_value

type pointer_value = CF.Impl_mem.pointer_value

(*** pattern matching *********************************************************)

(* pattern-matches and binds *)
let rec check_and_match_pattern (Mu.Pattern (loc, _, bty, pattern)) it =
  match pattern with
  | CaseBase (o_s, _has_cbt) ->
    (match o_s with
     | Some s ->
       let@ () = add_a_value s it (loc, lazy (Sym.pp s)) in
       return [ s ]
     | None -> return [])
  | CaseCtor (constructor, pats) ->
    (match (constructor, pats) with
     | Cnil _item_cbt, [] ->
       let@ item_bt =
         match bty with
         | BT.List item_bt -> return item_bt
         | _ ->
           fail (fun _ -> { loc; msg = Mismatch { has = !^"list"; expect = BT.pp bty } })
       in
       let@ () = add_c loc (LC.T (eq__ it (nil_ ~item_bt loc) loc)) in
       return []
     | Ccons, [ p1; p2 ] ->
       let@ () = ensure_base_type loc ~expect:bty (List (Mu.bt_of_pattern p1)) in
       let@ () = ensure_base_type loc ~expect:bty (Mu.bt_of_pattern p2) in
       let item_bt = Mu.bt_of_pattern p1 in
       let@ a1 = check_and_match_pattern p1 (head_ ~item_bt it loc) in
       let@ a2 = check_and_match_pattern p2 (tail_ it loc) in
       let@ () = add_c loc (LC.T (ne_ (it, nil_ ~item_bt loc) loc)) in
       return (a1 @ a2)
     | Ctuple, pats ->
       let@ () =
         ensure_base_type loc ~expect:bty (Tuple (List.map Mu.bt_of_pattern pats))
       in
       let@ all_as =
         ListM.mapiM
           (fun i p ->
             let ith = Simplify.IndexTerms.tuple_nth_reduce it i (Mu.bt_of_pattern p) in
             check_and_match_pattern p ith)
           pats
       in
       return (List.concat all_as)
     | Carray, _ -> Cerb_debug.error "todo: array patterns"
     | _ -> assert false)


(*** pure value inference *****************************************************)

let check_computational_bound loc s =
  let@ is_bound = bound_a s in
  if is_bound then
    return ()
  else
    fail (fun _ -> { loc; msg = Unknown_variable s })


let unsupported loc doc =
  fail (fun _ -> { loc; msg = Unsupported (!^"unsupported" ^^^ doc) })


let check_ptrval (loc : Locations.t) ~(expect : BT.t) (ptrval : pointer_value) : IT.t m =
  let@ () = ensure_base_type loc ~expect BT.(Loc ()) in
  CF.Impl_mem.case_ptrval
    ptrval
    (fun ct ->
      let sct = Sctypes.of_ctype_unsafe loc ct in
      let@ () = WellTyped.WCT.is_ct loc sct in
      return (IT.null_ loc))
    (function
      | None ->
        (* FIXME(CHERI merge) *)
        (* we can now have invalid function pointer values (e.g. if someone touched the bytes in a wrong way) *)
        unsupported loc !^"invalid function pointer"
      | Some sym ->
        (* just to make sure it exists *)
        let@ _fun_loc, _, _ = get_fun_decl loc sym in
        (* the symbol of a function is the same as the symbol of its address *)
        let here = Locations.other __LOC__ in
        return (sym_ (sym, BT.(Loc ()), here)))
    (fun prov p ->
      let@ alloc_id =
        match prov with
        | Some id -> return id
        | None -> fail (fun _ -> { loc; msg = Empty_provenance })
      in
      return (pointer_ ~alloc_id ~addr:p loc))


let expect_must_be_map_bt loc ~expect =
  match expect with
  | BT.Map (index_bt, item_bt) -> return (index_bt, item_bt)
  | _ ->
    let msg = Mismatch { has = !^"array"; expect = BT.pp expect } in
    fail (fun _ -> { loc; msg })


let rec check_mem_value (loc : Locations.t) ~(expect : BT.t) (mem : mem_value) : IT.t m =
  CF.Impl_mem.case_mem_value
    mem
    (fun ct ->
      let@ () = WellTyped.WCT.is_ct loc (Sctypes.of_ctype_unsafe loc ct) in
      fail (fun _ -> { loc; msg = Unspecified ct }))
    (fun _ _ -> unsupported loc !^"infer_mem_value: concurrent read case")
    (fun ity iv ->
      let@ () = WellTyped.WCT.is_ct loc (Integer ity) in
      let bt = Memory.bt_of_sct (Integer ity) in
      let@ () = ensure_base_type loc ~expect bt in
      return (int_lit_ (Memory.int_of_ival iv) bt loc))
    (fun _ft _fv -> unsupported loc !^"floats")
    (fun ct ptrval ->
      (* TODO: do anything else with ct? *)
      let@ () = WellTyped.WCT.is_ct loc (Sctypes.of_ctype_unsafe loc ct) in
      check_ptrval loc ~expect ptrval)
    (fun mem_values ->
      let@ index_bt, item_bt = expect_must_be_map_bt loc ~expect in
      assert (Option.is_some (BT.is_bits_bt index_bt));
      let@ values = ListM.mapM (check_mem_value loc ~expect:item_bt) mem_values in
      return (make_array_ ~index_bt ~item_bt values loc))
    (fun tag mvals ->
      let@ () = WellTyped.WCT.is_ct loc (Struct tag) in
      let@ () = ensure_base_type loc ~expect (Struct tag) in
      let mvals =
        List.map (fun (id, ct, mv) -> (id, Sctypes.of_ctype_unsafe loc ct, mv)) mvals
      in
      check_struct loc tag mvals)
    (fun tag id mv -> check_union loc tag id mv)


and check_struct
  (loc : Locations.t)
  (tag : Sym.t)
  (member_values : (Id.t * Sctypes.t * mem_value) list)
  : IT.t m
  =
  let@ layout = get_struct_decl loc tag in
  let member_types = Memory.member_types layout in
  assert (
    List.for_all2
      (fun (id, ct) (id', ct', _mv') -> Id.equal id id' && Sctypes.equal ct ct')
      member_types
      member_values);
  let@ member_its =
    ListM.mapM
      (fun (member, sct, mv) ->
        let@ member_lvt = check_mem_value loc ~expect:(Memory.bt_of_sct sct) mv in
        return (member, member_lvt))
      member_values
  in
  return (IT.struct_ (tag, member_its) loc)


and check_union (_loc : Locations.t) (_tag : Sym.t) (_id : Id.t) (_mv : mem_value)
  : IT.t m
  =
  Cerb_debug.error "todo: union types"


let ensure_bitvector_type (loc : Locations.t) ~(expect : BT.t) : (BT.sign * int) m =
  match BT.is_bits_bt expect with
  | Some (sign, n) -> return (sign, n)
  | None ->
    fail (fun _ ->
      { loc;
        msg = Mismatch { has = !^"(unspecified) bitvector type"; expect = BT.pp expect }
      })


let rec check_object_value (loc : Locations.t) (Mu.OV (expect, ov)) : IT.t m =
  match ov with
  | OVinteger iv ->
    (* TODO: maybe check whether iv is within range of the type? *)
    let@ bt_info = ensure_bitvector_type loc ~expect in
    let z = Memory.z_of_ival iv in
    let min_z, max_z = BT.bits_range bt_info in
    if Z.leq min_z z && Z.leq z max_z then
      return (num_lit_ z expect loc)
    else
      fail (fun _ ->
        { loc;
          msg =
            Generic
              (!^"integer literal not representable at type"
               ^^^ Pp.typ (Pp.z z) (BT.pp expect))
        })
  | OVpointer p -> check_ptrval loc ~expect p
  | OVarray items ->
    let@ index_bt, item_bt = expect_must_be_map_bt loc ~expect in
    assert (Option.is_some (BT.is_bits_bt index_bt));
    let@ () =
      ListM.iterM
        (fun i -> ensure_base_type loc ~expect:item_bt (Mu.bt_of_object_value i))
        items
    in
    let@ values = ListM.mapM (check_object_value loc) items in
    return (make_array_ ~index_bt ~item_bt values loc)
  | OVstruct (tag, fields) ->
    let@ () = ensure_base_type loc ~expect (Struct tag) in
    check_struct loc tag fields
  | OVunion (tag, id, mv) -> check_union loc tag id mv
  | OVfloating _iv -> unsupported loc !^"floats"


let rec check_value (loc : Locations.t) (Mu.V (expect, v)) : IT.t m =
  match v with
  | Vobject ov ->
    let@ () = ensure_base_type loc ~expect (Mu.bt_of_object_value ov) in
    check_object_value loc ov
  | Vctype ct ->
    let@ () = ensure_base_type loc ~expect CType in
    let ct = Sctypes.of_ctype_unsafe loc ct in
    let@ () = WellTyped.WCT.is_ct loc ct in
    return (IT.const_ctype_ ct loc)
  | Vunit ->
    let@ () = ensure_base_type loc ~expect Unit in
    return (IT.unit_ loc)
  | Vtrue ->
    let@ () = ensure_base_type loc ~expect Bool in
    return (IT.bool_ true loc)
  | Vfalse ->
    let@ () = ensure_base_type loc ~expect Bool in
    return (IT.bool_ false loc)
  | Vfunction_addr sym ->
    let@ () = ensure_base_type loc ~expect (Loc ()) in
    (* check it is a valid function address *)
    let@ _ = get_fun_decl loc sym in
    return (IT.sym_ (sym, BT.(Loc ()), loc))
  | Vlist (_item_cbt, vals) ->
    let item_bt = Mu.bt_of_value (List.hd vals) in
    let@ () = ensure_base_type loc ~expect (List item_bt) in
    let@ () =
      ListM.iterM (fun i -> ensure_base_type loc ~expect:item_bt (Mu.bt_of_value i)) vals
    in
    let@ values = ListM.mapM (check_value loc) vals in
    return (list_ ~item_bt values ~nil_loc:loc)
  | Vtuple vals ->
    let item_bts = List.map Mu.bt_of_value vals in
    let@ () = ensure_base_type loc ~expect (Tuple item_bts) in
    let@ values = ListM.mapM (check_value loc) vals in
    return (tuple_ values loc)


(*** pure expression inference ************************************************)

(* try to follow is_representable_integer from runtime/libcore/std.core *)
let is_representable_integer arg ity =
  let here = Locations.other __LOC__ in
  let bt = IT.get_bt arg in
  let arg_bits = Option.get (BT.is_bits_bt bt) in
  let maxInt = Memory.max_integer_type ity in
  assert (BT.fits_range arg_bits maxInt);
  let minInt = Memory.min_integer_type ity in
  assert (BT.fits_range arg_bits minInt);
  and_
    [ le_ (num_lit_ minInt bt here, arg) here; le_ (arg, num_lit_ maxInt bt here) here ]
    here


let eq_value_with f expr =
  match f expr with
  | Some y -> return (Some (expr, y))
  | None ->
    let@ group = value_eq_group None expr in
    (match
       List.find_opt (fun t -> Option.is_some (f t)) (EqTable.ITSet.elements group)
     with
     | Some x ->
       let y = Option.get (f x) in
       return (Some (x, y))
     | None -> return None)


let prefer_value_with f expr =
  let@ r = eq_value_with (fun it -> if f it then Some () else None) expr in
  match r with None -> return expr | Some (x, _) -> return x


let try_prove_constant loc expr =
  let@ known = eq_value_with IT.is_const expr in
  match known with
  | Some (it, _) -> return it
  | None ->
    (* backup strategy, try to figure out the single value *)
    let fail2 msg =
      fail (fun _ -> { loc; msg = Generic (!^"model constant calculation:" ^^^ !^msg) })
    in
    let fail_on_none msg = function Some m -> return m | None -> fail2 msg in
    let here = Locations.other __LOC__ in
    let@ m = model_with loc (IT.bool_ true here) in
    let@ m = fail_on_none "cannot get model" m in
    let@ y = fail_on_none "cannot eval term" (Solver.eval (fst m) expr) in
    let@ _ = fail_on_none "eval to non-constant term" (IT.is_const y) in
    let eq = IT.eq_ (expr, y) here in
    let@ provable = provable loc in
    (match provable (LC.T eq) with
     | `True ->
       let@ () = add_c loc (LC.T eq) in
       return y
     | `False -> return expr)


let check_single_ct loc expr =
  let@ _pointer = WellTyped.WIT.check loc BT.CType expr in
  let@ t = try_prove_constant loc expr in
  match IT.is_const t with
  | Some (IT.CType_const ct, _) -> return ct
  | Some _ -> assert false (* should be impossible given the type *)
  | None ->
    fail (fun _ -> { loc; msg = Generic !^"use of non-constant ctype mucore expression" })


let is_fun_addr global t =
  match IT.is_sym t with
  | Some (s, _) ->
    if Sym.Map.mem s global.Global.fun_decls then
      Some s
    else
      None
  | _ -> None


let known_function_pointer loc p =
  let@ global = get_global () in
  let@ already_known = eq_value_with (is_fun_addr global) p in
  let@ () =
    match already_known with
    | Some _ -> (* no need to find more eqs *) return ()
    | None ->
      let global_funs = Sym.Map.bindings global.Global.fun_decls in
      let fun_addrs =
        List.map (fun (sym, (loc, _, _)) -> IT.sym_ (sym, BT.(Loc ()), loc)) global_funs
      in
      test_value_eqs loc None p fun_addrs
  in
  let@ now_known = eq_value_with (is_fun_addr global) p in
  match now_known with
  | Some (_, sym) -> return sym
  | None ->
    fail (fun _ ->
      { loc;
        msg =
          Generic
            (Pp.item
               "function pointer must be provably equal to a defined function"
               (IT.pp p))
      })


let check_conv_int loc ~expect ct arg =
  assert (match expect with BT.Bits _ -> true | _ -> false);
  (* try to follow conv_int from runtime/libcore/std.core *)
  let ity =
    match ct with
    | Sctypes.Integer ity -> ity
    | _ -> Cerb_debug.error "conv_int applied to non-integer type"
  in
  let@ provable = provable loc in
  let fail_unrepresentable () =
    let@ model = model () in
    fail (fun ctxt ->
      { loc; msg = Int_unrepresentable { value = arg; ict = ct; ctxt; model } })
  in
  let bt = IT.get_bt arg in
  (* TODO: can we (later) optimise this? *)
  let here = Locations.other __LOC__ in
  let@ value =
    match ity with
    | Bool ->
      (* TODO: can we (later) express this more efficiently without ITE? *)
      return
        (ite_
           ( eq_ (arg, num_lit_ Z.zero bt here) here,
             num_lit_ Z.zero expect loc,
             num_lit_ Z.one expect loc )
           loc)
    | _ when Sctypes.is_unsigned_integer_type ity ->
      (* casting to the relevant type does the same thing as wrapI *)
      return (cast_ (Memory.bt_of_sct ct) arg loc)
    | _ ->
      (match provable (LC.T (representable_ (ct, arg) here)) with
       | `True ->
         (* this proves that this cast does not change the (integer) interpretation *)
         return (cast_ (Memory.bt_of_sct ct) arg loc)
       | `False -> fail_unrepresentable ())
  in
  return value


let check_against_core_bt loc msg2 cbt bt =
  Typing.lift
    (CoreTypeChecks.check_against_core_bt
       (fun msg -> Or_TypeError.fail { loc; msg = Generic (msg ^^ Pp.hardline ^^ msg2) })
       cbt
       bt)


let check_has_alloc_id loc ptr ub_unspec =
  if !use_vip then
    let@ provable = provable loc in
    match provable (LC.T (hasAllocId_ ptr loc)) with
    | `True -> return ()
    | `False ->
      let@ model = model () in
      let ub = CF.Undefined.(UB_CERB004_unspecified ub_unspec) in
      fail (fun ctxt -> { loc; msg = Needs_alloc_id { ptr; ub; ctxt; model } })
  else
    return ()


let in_bounds ptr =
  let here = Locations.other __LOC__ in
  let module H = Alloc.History in
  let H.{ base; size } = H.(split (lookup_ptr ptr here) here) in
  let addr = addr_ ptr here in
  let lower = le_ (base, addr) here in
  let upper = le_ (addr, add_ (base, size) here) here in
  [ lower; upper ]


let check_both_eq_alloc loc arg1 arg2 ub =
  let here = Locations.other __LOC__ in
  let both_alloc =
    and_
      [ hasAllocId_ arg1 here;
        hasAllocId_ arg2 here;
        eq_ (allocId_ arg1 here, allocId_ arg2 here) here
      ]
      here
  in
  let@ provable = provable loc in
  match provable @@ LC.T both_alloc with
  | `False ->
    let@ model = model () in
    fail (fun ctxt -> { loc; msg = Undefined_behaviour { ub; ctxt; model } })
  | `True -> return ()


(** If [ptrs] has more than one element, the allocation IDs must be equal *)
let check_live_alloc_bounds ?(skip_live = false) reason loc ub ptrs =
  if !use_vip then
    let@ () =
      if skip_live then
        return ()
      else
        RI.Special.check_live_alloc reason loc (List.hd ptrs)
    in
    let here = Locations.other __LOC__ in
    let constr = and_ (List.concat_map in_bounds ptrs) here in
    let@ provable = provable loc in
    match provable @@ LC.T constr with
    | `True -> return ()
    | `False ->
      let@ model = model () in
      fail (fun ctxt ->
        let term = if List.length ptrs = 1 then List.hd ptrs else IT.tuple_ ptrs here in
        { loc; msg = Alloc_out_of_bounds { constr; term; ub; ctxt; model } })
  else
    return ()


let valid_for_deref loc pointer ct =
  RI.Special.has_predicate
    loc
    (Access Deref)
    ({ name = Owned (ct, Uninit); pointer; iargs = [] }, None)


let rec check_pexpr (pe : BT.t Mu.pexpr) (k : IT.t -> unit m) : unit m =
  let orig_pe = pe in
  let (Mu.Pexpr (loc, _, expect, pe_)) = pe in
  let@ omodel = model_with loc (bool_ true @@ Locations.other __LOC__) in
  let@ () =
    print_with_ctxt (fun ctxt ->
      debug 3 (lazy (action "inferring pure expression"));
      debug 3 (lazy (item "expr" (Pp_mucore.pp_pexpr pe)));
      debug 3 (lazy (item "ctxt" (Context.pp ctxt))))
  in
  match omodel with
  | None ->
    warn loc !^"Completed type-checking early along this path due to inconsistent facts.";
    return ()
  | Some _ ->
    (match pe_ with
     | PEsym sym ->
       let@ () = check_computational_bound loc sym in
       let@ binding = get_a sym in
       (match binding with
        | BaseType bt ->
          let@ () = ensure_base_type loc ~expect bt in
          k (sym_ (sym, bt, loc))
        | Value lvt ->
          let@ () = ensure_base_type loc ~expect (IT.get_bt lvt) in
          k lvt)
     | PEval v ->
       let@ () = ensure_base_type loc ~expect (Mu.bt_of_value v) in
       let@ vt = check_value loc v in
       k vt
     | PEconstrained _ -> Cerb_debug.error "todo: PEconstrained"
     | PEctor (ctor, pes) ->
       (match (ctor, pes) with
        | Ctuple, _ ->
          let@ () = ensure_base_type loc ~expect (Tuple (List.map Mu.bt_of_pexpr pes)) in
          check_pexprs pes (fun values -> k (tuple_ values loc))
        | Carray, _ ->
          let@ index_bt, item_bt = expect_must_be_map_bt loc ~expect in
          assert (Option.is_some (BT.is_bits_bt index_bt));
          let@ () =
            ListM.iterM
              (fun i -> ensure_base_type loc ~expect:item_bt (Mu.bt_of_pexpr i))
              pes
          in
          check_pexprs pes (fun values -> k (make_array_ ~index_bt ~item_bt values loc))
        | Cnil item_cbt, [] ->
          let@ item_bt =
            match expect with
            | List item_bt -> return item_bt
            | _ ->
              let msg = Mismatch { has = !^"list"; expect = BT.pp expect } in
              fail (fun _ -> { loc; msg })
          in
          let@ () = check_against_core_bt loc !^"checking Cnil" item_cbt item_bt in
          k (nil_ ~item_bt loc)
        | Cnil _item_bt, _ ->
          fail (fun _ ->
            { loc; msg = Number_arguments { has = List.length pes; expect = 0 } })
        | Ccons, [ pe1; pe2 ] ->
          let@ () = ensure_base_type loc ~expect (List (Mu.bt_of_pexpr pe1)) in
          let@ () = ensure_base_type loc ~expect (Mu.bt_of_pexpr pe2) in
          check_pexpr pe1 (fun vt1 ->
            check_pexpr pe2 (fun vt2 -> k (cons_ (vt1, vt2) loc)))
        | Ccons, _ ->
          fail (fun _ ->
            { loc; msg = Number_arguments { has = List.length pes; expect = 2 } }))
     | PEbitwise_unop (unop, pe1) ->
       let@ _ = ensure_bitvector_type loc ~expect in
       let@ () = ensure_base_type loc ~expect (Mu.bt_of_pexpr pe1) in
       check_pexpr pe1 (fun vt1 ->
         let unop =
           match unop with
           | BW_FFS -> BW_FFS_NoSMT
           | BW_CTZ -> BW_CTZ_NoSMT
           | BW_COMPL -> BW_Compl
         in
         let value = arith_unop unop vt1 loc in
         k value)
     | PEbitwise_binop (binop, pe1, pe2) ->
       let@ _ = ensure_bitvector_type loc ~expect in
       let@ () = ensure_base_type loc ~expect (Mu.bt_of_pexpr pe1) in
       let@ () = ensure_base_type loc ~expect (Mu.bt_of_pexpr pe2) in
       let binop =
         match binop with BW_AND -> BW_And | BW_OR -> BW_Or | BW_XOR -> BW_Xor
       in
       check_pexpr pe1 (fun vt1 ->
         check_pexpr pe2 (fun vt2 ->
           let value = arith_binop binop (vt1, vt2) loc in
           k value))
     | Cfvfromint _ -> unsupported loc !^"floats"
     | Civfromfloat _ -> unsupported loc !^"floats"
     | PEarray_shift (pe1, ct, pe2) ->
       let@ () = ensure_base_type loc ~expect (Loc ()) in
       let@ () = WellTyped.WCT.is_ct loc ct in
       let@ () = ensure_base_type loc ~expect:(Loc ()) (Mu.bt_of_pexpr pe1) in
       let@ () = WellTyped.ensure_bits_type loc (Mu.bt_of_pexpr pe2) in
       check_pexpr pe1 (fun vt1 ->
         check_pexpr pe2 (fun vt2 ->
           (* NOTE: This case should not be present - only PtrArrayShift. The issue
              is that the elaboration of create_rdonly uses PtrArrayShift, but right
              now we don't have fractional resources to prove that such objects are
              live. Might be worth considering a read-only resource as a stop-gap.
              But for now, I just skip the liveness check. *)
           let result =
             arrayShift_ ~base:vt1 ct ~index:(cast_ Memory.uintptr_bt vt2 loc) loc
           in
           let@ has_owned = valid_for_deref loc result ct in
           let@ () =
             if has_owned then
               return ()
             else (
               let unspec = CF.Undefined.UB_unspec_pointer_add in
               let@ () = check_has_alloc_id loc vt1 unspec in
               let ub = CF.Undefined.(UB_CERB004_unspecified unspec) in
               check_live_alloc_bounds ~skip_live:true `ISO_array_shift loc ub [ result ])
           in
           k result))
     | PEmember_shift (pe, tag, member) ->
       let@ () = ensure_base_type loc ~expect (Loc ()) in
       let@ () = ensure_base_type loc ~expect:(Loc ()) (Mu.bt_of_pexpr pe) in
       check_pexpr pe (fun vt ->
         let@ ct = get_struct_member_type loc tag member in
         let result = memberShift_ (vt, tag, member) loc in
         (* This should only be called after a PtrValidForDeref, so if we
            were willing to optimise, we could skip to [k result]. *)
         let@ has_owned = valid_for_deref loc result ct in
         let@ () =
           if has_owned then
             return ()
           else (
             let unspec = CF.Undefined.UB_unspec_pointer_add in
             let@ () = check_has_alloc_id loc vt unspec in
             let ub = CF.Undefined.(UB_CERB004_unspecified unspec) in
             check_live_alloc_bounds `ISO_member_shift loc ub [ result ])
         in
         k result)
     | PEnot pe ->
       let@ () = ensure_base_type loc ~expect Bool in
       let@ () = ensure_base_type loc ~expect:Bool (Mu.bt_of_pexpr pe) in
       check_pexpr pe (fun vt -> k (not_ vt loc))
     | PEop (op, pe1, pe2) ->
       let check_cmp_ty = function
         | BT.Integer | Bits _ | Real -> return ()
         | ty ->
           fail (fun _ ->
             { loc; msg = Mismatch { has = BT.pp ty; expect = !^"comparable type" } })
       in
       let not_yet x =
         Pp.debug 1 (lazy (Pp.item "not yet restored" (Pp_mucore_ast.pp_pexpr orig_pe)));
         failwith ("todo: " ^ x)
       in
       (match op with
        | OpDiv ->
          let@ () = ensure_base_type loc ~expect (Mu.bt_of_pexpr pe1) in
          let@ () = WellTyped.ensure_bits_type loc expect in
          let@ () = WellTyped.ensure_bits_type loc (Mu.bt_of_pexpr pe2) in
          check_pexpr pe1 (fun v1 ->
            check_pexpr pe2 (fun v2 ->
              let@ provable = provable loc in
              let v2_bt = Mu.bt_of_pexpr pe2 in
              let here = Locations.other __LOC__ in
              match provable (LC.T (ne_ (v2, int_lit_ 0 v2_bt here) here)) with
              | `True -> k (div_ (v1, v2) loc)
              | `False ->
                let@ model = model () in
                let ub = CF.Undefined.UB045a_division_by_zero in
                fail (fun ctxt -> { loc; msg = Undefined_behaviour { ub; ctxt; model } })))
        | OpRem_t ->
          let@ () = ensure_base_type loc ~expect (Mu.bt_of_pexpr pe1) in
          let@ () = WellTyped.ensure_bits_type loc expect in
          let@ () = WellTyped.ensure_bits_type loc (Mu.bt_of_pexpr pe2) in
          check_pexpr pe1 (fun v1 ->
            check_pexpr pe2 (fun v2 ->
              let@ provable = provable loc in
              let v2_bt = Mu.bt_of_pexpr pe2 in
              let here = Locations.other __LOC__ in
              match provable (LC.T (ne_ (v2, int_lit_ 0 v2_bt here) here)) with
              | `True -> k (rem_ (v1, v2) loc)
              | `False ->
                let@ model = model () in
                let ub = CF.Undefined.UB045b_modulo_by_zero in
                fail (fun ctxt -> { loc; msg = Undefined_behaviour { ub; ctxt; model } })))
        | OpEq ->
          let@ () = ensure_base_type loc ~expect Bool in
          let@ () =
            ensure_base_type loc ~expect:(Mu.bt_of_pexpr pe1) (Mu.bt_of_pexpr pe2)
          in
          check_pexpr pe1 (fun v1 -> check_pexpr pe2 (fun v2 -> k (eq_ (v1, v2) loc)))
        | OpGt ->
          let@ () = ensure_base_type loc ~expect Bool in
          let@ () = check_cmp_ty (Mu.bt_of_pexpr pe1) in
          let@ () =
            ensure_base_type loc ~expect:(Mu.bt_of_pexpr pe1) (Mu.bt_of_pexpr pe2)
          in
          check_pexpr pe1 (fun v1 -> check_pexpr pe2 (fun v2 -> k (gt_ (v1, v2) loc)))
        | OpLt ->
          let@ () = ensure_base_type loc ~expect Bool in
          let@ () = check_cmp_ty (Mu.bt_of_pexpr pe1) in
          let@ () =
            ensure_base_type loc ~expect:(Mu.bt_of_pexpr pe1) (Mu.bt_of_pexpr pe2)
          in
          check_pexpr pe1 (fun v1 -> check_pexpr pe2 (fun v2 -> k (lt_ (v1, v2) loc)))
        | OpGe ->
          let@ () = ensure_base_type loc ~expect Bool in
          let@ () = check_cmp_ty (Mu.bt_of_pexpr pe1) in
          let@ () =
            ensure_base_type loc ~expect:(Mu.bt_of_pexpr pe1) (Mu.bt_of_pexpr pe2)
          in
          check_pexpr pe1 (fun v1 -> check_pexpr pe2 (fun v2 -> k (ge_ (v1, v2) loc)))
        | OpLe ->
          let@ () = ensure_base_type loc ~expect Bool in
          let@ () = check_cmp_ty (Mu.bt_of_pexpr pe1) in
          let@ () =
            ensure_base_type loc ~expect:(Mu.bt_of_pexpr pe1) (Mu.bt_of_pexpr pe2)
          in
          check_pexpr pe1 (fun v1 -> check_pexpr pe2 (fun v2 -> k (le_ (v1, v2) loc)))
        | OpAnd ->
          let@ () = ensure_base_type loc ~expect Bool in
          let@ () = ensure_base_type loc ~expect:Bool (Mu.bt_of_pexpr pe1) in
          let@ () = ensure_base_type loc ~expect:Bool (Mu.bt_of_pexpr pe2) in
          check_pexpr pe1 (fun v1 -> check_pexpr pe2 (fun v2 -> k (and_ [ v1; v2 ] loc)))
        | OpOr ->
          let@ () = ensure_base_type loc ~expect Bool in
          let@ () = ensure_base_type loc ~expect:Bool (Mu.bt_of_pexpr pe1) in
          let@ () = ensure_base_type loc ~expect:Bool (Mu.bt_of_pexpr pe2) in
          check_pexpr pe1 (fun v1 -> check_pexpr pe2 (fun v2 -> k (or_ [ v1; v2 ] loc)))
        | OpAdd -> not_yet "OpAdd"
        | OpSub ->
          let@ () = WellTyped.ensure_bits_type loc expect in
          let@ () = WellTyped.ensure_bits_type loc (Mu.bt_of_pexpr pe1) in
          let@ () = WellTyped.ensure_bits_type loc (Mu.bt_of_pexpr pe2) in
          check_pexpr pe1 (fun v1 -> check_pexpr pe2 (fun v2 -> k (sub_ (v1, v2) loc)))
        | OpMul -> not_yet "OpMul"
        | OpRem_f -> not_yet "OpRem_f"
        | OpExp -> not_yet "OpExp")
     | PEapply_fun (fun_id, args) ->
       let@ () =
         match Mu.fun_return_type fun_id args with
         | Some (`Returns_BT bt) -> ensure_base_type loc ~expect bt
         | Some `Returns_Integer -> WellTyped.ensure_bits_type loc expect
         | None ->
           fail (fun _ ->
             { loc;
               msg =
                 Generic
                   (Pp.item "untypeable mucore function" (Pp_mucore_ast.pp_pexpr orig_pe))
             })
       in
       let expect_args = Mucore.fun_param_types fun_id in
       let@ () =
         let has = List.length args in
         let expect = List.length expect_args in
         if expect = has then
           return ()
         else
           fail (fun _ -> { loc; msg = Number_arguments { has; expect } })
       in
       let@ _ =
         ListM.map2M
           (fun pe expect -> ensure_base_type loc ~expect (Mu.bt_of_pexpr pe))
           args
           expect_args
       in
       check_pexprs args (fun args ->
         let@ res = CLogicalFuns.eval_fun fun_id args orig_pe in
         k res)
     | PEstruct (tag, xs) ->
       let@ () = WellTyped.WCT.is_ct loc (Struct tag) in
       let@ () = ensure_base_type loc ~expect (Struct tag) in
       let@ layout = get_struct_decl loc tag in
       let member_types = Memory.member_types layout in
       let@ _ =
         ListM.map2M
           (fun (id, ct) (id', pe') ->
             assert (Id.equal id id');
             ensure_base_type loc ~expect:(Memory.bt_of_sct ct) (Mu.bt_of_pexpr pe'))
           member_types
           xs
       in
       check_pexprs (List.map snd xs) (fun vs ->
         let members = List.map2 (fun (nm, _) v -> (nm, v)) xs vs in
         k (struct_ (tag, members) loc))
     | PEunion _ -> Cerb_debug.error "todo: PEunion"
     | PEcfunction pe2 ->
       let@ () = ensure_base_type loc ~expect (Tuple [ CType; List CType; Bool; Bool ]) in
       let@ () = ensure_base_type loc ~expect:(Loc ()) (Mu.bt_of_pexpr pe2) in
       check_pexpr pe2 (fun ptr ->
         let@ _global = get_global () in
         (* function vals are just symbols the same as the names of functions *)
         let@ sym = known_function_pointer loc ptr in
         (* need to conjure up the characterising 4-tuple *)
         let@ _, _, c_sig = get_fun_decl loc sym in
         match IT.const_of_c_sig c_sig loc with
         | Some it -> k it
         | None ->
           fail (fun _ ->
             { loc; msg = Generic (!^"unsupported c-type in sig of:" ^^^ Sym.pp sym) }))
     | PEmemberof _ -> Cerb_debug.error "todo: PEmemberof"
     | PEbool_to_integer pe ->
       let@ _ = ensure_bitvector_type loc ~expect in
       let@ () = ensure_base_type loc ~expect:Bool (Mu.bt_of_pexpr pe) in
       check_pexpr pe (fun arg ->
         k (ite_ (arg, int_lit_ 1 expect loc, int_lit_ 0 expect loc) loc))
     | PEbounded_binop (Bound_Wrap act, iop, pe1, pe2) ->
       (* in integers, perform this op and round. in bitvector types, just perform
          the op (for all the ops where wrapping is consistent) *)
       let@ () = WellTyped.WCT.is_ct act.loc act.ct in
       assert (
         match act.ct with
         | Integer ity when Sctypes.is_unsigned_integer_type ity -> true
         | _ -> false);
       let@ () = ensure_base_type loc ~expect (Memory.bt_of_sct act.ct) in
       let@ () = ensure_base_type loc ~expect (Mu.bt_of_pexpr pe1) in
       let@ () = WellTyped.ensure_bits_type loc expect in
       let@ () = WellTyped.ensure_bits_type loc (Mu.bt_of_pexpr pe2) in
       let@ () =
         match iop with
         | IOpShl | IOpShr -> return ()
         | _ -> ensure_base_type loc ~expect (Mu.bt_of_pexpr pe2)
       in
       check_pexpr pe1 (fun arg1 ->
         check_pexpr pe2 (fun arg2 ->
           let arg1_bt_range =
             BT.bits_range (Option.get (BT.is_bits_bt (IT.get_bt arg1)))
           in
           let here = Locations.other __LOC__ in
           let arg2_bits_lost = IT.not_ (IT.in_z_range arg2 arg1_bt_range here) here in
           let x =
             match iop with
             | IOpAdd -> add_ (arg1, arg2) loc
             | IOpSub -> sub_ (arg1, arg2) loc
             | IOpMul -> mul_ (arg1, arg2) loc
             | IOpShl ->
               ite_
                 ( arg2_bits_lost,
                   IT.int_lit_ 0 expect loc,
                   arith_binop Terms.ShiftLeft (arg1, cast_ (IT.get_bt arg1) arg2 loc) loc
                 )
                 loc
             | IOpShr ->
               ite_
                 ( arg2_bits_lost,
                   IT.int_lit_ 0 expect loc,
                   arith_binop
                     Terms.ShiftRight
                     (arg1, cast_ (IT.get_bt arg1) arg2 loc)
                     loc )
                 loc
           in
           k x))
     | PEbounded_binop (Bound_Except act, iop, pe1, pe2) ->
       let@ () = WellTyped.WCT.is_ct act.loc act.ct in
       let ity = match act.ct with Integer ity -> ity | _ -> assert false in
       let@ () = ensure_base_type loc ~expect (Memory.bt_of_sct act.ct) in
       let@ () = ensure_base_type loc ~expect (Mu.bt_of_pexpr pe1) in
       let@ () = WellTyped.ensure_bits_type loc expect in
       let@ () = WellTyped.ensure_bits_type loc (Mu.bt_of_pexpr pe2) in
       let@ () =
         match iop with
         | IOpShl | IOpShr -> return ()
         | _ -> ensure_base_type loc ~expect (Mu.bt_of_pexpr pe2)
       in
       let _, bits = Option.get (BT.is_bits_bt expect) in
       check_pexpr pe1 (fun arg1 ->
         check_pexpr pe2 (fun arg2 ->
           let large_bt = BT.Bits (BT.Signed, (2 * bits) + 4) in
           let here = Locations.other __LOC__ in
           let large x = cast_ large_bt x here in
           let direct_x, via_large_x, premise =
             match iop with
             | IOpAdd ->
               (add_ (arg1, arg2) loc, add_ (large arg1, large arg2) loc, bool_ true here)
             | IOpSub ->
               (sub_ (arg1, arg2) loc, sub_ (large arg1, large arg2) loc, bool_ true here)
             | IOpMul ->
               (mul_ (arg1, arg2) loc, mul_ (large arg1, large arg2) loc, bool_ true here)
             | IOpShl ->
               ( arith_binop Terms.ShiftLeft (arg1, cast_ (IT.get_bt arg1) arg2 loc) loc,
                 arith_binop Terms.ShiftLeft (large arg1, large arg2) loc,
                 IT.in_z_range arg2 (Z.zero, Z.of_int bits) loc )
             | IOpShr ->
               ( arith_binop Terms.ShiftRight (arg1, cast_ (IT.get_bt arg1) arg2 loc) loc,
                 arith_binop Terms.ShiftRight (large arg1, large arg2) loc,
                 IT.in_z_range arg2 (Z.zero, Z.of_int bits) loc )
           in
           let@ provable = provable loc in
           let@ () =
             match
               provable
                 (LC.T (and_ [ premise; is_representable_integer via_large_x ity ] here))
             with
             | `True -> return ()
             | `False ->
               let@ model = model () in
               let ub = CF.Undefined.UB036_exceptional_condition in
               fail (fun ctxt -> { loc; msg = Undefined_behaviour { ub; ctxt; model } })
           in
           k direct_x))
     | PEconv_int (ct_expr, pe) | PEconv_loaded_int (ct_expr, pe) ->
       let@ () = ensure_base_type loc ~expect:CType (Mu.bt_of_pexpr ct_expr) in
       let@ () = WellTyped.ensure_bits_type loc (Mu.bt_of_pexpr pe) in
       check_pexpr ct_expr (fun ct_it ->
         let@ ct = check_single_ct loc ct_it in
         let@ () = WellTyped.WCT.is_ct loc ct in
         let@ () = ensure_base_type loc ~expect (Memory.bt_of_sct ct) in
         check_pexpr pe (fun lvt ->
           let@ vt = check_conv_int loc ~expect ct lvt in
           k vt))
     | PEwrapI (act, pe) ->
       let@ () = WellTyped.WCT.is_ct act.loc act.ct in
       let@ () = WellTyped.ensure_bits_type loc (Mu.bt_of_pexpr pe) in
       check_pexpr pe (fun arg ->
         let bt = Memory.bt_of_sct act.ct in
         let@ () = WellTyped.ensure_bits_type loc bt in
         k (cast_ bt arg loc))
     | PEcatch_exceptional_condition (act, pe) ->
       let@ () = WellTyped.WCT.is_ct act.loc act.ct in
       let@ () = WellTyped.ensure_bits_type loc (Mu.bt_of_pexpr pe) in
       check_pexpr pe (fun arg ->
         let bt = Memory.bt_of_sct act.ct in
         let@ () = WellTyped.ensure_bits_type loc bt in
         let ity = Option.get (Sctypes.is_integer_type act.ct) in
         let@ provable = provable loc in
         match provable (LC.T (is_representable_integer arg ity)) with
         | `True -> k arg
         | `False ->
           let@ model = model () in
           let ub = CF.Undefined.UB036_exceptional_condition in
           fail (fun ctxt -> { loc; msg = Undefined_behaviour { ub; ctxt; model } }))
     | PEis_representable_integer (pe, act) ->
       let@ () = WellTyped.WCT.is_ct act.loc act.ct in
       let@ () = ensure_base_type loc ~expect Bool in
       let@ () = WellTyped.ensure_bits_type loc (Mu.bt_of_pexpr pe) in
       let ity = Option.get (Sctypes.is_integer_type act.ct) in
       check_pexpr pe (fun arg -> k (is_representable_integer arg ity))
     | PEif (pe, e1, e2) ->
       let@ () = ensure_base_type loc ~expect (Mu.bt_of_pexpr e1) in
       let@ () = ensure_base_type loc ~expect (Mu.bt_of_pexpr e2) in
       let@ () = ensure_base_type loc ~expect:Bool (Mu.bt_of_pexpr pe) in
       check_pexpr pe (fun c ->
         let aux e cond name =
           let@ () = add_c loc (LC.T cond) in
           Pp.debug
             5
             (lazy (Pp.item ("checking consistency of " ^ name ^ "-branch") (IT.pp cond)));
           let@ provable = provable loc in
           let here = Locations.other __LOC__ in
           match provable (LC.T (bool_ false here)) with
           | `True ->
             Pp.debug 5 (lazy (Pp.headline "inconsistent, skipping"));
             return ()
           | `False ->
             Pp.debug 5 (lazy (Pp.headline "consistent, checking"));
             check_pexpr e k
         in
         let@ () = pure (aux e1 c "then") in
         let here = Locations.other __LOC__ in
         let@ () = pure (aux e2 (not_ c here) "else") in
         return ())
     | PElet (p, e1, e2) ->
       let@ () = ensure_base_type loc ~expect (Mu.bt_of_pexpr e2) in
       let@ () = ensure_base_type loc ~expect:(Mu.bt_of_pexpr e1) (Mu.bt_of_pattern p) in
       check_pexpr e1 (fun v1 ->
         let@ bound_a = check_and_match_pattern p v1 in
         check_pexpr e2 (fun lvt ->
           let@ () = remove_as bound_a in
           k lvt))
     | PEundef (loc, ub) ->
       let@ provable = provable loc in
       let here = Locations.other __LOC__ in
       (match provable (LC.T (bool_ false here)) with
        | `True -> return ()
        | `False ->
          let@ model = model () in
          fail (fun ctxt -> { loc; msg = Undefined_behaviour { ub; ctxt; model } }))
     | PEerror (err, _pe) ->
       let@ provable = provable loc in
       let here = Locations.other __LOC__ in
       (match provable (LC.T (bool_ false here)) with
        | `True -> return ()
        | `False ->
          let@ model = model () in
          fail (fun ctxt -> { loc; msg = StaticError { err; ctxt; model } })))


and check_pexprs (pes : BT.t Mu.pexpr list) (k : IT.t list -> unit m) : unit m =
  match pes with
  | [] -> k []
  | pe :: pes' ->
    check_pexpr pe (fun lvt -> check_pexprs pes' (fun lvts -> k (lvt :: lvts)))


module Spine : sig
  val calltype_ft
    :  Loc.t ->
    fsym:Sym.t ->
    BT.t Mu.pexpr list ->
    AT.ft ->
    (RT.t -> unit m) ->
    unit m

  val calltype_lt
    :  Loc.t ->
    BT.t Mu.pexpr list ->
    AT.lt * Where.label ->
    (False.t -> unit m) ->
    unit m

  val calltype_lemma
    :  Loc.t ->
    lemma:Sym.t ->
    (Loc.t * IT.t) list ->
    AT.lemmat ->
    (LRT.t -> unit m) ->
    unit m

  val subtype : Locations.t -> LRT.t -> (unit -> unit m) -> unit m
end = struct
  let spine_l rt_subst rt_pp loc (situation : call_situation) ftyp k =
    let start_spine = time_log_start "spine_l" "" in
    let@ original_resources = all_resources_tagged loc in
    let@ rt =
      let rec check ftyp =
        let@ () =
          print_with_ctxt (fun ctxt ->
            debug 6 (lazy (item "ctxt" (Context.pp ctxt)));
            debug 6 (lazy (item "spec" (LAT.pp rt_pp ftyp))))
        in
        let uiinfo = ((Call situation : situation), []) in
        let@ ftyp =
          RI.General.ftyp_args_request_step rt_subst loc uiinfo original_resources ftyp
        in
        match ftyp with I rt -> return rt | _ -> check ftyp
      in
      check ftyp
    in
    let@ () = return (debug 9 (lazy !^"done")) in
    time_log_end start_spine;
    k rt


  let spine check_arg rt_subst rt_pp loc (situation : call_situation) args ftyp k =
    let open ArgumentTypes in
    let original_ftyp = ftyp in
    let original_args = args in
    let@ () =
      print_with_ctxt (fun ctxt ->
        debug 6 (lazy (call_situation situation));
        debug 6 (lazy (item "ctxt" (Context.pp ctxt)));
        debug 6 (lazy (item "spec" (pp rt_pp ftyp))))
    in
    let check =
      let rec aux args_acc args ftyp k =
        match (args, ftyp) with
        | arg :: args, Computational ((s, bt), _info, ftyp) ->
          check_arg arg ~expect:bt (fun arg ->
            aux
              (args_acc @ [ arg ])
              args
              (subst rt_subst (make_subst [ (s, arg) ]) ftyp)
              k)
        | [], L ftyp ->
          let@ () =
            match situation with
            | FunctionCall fsym -> record_action (Call (fsym, args_acc), loc)
            | Subtyping | LabelCall LAreturn ->
              let returned = match args_acc with [ v ] -> v | _ -> assert false in
              record_action (Return returned, loc)
            | _ -> return ()
          in
          k ftyp
        | _ ->
          let expect = count_computational original_ftyp in
          let has = List.length original_args in
          fail (fun _ -> { loc; msg = Number_arguments { expect; has } })
      in
      fun args ftyp k -> aux [] args ftyp k
    in
    check args ftyp (fun lftyp -> spine_l rt_subst rt_pp loc situation lftyp k)


  let check_arg_pexpr (pe : BT.t Mu.pexpr) ~expect k =
    let@ () = ensure_base_type (Mu.loc_of_pexpr pe) ~expect (Mu.bt_of_pexpr pe) in
    check_pexpr pe k


  let check_arg_it (loc, it_arg) ~(expect : BT.t) k =
    let@ it_arg = WellTyped.WIT.check loc expect it_arg in
    k it_arg


  let calltype_ft loc ~fsym args (ftyp : AT.ft) k =
    spine check_arg_pexpr RT.subst RT.pp loc (FunctionCall fsym) args ftyp k


  let calltype_lt loc args ((ltyp : AT.lt), label_kind) k =
    spine check_arg_pexpr False.subst False.pp loc (LabelCall label_kind) args ltyp k


  let calltype_lemma loc ~lemma args lemma_typ k =
    spine check_arg_it LRT.subst LRT.pp loc (LemmaApplication lemma) args lemma_typ k


  (* The "subtyping" judgment needs the same resource/lvar/constraint
     inference as the spine judgment. So implement the subtyping
     judgment 'arg <: LRT' by type checking 'f()' for 'f: LRT -> False'. *)
  let subtype (loc : Locations.t) (rtyp : LRT.t) k =
    let lft = LAT.of_lrt rtyp (LAT.I False.False) in
    spine_l False.subst False.pp loc Subtyping lft (fun False.False -> k ())
end

(*** impure expression inference **********************************************)

let filter_empty_resources loc =
  let@ provable = provable loc in
  let@ filtered, _rw_time =
    map_and_fold_resources
      loc
      (fun resource xs ->
        match Pack.resource_empty provable resource with
        | `Empty -> (Deleted, xs)
        | `NonEmpty (constr, model) -> (Unchanged, (resource, constr, model) :: xs))
      []
  in
  return filtered


let all_empty loc _original_resources =
  let@ remaining_resources = filter_empty_resources loc in
  (* there will be a model available if at least one resource persisted *)
  match remaining_resources with
  | [] -> return ()
  | (resource, constr, model) :: _ ->
    let@ simp_ctxt = simp_ctxt () in
    RI.debug_constraint_failure_diagnostics 6 model simp_ctxt constr;
    fail (fun ctxt ->
      (* let ctxt = { ctxt with resources = original_resources } in *)
      { loc; msg = Unused_resource { resource; ctxt; model } })


let compute_used loc (prev_rs, prev_ix) (post_rs, _) =
  let module IntSet = Set.Make (Int) in
  let post_ixs = IntSet.of_list (List.map snd post_rs) in
  (* restore previous resources that have disappeared from the context, since they
     might participate in a race *)
  let all_rs =
    post_rs @ List.filter (fun (_, i) -> not (IntSet.mem i post_ixs)) prev_rs
  in
  ListM.fold_leftM
    (fun (rs, ws) (r, i) ->
      let@ h = res_history loc i in
      if h.last_written_id >= prev_ix then
        return (rs, (r, h, i) :: ws)
      else if h.last_read_id >= prev_ix then
        return ((r, h, i) :: rs, ws)
      else
        return (rs, ws))
    ([], [])
    all_rs


let _check_used_distinct loc used =
  let module IntMap = Map.Make (Int) in
  let render_upd h =
    !^"resource"
    ^^^ !^(h.Context.reason_written)
    ^^^ !^"at"
    ^^^ Locations.pp h.Context.last_written
  in
  let render_read h = !^"resource read at " ^^^ Locations.pp h.Context.last_read in
  let rec check_ws m = function
    | [] -> return m
    | (r, h, i) :: ws ->
      (match IntMap.find_opt i m with
       | None -> check_ws (IntMap.add i h m) ws
       | Some h2 ->
         Pp.debug 3 (lazy (Pp.typ !^"concurrent upds on" (Pp.int i)));
         fail (fun _ ->
           { loc;
             msg =
               Generic
                 (Pp.item
                    "undefined behaviour: concurrent update"
                    (Resource.pp r
                     ^^^ break 1
                     ^^^ render_upd h
                     ^^^ break 1
                     ^^^ render_upd h2))
           }))
  in
  let@ w_map = check_ws IntMap.empty (List.concat (List.map snd used)) in
  let check_rd (r, h, i) =
    match IntMap.find_opt i w_map with
    | None -> return ()
    | Some h2 ->
      Pp.debug 3 (lazy (Pp.typ !^"concurrent accs on" (Pp.int i)));
      fail (fun _ ->
        { loc;
          msg =
            Generic
              (Pp.item
                 "undefined behaviour: concurrent read & update"
                 (Resource.pp r
                  ^^^ break 1
                  ^^^ render_read h
                  ^^^ break 1
                  ^^^ render_upd h2))
        })
  in
  ListM.iterM check_rd (List.concat (List.map fst used))


(*type labels = (AT.lt * label_kind) Sym.Map.t*)

let load loc pointer ct =
  let@ value =
    pure
      (let@ (_point, O value), _ =
         RI.Special.predicate_request
           loc
           (Access Load)
           ({ name = Owned (ct, Init); pointer; iargs = [] }, None)
       in
       return value)
  in
  let@ () = record_action (Read (pointer, value), loc) in
  return value


let instantiate loc filter arg =
  let arg_s = Sym.fresh_make_uniq "instance" in
  let arg_it = sym_ (arg_s, IT.get_bt arg, loc) in
  let@ () = add_l arg_s (IT.get_bt arg_it) (loc, lazy (Sym.pp arg_s)) in
  let@ () = add_c loc (LC.T (eq__ arg_it arg loc)) in
  let@ constraints = get_cs () in
  let extra_assumptions1 =
    List.filter_map
      (function LC.Forall ((s, bt), t) when filter t -> Some ((s, bt), t) | _ -> None)
      (LC.Set.elements constraints)
  in
  let extra_assumptions2, type_mismatch =
    List.partition (fun ((_, bt), _) -> BT.equal bt (IT.get_bt arg_it)) extra_assumptions1
  in
  let extra_assumptions =
    List.map
      (fun ((s, _), t) -> LC.T (IT.subst (IT.make_subst [ (s, arg_it) ]) t))
      extra_assumptions2
  in
  if List.length extra_assumptions == 0 then
    Pp.warn loc !^"nothing instantiated"
  else
    ();
  List.iteri
    (fun i ((_, bt), _) ->
      if i < 2 then
        Pp.warn
          loc
          (!^"did not instantiate on basetype mismatch:"
           ^^^ Pp.list BT.pp [ bt; IT.get_bt arg_it ]))
    type_mismatch;
  add_cs loc extra_assumptions


let add_trace_information _labels annots =
  let open Where in
  let open CF.Annot in
  let inlined_labels =
    List.filter_map (function Ainlined_label l -> Some l | _ -> None) annots
  in
  let locs = List.filter_map (function Aloc l -> Some l | _ -> None) annots in
  let is_stmt = List.exists (function Astmt -> true | _ -> false) annots in
  let is_expr = List.exists (function Aexpr -> true | _ -> false) annots in
  let@ () =
    match inlined_labels with
    | [] -> return ()
    | [ (lloc, _lsym, lannot) ] ->
      modify_where (set_section (Label { loc = lloc; label = lannot }))
    | _ -> assert false
  in
  let@ () =
    match locs with
    | [] -> return ()
    | l :: _ ->
      if is_stmt then
        modify_where (set_statement l)
      else if is_expr then
        modify_where (set_expression l)
      else
        return ()
  in
  return ()


let bytes_qpred sym size pointer init : Req.QPredicate.t =
  let here = Locations.other __LOC__ in
  let bt' = WellTyped.quantifier_bt in
  { q = (sym, bt');
    q_loc = here;
    step = IT.num_lit_ Z.one bt' here;
    permission = IT.(lt_ (sym_ (sym, bt', here), size) here);
    name = Owned (Sctypes.uchar_ct, init);
    pointer;
    iargs = []
  }


let rec check_expr labels (e : BT.t Mu.expr) (k : IT.t -> unit m) : unit m =
  let (Expr (loc, annots, expect, e_)) = e in
  let@ () = add_trace_information labels annots in
  let here = Locations.other __LOC__ in
  let@ omodel = model_with loc (bool_ true here) in
  match omodel with
  | None ->
    warn loc !^"Completed type-checking early along this path due to inconsistent facts.";
    return ()
  | Some _ ->
    let@ () =
      print_with_ctxt (fun ctxt ->
        debug 3 (lazy (action "inferring expression"));
        debug 3 (lazy (item "expr" (group (Pp_mucore.pp_expr e))));
        debug 3 (lazy (item "ctxt" (Context.pp ctxt))))
    in
    let bytes_qpred sym ct pointer init : Req.QPredicate.t =
      let here = Locations.other __LOC__ in
      bytes_qpred sym (sizeOf_ ct here) pointer init
    in
    (match e_ with
     | Epure pe ->
       let@ () = ensure_base_type loc ~expect (Mu.bt_of_pexpr pe) in
       check_pexpr pe (fun lvt -> k lvt)
     | Ememop memop ->
       let here = Locations.other __LOC__ in
       let pointer_eq ?(negate = false) pe1 pe2 =
         let@ () = ensure_base_type loc ~expect Bool in
         let k, case, res =
           if negate then ((fun x -> k (not_ x loc)), "in", "ptrNeq") else (k, "", "ptrEq")
         in
         check_pexpr pe1 (fun arg1 ->
           check_pexpr pe2 (fun arg2 ->
             let bind name term =
               let sym, it = IT.fresh_named BT.Bool name loc in
               let@ _ = add_a sym Bool (here, lazy (Sym.pp sym)) in
               let@ () = add_c loc (LC.T (term it)) in
               return it
             in
             let@ ambiguous =
               bind "ambiguous"
               @@ fun ambiguous ->
               eq_
                 ( ambiguous,
                   and_
                     [ hasAllocId_ arg1 here;
                       hasAllocId_ arg2 here;
                       ne_ (allocId_ arg1 here, allocId_ arg2 here) here;
                       eq_ (addr_ arg1 here, addr_ arg2 here) here
                     ]
                     here )
                 here
             in
             let@ provable = provable loc in
             let@ () =
               match provable @@ LC.T (not_ ambiguous here) with
               | `True -> return ()
               | `False ->
                 let msg =
                   Printf.sprintf
                     "Cannot rule out ambiguous pointer %sequality case (addresses \
                      equal, but provenances differ)"
                     case
                 in
                 warn loc !^msg;
                 return ()
             in
             let@ both_eq =
               bind "both_eq" @@ fun both_eq -> eq_ (both_eq, eq_ (arg1, arg2) here) here
             in
             let@ neither =
               bind "neither"
               @@ fun neither ->
               eq_ (neither, and_ [ not_ both_eq here; not_ ambiguous here ] here) here
             in
             let@ res =
               bind res
               @@ fun res ->
               (* NOTE: ambiguous case is intentionally under-specified *)
               and_ [ impl_ (both_eq, res) here; impl_ (neither, not_ res here) here ] loc
             in
             k res
             (* (* TODO: use this if SW_strict_pointer_equality is enabled *)
                k
                (or_
                [ and_ [ eq_ (null_ here, arg1) here; eq_ (null_ here, arg2) here ] here;
                       and_
                         [ hasAllocId_ arg1 here;
                           hasAllocId_ arg2 here;
                           eq_ (addr_ arg1 here, addr_ arg2 here) here
                         ]
                         here
                     ]
                here)
             *)))
       in
       let pointer_op op pe1 pe2 =
         let ub = CF.Undefined.UB053_distinct_aggregate_union_pointer_comparison in
         let@ () = ensure_base_type loc ~expect Bool in
         let@ () = ensure_base_type loc ~expect:(Loc ()) (Mu.bt_of_pexpr pe1) in
         let@ () = ensure_base_type loc ~expect:(Loc ()) (Mu.bt_of_pexpr pe2) in
         check_pexpr pe1 (fun arg1 ->
           check_pexpr pe2 (fun arg2 ->
             let@ () = check_both_eq_alloc loc arg1 arg2 ub in
             let@ () = check_live_alloc_bounds `Ptr_cmp loc ub [ arg1; arg2 ] in
             k (op (arg1, arg2))))
       in
       (match memop with
        | PtrEq (pe1, pe2) -> pointer_eq pe1 pe2
        | PtrNe (pe1, pe2) -> pointer_eq ~negate:true pe1 pe2
        | PtrLt (pe1, pe2) -> pointer_op (Fun.flip ltPointer_ loc) pe1 pe2
        | PtrGt (pe1, pe2) -> pointer_op (Fun.flip gtPointer_ loc) pe1 pe2
        | PtrLe (pe1, pe2) -> pointer_op (Fun.flip lePointer_ loc) pe1 pe2
        | PtrGe (pe1, pe2) -> pointer_op (Fun.flip gePointer_ loc) pe1 pe2
        | Ptrdiff (act, pe1, pe2) ->
          let@ () = WellTyped.WCT.is_ct act.loc act.ct in
          let@ () = ensure_base_type loc ~expect (Memory.bt_of_sct (Integer Ptrdiff_t)) in
          let@ () = ensure_base_type loc ~expect:(Loc ()) (Mu.bt_of_pexpr pe1) in
          let@ () = ensure_base_type loc ~expect:(Loc ()) (Mu.bt_of_pexpr pe2) in
          check_pexpr pe1 (fun arg1 ->
            check_pexpr pe2 (fun arg2 ->
              (* copying and adapting from memory/concrete/impl_mem.ml *)
              let divisor =
                match act.ct with
                | Array (item_ty, _) -> Memory.size_of_ctype item_ty
                | ct -> Memory.size_of_ctype ct
              in
              let ub = CF.Undefined.UB048_disjoint_array_pointers_subtraction in
              let@ () = check_both_eq_alloc loc arg1 arg2 ub in
              let ub_unspec = CF.Undefined.UB_unspec_pointer_sub in
              let ub = CF.Undefined.(UB_CERB004_unspecified ub_unspec) in
              let ptr_diff_bt = Memory.bt_of_sct (Integer Ptrdiff_t) in
              let@ () = check_live_alloc_bounds `Ptr_diff loc ub [ arg1; arg2 ] in
              let result =
                (* TODO: confirm that the cast from uintptr_t to ptrdiff_t
                   yields the expected result, or signal
                   UB050_pointers_subtraction_not_representable *)
                div_
                  ( cast_ ptr_diff_bt (sub_ (addr_ arg1 loc, addr_ arg2 loc) loc) loc,
                    int_lit_ divisor ptr_diff_bt loc )
                  loc
              in
              k result))
        | IntFromPtr (act_from, act_to, pe) ->
          let@ () = WellTyped.WCT.is_ct act_from.loc act_from.ct in
          let@ () = WellTyped.WCT.is_ct act_to.loc act_to.ct in
          assert (match act_to.ct with Integer _ -> true | _ -> false);
          let@ () = ensure_base_type loc ~expect (Memory.bt_of_sct act_to.ct) in
          let@ () = ensure_base_type loc ~expect:(Loc ()) (Mu.bt_of_pexpr pe) in
          check_pexpr pe (fun arg ->
            let actual_value = cast_ (Memory.bt_of_sct act_to.ct) arg loc in
            (* NOTE: After discussing with Kavyan
               (1) The pointer does NOT need to be live. The PNVI/VIP
               formalisations are missing a rule for the dead pointer case.
               The PNVI rules state that the pointer must be live so that
               allocations are exposed.
               (2) So, the only UB possible is unrepresentable results. *)
            let@ provable = provable loc in
            let here = Locations.other __LOC__ in
            let lc = LC.T (representable_ (act_to.ct, arg) here) in
            let@ () =
              match provable lc with
              | `True -> return ()
              | `False ->
                let@ model = model () in
                fail (fun ctxt ->
                  let ict = act_to.ct in
                  { loc; msg = Int_unrepresentable { value = arg; ict; ctxt; model } })
            in
            k actual_value)
        | PtrFromInt (act_from, act_to, pe) ->
          let@ () = WellTyped.WCT.is_ct act_from.loc act_from.ct in
          let@ () = WellTyped.WCT.is_ct act_to.loc act_to.ct in
          let@ () = ensure_base_type loc ~expect (Loc ()) in
          let@ () =
            ensure_base_type
              loc
              ~expect:(Memory.bt_of_sct act_from.ct)
              (Mu.bt_of_pexpr pe)
          in
          let@ _bt_info = ensure_bitvector_type loc ~expect:(Mu.bt_of_pexpr pe) in
          check_pexpr pe (fun arg ->
            let sym, result = IT.fresh_named (BT.Loc ()) "intToPtr" loc in
            let@ _ = add_a sym (Loc ()) (here, lazy (Sym.pp sym)) in
            let cond = eq_ (arg, int_lit_ 0 (get_bt arg) here) here in
            let null_case = eq_ (result, null_ here) here in
            (* NOTE: the allocation ID is intentionally left unconstrained *)
            let alloc_case =
              and_
                [ hasAllocId_ result here;
                  eq_ (cast_ Memory.uintptr_bt arg here, addr_ result here) here
                ]
                here
            in
            let constr = ite_ (cond, null_case, alloc_case) here in
            let@ () = add_c loc (LC.T constr) in
            k result)
        | PtrValidForDeref (act, pe) ->
          (* TODO (DCM, VIP) *)
          let@ () = WellTyped.WCT.is_ct act.loc act.ct in
          let@ () = ensure_base_type loc ~expect Bool in
          let@ () = ensure_base_type loc ~expect:(Loc ()) (Mu.bt_of_pexpr pe) in
          (* TODO (DCM, VIP): error if called on Void or Function Ctype.
             return false if resource missing *)
          check_pexpr pe (fun arg ->
            (* let unspec = CF.Undefined.UB_unspec_pointer_add in *)
            (* let@ () = check_has_alloc_id loc arg unspec in *)
            (* let index = num_lit_ Z.one Memory.uintptr_bt here in *)
            (* let check_this = arrayShift_ ~base:arg ~index act.ct loc in *)
            (* let ub = CF.Undefined.(UB_CERB004_unspecified unspec) in *)
            (* let@ () = check_live_alloc_bounds `ISO_array_shift loc ub [ check_this ] in *)
            let result = aligned_ (arg, act.ct) loc in
            k result)
        | PtrWellAligned (act, pe) ->
          let@ () = WellTyped.WCT.is_ct act.loc act.ct in
          let@ () = ensure_base_type loc ~expect Bool in
          let@ () = ensure_base_type loc ~expect:(Loc ()) (Mu.bt_of_pexpr pe) in
          (* TODO (DCM, VIP): error if called on Void or Function Ctype *)
          check_pexpr pe (fun arg ->
            (* let unspec = CF.Undefined.UB_unspec_pointer_add in *)
            (* let@ () = check_has_alloc_id loc arg unspec in *)
            let result = aligned_ (arg, act.ct) loc in
            k result)
        | PtrArrayShift (pe1, act, pe2) ->
          let@ () = ensure_base_type loc ~expect (Loc ()) in
          let@ () = ensure_base_type loc ~expect:(Loc ()) (Mu.bt_of_pexpr pe1) in
          let@ () = WellTyped.WCT.is_ct act.loc act.ct in
          let@ () = WellTyped.ensure_bits_type loc (Mu.bt_of_pexpr pe2) in
          check_pexpr pe1 (fun vt1 ->
            check_pexpr pe2 (fun vt2 ->
              let result =
                arrayShift_ ~base:vt1 act.ct ~index:(cast_ Memory.uintptr_bt vt2 loc) loc
              in
              let@ has_owned = valid_for_deref loc result act.ct in
              let@ () =
                if has_owned then
                  k result
                else (
                  let unspec = CF.Undefined.UB_unspec_pointer_add in
                  let@ () = check_has_alloc_id loc vt1 unspec in
                  let ub = CF.Undefined.(UB_CERB004_unspecified unspec) in
                  check_live_alloc_bounds `ISO_array_shift loc ub [ result ])
              in
              k result))
        | PtrMemberShift _ ->
          unsupported
            (Loc.other __LOC__)
            !^"PtrMemberShift should be a CHERI only construct"
        | CopyAllocId (pe1, pe2) ->
          let@ () = ensure_base_type loc ~expect:Memory.uintptr_bt (Mu.bt_of_pexpr pe1) in
          let@ () = ensure_base_type loc ~expect:BT.(Loc ()) (Mu.bt_of_pexpr pe2) in
          check_pexpr pe1 (fun vt1 ->
            check_pexpr pe2 (fun vt2 ->
              let unspec = CF.Undefined.UB_unspec_copy_alloc_id in
              let@ () = check_has_alloc_id loc vt2 unspec in
              let ub = CF.Undefined.(UB_CERB004_unspecified unspec) in
              let result = copyAllocId_ ~addr:vt1 ~loc:vt2 loc in
              let@ () = check_live_alloc_bounds `Copy_alloc_id loc ub [ result ] in
              k result))
        | Memcpy _ ->
          (* should have been intercepted by memcpy_proxy *)
          assert false
        | Memcmp _ ->
          (* TODO (DCM, VIP) *)
          Cerb_debug.error "todo: Memcmp"
        | Realloc _ (* (asym 'bty * asym 'bty * asym 'bty) *) ->
          Cerb_debug.error "todo: Realloc"
        | Va_start _ (* (asym 'bty * asym 'bty) *) -> Cerb_debug.error "todo: Va_start"
        | Va_copy _ (* (asym 'bty) *) -> Cerb_debug.error "todo: Va_copy"
        | Va_arg _ (* (asym 'bty * actype 'bty) *) -> Cerb_debug.error "todo: Va_arg"
        | Va_end _ (* (asym 'bty) *) -> Cerb_debug.error "todo: Va_end")
     | Eaction (Paction (_pol, Action (_aloc, action_))) ->
       (match action_ with
        | Create (pe, act, prefix) ->
          let@ () = WellTyped.WCT.is_ct act.loc act.ct in
          let@ () = ensure_base_type loc ~expect (Loc ()) in
          let@ () = WellTyped.ensure_bits_type loc (Mu.bt_of_pexpr pe) in
          check_pexpr pe (fun arg ->
            let ret_s, ret =
              match prefix with
              | PrefSource (_loc, syms) ->
                let syms = List.rev syms in
                (match syms with
                 | Symbol (_, _, SD_ObjectAddress str) :: _ ->
                   IT.fresh_named BT.(Loc ()) ("&" ^ str) loc
                 | _ -> IT.fresh BT.(Loc ()) loc)
              | PrefFunArg (_loc, _, n) ->
                IT.fresh_named (BT.Loc ()) ("&ARG" ^ string_of_int n) loc
              | _ -> IT.fresh (BT.Loc ()) loc
            in
            let@ () = add_a ret_s (IT.get_bt ret) (loc, lazy (Pp.string "allocation")) in
            (* let@ () = add_c loc (LC.T (representable_ (Pointer act.ct, ret) loc)) in *)
            let align_v = cast_ Memory.uintptr_bt arg loc in
            let@ () = add_c loc (LC.T (alignedI_ ~align:align_v ~t:ret loc)) in
            let@ () =
              add_r
                loc
                ( P { name = Owned (act.ct, Uninit); pointer = ret; iargs = [] },
                  O (default_ (Memory.bt_of_sct act.ct) loc) )
            in
            let lookup = Alloc.History.lookup_ptr ret here in
            let value =
              let size = Memory.size_of_ctype act.ct in
              Alloc.History.make_value ~base:(addr_ ret here) ~size here
            in
            let@ () =
              if !use_vip then
                (* This is not backwards compatible because in the solver
                 * Alloc_id maps to unit if not (!use_vip) *)
                add_c loc (LC.T (eq_ (lookup, value) here))
              else
                return ()
            in
            let@ () = add_r loc (P (Req.make_alloc ret), O lookup) in
            let@ () = record_action (Create ret, loc) in
            k ret)
        | CreateReadOnly (_sym1, _ct, _sym2, _prefix) ->
          Cerb_debug.error "todo: CreateReadOnly"
        | Alloc (_ct, _sym, _prefix) ->
          (* TODO (DCM, VIP) *)
          Cerb_debug.error "todo: Alloc"
        | Kill (Dynamic, _asym) ->
          (* TODO (DCM, VIP) *)
          Cerb_debug.error "todo: Free"
        | Kill (Static ct, pe) ->
          let@ () = WellTyped.WCT.is_ct loc ct in
          let@ () = ensure_base_type loc ~expect Unit in
          let@ () = ensure_base_type loc ~expect:(Loc ()) (Mu.bt_of_pexpr pe) in
          check_pexpr pe (fun arg ->
            let@ _ =
              RI.Special.predicate_request
                loc
                (Access Kill)
                ({ name = Owned (ct, Uninit); pointer = arg; iargs = [] }, None)
            in
            let@ _ =
              RI.Special.predicate_request loc (Access Kill) (Req.make_alloc arg, None)
            in
            let@ () = record_action (Kill arg, loc) in
            k (unit_ loc))
        | Store (_is_locking, act, p_pe, v_pe, _mo) ->
          let@ () = WellTyped.WCT.is_ct act.loc act.ct in
          let@ () = ensure_base_type loc ~expect Unit in
          let@ () = ensure_base_type loc ~expect:(Loc ()) (Mu.bt_of_pexpr p_pe) in
          let@ () =
            ensure_base_type loc ~expect:(Memory.bt_of_sct act.ct) (Mu.bt_of_pexpr v_pe)
          in
          check_pexpr p_pe (fun parg ->
            check_pexpr v_pe (fun varg ->
              (* The generated Core program will in most cases before this
                 already have checked whether the store value is
                 representable and done the right thing. Pointers, as I
                 understand, are an exception. *)
              let@ () =
                let here = Locations.other __LOC__ in
                let in_range_lc = representable_ (act.ct, varg) here in
                let@ provable = provable loc in
                let holds = provable (LC.T in_range_lc) in
                match holds with
                | `True -> return ()
                | `False ->
                  let@ model = model () in
                  fail (fun ctxt ->
                    let msg =
                      Write_value_unrepresentable
                        { ct = act.ct; location = parg; value = varg; ctxt; model }
                    in
                    { loc; msg })
              in
              let@ _ =
                RI.Special.predicate_request
                  loc
                  (Access Store)
                  ({ name = Owned (act.ct, Uninit); pointer = parg; iargs = [] }, None)
              in
              let@ () =
                add_r
                  loc
                  (P { name = Owned (act.ct, Init); pointer = parg; iargs = [] }, O varg)
              in
              let@ () = record_action (Write (parg, varg), loc) in
              k (unit_ loc)))
        | Load (act, p_pe, _mo) ->
          let@ () = WellTyped.WCT.is_ct act.loc act.ct in
          let@ () = ensure_base_type loc ~expect (Memory.bt_of_sct act.ct) in
          let@ () = ensure_base_type loc ~expect:(Loc ()) (Mu.bt_of_pexpr p_pe) in
          check_pexpr p_pe (fun pointer ->
            let@ value = load loc pointer act.ct in
            k value)
        | RMW (_ct, _sym1, _sym2, _sym3, _mo1, _mo2) -> Cerb_debug.error "todo: RMW"
        | Fence _mo -> Cerb_debug.error "todo: Fence"
        | CompareExchangeStrong (_ct, _sym1, _sym2, _sym3, _mo1, _mo2) ->
          Cerb_debug.error "todo: CompareExchangeStrong"
        | CompareExchangeWeak (_ct, _sym1, _sym2, _sym3, _mo1, _mo2) ->
          Cerb_debug.error "todo: CompareExchangeWeak"
        | LinuxFence _mo -> Cerb_debug.error "todo: LinuxFemce"
        | LinuxLoad (_ct, _sym1, _mo) -> Cerb_debug.error "todo: LinuxLoad"
        | LinuxStore (_ct, _sym1, _sym2, _mo) -> Cerb_debug.error "todo: LinuxStore"
        | LinuxRMW (_ct, _sym1, _sym2, _mo) -> Cerb_debug.error "todo: LinuxRMW")
     | Eskip ->
       let@ () = ensure_base_type loc ~expect Unit in
       k (unit_ loc)
     | Eccall (act, f_pe, pes) ->
       let@ () = WellTyped.WCT.is_ct act.loc act.ct in
       (* copied TS's, from wellTyped.ml *)
       (* let@ (_ret_ct, _arg_cts) = match act.ct with *)
       (*     | Pointer (Function (ret_v_ct, arg_r_cts, is_variadic)) -> *)
       (*         assert (not is_variadic); *)
       (*         return (snd ret_v_ct, List.map fst arg_r_cts) *)
       (*     | _ -> fail (fun _ -> {loc; msg = Generic (Pp.item "not a function pointer at call-site" *)
       (*                                                  (Sctypes.pp act.ct))}) *)
       (* in *)
       let@ () = ensure_base_type loc ~expect:(Loc ()) (Mu.bt_of_pexpr f_pe) in
       check_pexpr f_pe (fun f_it ->
         let@ _global = get_global () in
         let@ fsym = known_function_pointer loc f_it in
         let@ _loc, opt_ft, _ = get_fun_decl loc fsym in
         let@ ft =
           match opt_ft with
           | Some ft -> return ft
           | None ->
             fail (fun _ ->
               { loc; msg = Generic (!^"Call to function with no spec:" ^^^ Sym.pp fsym) })
         in
         (* checks pes against their annotations, and that they match ft's argument types *)
         Spine.calltype_ft loc ~fsym pes ft (fun (Computational ((_, bt), _, _) as rt) ->
           let@ () = ensure_base_type loc ~expect bt in
           let@ _, members =
             make_return_record
               loc
               (TypeErrors.call_prefix (FunctionCall fsym))
               (RT.binders rt)
           in
           let@ lvt = bind_return loc members rt in
           k lvt))
     | Eif (c_pe, e1, e2) ->
       let@ () = ensure_base_type (Mu.loc_of_expr e1) ~expect (Mu.bt_of_expr e1) in
       let@ () = ensure_base_type (Mu.loc_of_expr e2) ~expect (Mu.bt_of_expr e2) in
       let@ () =
         ensure_base_type (Mu.loc_of_pexpr c_pe) ~expect:Bool (Mu.bt_of_pexpr c_pe)
       in
       check_pexpr c_pe (fun carg ->
         let aux lc _nm e =
           let@ () = add_c loc (LC.T lc) in
           let@ provable = provable loc in
           let here = Locations.other __LOC__ in
           match provable (LC.T (bool_ false here)) with
           | `True -> return ()
           | `False -> check_expr labels e k
         in
         let@ () = pure (aux carg "true" e1) in
         let@ () = pure (aux (not_ carg loc) "false" e2) in
         return ())
     | Ebound e ->
       let@ () = ensure_base_type (Mu.loc_of_expr e) ~expect (Mu.bt_of_expr e) in
       check_expr labels e k
     | End _ -> Cerb_debug.error "todo: End"
     | Elet (p, e1, e2) ->
       let@ () = ensure_base_type (Mu.loc_of_expr e2) ~expect (Mu.bt_of_expr e2) in
       let@ () =
         ensure_base_type
           (Mu.loc_of_pattern p)
           ~expect:(Mu.bt_of_pexpr e1)
           (Mu.bt_of_pattern p)
       in
       check_pexpr e1 (fun v1 ->
         let@ bound_a = check_and_match_pattern p v1 in
         check_expr labels e2 (fun rt ->
           let@ () = remove_as bound_a in
           k rt))
     | Eunseq es ->
       let@ () = ensure_base_type loc ~expect (Tuple (List.map Mu.bt_of_expr es)) in
       let rec aux es vs prev_used =
         match es with
         | e :: es' ->
           let@ pre_check = all_resources_tagged loc in
           check_expr labels e (fun v ->
             let@ post_check = all_resources_tagged loc in
             let@ used = compute_used loc pre_check post_check in
             aux es' (v :: vs) (used :: prev_used))
         | [] ->
           (* let@ () = check_used_distinct loc prev_used in *)
           k (tuple_ (List.rev vs) loc)
       in
       aux es [] []
     | CN_progs (_, cn_progs) ->
       let bytes_pred ct pointer init : Req.Predicate.t =
         { name = Owned (ct, init); pointer; iargs = [] }
       in
       let bytes_constraints ~(value : IT.t) ~(byte_arr : IT.t) (ct : Sctypes.t) =
         (* FIXME this hard codes big endianness but this should be switchable *)
         let here = Locations.other __LOC__ in
         match ct with
         | Sctypes.Void | Array (_, _) | Struct _ | Function (_, _, _) -> assert false
         | Integer it ->
           let bt = IT.get_bt value in
           let lhs = value in
           let rhs =
             let[@ocaml.warning "-8"] (b :: bytes) =
               List.init (Memory.size_of_integer_type it) (fun i ->
                 let index = int_lit_ i WellTyped.quantifier_bt here in
                 let casted = cast_ bt (map_get_ byte_arr index here) here in
                 let shift_amt = int_lit_ (i * 8) bt here in
                 IT.IT (Binop (ShiftLeft, casted, shift_amt), bt, here))
             in
             List.fold_left (fun x y -> IT.add_ (x, y) here) b bytes
           in
           eq_ (lhs, rhs) here
         | Pointer _ ->
           (* FIXME this totally ignores provenances *)
           let bt = WellTyped.quantifier_bt in
           let lhs = cast_ bt value here in
           let rhs =
             let[@ocaml.warning "-8"] (b :: bytes) =
               List.init Memory.size_of_pointer (fun i ->
                 let index = int_lit_ i bt here in
                 let casted = cast_ bt (map_get_ byte_arr index here) here in
                 let shift_amt = int_lit_ (i * 8) bt here in
                 IT.IT (Binop (ShiftLeft, casted, shift_amt), bt, here))
             in
             List.fold_left (fun x y -> IT.add_ (x, y) here) b bytes
           in
           eq_ (lhs, rhs) here
       in
       let@ () = ensure_base_type loc ~expect Unit in
       let aux loc stmt =
         (* copying bits of code from elsewhere in check.ml *)
         match stmt with
         | Cnprog.Pack_unpack (_pack_unpack, _pt) ->
           warn loc !^"Explicit pack/unpack unsupported.";
           return ()
         | To_from_bytes ((To | From), { name = PName _; _ }) ->
           fail (fun _ -> { loc; msg = Byte_conv_needs_owned })
         | To_from_bytes (To, { name = Owned (ct, init); pointer; _ }) ->
           let@ pointer = WellTyped.WIT.infer pointer in
           let@ (_, O value), _ =
             RI.Special.predicate_request
               loc
               (Access To_bytes)
               (bytes_pred ct pointer init, None)
           in
           let q_sym = Sym.fresh_named "to_bytes" in
           let bt = WellTyped.quantifier_bt in
           let map_bt = BT.Map (bt, Memory.bt_of_sct Sctypes.uchar_ct) in
           let byte_sym, byte_arr = IT.fresh_named map_bt "byte_arr" here in
           let@ () = add_a byte_sym map_bt (loc, lazy (Pp.string "byte array")) in
           let@ () = add_r loc (Q (bytes_qpred q_sym ct pointer init), O byte_arr) in
           (match init with
            | Uninit -> add_c loc (LC.T (IT.eq_ (byte_arr, default_ map_bt here) here))
            | Init -> add_c loc (LC.T (bytes_constraints ~value ~byte_arr ct)))
         | To_from_bytes (From, { name = Owned (ct, init); pointer; _ }) ->
           let@ pointer = WellTyped.WIT.infer pointer in
           let q_sym = Sym.fresh_named "from_bytes" in
           let@ (_, O byte_arr), _ =
             RI.Special.qpredicate_request
               loc
               (Access From_bytes)
               (bytes_qpred q_sym ct pointer init, None)
           in
           let value_bt = Memory.bt_of_sct ct in
           let value_sym, value = IT.fresh_named value_bt "value" here in
           let@ () =
             add_a value_sym value_bt (loc, lazy (Pp.string "value from bytes"))
           in
           let@ () = add_r loc (P (bytes_pred ct pointer init), O value) in
           let@ () =
             (* TODO - why is this constraint necessary here? *)
             add_c here (LC.T (IT.good_pointer ~pointee_ct:ct pointer here))
           in
           (match init with
            | Uninit -> add_c loc (LC.T (IT.eq_ (value, default_ value_bt here) here))
            | Init -> add_c loc (LC.T (bytes_constraints ~value ~byte_arr ct)))
         | Have lc ->
           let@ _lc = WellTyped.WLC.welltyped loc lc in
           fail (fun _ -> { loc; msg = Generic !^"todo: 'have' not implemented yet" })
         | Instantiate (to_instantiate, it) ->
           let@ filter =
             match to_instantiate with
             | I_Everything -> return (fun _ -> true)
             | I_Function f ->
               let@ _ = get_logical_function_def loc f in
               return (IT.mentions_call f)
             | I_Good ct ->
               let@ () = WellTyped.WCT.is_ct loc ct in
               return (IT.mentions_good ct)
           in
           let@ it = WellTyped.WIT.infer it in
           instantiate loc filter it
         | Split_case _ -> assert false
         | Extract (attrs, to_extract, it) ->
           let@ predicate_name =
             match to_extract with
             | E_Everything ->
               let msg = "'extract' requires a predicate name annotation" in
               fail (fun _ -> { loc; msg = Generic !^msg })
             | E_Pred (CN_owned None) ->
               let msg = "'extract' requires a C-type annotation for 'Owned'" in
               fail (fun _ -> { loc; msg = Generic !^msg })
             | E_Pred (CN_owned (Some ct)) ->
               let@ () = WellTyped.WCT.is_ct loc ct in
               return (Request.Owned (ct, Init))
             | E_Pred (CN_block None) ->
               let msg = "'extract' requires a C-type annotation for 'Block'" in
               fail (fun _ -> { loc; msg = Generic !^msg })
             | E_Pred (CN_block (Some ct)) ->
               let@ () = WellTyped.WCT.is_ct loc ct in
               return (Request.Owned (ct, Uninit))
             | E_Pred (CN_named pn) ->
               let@ _ = get_resource_predicate_def loc pn in
               return (Request.PName pn)
           in
           let@ it = WellTyped.WIT.infer it in
           let@ original_rs, _ = all_resources_tagged loc in
           (* let verbose = List.exists (Id.is_str "verbose") attrs in *)
           let quiet = List.exists (Id.equal_string "quiet") attrs in
           let@ () = add_movable_index loc (predicate_name, it) in
           let@ upd_rs, _ = all_resources_tagged loc in
           if
             List.equal Int.equal (List.map snd original_rs) (List.map snd upd_rs)
             && not quiet
           then
             warn loc !^"extract: index added, no resources (yet) extracted."
           else
             ();
           return ()
         | Unfold (f, args) ->
           let@ def = get_logical_function_def loc f in
           let has_args, expect_args = (List.length args, List.length def.args) in
           let@ () =
             WellTyped.ensure_same_argument_number
               loc
               `General
               has_args
               ~expect:expect_args
           in
           let@ args =
             ListM.map2M
               (fun has_arg (_, def_arg_bt) -> WellTyped.WIT.check loc def_arg_bt has_arg)
               args
               def.args
           in
           (match Definition.Function.unroll_once def args with
            | None ->
              let msg =
                !^"Cannot unfold definition of uninterpreted function" ^^^ Sym.pp f ^^ dot
              in
              fail (fun _ -> { loc; msg = Generic msg })
            | Some body ->
              add_c loc (LC.T (eq_ (apply_ f args def.return_bt loc, body) loc)))
         | Apply (lemma, args) ->
           let@ _loc, lemma_typ = get_lemma loc lemma in
           let args = List.map (fun arg -> (loc, arg)) args in
           Spine.calltype_lemma loc ~lemma args lemma_typ (fun lrt ->
             let@ _, members =
               make_return_record
                 loc
                 (TypeErrors.call_prefix (LemmaApplication lemma))
                 (LRT.binders lrt)
             in
             let@ () = bind_logical_return loc members lrt in
             return ())
         | Assert lc ->
           let@ lc = WellTyped.WLC.welltyped loc lc in
           let@ provable = provable loc in
           (match provable lc with
            | `True -> return ()
            | `False ->
              let@ model = model () in
              let@ simp_ctxt = simp_ctxt () in
              RI.debug_constraint_failure_diagnostics 6 model simp_ctxt lc;
              let@ () = Diagnostics.investigate model lc in
              fail (fun ctxt ->
                { loc;
                  msg =
                    Unproven_constraint
                      { constr = lc; info = (loc, None); requests = []; ctxt; model }
                }))
         | Inline _nms -> return ()
         | Print it ->
           let@ it = WellTyped.WIT.infer it in
           let@ simp_ctxt = simp_ctxt () in
           let it = Simplify.IndexTerms.simp simp_ctxt it in
           print stdout (item "printed" (IT.pp it));
           return ()
       in
       let rec loop = function
         | [] -> k (unit_ loc)
         | Cnprog.Let (loc, (sym, { ct; pointer }), cn_prog) :: cn_progs ->
           let@ pointer = WellTyped.WIT.check loc (Loc ()) pointer in
           let@ () = WellTyped.WCT.is_ct loc ct in
           let@ value = load loc pointer ct in
           let subbed = Cnprog.subst (IT.make_subst [ (sym, value) ]) cn_prog in
           loop (subbed :: cn_progs)
         | Cnprog.Statement (loc, cn_statement) :: cn_progs ->
           (match cn_statement with
            | Cnprog.Split_case lc ->
              Pp.debug 5 (lazy (Pp.headline "checking split_case"));
              let@ lc = WellTyped.WLC.welltyped loc lc in
              let@ it =
                match lc with
                | T it -> return it
                | Forall ((_sym, _bt), _it) ->
                  fail (fun _ ->
                    { loc; msg = Generic !^"Cannot split on forall condition" })
              in
              let branch it nm =
                let@ () = add_c loc (LC.T it) in
                debug 5 (lazy (item ("splitting case " ^ nm) (IT.pp it)));
                let@ provable = provable loc in
                let here = Locations.other __LOC__ in
                match provable (LC.T (bool_ false here)) with
                | `True ->
                  Pp.debug 5 (lazy (Pp.headline "inconsistent, skipping"));
                  return ()
                | `False ->
                  Pp.debug 5 (lazy (Pp.headline "consistent, continuing"));
                  loop cn_progs
              in
              let@ () = pure @@ branch it "true" in
              let@ () = pure @@ branch (not_ it loc) "false" in
              return ()
            | _ ->
              let@ () = aux loc cn_statement in
              loop cn_progs)
       in
       loop cn_progs
     | Ewseq (p, e1, e2) | Esseq (p, e1, e2) ->
       let@ () = ensure_base_type loc ~expect (Mu.bt_of_expr e2) in
       let@ () =
         ensure_base_type
           (Mu.loc_of_pattern p)
           ~expect:(Mu.bt_of_expr e1)
           (Mu.bt_of_pattern p)
       in
       check_expr labels e1 (fun it ->
         let@ bound_a = check_and_match_pattern p it in
         check_expr labels e2 (fun it2 ->
           let@ () = remove_as bound_a in
           k it2))
     | Erun (label_sym, pes) ->
       let@ () = ensure_base_type loc ~expect Unit in
       let@ lt, lkind =
         match Sym.Map.find_opt label_sym labels with
         | None ->
           fail (fun _ ->
             { loc; msg = Generic (!^"undefined code label" ^/^ Sym.pp label_sym) })
         | Some (lt, lkind, _) -> return (lt, lkind)
       in
       let@ original_resources = all_resources_tagged loc in
       Spine.calltype_lt loc pes (lt, lkind) (fun False ->
         let@ () = all_empty loc original_resources in
         return ()))


let check_expr_top loc labels rt e =
  let@ () = ensure_base_type loc ~expect:Unit (Mu.bt_of_expr e) in
  check_expr labels e (fun lvt ->
    let (RT.Computational ((return_s, return_bt), _info, lrt)) = rt in
    match return_bt with
    | Unit ->
      let lrt = LRT.subst (IT.make_subst [ (return_s, lvt) ]) lrt in
      let@ original_resources = all_resources_tagged loc in
      Spine.subtype loc lrt (fun () ->
        let@ () = all_empty loc original_resources in
        return ())
    | _ ->
      let msg = "Non-void-return function does not call 'return'." in
      fail (fun _ -> { loc; msg = Generic !^msg }))


(* let check_pexpr_rt loc pexpr (RT.Computational ((return_s, return_bt), info, lrt)) = *)
(*   check_pexpr pexpr ~expect:return_bt (fun lvt -> *)
(*   let lrt = LRT.subst (IT.make_subst [(return_s, lvt)]) lrt in *)
(*   let@ original_resources = all_resources_tagged () in *)
(*   Spine.subtype loc lrt (fun () -> *)
(*   let@ () = all_empty loc original_resources in *)
(*   return ())) *)

let bind_arguments (_loc : Locations.t) (full_args : _ Mu.arguments) =
  let rec aux_l resources = function
    | Mu.Define ((s, it), ((loc, _) as info), args) ->
      let@ () = add_l s (IT.get_bt it) (fst info, lazy (Sym.pp s)) in
      let@ () = add_c (fst info) (LC.T (def_ s it loc)) in
      aux_l resources args
    | Constraint (lc, info, args) ->
      let@ () = add_c (fst info) lc in
      aux_l resources args
    | Resource ((s, (re, bt)), ((loc, _) as info), args) ->
      let@ () = add_l s bt (fst info, lazy (Sym.pp s)) in
      aux_l (resources @ [ (re, Resource.O (sym_ (s, bt, loc))) ]) args
    | I i -> return (i, resources)
  in
  let rec aux_a = function
    | Mu.Computational ((s, bt), info, args) ->
      let@ () = add_a s bt (fst info, lazy (Sym.pp s)) in
      aux_a args
    | L args -> aux_l [] args
  in
  aux_a full_args


let post_state_of_rt loc rt =
  let open False in
  let rt_as_at = AT.of_rt rt (LAT.I False) in
  let rt_as_args = Core_to_mucore.arguments_of_at (fun False -> False) rt_as_at in
  pure
    (let@ False, final_resources = bind_arguments loc rt_as_args in
     let@ () = add_rs loc final_resources in
     get_typing_context ())


(* check_procedure: type check an (impure) procedure *)
let check_procedure
  (loc : Locations.t)
  (fsym : Sym.t)
  (args_and_body : _ Mu.args_and_body)
  : unit m
  =
  debug 2 (lazy (headline ("checking procedure " ^ Sym.pp_string fsym)));
  pure
    (let@ () = modify_where (Where.set_function fsym) in
     let@ (body, label_defs, rt), initial_resources = bind_arguments loc args_and_body in
     let label_context = WellTyped.WProc.label_context rt label_defs in
     let label_defs = Pmap.bindings_list label_defs in
     let@ (), _mete_pre_state =
       debug 2 (lazy (headline ("checking function body " ^ Sym.pp_string fsym)));
       pure
         (let@ () = add_rs loc initial_resources in
          let@ pre_state = get_typing_context () in
          let@ () = modify_where (Where.set_section Body) in
          let@ () = check_expr_top loc label_context rt body in
          return ((), pre_state))
     in
     let@ _mete_post_state = post_state_of_rt loc rt in
     let@ () =
       ListM.iterM
         (fun (lsym, def) ->
           pure
             (match def with
              | Mu.Return _loc -> return ()
              | Label (loc, label_args_and_body, _annots, _, _loop_info) ->
                debug
                  2
                  (lazy
                    (headline
                       ("checking label "
                        ^ Sym.pp_string lsym
                        ^ " "
                        ^ Locations.to_string loc)));
                let@ label_body, label_resources =
                  bind_arguments loc label_args_and_body
                in
                let@ () = add_rs loc label_resources in
                let _, label_kind, loc = Sym.Map.find lsym label_context in
                let@ () =
                  modify_where Where.(set_section (Label { loc; label = label_kind }))
                in
                check_expr_top loc label_context rt label_body))
         label_defs
     in
     return ())


let skip_and_only = ref (([] : string list), ([] : string list))

(** When set, causes verification of multiple functions to abort as soon as a
    single function fails to verify. *)
let fail_fast = ref false

let record_tagdefs tagDefs =
  PmapM.iterM
    (fun tag def ->
      match def with
      | Mu.UnionDef -> unsupported (Loc.other __LOC__) !^"todo: union types"
      | StructDef layout -> add_struct_decl tag layout)
    tagDefs


let check_tagdefs tagDefs =
  PmapM.iterM
    (fun _tag def ->
      let open Memory in
      match def with
      | Mu.UnionDef -> unsupported (Loc.other __LOC__) !^"todo: union types"
      | StructDef layout ->
        let@ _ =
          ListM.fold_rightM
            (fun piece have ->
              match piece.member_or_padding with
              | Some (name, _) when IdSet.mem name have ->
                (* this should have been checked earlier by the frontend *)
                assert false
              | Some (name, ct) ->
                let@ () = WellTyped.WCT.is_ct (Loc.other __LOC__) ct in
                return (IdSet.add name have)
              | None -> return have)
            layout
            IdSet.empty
        in
        return ())
    tagDefs


let record_and_check_logical_functions funs =
  let recursive, _nonrecursive =
    List.partition (fun (_, def) -> Definition.Function.is_recursive def) funs
  in
  let n_funs = List.length funs in
  (* Add all recursive functions (without their actual bodies), so that they
     can depend on themselves and each other. *)
  let@ () =
    ListM.iterM
      (fun (name, def) ->
        let@ simple_def = WellTyped.WLFD.welltyped { def with body = Uninterp } in
        add_logical_function name simple_def)
      recursive
  in
  (* Now check all functions in order. *)
  ListM.iteriM
    (fun i (name, def) ->
      debug
        2
        (lazy
          (headline
             ("checking welltypedness of function"
              ^ Pp.of_total i n_funs
              ^ ": "
              ^ Sym.pp_string name)));
      let@ def = WellTyped.WLFD.welltyped def in
      add_logical_function name def)
    funs


let record_and_check_resource_predicates preds =
  (* add the names to the context, so recursive preds check *)
  let@ () =
    ListM.iterM
      (fun (name, def) ->
        let@ simple_def = WellTyped.WRPD.welltyped { def with clauses = None } in
        add_resource_predicate name simple_def)
      preds
  in
  ListM.iteriM
    (fun i (name, def) ->
      debug
        2
        (lazy
          (headline
             ("checking welltypedness of resource pred"
              ^ Pp.of_total i (List.length preds)
              ^ ": "
              ^ Sym.pp_string name)));
      let@ def = WellTyped.WRPD.welltyped def in
      (* add simplified def to the context *)
      add_resource_predicate name def)
    preds


let record_globals : 'bty. (Sym.t * 'bty Mu.globs) list -> LC.t list m =
  fun globs ->
  ListM.fold_leftM
    (fun acc (sym, def) ->
      match def with
      | Mu.GlobalDef (ct, _) | GlobalDecl ct ->
        let@ () = WellTyped.WCT.is_ct (Loc.other __LOC__) ct in
        let bt = BT.(Loc ()) in
        let info = (Loc.other __LOC__, lazy (Pp.item "global" (Sym.pp sym))) in
        let@ () = add_a sym bt info in
        let here = Locations.other __LOC__ in
        let good = LC.T (IT.good_pointer ~pointee_ct:ct (sym_ (sym, bt, here)) here) in
        let ptr = sym_ (sym, bt, here) in
        let hasAllocId = LC.T (IT.hasAllocId_ ptr here) in
        let range =
          if !IT.use_vip then
            let module H = Alloc.History in
            let H.{ base; size } = H.(split (lookup_ptr ptr here) here) in
            let addr = addr_ ptr here in
            let upper = IT.upper_bound addr ct here in
            let bounds =
              and_
                [ le_ (base, addr) here;
                  le_ (addr, upper) here;
                  le_ (upper, add_ (base, size) here) here
                ]
                here
            in
            [ LC.T bounds ]
          else
            []
        in
        (* TODO: check the expressions *)
        return (good :: hasAllocId :: (range @ acc)))
    []
    globs


let register_fun_syms file =
  let add fsym loc =
    (* add to context *)
    (* let lc1 = LC.T (ne_ (null_, sym_ (fsym, Loc))) in *)
    (* let lc2 = LC.T (representable_ (Pointer Void, sym_ (fsym, Loc, loc)) loc) in *)
    let@ () = add_l fsym (Loc ()) (loc, lazy (Pp.item "global fun-ptr" (Sym.pp fsym))) in
    (* let@ () = add_cs loc [(\* lc1; *\) lc2] in *)
    return ()
  in
  PmapM.iterM
    (fun fsym def ->
      match def with
      | Mu.Proc { loc; _ } -> add fsym loc
      | ProcDecl (loc, _) -> add fsym loc)
    file.Mu.funs


let wf_check_and_record_functions funs call_sigs =
  let n_syms = List.length (Pmap.bindings_list funs) in
  let welltyped_ping i fsym =
    debug
      2
      (lazy
        (headline
           ("checking welltypedness of procedure"
            ^ Pp.of_total i n_syms
            ^ ": "
            ^ Sym.pp_string fsym)))
  in
  PmapM.foldiM
    (fun i fsym def (trusted, checked) ->
      match def with
      | Mu.Proc { loc; args_and_body; trusted = tr; _ } ->
        welltyped_ping i fsym;
        let@ args_and_body = WellTyped.WProc.welltyped loc args_and_body in
        let ft = WellTyped.WProc.typ args_and_body in
        debug 6 (lazy (!^"function type" ^^^ Sym.pp fsym));
        debug 6 (lazy (CF.Pp_ast.pp_doc_tree (AT.dtree RT.dtree ft)));
        let@ () = add_fun_decl fsym (loc, Some ft, Pmap.find fsym call_sigs) in
        (match tr with
         | Trusted _ -> return ((fsym, (loc, ft)) :: trusted, checked)
         | Checked -> return (trusted, (fsym, (loc, args_and_body)) :: checked))
      | ProcDecl (loc, oft) ->
        welltyped_ping i fsym;
        let@ oft =
          match oft with
          | None -> return None
          | Some ft ->
            let@ ft = WellTyped.WFT.welltyped "function" loc ft in
            return (Some ft)
        in
        let@ () = add_fun_decl fsym (loc, oft, Pmap.find fsym call_sigs) in
        return (trusted, checked))
    funs
    ([], [])


type c_function = Sym.t * (Locations.t * BT.t Mu.args_and_body)

let c_function_name ((fsym, (_loc, _args_and_body)) : c_function) : string =
  Sym.pp_string fsym


(** Filter functions according to [skip_and_only]: first according to "only",
    then according to "skip" *)
let select_functions (fsyms : Sym.Set.t) : Sym.Set.t =
  let matches_str s fsym = String.equal s (Sym.pp_string fsym) in
  let str_fsyms s =
    let ss = Sym.Set.filter (matches_str s) fsyms in
    if Sym.Set.is_empty ss then (
      Pp.warn_noloc (!^"function" ^^^ !^s ^^^ !^"not found");
      Sym.Set.empty)
    else
      ss
  in
  let strs_fsyms ss =
    ss |> List.map str_fsyms |> List.fold_left Sym.Set.union Sym.Set.empty
  in
  let skip = strs_fsyms (fst !skip_and_only) in
  let only = strs_fsyms (snd !skip_and_only) in
  let only_funs =
    match snd !skip_and_only with
    | [] -> fsyms
    | _ss -> Sym.Set.filter (fun fsym -> Sym.Set.mem fsym only) fsyms
  in
  Sym.Set.filter (fun fsym -> not (Sym.Set.mem fsym skip)) only_funs


(** Check a single C function. Failure of the check is encoded monadically. *)
let check_c_function ((fsym, (loc, args_and_body)) : c_function) : unit m =
  check_procedure loc fsym args_and_body


(** Check the provided C functions. The first failed check will short-circuit
    the remainder of the checks, and the associated error will be returned as
    [Some], along with the name of the function in which it occurred. *)
let check_c_functions_fast (funs : c_function list) : (string * TypeErrors.t) option m =
  let total = List.length funs in
  let check_and_record (num_checked, prev_error) c_fn =
    match prev_error with
    | Some _ -> return (num_checked, prev_error)
    | None ->
      let fn_name = c_function_name c_fn in
      let@ outcome = sandbox (check_c_function c_fn) in
      let checked = num_checked + 1 in
      (match outcome with
       | Ok () ->
         progress_simple (of_total checked total) (fn_name ^ " -- pass");
         return (checked, None)
       | Error err ->
         progress_simple (of_total checked total) (fn_name ^ " -- fail");
         return (checked, Some (fn_name, err)))
  in
  let@ _num_checked, error = ListM.fold_leftM check_and_record (0, None) funs in
  return error


(** Check the provided C functions, each in an isolated context, capturing any
    (monadic) check failures and returning them. All checks will be performed
    regardless of intermediate failures. Errors are paired with the name of
    the function in which they occurred.

    The result's order is determined by the input's order: if function [f]
    appears before function [g], then function [f]'s error (if any) will appear
    before function [g]'s error (if any). *)
let check_c_functions_all (funs : c_function list) : (string * TypeErrors.t) list m =
  let total = List.length funs in
  let check_and_record (num_checked, errors) c_fn =
    let fn_name = c_function_name c_fn in
    let@ outcome = sandbox (check_c_function c_fn) in
    let checked = num_checked + 1 in
    match outcome with
    | Ok () ->
      progress_simple (of_total checked total) (fn_name ^ " -- pass");
      return (checked, errors)
    | Error err ->
      progress_simple (of_total checked total) (fn_name ^ " -- fail");
      return (checked, (fn_name, err) :: errors)
  in
  let@ _num_checked, errors = ListM.fold_leftM check_and_record (0, []) funs in
  return (List.rev errors)


(** Downselect from the provided functions with [select_functions] and check the
    results. Errors in checking are captured, collected, and returned, along
    with the name of the function in which they occurred. When [fail_fast] is
    set, the first error encountered will halt checking. *)
let check_c_functions (funs : c_function list) : (string * TypeErrors.t) list m =
  let selected_fsyms = select_functions (Sym.Set.of_list (List.map fst funs)) in
  let selected_funs =
    List.filter (fun (fsym, _) -> Sym.Set.mem fsym selected_fsyms) funs
  in
  match !fail_fast with
  | true ->
    let@ error_opt = check_c_functions_fast selected_funs in
    return (Option.to_list error_opt)
  | false -> check_c_functions_all selected_funs


(* (Sym.t * (Locations.t * ArgumentTypes.lemmat)) list *)

let wf_check_and_record_lemma (lemma_s, (loc, lemma_typ)) =
  let@ lemma_typ = WellTyped.WLemma.welltyped loc lemma_s lemma_typ in
  let@ () = add_lemma lemma_s (loc, lemma_typ) in
  return (lemma_s, (loc, lemma_typ))


let ctz_proxy_ft =
  let here = Locations.other __LOC__ in
  let info = (here, Some "ctz_proxy builtin ft") in
  let n_sym, n = IT.fresh_named BT.(Bits (Unsigned, 32)) "n_" here in
  let ret_sym, ret = IT.fresh_named BT.(Bits (Signed, 32)) "return" here in
  let neq_0 = LC.T (IT.not_ (IT.eq_ (n, IT.int_lit_ 0 (IT.get_bt n) here) here) here) in
  let eq_ctz =
    LC.T
      (IT.eq_
         (ret, cast_ (IT.get_bt ret) (IT.arith_unop Terms.BW_CTZ_NoSMT n here) here)
         here)
  in
  let rt =
    RT.mComputational
      ((ret_sym, IT.get_bt ret), info)
      (LRT.mConstraint (eq_ctz, info) LRT.I)
  in
  let ft =
    AT.mComputationals
      [ (n_sym, IT.get_bt n, info) ]
      (AT.L (LAT.mConstraint (neq_0, info) (LAT.I rt)))
  in
  ft


let ffs_proxy_ft sz =
  let here = Locations.other __LOC__ in
  let sz_name = CF.Pp_ail.string_of_integerBaseType sz in
  let bt = Memory.bt_of_sct Sctypes.(Integer (Signed sz)) in
  let ret_bt = Memory.bt_of_sct Sctypes.(Integer (Signed Int_)) in
  let info = (Locations.other __LOC__, Some ("ffs_proxy builtin ft: " ^ sz_name)) in
  let n_sym, n = IT.fresh_named bt "n_" here in
  let ret_sym, ret = IT.fresh_named ret_bt "return" here in
  let eq_ffs =
    LC.T
      (IT.eq_ (ret, IT.cast_ ret_bt (IT.arith_unop Terms.BW_FFS_NoSMT n here) here) here)
  in
  let rt =
    RT.mComputational ((ret_sym, ret_bt), info) (LRT.mConstraint (eq_ffs, info) LRT.I)
  in
  let ft = AT.mComputationals [ (n_sym, bt, info) ] (AT.L (LAT.I rt)) in
  ft


let memcpy_proxy_ft =
  let here = Locations.other __LOC__ in
  let info = (here, Some "memcpy_proxy") in
  (* C arguments *)
  let dest_sym, dest = IT.fresh_named (BT.Loc ()) "dest" here in
  let src_sym, src = IT.fresh_named (BT.Loc ()) "src" here in
  let n_sym, n = IT.fresh_named Memory.size_bt "n" here in
  (* requires *)
  let q_bt = WellTyped.quantifier_bt in
  let uchar_bt = Memory.bt_of_sct Sctypes.uchar_ct in
  let map_bt = BT.Map (q_bt, uchar_bt) in
  let destIn_sym, _ = IT.fresh_named map_bt "destIn" here in
  let srcIn_sym, srcIn = IT.fresh_named map_bt "srcIn" here in
  let destRes str init = Req.Q (bytes_qpred (Sym.fresh_named str) n dest init) in
  let srcRes str = Req.Q (bytes_qpred (Sym.fresh_named str) n src Init) in
  (* ensures *)
  let ret_sym, ret = IT.fresh_named (BT.Loc ()) "return" here in
  let destOut_sym, destOut = IT.fresh_named map_bt "destOut" here in
  let srcOut_sym, srcOut = IT.fresh_named map_bt "srcOut" here in
  AT.mComputationals
    [ (dest_sym, Loc (), info); (src_sym, Loc (), info); (n_sym, Memory.size_bt, info) ]
    (AT.L
       (LAT.mResources
          [ ((destIn_sym, (destRes "i_d" Uninit, map_bt)), info);
            ((srcIn_sym, (srcRes "i_s", map_bt)), info)
          ]
          (LAT.I
             (RT.mComputational
                ((ret_sym, BT.Loc ()), info)
                (LRT.mResources
                   [ ((destOut_sym, (destRes "j_d" Init, map_bt)), info);
                     ((srcOut_sym, (srcRes "j_s", map_bt)), info)
                   ]
                   (LRT.Constraint
                      ( LC.T
                          (and_
                             [ eq_ (ret, dest) here;
                               eq_ (srcIn, srcOut) here;
                               eq_ (srcIn, destOut) here
                             ]
                             here),
                        info,
                        I )))))))


let add_stdlib_spec =
  let module StrMap = Map.Make (String) in
  let proxies =
    List.fold_left
      (fun map (name, ft) -> StrMap.add name ft map)
      StrMap.empty
      [ ("ctz_proxy", ctz_proxy_ft);
        ("ffs_proxy", ffs_proxy_ft Sctypes.IntegerBaseTypes.Int_);
        ("ffsl_proxy", ffs_proxy_ft Sctypes.IntegerBaseTypes.Long);
        ("ffsll_proxy", ffs_proxy_ft Sctypes.IntegerBaseTypes.LongLong);
        ("memcpy_proxy", memcpy_proxy_ft)
      ]
  in
  let add ct fsym ft =
    Pp.debug
      2
      (lazy (Pp.headline ("adding builtin spec for procedure " ^ Sym.pp_string fsym)));
    add_fun_decl fsym (Locations.other __LOC__, Some ft, ct)
  in
  fun call_sigs fsym ->
    match
      Option.(
        let@ s = Sym.has_id fsym in
        let@ ft = StrMap.find_opt s proxies in
        (* The C signatures for most of the proxies are included in
           ./runtime/libc/include/builtins.h, and so show up in every file,
           regardless of whether or not they are used, but the same is not true
           for memcpy (its C signature is only present when it is used) hence
           (1) the extra lookup and (2) it being safe to skip if absent *)
        let@ ct = Pmap.lookup fsym call_sigs in
        return (ft, ct))
    with
    | None -> return ()
    | Some (ft, ct) -> add ct fsym ft


let record_and_check_datatypes datatypes =
  (* add "empty datatypes" for checks on recursive types to succeed *)
  let@ () =
    ListM.iterM
      (fun (s, Mu.{ loc = _; cases = _ }) ->
        add_datatype s { constrs = []; all_params = [] })
      datatypes
  in
  (* check and normalise datatypes *)
  let@ datatypes = ListM.mapM WellTyped.WDT.welltyped datatypes in
  let@ sccs = WellTyped.WDT.check_recursion_ok datatypes in
  let@ () = set_datatype_order (Some sccs) in
  (* properly add datatypes *)
  ListM.iterM
    (fun (s, Mu.{ loc = _; cases }) ->
      let@ () =
        add_datatype
          s
          { constrs = List.map fst cases; all_params = List.concat_map snd cases }
      in
      ListM.iterM
        (fun (c, params) -> add_datatype_constr c { params; datatype_tag = s })
        cases)
    datatypes


(** Note: this does not check loop invariants and CN statements! *)
let check_decls_lemmata_fun_specs (file : unit Mu.file) =
  Cerb_debug.begin_csv_timing ();
  (* decl, lemmata, function specification checking *)
  Pp.debug 3 (lazy (Pp.headline "checking decls, lemmata and function specifications"));
  let@ () = record_tagdefs file.tagDefs in
  let@ () = check_tagdefs file.tagDefs in
  let@ () = record_and_check_datatypes file.datatypes in
  let@ global_var_constraints = record_globals file.globs in
  let@ () = register_fun_syms file in
  let@ () =
    ListM.iterM (add_stdlib_spec file.call_funinfo) (Sym.Set.elements file.stdlib_syms)
  in
  Pp.debug 3 (lazy (Pp.headline "added top-level types and constants."));
  let@ () = record_and_check_logical_functions file.logical_predicates in
  let@ () = record_and_check_resource_predicates file.resource_predicates in
  let@ lemmata = ListM.mapM wf_check_and_record_lemma file.lemmata in
  let@ () =
    CLogicalFuns.add_logical_funs_from_c file.call_funinfo file.mk_functions file.funs
  in
  Pp.debug 3 (lazy (Pp.headline "type-checked CN top-level declarations."));
  let@ _trusted, checked = wf_check_and_record_functions file.funs file.call_funinfo in
  Pp.debug 3 (lazy (Pp.headline "type-checked C functions and specifications."));
  Cerb_debug.end_csv_timing "decl, lemmata, function specification checking";
  return (List.rev checked, global_var_constraints, lemmata)


(** With CSV timing enabled, check the provided functions with
    [check_c_functions]. See that function for more information on the
    semantics of checking. *)
let time_check_c_functions (global_var_constraints, (checked : c_function list))
  : (string * TypeErrors.t) list m
  =
  Cerb_debug.begin_csv_timing () (*type checking functions*);
  let@ () = init_solver () in
  let here = Locations.other __LOC__ in
  let@ () = add_cs here global_var_constraints in
  let@ global = get_global () in
  let@ () =
    Sym.Map.fold
      (fun _ def acc ->
        (* I think this avoids a left-recursion in the monad bind *)
        let@ () = WellTyped.WRPD.consistent def in
        acc)
      global.resource_predicates
      (return ())
  in
  let@ () =
    Sym.Map.fold
      (fun _ (loc, def, _) acc ->
        match def with
        | None -> acc
        | Some def ->
          (* I think this avoids a left-recursion in the monad bind *)
          let@ () = WellTyped.WFT.consistent "proc/fun" loc def in
          acc)
      global.fun_decls
      (return ())
  in
  let@ errors = check_c_functions checked in
  Cerb_debug.end_csv_timing "type checking functions";
  return errors


let generate_lemmas lemmata o_lemma_mode =
  let@ global = get_global () in
  match o_lemma_mode with
  | Some mode ->
    let@ () =
      Sym.Map.fold
        (fun sym (loc, lemma_typ) acc ->
          (* I think this avoids a left-recursion in the monad bind *)
          let@ () = WellTyped.WLemma.consistent loc sym lemma_typ in
          acc)
        global.lemmata
        (return ())
    in
    lift (Lemmata.generate global mode lemmata)
  | None -> return ()

(* TODO:
   - sequencing strength
   - rem_t vs rem_f
   - check globals with expressions
   - inline TODOs
   - make sure all variables disjoint from global variables and function names
   - check datatype definition wellformedness
*)
