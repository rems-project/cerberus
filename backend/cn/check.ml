module CF=Cerb_frontend
module RE = Resources
module RET = ResourceTypes
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module LRT = LogicalReturnTypes
module RT = ReturnTypes
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module TE = TypeErrors
module IdSet = Set.Make(Id)
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module S = Solver
module Loc = Locations
module LF = LogicalFunctions
module Mu = Mucore
module RI = ResourceInference
module IntSet = Set.Make(Int)
module IntMap = Map.Make(Int)

open Sctypes
open Context
open IT
open TypeErrors
open Mucore
open Pp
open BT
open Resources
open ResourceTypes
open ResourcePredicates
open LogicalConstraints
open List
open Typing
open Effectful.Make(Typing)
open WellTyped



(* some of this is informed by impl_mem *)


type mem_value = CF.Impl_mem.mem_value
type pointer_value = CF.Impl_mem.pointer_value




(*** pattern matching *********************************************************)


(* pattern-matches and binds *)
let rec check_and_match_pattern (M_Pattern (loc, _, bty, pattern)) it =
   match pattern with
   | M_CaseBase (o_s, _has_cbt) ->
      begin match o_s with
      | Some s ->
         let@ () = add_a_value s it (loc, lazy (Sym.pp s)) in
         return [s]
      | None ->
         return []
      end
   | M_CaseCtor (constructor, pats) ->
      match constructor, pats with
      | M_Cnil _item_cbt, [] ->
         let@ item_bt = match bty with
           | List item_bt -> return item_bt
           | _ -> fail (fun _ -> {loc; msg = Mismatch {has = !^"list"; expect = BT.pp bty}})
         in
         let@ () = add_c loc (LC.t_ (eq__ it (nil_ ~item_bt loc) loc)) in
         return []
      | M_Ccons, [p1; p2] ->
         let@ () = ensure_base_type loc ~expect:bty (List (bt_of_pattern p1)) in
         let@ () = ensure_base_type loc ~expect:bty (bt_of_pattern p2) in
         let item_bt = bt_of_pattern p1 in
         let@ a1 = check_and_match_pattern p1 (head_ ~item_bt it loc) in
         let@ a2 = check_and_match_pattern p2 (tail_ it loc) in
         let@ () = add_c loc (LC.t_ (ne_ (it, nil_ ~item_bt loc) loc)) in
         return (a1 @ a2)
      | M_Ctuple, pats ->
         let@ () = ensure_base_type loc ~expect:bty (Tuple (List.map bt_of_pattern pats)) in
         let@ all_as =
           ListM.mapiM (fun i p ->
               let ith = Simplify.IndexTerms.tuple_nth_reduce it i (bt_of_pattern p) in
               check_and_match_pattern p ith
             ) pats
         in
         return (List.concat all_as)
      | M_Carray, _ ->
         Cerb_debug.error "todo: array patterns"
      | _ ->
         assert false







(*** pure value inference *****************************************************)


let check_computational_bound loc s =
  let@ is_bound = bound_a s in
  if is_bound
  then return ()
  else fail (fun _ -> {loc; msg = Unknown_variable s})


let unsupported loc doc =
  fail (fun _ -> {loc; msg = Unsupported (!^"unsupported" ^^^ doc) })

let check_ptrval (loc : loc) ~(expect:BT.t) (ptrval : pointer_value) : IT.t m =
  let@ () = ensure_base_type loc ~expect BT.Loc in
  CF.Impl_mem.case_ptrval ptrval
    ( fun ct ->
      let sct = Sctypes.of_ctype_unsafe loc ct in
      let@ () = WellTyped.WCT.is_ct loc sct in
      return (IT.null_ loc) )
    ( function
        | None ->
            (* FIXME(CHERI merge) *)
            (* we can now have invalid function pointer values (e.g. if someone touched the bytes in a wrong way) *)
            unsupported loc !^"invalid function pointer"
        | Some sym ->
            (* just to make sure it exists *)
            let@ (_fun_loc, _, _) = get_fun_decl loc sym in
            (* the symbol of a function is the same as the symbol of its address *)
            let here = Locations.other __FUNCTION__ in
            return (sym_ (sym, BT.Loc, here)) )
    ( fun prov p ->
       let@ alloc_id =
          match prov with
            | Some id -> return id
            | None -> fail (fun _ -> {loc; msg = Empty_provenance }) in
        return (pointer_ ~alloc_id ~addr:p loc) )

let rec check_mem_value (loc : loc) ~(expect:BT.t) (mem : mem_value) : IT.t m =
  CF.Impl_mem.case_mem_value mem
    ( fun ct ->
      let@ () = WellTyped.WCT.is_ct loc (Sctypes.of_ctype_unsafe loc ct) in
      fail (fun _ -> {loc; msg = Unspecified ct}) )
    ( fun _ _ ->
      unsupported loc !^"infer_mem_value: concurrent read case" )
    ( fun ity iv ->
      let@ () = WellTyped.WCT.is_ct loc (Integer ity) in
      let bt = Memory.bt_of_sct (Integer ity) in
      let@ () = WellTyped.ensure_base_type loc ~expect bt in
      return (int_lit_ (Memory.int_of_ival iv) bt loc) )
    ( fun ft fv ->
      unsupported loc !^"floats" )
    ( fun ct ptrval ->
      (* TODO: do anything else with ct? *)
      let@ () = WellTyped.WCT.is_ct loc (Sctypes.of_ctype_unsafe loc ct) in
      check_ptrval loc ~expect ptrval )
    ( fun mem_values ->
      let@ index_bt, item_bt = match expect with
        | BT.Map (index_bt, item_bt) -> return (index_bt, item_bt)
        | _ ->
           let msg = Mismatch {has = !^"array"; expect = BT.pp expect} in
           fail (fun _ -> {loc; msg})
      in
      assert (BT.equal index_bt Integer);
      let@ values = ListM.mapM (check_mem_value loc ~expect:item_bt) mem_values in
      return (make_array_ ~item_bt values loc) )
    ( fun tag mvals ->
      let@ () = WellTyped.WCT.is_ct loc (Struct tag) in
      let@ () = WellTyped.ensure_base_type loc ~expect (Struct tag) in
      let mvals = List.map (fun (id,ct,mv) -> (id, Sctypes.of_ctype_unsafe loc ct, mv)) mvals in
      check_struct loc tag mvals )
    ( fun tag id mv ->
      check_union loc tag id mv )

and check_struct (loc : loc)
                 (tag : Sym.t)
                 (member_values : (Id.t * Sctypes.t * mem_value) list) : IT.t m =
  let@ layout = get_struct_decl loc tag in
  let member_types = Memory.member_types layout in
  assert (List.for_all2 (fun (id,ct) (id',ct',mv') -> Id.equal id id' && Sctypes.equal ct ct')
            member_types member_values);
  let@ member_its =
    ListM.mapM (fun (member, sct, mv) ->
        let@ member_lvt = check_mem_value loc ~expect:(Memory.bt_of_sct sct) mv in
        return (member, member_lvt)
      ) member_values
  in
  return (IT.struct_ (tag, member_its) loc)

and check_union (loc : loc) (tag : Sym.t) (id : Id.t)
                (mv : mem_value) : IT.t m =
  Cerb_debug.error "todo: union types"

let ensure_bitvector_type (loc : Loc.loc) ~(expect : BT.t) : (sign * int) m =
  match BT.is_bits_bt expect with
  | Some (sign, n) -> return (sign, n)
  | None -> fail (fun _ -> {loc; msg = Mismatch {has = !^"(unspecified) bitvector type";
    expect = BT.pp expect}})

let rec check_object_value (loc : loc) (M_OV (expect, ov)) : IT.t m =
  match ov with
  | M_OVinteger iv ->
     (* TODO: maybe check whether iv is within range of the type? *)
     let@ bt_info = ensure_bitvector_type loc ~expect in
     let z = Memory.z_of_ival iv in
     let (min_z, max_z) = BT.bits_range bt_info in
     if Z.leq min_z z && Z.leq z max_z
     then return (num_lit_ z expect loc)
     else fail (fun _ -> {loc;
        msg = Generic (!^ "integer literal not representable at type" ^^^
          Pp.typ (Pp.z z) (BT.pp expect))})
  | M_OVpointer p ->
     check_ptrval loc ~expect p
  | M_OVarray items ->
     let item_bt = bt_of_object_value (List.hd items) in
     let@ () = ensure_base_type loc ~expect (Map (Integer, item_bt)) in
     let@ () = ListM.iterM (fun i -> ensure_base_type loc ~expect:item_bt (bt_of_object_value i)) items in
     let@ values = ListM.mapM (check_object_value loc) items in
     return (make_array_ ~item_bt values loc)
  | M_OVstruct (tag, fields) ->
     let@ () = ensure_base_type loc ~expect (Struct tag) in
     check_struct loc tag fields
  | M_OVunion (tag, id, mv) ->
     check_union loc tag id mv
  | M_OVfloating iv ->
     unsupported loc !^"floats"







let rec check_value (loc : loc) (M_V (expect,v)) : IT.t m =
  match v with
  | M_Vobject ov ->
     let@ () = ensure_base_type loc ~expect (bt_of_object_value ov) in
     check_object_value loc ov
  | M_Vctype ct ->
     let@ () = WellTyped.ensure_base_type loc ~expect CType in
     let ct = Sctypes.of_ctype_unsafe loc ct in
     let@ () = WellTyped.WCT.is_ct loc ct in
     return (IT.const_ctype_ ct loc)
  | M_Vunit ->
     let@ () = WellTyped.ensure_base_type loc ~expect Unit in
     return (IT.unit_ loc)
  | M_Vtrue ->
     let@ () = WellTyped.ensure_base_type loc ~expect Bool in
     return (IT.bool_ true loc)
  | M_Vfalse ->
     let@ () = WellTyped.ensure_base_type loc ~expect Bool in
     return (IT.bool_ false loc)
  | M_Vfunction_addr sym ->
     let@ () = ensure_base_type loc ~expect Loc in
     (* check it is a valid function address *)
     let@ _ = get_fun_decl loc sym in
     return (IT.sym_ (sym, Loc, loc))
  | M_Vlist (_item_cbt, vals) ->
     let item_bt = bt_of_value (List.hd vals) in
     let@ () = WellTyped.ensure_base_type loc ~expect (List item_bt) in
     let@ () = ListM.iterM (fun i -> ensure_base_type loc ~expect:item_bt (bt_of_value i)) vals in
     let@ values = ListM.mapM (check_value loc) vals in
     return (list_ ~item_bt values ~nil_loc:loc)
  | M_Vtuple vals ->
     let item_bts = List.map bt_of_value vals in
     let@ () = ensure_base_type loc ~expect (Tuple item_bts) in
     let@ values = ListM.mapM (check_value loc) vals in
     return (tuple_ values loc)




(*** pure expression inference ************************************************)


(* try to follow is_representable_integer from runtime/libcore/std.core *)
let is_representable_integer arg ity =
  let here = Locations.other __FUNCTION__ in
  let bt = IT.bt arg in
  let arg_bits = Option.get (BT.is_bits_bt bt) in
  let maxInt = Memory.max_integer_type ity in
  assert (BT.fits_range arg_bits maxInt);
  let minInt = Memory.min_integer_type ity in
  assert (BT.fits_range arg_bits minInt);
  and_ [le_ (num_lit_ minInt bt here, arg) here; le_ (arg, num_lit_ maxInt bt here) here] here


let eq_value_with f expr = match f expr with
  | Some y -> return (Some (expr, y))
  | None -> begin
    let@ group = value_eq_group None expr in
    match List.find_opt (fun t -> Option.is_some (f t)) (EqTable.ITSet.elements group) with
    | Some x ->
      let y = Option.get (f x) in
      return (Some (x, y))
    | None ->
      return None
  end

let prefer_value_with f expr =
  let@ r = eq_value_with (fun it -> if f it then Some () else None) expr in
  match r with
  | None -> return expr
  | Some (x, _) -> return x

let try_prove_constant loc expr =
  let@ known = eq_value_with IT.is_const expr in
  match known with
  | Some (it, _) -> return it
  | None ->
    (* backup strategy, try to figure out the single value *)
    let fail2 = (fun msg -> fail (fun _ -> {loc;
        msg = Generic (!^ "model constant calculation:" ^^^ (!^ msg))})) in
    let fail_on_none msg = function
      | Some m -> return m
      | None -> fail2 msg
    in
    let here = Locations.other __FUNCTION__ in
    let@ m = model_with loc (IT.bool_ true here) in
    let@ m = fail_on_none "cannot get model" m in
    let@ g = get_global () in
    let@ y = fail_on_none "cannot eval term" (Solver.eval g (fst m) expr) in
    let@ _ = fail_on_none "eval to non-constant term" (IT.is_const y) in
    let eq = IT.eq_ (expr, y) here in
    let@ provable = provable loc in
    begin match provable (t_ eq) with
      | `True ->
        let@ () = add_c loc (t_ eq) in
        return y
      | `False ->
        return expr
    end

let check_single_ct loc expr =
  let@ pointer = WellTyped.WIT.check loc BT.CType expr in
  let@ t = try_prove_constant loc expr in
  match IT.is_const t with
    | Some (IT.CType_const ct, _) -> return ct
    | Some _ -> assert false (* should be impossible given the type *)
    | None -> fail (fun _ -> {loc;
        msg = Generic (!^ "use of non-constant ctype mucore expression")})

let is_fun_addr global t = match IT.is_sym t with
  | Some (s, _) -> if SymMap.mem s global.Global.fun_decls
      then Some s else None
  | _ -> None

let known_function_pointer loc p =
  let@ global = get_global () in
  let@ already_known = eq_value_with (is_fun_addr global) p in
  let@ () = match already_known with
    | Some _ -> (* no need to find more eqs *) return ()
    | None ->
      let global_funs = SymMap.bindings global.Global.fun_decls in
      let fun_addrs = List.map (fun (sym, (loc, _, _)) -> IT.sym_ (sym, BT.Loc, loc)) global_funs in
      test_value_eqs loc None p fun_addrs
  in
  let@ now_known = eq_value_with (is_fun_addr global) p in
  match now_known with
    | Some (_, sym) -> return sym
    | None ->
      fail (fun _ -> {loc;
          msg = Generic (Pp.item "function pointer must be provably equal to a defined function"
              (IT.pp p))})

let check_conv_int loc ~expect ct arg =
  assert (match expect with | Bits _ -> true | _ -> false);
  (* try to follow conv_int from runtime/libcore/std.core *)
  let ity = match ct with
    | Sctypes.Integer ity -> ity
    | _ -> Cerb_debug.error "conv_int applied to non-integer type"
  in
  let@ provable = provable loc in
  let fail_unrepresentable () =
    let@ model = model () in
    fail (fun ctxt ->
        {loc; msg = Int_unrepresentable {value = arg; ict = ct; ctxt; model}}
      )
  in
  let bt = IT.bt arg in
  (* TODO: can we (later) optimise this? *)
  let here = Locations.other __FUNCTION__ in
  let@ value = match ity with
    | Bool ->
       (* TODO: can we (later) express this more efficiently without ITE? *)
       return (ite_ (eq_ (arg, num_lit_ Z.zero bt here) here,
                     num_lit_ Z.zero expect loc,
                     num_lit_ Z.one expect loc) loc)
    | _ when Sctypes.is_unsigned_integer_type ity ->
       (* casting to the relevant type does the same thing as wrapI *)
       return (cast_ (Memory.bt_of_sct ct) arg loc)
    | _ ->
       begin match provable (t_ (representable_ (ct, arg) here)) with
       | `True ->
          (* this proves that this cast does not change the (integer) interpretation *)
          return (cast_ (Memory.bt_of_sct ct) arg loc)
       | `False ->
          fail_unrepresentable ()
       end
  in
  return value

let _check_array_shift loc ~expect vt1 (loc_ct, ct) vt2 =
  let@ () = WellTyped.ensure_base_type loc ~expect Loc in
  let@ () = WellTyped.WCT.is_ct loc_ct ct in
  return (arrayShift_ ~base:vt1 ct  ~index:vt2)

let check_against_core_bt loc msg2 cbt bt =
  Typing.embed_resultat
    (CoreTypeChecks.check_against_core_bt
       (fun msg -> Resultat.fail {loc; msg = Generic (msg ^^ Pp.hardline ^^ msg2)})
       cbt bt)



let rec check_pexpr (pe : BT.t mu_pexpr) (k : IT.t -> unit m) : unit m =
  let orig_pe = pe in
  let (M_Pexpr (loc, _, expect, pe_)) = pe in
  let@ omodel = model_with loc (bool_ true @@ Locations.other __FUNCTION__) in
  match omodel with
  | None -> 
      warn loc !^"Completed type-checking early along this path due to inconsistent facts.";
      return ()
  | Some _ ->
  let@ () = print_with_ctxt (fun ctxt ->
      debug 3 (lazy (action "inferring pure expression"));
      debug 3 (lazy (item "expr" (Pp_mucore.pp_pexpr pe)));
      debug 3 (lazy (item "ctxt" (Context.pp ctxt)))
    )
  in
  match pe_ with
  | M_PEsym sym ->
     let@ () = check_computational_bound loc sym in
     let@ binding = get_a sym in
     begin match binding with
     | BaseType bt ->
        let@ () = WellTyped.ensure_base_type loc ~expect bt in
        k (sym_ (sym, bt, loc))
     | Value lvt ->
        let@ () = WellTyped.ensure_base_type loc ~expect (IT.bt lvt) in
        k lvt
     end
  | M_PEval v ->
     let@ () = ensure_base_type loc ~expect (bt_of_value v) in
     let@ vt = check_value loc v in
     k vt
  | M_PEconstrained _ ->
     Cerb_debug.error "todo: PEconstrained"
  | M_PEctor (ctor, pes) ->
     begin match ctor, pes with
     | M_Ctuple, _ ->
        let@ () = ensure_base_type loc ~expect (Tuple (List.map bt_of_pexpr pes)) in
        check_pexprs pes (fun values -> k (tuple_ values loc))
     | M_Carray, _ ->
        let item_bt = bt_of_pexpr (List.hd pes) in
        let@ () = ensure_base_type loc ~expect (Map (Integer, item_bt)) in
        let@ () = ListM.iterM (fun i -> ensure_base_type loc ~expect:item_bt (bt_of_pexpr i)) pes in
        check_pexprs pes (fun values ->
        k (make_array_ ~item_bt values loc))
     | M_Cnil item_cbt, [] ->
        let@ item_bt = match expect with
          | List item_bt -> return item_bt
          | _ ->
             let msg = Mismatch {has = !^"list"; expect = BT.pp expect} in
             fail (fun _ -> {loc; msg})
        in
        let@ () = check_against_core_bt loc (!^ "checking Cnil") item_cbt item_bt in
        k (nil_ ~item_bt loc)
     | M_Cnil item_bt, _ ->
        fail (fun _ -> {loc; msg = Number_arguments {has = List.length pes; expect=0}})
     | M_Ccons, [pe1; pe2] ->
        let@ () = ensure_base_type loc ~expect (List (bt_of_pexpr pe1)) in
        let@ () = ensure_base_type loc ~expect (bt_of_pexpr pe2) in
        check_pexpr pe1 (fun vt1 ->
        check_pexpr pe2 (fun vt2 ->
        k (cons_ (vt1, vt2) loc)))
     | M_Ccons, _ ->
        fail (fun _ -> {loc; msg = Number_arguments {has = List.length pes; expect = 2}})
     end
  | M_PEbitwise_unop (unop, pe1) ->
     let@ _ = ensure_bitvector_type loc ~expect in
     let@ () = ensure_base_type loc ~expect (bt_of_pexpr pe1) in
     check_pexpr pe1 (fun vt1 ->
     let unop = match unop with
       | M_BW_FFS -> BWFFSNoSMT
       | M_BW_CTZ -> BWCTZNoSMT
       | M_BW_COMPL -> Cerb_debug.error "todo: M_BW_COMPL"
     in
     let value = arith_unop unop vt1 loc in
     k value)
  | M_PEbitwise_binop (binop, pe1, pe2) ->
     let@ _ = ensure_bitvector_type loc ~expect in
     let@ () = ensure_base_type loc ~expect (bt_of_pexpr pe1) in
     let@ () = ensure_base_type loc ~expect (bt_of_pexpr pe2) in
     let binop = match binop with
       | M_BW_AND -> BWAndNoSMT
       | M_BW_OR -> BWOrNoSMT
       | M_BW_XOR -> XORNoSMT
     in
     check_pexpr pe1 (fun vt1 ->
     check_pexpr pe2 (fun vt2 ->
     let value = arith_binop binop (vt1, vt2) loc in
     k value))
  | M_Cfvfromint _ ->
     unsupported loc !^"floats"
  | M_Civfromfloat _ ->
     unsupported loc !^"floats"
  | M_PEarray_shift (pe1, ct, pe2) ->
     let@ () = WellTyped.ensure_base_type loc ~expect Loc in
     let@ () = WellTyped.WCT.is_ct loc ct in
     let@ () = ensure_base_type loc ~expect:Loc (bt_of_pexpr pe1) in
     let@ () = WellTyped.ensure_bits_type loc (bt_of_pexpr pe2) in
     check_pexpr pe1 (fun vt1 ->
     check_pexpr pe2 (fun vt2 ->
     k (arrayShift_ ~base:vt1 ct ~index:(cast_ Memory.intptr_bt vt2 loc) loc)))
  | M_PEmember_shift (pe, tag, member) ->
     let@ () = WellTyped.ensure_base_type loc ~expect Loc in
     let@ () = ensure_base_type loc ~expect:Loc (bt_of_pexpr pe) in
     check_pexpr pe (fun vt ->
     let@ _ = get_struct_member_type loc tag member in
     k (memberShift_ (vt, tag, member) loc))
  | M_PEnot pe ->
     let@ () = WellTyped.ensure_base_type loc ~expect Bool in
     let@ () = ensure_base_type loc ~expect:Bool (bt_of_pexpr pe) in
     check_pexpr pe (fun vt ->
     k (not_ vt loc))
  | M_PEop (op, pe1, pe2) ->
     let check_cmp_ty = function
       | Integer | Bits _ | Real -> return ()
       | ty -> fail (fun _ -> {loc; msg = Mismatch {has = BT.pp ty; expect = !^"comparable type"}})
     in
     begin match op with
     | OpEq ->
        let@ () = WellTyped.ensure_base_type loc ~expect Bool in
        let@ () = WellTyped.ensure_base_type loc ~expect:(bt_of_pexpr pe1) (bt_of_pexpr pe2) in
        check_pexpr pe1 (fun v1 ->
        check_pexpr pe2 (fun v2 ->
        k (eq_ (v1, v2) loc)))
     | OpGt ->
        let@ () = WellTyped.ensure_base_type loc ~expect Bool in
        let@ () = check_cmp_ty (bt_of_pexpr pe1) in
        let@ () = WellTyped.ensure_base_type loc ~expect:(bt_of_pexpr pe1) (bt_of_pexpr pe2) in
        check_pexpr pe1 (fun v1 ->
        check_pexpr pe2 (fun v2 ->
        k (gt_ (v1, v2) loc)))
     | OpLt ->
        let@ () = WellTyped.ensure_base_type loc ~expect Bool in
        let@ () = check_cmp_ty (bt_of_pexpr pe1) in
        let@ () = WellTyped.ensure_base_type loc ~expect:(bt_of_pexpr pe1) (bt_of_pexpr pe2) in
        check_pexpr pe1 (fun v1 ->
        check_pexpr pe2 (fun v2 ->
        k (lt_ (v1, v2) loc)))
     | OpGe ->
        let@ () = WellTyped.ensure_base_type loc ~expect Bool in
        let@ () = check_cmp_ty (bt_of_pexpr pe1) in
        let@ () = WellTyped.ensure_base_type loc ~expect:(bt_of_pexpr pe1) (bt_of_pexpr pe2) in
        check_pexpr pe1 (fun v1 ->
        check_pexpr pe2 (fun v2 ->
        k (ge_ (v1, v2) loc)))
     | OpLe ->
        let@ () = WellTyped.ensure_base_type loc ~expect Bool in
        let@ () = check_cmp_ty (bt_of_pexpr pe1) in
        let@ () = WellTyped.ensure_base_type loc ~expect:(bt_of_pexpr pe1) (bt_of_pexpr pe2) in
        check_pexpr pe1 (fun v1 ->
        check_pexpr pe2 (fun v2 ->
        k (le_ (v1, v2) loc)))
     | OpAnd ->
        let@ () = WellTyped.ensure_base_type loc ~expect Bool in
        let@ () = WellTyped.ensure_base_type loc ~expect:Bool (bt_of_pexpr pe1) in
        let@ () = WellTyped.ensure_base_type loc ~expect:Bool (bt_of_pexpr pe2) in
        check_pexpr pe1 (fun v1 ->
        check_pexpr pe2 (fun v2 ->
        k (and_ [v1; v2] loc)))
     | OpOr ->
        let@ () = WellTyped.ensure_base_type loc ~expect Bool in
        let@ () = WellTyped.ensure_base_type loc ~expect:Bool (bt_of_pexpr pe1) in
        let@ () = WellTyped.ensure_base_type loc ~expect:Bool (bt_of_pexpr pe2) in
        check_pexpr pe1 (fun v1 ->
        check_pexpr pe2 (fun v2 ->
        k (or_ [v1; v2] loc)))
     | _ ->
       Pp.debug 1 (lazy (Pp.item "not yet restored" (Pp_mucore_ast.pp_pexpr orig_pe)));
       failwith "todo"
     end
  | M_PEapply_fun (fun_id, args) ->
     let@ () = match mu_fun_return_type fun_id args with
       | Some (`Returns_BT bt) -> ensure_base_type loc ~expect bt
       | Some (`Returns_Integer) -> ensure_bits_type loc expect
       | None -> fail (fun _ -> {loc; msg = Generic (Pp.item "untypeable mucore function"
              (Pp_mucore_ast.pp_pexpr orig_pe))})
     in
     let expect_args = Mucore.mu_fun_param_types fun_id in
     let@ () =
       let has = List.length args in
       let expect = List.length expect_args in
       if expect = has then return ()
       else fail (fun _ -> {loc; msg = Number_arguments {has; expect}})
     in
     let@ _ =
       ListM.map2M (fun pe expect ->
           ensure_base_type loc ~expect (bt_of_pexpr pe)
         ) args expect_args
     in
     check_pexprs args (fun args ->
     let@ res = CLogicalFuns.eval_mu_fun fun_id args orig_pe in
     k res
     )
  | M_PEstruct (tag, xs) ->
     let@ () = WellTyped.WCT.is_ct loc (Struct tag) in
     let@ () = ensure_base_type loc ~expect (Struct tag) in
     let@ layout = get_struct_decl loc tag in
     let member_types = Memory.member_types layout in
     let@ _ =
       ListM.map2M (fun (id,ct) (id',pe') ->
           assert (Id.equal id id');
           ensure_base_type loc ~expect:(Memory.bt_of_sct ct) (bt_of_pexpr pe')
         ) member_types xs
     in
     check_pexprs (List.map snd xs) (fun vs ->
     let members = List.map2 (fun (nm, _) v -> (nm, v)) xs vs in
     k (struct_ (tag, members) loc))
  | M_PEunion _ ->
     Cerb_debug.error "todo: PEunion"
  | M_PEcfunction pe2 ->
     let@ () = ensure_base_type loc ~expect (Tuple [CType; List CType; Bool; Bool]) in
     let@ () = ensure_base_type loc ~expect:Loc (bt_of_pexpr pe2) in
     check_pexpr pe2 (fun ptr ->
     let@ global = get_global () in
     (* function vals are just symbols the same as the names of functions *)
     let@ sym = known_function_pointer loc ptr in
     (* need to conjure up the characterising 4-tuple *)
     let@ (_, _, c_sig) = get_fun_decl loc sym in
     begin match IT.const_of_c_sig c_sig loc with
       | Some it -> k it
       | None -> fail (fun _ -> {loc; msg = Generic (!^ "unsupported c-type in sig of:" ^^^
           Sym.pp sym)})
     end
  )
  | M_PEmemberof _ ->
     Cerb_debug.error "todo: M_PEmemberof"
  | M_PEbool_to_integer pe ->
     let@ _ = ensure_bitvector_type loc ~expect in
     let@ () = ensure_base_type loc ~expect:Bool (bt_of_pexpr pe) in
     check_pexpr pe (fun arg ->
     k (ite_ (arg, int_lit_ 1 expect loc, int_lit_ 0 expect loc) loc))
  | M_PEbounded_binop (M_Bound_Wrap act, iop, pe1, pe2) ->
     (* in integers, perform this op and round. in bitvector types, just perform
        the op (for all the ops where wrapping is consistent) *)
     let@ () = WellTyped.WCT.is_ct act.loc act.ct in
     assert (match act.ct with Integer ity when is_unsigned_integer_type ity -> true | _ -> false);
     let@ () = ensure_base_type loc ~expect (Memory.bt_of_sct act.ct) in
     let@ () = ensure_base_type loc ~expect (bt_of_pexpr pe1) in
     let@ () = ensure_bits_type loc expect in
     let@ () = ensure_bits_type loc (bt_of_pexpr pe2) in
     let@ () = match iop with
       | IOpShl | IOpShr -> return ()
       | _ -> ensure_base_type loc ~expect (bt_of_pexpr pe2)
     in
     check_pexpr pe1 (fun arg1 ->
     check_pexpr pe2 (fun arg2 ->
     let arg1_bt_range = BT.bits_range (Option.get (BT.is_bits_bt (IT.bt arg1))) in
     let here = Locations.other __FUNCTION__ in
     let arg2_bits_lost = IT.not_ (IT.in_z_range arg2 arg1_bt_range here) here in
     let x = match iop with
       | IOpAdd -> add_ (arg1, arg2) loc
       | IOpSub -> sub_ (arg1, arg2) loc
       | IOpMul -> mul_ (arg1, arg2) loc
       | IOpShl -> ite_ (arg2_bits_lost, IT.int_lit_ 0 expect loc,
               arith_binop Terms.ShiftLeft (arg1, cast_ (IT.bt arg1) arg2 loc) loc) loc
       | IOpShr -> ite_ (arg2_bits_lost, IT.int_lit_ 0 expect loc,
               arith_binop Terms.ShiftRight (arg1, cast_ (IT.bt arg1) arg2 loc) loc) loc
     in
     k x))
  | M_PEbounded_binop (M_Bound_Except act, iop, pe1, pe2) ->
     let@ () = WellTyped.WCT.is_ct act.loc act.ct in
     let ity = match act.ct with
       | Integer ity -> ity
       | _ -> assert false
     in
     let@ () = ensure_base_type loc ~expect (Memory.bt_of_sct act.ct) in
     let@ () = ensure_base_type loc ~expect (bt_of_pexpr pe1) in
     let@ () = WellTyped.ensure_bits_type loc expect in
     let@ () = WellTyped.ensure_bits_type loc (bt_of_pexpr pe2) in
     let@ () = match iop with
       | IOpShl | IOpShr -> return ()
       | _ -> ensure_base_type loc ~expect (bt_of_pexpr pe2)
     in
     let (_, bits) = Option.get (BT.is_bits_bt expect) in
     check_pexpr pe1 (fun arg1 ->
     check_pexpr pe2 (fun arg2 ->
     let large_bt = BT.Bits (BT.Signed, (2 * bits) + 4) in
     let here = Locations.other __FUNCTION__ in
     let large x = cast_ large_bt x here in
     let (direct_x, via_large_x, premise) = match iop with
       | IOpAdd -> (add_ (arg1, arg2) loc, add_ (large arg1, large arg2) loc, bool_ true here)
       | IOpSub -> (sub_ (arg1, arg2) loc, sub_ (large arg1, large arg2) loc, bool_ true here)
       | IOpMul -> (mul_ (arg1, arg2) loc, mul_ (large arg1, large arg2) loc, bool_ true here)
       | IOpShl ->
         ( arith_binop Terms.ShiftLeft (arg1, cast_ (IT.bt arg1) arg2 loc) loc
         , arith_binop Terms.ShiftLeft (large arg1, large arg2) loc
         , IT.in_z_range arg2 (Z.zero, Z.of_int bits) loc)
       | IOpShr ->
         ( arith_binop Terms.ShiftRight (arg1, cast_ (IT.bt arg1) arg2 loc) loc
         , arith_binop Terms.ShiftRight (large arg1, large arg2) loc
         , IT.in_z_range arg2 (Z.zero, Z.of_int bits) loc)
     in
     let@ provable = provable loc in
     let@ () = match provable (t_ (and_ [premise; is_representable_integer via_large_x ity] here)) with
     | `True -> return ()
     | `False ->
        let@ model = model () in
        let ub = CF.Undefined.UB036_exceptional_condition in
        fail (fun ctxt -> {loc; msg = Undefined_behaviour {ub; ctxt; model}})
     in
     k direct_x))
  | M_PEconv_int (ct_expr, pe)
  | M_PEconv_loaded_int (ct_expr, pe) ->
     let@ () = ensure_base_type loc ~expect:CType (bt_of_pexpr ct_expr) in
     let@ () = WellTyped.ensure_bits_type loc (bt_of_pexpr pe) in
     check_pexpr ct_expr (fun ct_it ->
     let@ ct = check_single_ct loc ct_it in
     let@ () = WellTyped.WCT.is_ct loc ct in
     let@ () = ensure_base_type loc ~expect (Memory.bt_of_sct ct) in
     check_pexpr pe (fun lvt ->
     let@ vt = check_conv_int loc ~expect ct lvt in
     k vt))
  | M_PEwrapI (act, pe) ->
     let@ () = WellTyped.WCT.is_ct act.loc act.ct in
     let@ () = WellTyped.ensure_bits_type loc (bt_of_pexpr pe) in
     check_pexpr pe (fun arg ->
     let bt = Memory.bt_of_sct act.ct in
     let@ () = WellTyped.ensure_bits_type loc bt in
     k (cast_ bt arg loc))
  | M_PEcatch_exceptional_condition (act, pe) ->
     let@ () = WellTyped.WCT.is_ct act.loc act.ct in
     let@ () = WellTyped.ensure_bits_type loc (bt_of_pexpr pe) in
     check_pexpr pe (fun arg ->
     let bt = Memory.bt_of_sct act.ct in
     let@ () = WellTyped.ensure_bits_type loc bt in
     let ity = Option.get (Sctypes.is_integer_type act.ct) in
     let@ provable = provable loc in
     match provable (t_ (is_representable_integer arg ity)) with
     | `True -> (k arg)
     | `False ->
        let@ model = model () in
        let ub = CF.Undefined.UB036_exceptional_condition in
        fail (fun ctxt -> {loc; msg = Undefined_behaviour {ub; ctxt; model}})
     )
  | M_PEis_representable_integer (pe, act) ->
     let@ () = WellTyped.WCT.is_ct act.loc act.ct in
     let@ () = WellTyped.ensure_base_type loc ~expect Bool in
     let@ () = WellTyped.ensure_bits_type loc (bt_of_pexpr pe) in
     let ity = Option.get (Sctypes.is_integer_type act.ct) in
     check_pexpr pe (fun arg ->
         k (is_representable_integer arg ity)
       )
  | M_PEif (pe, e1, e2) ->
     let@ () = ensure_base_type loc ~expect (bt_of_pexpr e1) in
     let@ () = ensure_base_type loc ~expect (bt_of_pexpr e2) in
     let@ () = ensure_base_type loc ~expect:Bool (bt_of_pexpr pe) in
     check_pexpr pe (fun c ->
     let aux e cond name =
       let@ () = add_c loc (t_ cond) in
       Pp.debug 5 (lazy (Pp.item ("checking consistency of "^ name ^ "-branch") (IT.pp cond)));
       let@ provable = provable loc in
       let here = Locations.other __FUNCTION__ in
       match provable (t_ (bool_ false here)) with
       | `True ->
          Pp.debug 5 (lazy (Pp.headline "inconsistent, skipping"));
          return ()
       | `False ->
          Pp.debug 5 (lazy (Pp.headline "consistent, checking"));
          check_pexpr e k
     in
     let@ () = pure (aux e1 c "then") in
     let here = Locations.other __FUNCTION__ in
     let@ () = pure (aux e2 (not_ c here) "else") in
     return ())
  | M_PElet (p, e1, e2) ->
     let@ () = ensure_base_type loc ~expect (bt_of_pexpr e2) in
     let@ () = ensure_base_type loc ~expect:(bt_of_pexpr e1) (bt_of_pattern p) in
     check_pexpr e1 (fun v1 ->
     let@ bound_a = check_and_match_pattern p v1 in
     check_pexpr e2 (fun lvt ->
     let@ () = remove_as bound_a in
     k lvt))
  | M_PEundef (loc, ub) ->
     let@ provable = provable loc in
     let here = Locations.other __FUNCTION__ in
     begin match provable (t_ (bool_ false here)) with
     | `True -> return ()
     | `False ->
        let@ model = model () in
        fail (fun ctxt -> {loc; msg = Undefined_behaviour {ub; ctxt; model}})
     end
  | M_PEerror (err, _pe) ->
     let@ provable = provable loc in
     let here = Locations.other __FUNCTION__ in
     begin match provable (t_ (bool_ false here)) with
     | `True -> return ()
     | `False ->
        let@ model = model () in
        fail (fun ctxt -> {loc; msg = StaticError {err; ctxt; model}})
     end


and check_pexprs (pes : (BT.t mu_pexpr) list) (k : IT.t list -> unit m) : unit m =
  match pes with
  | [] -> k []
  | pe :: pes' ->
     check_pexpr pe (fun lvt ->
     check_pexprs pes' (fun lvts ->
     k (lvt :: lvts)))






module Spine : sig
  val calltype_ft :
    Loc.t -> fsym:Sym.t -> BT.t mu_pexpr list -> AT.ft -> (RT.t -> unit m) -> unit m
  val calltype_lt :
    Loc.t -> BT.t mu_pexpr list -> AT.lt * label_kind -> (False.t -> unit m) -> unit m
  val calltype_lemma :
    Loc.t -> lemma:Sym.t -> (Loc.t * IT.t) list -> AT.lemmat -> (LRT.t -> unit m) -> unit m
  val subtype :
    Loc.t -> LRT.t -> (unit -> unit m) -> unit m
end = struct


  let spine_l rt_subst rt_pp loc (situation : call_situation) ftyp k =

    let start_spine = time_log_start "spine_l" "" in

    (* record the resources now, so errors are raised with all
       the resources present, rather than those that remain after some
       arguments are claimed *)
    let@ original_resources = all_resources_tagged loc in

    let@ rt =
      let rec check ftyp =
        let@ () = print_with_ctxt (fun ctxt ->
            debug 6 (lazy (item "ctxt" (Context.pp ctxt)));
            debug 6 (lazy (item "spec" (LAT.pp rt_pp ftyp)));
          )
        in
        let uiinfo = (Call situation, []) in
        let@ ftyp = RI.General.ftyp_args_request_step rt_subst loc uiinfo
                      original_resources ftyp in
        match ftyp with
        | I rt -> return rt
        | _ -> check ftyp
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

    let@ () = print_with_ctxt (fun ctxt ->
        debug 6 (lazy (call_situation situation));
        debug 6 (lazy (item "ctxt" (Context.pp ctxt)));
        debug 6 (lazy (item "spec" (pp rt_pp ftyp)))
      )
    in

    let check = 
      let rec aux args_acc args ftyp k =
        match args, ftyp with
        | (arg :: args), (Computational ((s, bt), _info, ftyp)) ->
           check_arg arg ~expect:bt (fun arg ->
           aux (args_acc @ [arg]) args (subst rt_subst (make_subst [(s, arg)]) ftyp) k)
        | [], (L ftyp) ->
           let@ () = match situation with
             | FunctionCall fsym ->
                 add_trace_item_to_trace (Call (fsym, args_acc),loc)
             | (Subtyping | LabelCall LAreturn) ->
                 let returned = match args_acc with
                   | [v] -> v
                   | _ -> assert false
                 in
                 add_trace_item_to_trace (Return returned, loc)
             | _ -> return ()
           in
           k ftyp
        | _ ->
           let expect = count_computational original_ftyp in
           let has = List.length original_args in
           fail (fun _ -> {loc; msg = Number_arguments {expect; has}})
      in
      fun args ftyp k -> aux [] args ftyp k
    in

    check args ftyp (fun lftyp ->
    spine_l rt_subst rt_pp loc situation lftyp k)


  let check_arg_pexpr (pe : BT.t mu_pexpr) ~expect k =
    let@ () = ensure_base_type (loc_of_pexpr pe) ~expect (bt_of_pexpr pe) in
    check_pexpr pe k

  let check_arg_it (loc, it_arg) ~(expect:LS.t) k =
    let@ it_arg = WellTyped.WIT.check loc expect it_arg in
    k it_arg

  let calltype_ft loc ~fsym args (ftyp : AT.ft) k =
    spine check_arg_pexpr RT.subst
      RT.pp loc (FunctionCall fsym) args ftyp k

  let calltype_lt loc args ((ltyp : AT.lt), label_kind) k =
    spine check_arg_pexpr False.subst False.pp
      loc (LabelCall label_kind) args ltyp k

  let calltype_lemma loc ~lemma args lemma_typ k =
    spine check_arg_it LRT.subst LRT.pp
      loc (LemmaApplication lemma) args lemma_typ k

  (* The "subtyping" judgment needs the same resource/lvar/constraint
     inference as the spine judgment. So implement the subtyping
     judgment 'arg <: LRT' by type checking 'f()' for 'f: LRT -> False'. *)
  let subtype (loc : loc) (rtyp : LRT.t) k =
    let lft = LAT.of_lrt rtyp (LAT.I False.False) in
    spine_l False.subst False.pp loc Subtyping lft (fun False.False ->
    k ())


end




(*** impure expression inference **********************************************)

let filter_empty_resources loc =
  let@ provable = provable loc in
  let@ filtered, _rw_time =
    map_and_fold_resources loc (fun resource xs ->
         match Pack.resource_empty provable resource with
         | `Empty -> (Deleted, xs)
         | `NonEmpty (constr, model) -> (Unchanged, ((resource, constr, model) :: xs))
   ) []
  in
  return filtered

let all_empty loc original_resources =
  let@ remaining_resources = filter_empty_resources loc in
  (* there will be a model available if at least one resource persisted *)
  match remaining_resources with
   | [] -> return ()
   | ((resource, constr, model) :: _) ->
      let@ global = get_global () in
      let@ simp_ctxt = simp_ctxt () in
      RI.debug_constraint_failure_diagnostics 6 model global simp_ctxt constr;
      fail(fun ctxt ->
            let ctxt = { ctxt with resources = original_resources } in
            {loc; msg = Unused_resource {resource; ctxt; model; }})


let compute_used loc (prev_rs, prev_ix) (post_rs, _) =
  let post_ixs = IntSet.of_list (List.map snd post_rs) in
  (* restore previous resources that have disappeared from the context, since they
     might participate in a race *)
  let all_rs = post_rs @ List.filter (fun (_, i) -> not (IntSet.mem i post_ixs)) prev_rs in
  ListM.fold_leftM (fun (rs, ws) (r, i) ->
    let@ h = res_history loc i in
    if h.last_written_id >= prev_ix
    then return (rs, (r, h, i) :: ws)
    else if h.last_read_id >= prev_ix
    then return ((r, h, i) :: rs, ws)
    else return (rs, ws)
  ) ([], []) all_rs

let _check_used_distinct loc used =
  let render_upd h =
    !^ "resource" ^^^ !^ (h.reason_written) ^^^ !^ "at" ^^^ Locations.pp h.last_written
  in
  let render_read h =
    !^ "resource read at " ^^^ Locations.pp h.last_read
  in
  let rec check_ws m = function
    | [] -> return m
    | ((r, h, i) :: ws) -> begin match IntMap.find_opt i m with
      | None -> check_ws (IntMap.add i h m) ws
      | Some h2 ->
        Pp.debug 3 (lazy (Pp.typ (!^ "concurrent upds on") (Pp.int i)));
        fail (fun _ -> {loc; msg = Generic (Pp.item "undefined behaviour: concurrent update"
          (RE.pp r ^^^ break 1 ^^^ render_upd h ^^^ break 1 ^^^ render_upd h2))})
    end
  in
  let@ w_map = check_ws IntMap.empty (List.concat (List.map snd used)) in
  let check_rd (r, h, i) = match IntMap.find_opt i w_map with
    | None -> return ()
    | Some h2 ->
      Pp.debug 3 (lazy (Pp.typ (!^ "concurrent accs on") (Pp.int i)));
      fail (fun _ -> {loc; msg = Generic (Pp.item "undefined behaviour: concurrent read & update"
        (RE.pp r ^^^ break 1 ^^^ render_read h ^^^ break 1 ^^^ render_upd h2))})
  in
  ListM.iterM check_rd (List.concat (List.map fst used))

(*type labels = (AT.lt * label_kind) SymMap.t*)


let load loc pointer ct =
  let@ value = 
    pure begin
      let@ (point, O value), _ =
        RI.Special.predicate_request loc (Access Load)
          ({name = Owned (ct, Init); pointer; iargs = []}, None)
      in
      return value
    end
  in
  let@ () = add_trace_item_to_trace (Read (pointer, value), loc) in
  return value


let instantiate loc filter arg =
  let arg_s = Sym.fresh_make_uniq "instance" in
  let arg_it = sym_ (arg_s, IT.bt arg, loc) in
  let@ () = add_l arg_s (IT.bt arg_it) (loc, lazy (Sym.pp arg_s)) in
  let@ () = add_c loc (LC.t_ (eq__ arg_it arg loc)) in
  let@ constraints = all_constraints () in
  let extra_assumptions1 = List.filter_map (function
        | Forall ((s, bt), t) when filter t -> Some ((s, bt), t)
        | _ -> None) (LCSet.elements constraints) in
  let extra_assumptions2, type_mismatch = List.partition (fun ((_, bt), _) ->
        BT.equal bt (IT.bt arg_it)) extra_assumptions1 in
  let extra_assumptions = List.map (fun ((s, _), t) ->
        LC.t_ (IT.subst (IT.make_subst [(s, arg_it)]) t)) extra_assumptions2
  in
  if List.length extra_assumptions == 0 then Pp.warn loc (!^ "nothing instantiated")
  else ();
  List.iteri (fun i ((_, bt), _) -> if i < 2
    then Pp.warn loc (!^ "did not instantiate on basetype mismatch:" ^^^
        (Pp.list BT.pp [bt; IT.bt arg_it]))) type_mismatch;
  add_cs loc extra_assumptions


  
let add_trace_information labels annots =
  let open CF.Annot in
  let inlined_labels = 
    List.filter_map (function Ainlined_label l -> Some l | _ -> None) annots in
  let stmt_locs = 
    List.filter_map (function Astmt loc -> Some loc | _ -> None) annots in 
  let expr_locs = 
    List.filter_map (function Aexpr loc -> Some loc | _ -> None) annots in
  let@ () = match inlined_labels with
    | [] -> return ()
    | [(lloc,lsym,lannot)] -> 
      add_label_to_trace (Some (lloc,lannot)) 
    | _ -> assert false
  in
  let@ () = match stmt_locs with
    | [] -> return ()
    | l :: _ -> add_trace_item_to_trace (Stmt, l) 
  in
  let@ () = match expr_locs with
    | [] -> return ()
    | l :: _ -> add_trace_item_to_trace (Context.Expr, l)
  in
  return ()


let rec check_expr labels (e : BT.t mu_expr) (k: IT.t -> unit m) : unit m =
  let (M_Expr (loc, annots, expect, e_)) = e in
  let@ () = add_trace_information labels annots in
  let here = Locations.other __FUNCTION__ in
  let@ omodel = model_with loc (bool_ true here) in
  match omodel with
  | None -> 
      warn loc !^"Completed type-checking early along this path due to inconsistent facts.";
      return ()
  | Some _ ->
  let@ () = add_loc_trace loc in
  let@ () = print_with_ctxt (fun ctxt ->
       debug 3 (lazy (action "inferring expression"));
       debug 3 (lazy (item "expr" (group (Pp_mucore.pp_expr e))));
       debug 3 (lazy (item "ctxt" (Context.pp ctxt)));
    )
  in
  match e_ with
  | M_Epure pe ->
     let@ () = ensure_base_type loc ~expect (bt_of_pexpr pe) in
     check_pexpr pe (fun lvt ->
     k lvt)
  | M_Ememop memop ->
      let here = Locations.other __FUNCTION__ in
      let pointer_eq ?(negate = false) pe1 pe2 =
       check_pexpr pe1 (fun arg1 ->
       check_pexpr pe2 (fun arg2 ->
       let prov1, prov2 = pointerToAllocIdCast_ arg1 here, pointerToAllocIdCast_ arg2 here in
       let addr1, addr2 = pointerToIntegerCast_ arg1 here, pointerToIntegerCast_ arg2 here in
       let addr_eq = eq_ (addr1, addr2) loc in
       let prov_eq = eq_ (prov1, prov2) loc in
       let prov_neq = ne_ (prov1, prov2) loc in
       let@ provable = provable loc in
       let@ () =
         match provable @@ t_ @@ and_ [prov_neq; addr_eq] here with
         | `False ->
           return ()
         | `True ->
           warn loc !^"ambiguous pointer (in)equality case: addresses equal, but provenances differ";
           return ()
       in
       let res_sym, res = IT.fresh_named Bool (if negate then "ptrNeq" else "ptrEq") loc in
       let@ result = add_a res_sym Bool (loc, lazy (Sym.pp res_sym)) in
       let@ () = add_c loc @@ t_ @@ impl_ (prov_eq, eq_ (res, addr_eq) loc) loc in
       (* this constraint may make the result non-deterministic *)
       let@ () = add_c loc @@ t_ @@ impl_ (prov_neq, or_ [eq_ (res, addr_eq) loc; eq_ (res, bool_ false here) loc] loc) loc in
       let@ () = WellTyped.ensure_base_type loc ~expect (IT.bt res) in
       k (if negate then not_ res loc else res)))
     in
     let pointer_op op pe1 pe2 =
       let@ () = ensure_base_type loc ~expect Bool in
       let@ () = ensure_base_type loc ~expect:Loc (bt_of_pexpr pe1) in
       let@ () = ensure_base_type loc ~expect:Loc (bt_of_pexpr pe2) in
       check_pexpr pe1 (fun arg1 ->
       check_pexpr pe2 (fun arg2 ->
       k (op (arg1, arg2))))
     in
     begin match memop with
     | M_PtrEq (pe1, pe2) ->
       pointer_eq pe1 pe2
     | M_PtrNe (pe1, pe2) ->
       pointer_eq ~negate:true pe1 pe2
     | M_PtrLt (pe1, pe2) ->
        pointer_op (Fun.flip ltPointer_ loc) pe1 pe2
     | M_PtrGt (pe1, pe2) ->
        pointer_op (Fun.flip gtPointer_ loc) pe1 pe2
     | M_PtrLe (pe1, pe2) ->
        pointer_op (Fun.flip lePointer_ loc) pe1 pe2
     | M_PtrGe (pe1, pe2) ->
        pointer_op (Fun.flip gePointer_ loc) pe1 pe2
     | M_Ptrdiff (act, pe1, pe2) ->
        let@ () = WellTyped.WCT.is_ct act.loc act.ct in
        let@ () = ensure_base_type loc ~expect (Memory.bt_of_sct (Integer Ptrdiff_t)) in
        let@ () = ensure_base_type loc ~expect:Loc (bt_of_pexpr pe1) in
        let@ () = ensure_base_type loc ~expect:Loc (bt_of_pexpr pe2) in
        check_pexpr pe1 (fun arg1 ->
        check_pexpr pe2 (fun arg2 ->
        (* copying and adapting from memory/concrete/impl_mem.ml *)
        let divisor = match act.ct with
          | Array (item_ty, _) -> Memory.size_of_ctype item_ty
          | ct -> Memory.size_of_ctype ct
        in
        let ptr_diff_bt = Memory.bt_of_sct (Integer Ptrdiff_t) in
        let value =
          (* TODO: confirm that the cast from intptr_t to ptrdiff_t
             yields the expected result. *)
          div_
            (cast_ ptr_diff_bt (sub_ (pointerToIntegerCast_ arg1 loc, pointerToIntegerCast_ arg2 loc) loc) loc,
             int_lit_ divisor ptr_diff_bt loc)
            loc
        in
        k value))
     | M_IntFromPtr (act_from, act_to, pe) ->
        let@ () = WellTyped.WCT.is_ct act_from.loc act_from.ct in
        let@ () = WellTyped.WCT.is_ct act_to.loc act_to.ct in
        assert (match act_to.ct with Integer _ -> true | _ -> false);
        let@ () = ensure_base_type loc ~expect (Memory.bt_of_sct act_to.ct) in
        let@ () = ensure_base_type loc ~expect:Loc (bt_of_pexpr pe) in
        check_pexpr pe (fun arg ->
        let here = Locations.other __FUNCTION__ in
        (* TODO: is this good? *)
        let test_value = cast_ Memory.intptr_bt arg here in
        let actual_value = cast_ (Memory.bt_of_sct act_to.ct) arg loc in
        let@ () =
          (* after discussing with Kavyan *)
          let@ provable = provable loc in
          let lc = t_ (representable_ (act_to.ct, test_value) here) in
          begin match provable lc with
          | `True -> return ()
          | `False ->
             let@ model = model () in
             fail (fun ctxt ->
                 let ict = act_to.ct in
                 {loc; msg = Int_unrepresentable {value = test_value; ict; ctxt; model}}
               )
          end
        in
        k actual_value)
     | M_PtrFromInt (act_from, act_to, pe) ->
        let@ () = WellTyped.WCT.is_ct act_from.loc act_from.ct in
        let@ () = WellTyped.WCT.is_ct act_to.loc act_to.ct in
        let@ () = WellTyped.ensure_base_type loc ~expect Loc in
        let@ () = WellTyped.ensure_base_type loc ~expect:(Memory.bt_of_sct act_from.ct)
            (bt_of_pexpr pe) in
        let@ bt_info = ensure_bitvector_type loc ~expect:(bt_of_pexpr pe) in
        check_pexpr pe (fun arg ->
        (* TODO: what about unrepresentable values? If that's possible
           we to make sure our cast semantics correctly matches C's *)
        let value = integerToPointerCast_ arg loc in
        k value)
     | M_PtrValidForDeref (act, pe) ->
        (* TODO: provenance things? *)
        let@ () = WellTyped.WCT.is_ct act.loc act.ct in
        let@ () = WellTyped.ensure_base_type loc ~expect Bool in
        let@ () = WellTyped.ensure_base_type loc ~expect:Loc (bt_of_pexpr pe) in
        (* TODO: check. Also: this is the same as PtrWellAligned *)
        check_pexpr pe (fun arg ->
        let value = aligned_ (arg, act.ct) loc in
        k value)
     | M_PtrWellAligned (act, pe) ->
        let@ () = WellTyped.WCT.is_ct act.loc act.ct in
        let@ () = WellTyped.ensure_base_type loc ~expect Bool in
        let@ () = WellTyped.ensure_base_type loc ~expect:Loc (bt_of_pexpr pe) in
        (* TODO: check *)
        check_pexpr pe (fun arg ->
        let value = aligned_ (arg, act.ct) loc in
        k value)
     | M_PtrArrayShift (pe1, act, pe2) ->
        let@ () = ensure_base_type loc ~expect Loc in
        let@ () = ensure_base_type loc ~expect:Loc (bt_of_pexpr pe1) in
        let@ () = WellTyped.WCT.is_ct act.loc act.ct in
        let@ () = WellTyped.ensure_bits_type loc (bt_of_pexpr pe2) in
        check_pexpr pe1 (fun vt1 ->
        check_pexpr pe2 (fun vt2 ->
        k (arrayShift_ ~base:vt1 act.ct ~index:vt2 loc)))
     | M_PtrMemberShift (tag_sym, memb_ident, pe) ->
        (* FIXME(CHERI merge) *)
        (* there is now an effectful variant of the member shift operator (which is UB when creating an out of bound pointer) *)
        Cerb_debug.error "todo: M_PtrMemberShift"
     | M_CopyAllocId (pe1, pe2) ->
        let@ () = WellTyped.ensure_base_type loc ~expect:Memory.intptr_bt (bt_of_pexpr pe1) in
        let@ () = WellTyped.ensure_base_type loc ~expect:BT.Loc (bt_of_pexpr pe2) in
        check_pexpr pe1 (fun vt1 ->
        check_pexpr pe2 (fun vt2 ->
        k (copyAllocId_ ~addr:vt1 ~loc:vt2 loc)))
     | M_Memcpy _ (* (asym 'bty * asym 'bty * asym 'bty) *) ->
        Cerb_debug.error "todo: M_Memcpy"
     | M_Memcmp _ (* (asym 'bty * asym 'bty * asym 'bty) *) ->
        Cerb_debug.error "todo: M_Memcmp"
     | M_Realloc _ (* (asym 'bty * asym 'bty * asym 'bty) *) ->
        Cerb_debug.error "todo: M_Realloc"
     | M_Va_start _ (* (asym 'bty * asym 'bty) *) ->
        Cerb_debug.error "todo: M_Va_start"
     | M_Va_copy _ (* (asym 'bty) *) ->
        Cerb_debug.error "todo: M_Va_copy"
     | M_Va_arg _ (* (asym 'bty * actype 'bty) *) ->
        Cerb_debug.error "todo: M_Va_arg"
     | M_Va_end _ (* (asym 'bty) *) ->
        Cerb_debug.error "todo: M_Va_end"
     end
  | M_Eaction (M_Paction (_pol, M_Action (_aloc, action_))) ->
     begin match action_ with
     | M_Create (pe, act, prefix) ->
        let@ () = WellTyped.WCT.is_ct act.loc act.ct in
        let@ () = WellTyped.ensure_base_type loc ~expect Loc in
        let@ () = WellTyped.ensure_bits_type loc (bt_of_pexpr pe) in
        check_pexpr pe (fun arg ->
        let ret_s, ret = match prefix with
          | PrefSource (_loc, syms) ->
             let syms = List.rev syms in
             begin match syms with
             | (Symbol (_, _, SD_ObjectAddress str)) :: _ ->
                IT.fresh_named Loc ("&" ^ str) loc
             | _ ->
                IT.fresh Loc loc
             end
          | PrefFunArg (_loc, _, n) ->
             IT.fresh_named Loc ("&ARG" ^ string_of_int n) loc
          | _ ->
             IT.fresh Loc loc
        in
        let@ () = add_a ret_s (IT.bt ret) (loc, lazy (Pp.string "allocation")) in
        (* let@ () = add_c loc (t_ (representable_ (Pointer act.ct, ret) loc)) in *)
        let align_v = cast_ Memory.intptr_bt arg loc in
        let@ () = add_c loc (t_ (alignedI_ ~align:align_v ~t:ret loc)) in
        let@ () =
          add_r loc
            (P { name = Owned (act.ct, Uninit);
                 pointer = ret;
                 iargs = [];
               },
             O (default_ (Memory.bt_of_sct act.ct) loc))
        in
        let@ () = add_r loc (P (Global.mk_alloc ret), O (IT.unit_ loc)) in
        let@ () = add_trace_item_to_trace (Create ret, loc) in
        k ret)
     | M_CreateReadOnly (sym1, ct, sym2, _prefix) ->
        Cerb_debug.error "todo: CreateReadOnly"
     | M_Alloc (ct, sym, _prefix) ->
        Cerb_debug.error "todo: Alloc"
     | M_Kill (M_Dynamic, asym) ->
        Cerb_debug.error "todo: Free"
     | M_Kill (M_Static ct, pe) ->
        let@ () = WellTyped.WCT.is_ct loc ct in
        let@ () = WellTyped.ensure_base_type loc ~expect Unit in
        let@ () = ensure_base_type loc ~expect:Loc (bt_of_pexpr pe) in
        check_pexpr pe (fun arg ->
        let@ _ =
          RI.Special.predicate_request loc (Access Kill) ({
            name = Owned (ct, Uninit);
            pointer = arg;
            iargs = [];
          }, None)
        in
        let@ _ =
          RI.Special.predicate_request loc (Access Kill) (Global.mk_alloc arg, None)
        in
        let@ () = add_trace_item_to_trace (Kill arg, loc) in
        k (unit_ loc))
     | M_Store (_is_locking, act, p_pe, v_pe, mo) ->
        let@ () = WellTyped.WCT.is_ct act.loc act.ct in
        let@ () = WellTyped.ensure_base_type loc ~expect Unit in
        let@ () = WellTyped.ensure_base_type loc ~expect:Loc (bt_of_pexpr p_pe) in
        let@ () = WellTyped.ensure_base_type loc ~expect:(Memory.bt_of_sct act.ct) (bt_of_pexpr v_pe) in
        check_pexpr p_pe (fun parg ->
        check_pexpr v_pe (fun varg ->
        (* The generated Core program will in most cases before this
           already have checked whether the store value is
           representable and done the right thing. Pointers, as I
           understand, are an exception. *)
        let@ () =
          let here = Locations.other __FUNCTION__ in
          let in_range_lc = representable_ (act.ct, varg) here in
          let@ provable = provable loc in
          let holds = provable (t_ in_range_lc) in
          match holds with
          | `True -> return ()
          | `False ->
             let@ model = model () in
             fail (fun ctxt ->
                 let msg =
                   Write_value_unrepresentable {
                       ct = act.ct;
                       location = parg;
                       value = varg;
                       ctxt;
                       model}
                 in
                 {loc; msg}
               )
        in
        let@ _ =
          RI.Special.predicate_request loc (Access Store) ({
              name = Owned (act.ct, Uninit);
              pointer = parg;
              iargs = [];
            }, None)
        in
        let@ () =
          add_r loc
            (P { name = Owned (act.ct, Init);
                 pointer = parg;
                 iargs = [];
               },
             O varg)
        in
        let@ () = add_trace_item_to_trace (Write (parg, varg), loc) in
        k (unit_ loc)))
     | M_Load (act, p_pe, _mo) ->
        let@ () = WellTyped.WCT.is_ct act.loc act.ct in
        let@ () = WellTyped.ensure_base_type loc ~expect (Memory.bt_of_sct act.ct) in
        let@ () = WellTyped.ensure_base_type loc ~expect:Loc (bt_of_pexpr p_pe) in
        check_pexpr p_pe (fun pointer ->
        let@ value = load loc pointer act.ct in
        k value)
     | M_RMW (ct, sym1, sym2, sym3, mo1, mo2) ->
        Cerb_debug.error "todo: RMW"
     | M_Fence mo ->
        Cerb_debug.error "todo: Fence"
     | M_CompareExchangeStrong (ct, sym1, sym2, sym3, mo1, mo2) ->
        Cerb_debug.error "todo: CompareExchangeStrong"
     | M_CompareExchangeWeak (ct, sym1, sym2, sym3, mo1, mo2) ->
        Cerb_debug.error "todo: CompareExchangeWeak"
     | M_LinuxFence mo ->
        Cerb_debug.error "todo: LinuxFemce"
     | M_LinuxLoad (ct, sym1, mo) ->
        Cerb_debug.error "todo: LinuxLoad"
     | M_LinuxStore (ct, sym1, sym2, mo) ->
        Cerb_debug.error "todo: LinuxStore"
     | M_LinuxRMW (ct, sym1, sym2, mo) ->
        Cerb_debug.error "todo: LinuxRMW"
     end
  | M_Eskip ->
     let@ () = WellTyped.ensure_base_type loc ~expect Unit in
     k (unit_ loc)
  | M_Eccall (act, f_pe, pes) ->
     let@ () = WellTyped.WCT.is_ct act.loc act.ct in
     (* copied TS's, from wellTyped.ml *)
     (* let@ (_ret_ct, _arg_cts) = match act.ct with *)
     (*     | Pointer (Function (ret_v_ct, arg_r_cts, is_variadic)) -> *)
     (*         assert (not is_variadic); *)
     (*         return (snd ret_v_ct, List.map fst arg_r_cts) *)
     (*     | _ -> fail (fun _ -> {loc; msg = Generic (Pp.item "not a function pointer at call-site" *)
     (*                                                  (Sctypes.pp act.ct))}) *)
     (* in *)
     let@ () = ensure_base_type loc ~expect:Loc (bt_of_pexpr f_pe) in
     check_pexpr f_pe (fun f_it ->
     let@ global = get_global () in
     let@ fsym = known_function_pointer loc f_it in
     let@ (_loc, opt_ft, _) = get_fun_decl loc fsym in
     let@ ft = match opt_ft with
       | Some ft -> return ft
       | None -> fail (fun _ -> {loc; msg = Generic (!^"Call to function with no spec:" ^^^ Sym.pp fsym)})
     in
     (* checks pes against their annotations, and that they match ft's argument types *)
     Spine.calltype_ft loc ~fsym pes ft (fun (Computational ((_, bt), _, _) as rt) ->
     let@ () = WellTyped.ensure_base_type loc ~expect bt in
     let@ _, members = make_return_record loc (TypeErrors.call_prefix (FunctionCall fsym)) (RT.binders rt) in
     let@ lvt = bind_return loc members rt in
     k lvt))
  | M_Eif (c_pe, e1, e2) ->
     let@ () = ensure_base_type (loc_of_expr e1) ~expect (bt_of_expr e1) in
     let@ () = ensure_base_type (loc_of_expr e2) ~expect (bt_of_expr e2) in
     let@ () = ensure_base_type (loc_of_pexpr c_pe) ~expect:Bool (bt_of_pexpr c_pe) in
     check_pexpr c_pe (fun carg ->
     let aux lc nm e =
       let@ () = add_c loc (t_ lc) in
       let@ provable = provable loc in
       let here = Locations.other __FUNCTION__ in
       match provable (t_ (bool_ false here)) with
       | `True -> return ()
       | `False -> check_expr labels e k
     in
     let@ () = pure (aux carg "true" e1) in
     let@ () = pure (aux (not_ carg loc) "false" e2) in
     return ())
  | M_Ebound e ->
     let@ () = ensure_base_type (loc_of_expr e) ~expect (bt_of_expr e) in
     check_expr labels e k
  | M_End _ ->
     Cerb_debug.error "todo: End"
  | M_Elet (p, e1, e2) ->
     let@ () = ensure_base_type (loc_of_expr e2) ~expect (bt_of_expr e2) in
     let@ () = ensure_base_type (loc_of_pattern p) ~expect:(bt_of_pexpr e1) (bt_of_pattern p) in
     check_pexpr e1 (fun v1 ->
     let@ bound_a = check_and_match_pattern p v1 in
     check_expr labels e2 (fun rt ->
         let@ () = remove_as bound_a in
         k rt
     ))
  | M_Eunseq es ->
     let@ () = ensure_base_type loc ~expect (Tuple (List.map bt_of_expr es)) in
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
  | M_CN_progs (_, cn_progs) ->
     let@ () = WellTyped.ensure_base_type loc ~expect Unit in
     let aux loc stmt =
          (* copying bits of code from elsewhere in check.ml *)
          match stmt with
            | Cnprog.M_CN_pack_unpack (pack_unpack, pt) ->
                    warn loc !^"Explicit pack/unpack unsupported.";
                    return ()
            | M_CN_have lc ->
               let@ lc = WLC.welltyped loc lc in
               fail (fun _ -> {loc; msg = Generic !^"todo: 'have' not implemented yet"})
            | M_CN_instantiate (to_instantiate, it) ->
               let@ filter = match to_instantiate with
                 | I_Everything ->
                    return (fun _ -> true)
                 | I_Function f ->
                    let@ _ = get_logical_function_def loc f in
                    return (IT.mentions_call f)
                 | I_Good ct ->
                    let@ () = WCT.is_ct loc ct in
                    return (IT.mentions_good ct)
               in
               let@ it = WIT.infer it in
               instantiate loc filter it
            | M_CN_split_case _ ->
              assert false
            | M_CN_extract (attrs, to_extract, it) ->
               let@ predicate_name = match to_extract with
                | E_Everything ->
                    let msg = "'extract' requires a predicate name annotation" in
                    fail (fun _ -> {loc; msg = Generic !^msg})
                | E_Pred (CN_owned None) ->
                    let msg = "'extract' requires a C-type annotation for 'Owned'" in
                    fail (fun _ -> {loc; msg = Generic !^msg})
                | E_Pred (CN_owned (Some ct)) ->
                    let@ () = WellTyped.WCT.is_ct loc ct in
                    return (Owned (ct, Init))
                | E_Pred (CN_block ct) ->
                    let@ () = WellTyped.WCT.is_ct loc ct in
                    return (Owned (ct, Uninit))
                | E_Pred (CN_named pn) ->
                    let@ _ = get_resource_predicate_def loc pn in
                    return (PName pn)
               in
               let@ it = WIT.infer it in
               let@ (original_rs, _) = all_resources_tagged loc in
               let verbose = List.exists (Id.is_str "verbose") attrs in
               let quiet = List.exists (Id.is_str "quiet") attrs in
               if verbose
               then Pp.print stdout (Pp.loc_headline loc (!^ "processing extract[verbose]"))
               else ();
               let@ () = add_movable_index loc ~verbose (predicate_name, it) in
               let@ (upd_rs, _) = all_resources_tagged loc in
               let msg1 = "extract: index added, no resources (yet) extracted." in
               let msg2 = "(consider extract[verbose] or extract[quiet])" in
               if (List.equal Int.equal (List.map snd original_rs) (List.map snd upd_rs)
                   && not quiet)
               then warn loc (if verbose then (!^ msg1)
                   else ((!^ msg1) ^^ Pp.hardline ^^ (!^ "    ") ^^ (!^ msg2)))
               else ();
               return ()
            | M_CN_unfold (f, args) ->
               let@ def = get_logical_function_def loc f in
               let has_args, expect_args = List.length args, List.length def.args in
               let@ () = WellTyped.ensure_same_argument_number loc `General has_args ~expect:expect_args in
               let@ args =
                 ListM.map2M (fun has_arg (_, def_arg_bt) ->
                     WellTyped.WIT.check loc def_arg_bt has_arg
                   ) args def.args
               in
               begin match LF.unroll_once def args with
               | None ->
                  let msg =
                    !^"Cannot unfold definition of uninterpreted function"
                    ^^^ Sym.pp f ^^ dot
                  in
                  fail (fun _ -> {loc; msg = Generic msg})
               | Some body ->
                  add_c loc (LC.t_ (eq_ (pred_ f args def.return_bt loc, body) loc))
               end
            | M_CN_apply (lemma, args) ->
               let@ (_loc, lemma_typ) = get_lemma loc lemma in
               let args = List.map (fun arg -> (loc, arg)) args in
               Spine.calltype_lemma loc ~lemma args lemma_typ (fun lrt ->
                   let@ _, members = make_return_record loc (TypeErrors.call_prefix (LemmaApplication lemma)) (LRT.binders lrt) in
                   let@ () = bind_logical_return loc members lrt in
                   return ()
                 )
            | M_CN_assert lc ->
               let@ lc = WellTyped.WLC.welltyped loc lc in
               let@ provable = provable loc in
               begin match provable lc with
               | `True -> return ()
               | `False ->
                  let@ model = model () in
                  let@ simp_ctxt = simp_ctxt () in
                  let@ global = get_global () in
                  RI.debug_constraint_failure_diagnostics 6 model global simp_ctxt lc;
                  let@ () = Diagnostics.investigate model lc in
                  fail (fun ctxt ->
                      {loc; msg = Unproven_constraint {constr = lc; info = (loc, None);
                          requests = []; ctxt; model; }}
                    )
               end
            | M_CN_inline _nms ->
               return ()
            | M_CN_print it ->
               let@ it = WellTyped.WIT.infer it in
               let@ simp_ctxt = simp_ctxt () in
               let it = Simplify.IndexTerms.simp simp_ctxt it in
               print stdout (item "printed" (IT.pp it));
               return ()
     in
     let rec loop = function
       | [] -> k (unit_ loc)
       | Cnprog.M_CN_let (loc, (sym, {ct; pointer}), cn_prog) :: cn_progs ->
          let@ pointer = WellTyped.WIT.check loc Loc pointer in
          let@ () = WCT.is_ct loc ct in
          let@ value = load loc pointer ct in
          let subbed = Cnprog.subst (IT.make_subst [(sym, value)]) cn_prog in
          loop (subbed :: cn_progs)
       | (Cnprog.M_CN_statement (loc, cn_statement)) :: cn_progs ->
          begin match cn_statement with
          | Cnprog.M_CN_split_case lc ->
             Pp.debug 5 (lazy (Pp.headline "checking split_case"));
             let@ lc = WellTyped.WLC.welltyped loc lc in
             let@ it = match lc with
               | T it ->
                 return it
               | Forall ((sym, bt), it) ->
                  fail (fun _ -> {loc; msg = Generic !^"Cannot split on forall condition"}) in
             let branch it nm =
               let@ () = add_c loc (t_ it) in
               debug 5 (lazy (item ("splitting case " ^ nm) (IT.pp it)));
               let@ provable = provable loc in
               let here = Locations.other __FUNCTION__ in
               match provable (t_ (bool_ false here)) with
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
            loop cn_progs
          end
     in
     loop cn_progs
  | M_Ewseq (p, e1, e2)
  | M_Esseq (p, e1, e2) ->
     let@ () = ensure_base_type loc ~expect (bt_of_expr e2) in
     let@ () = ensure_base_type (loc_of_pattern p) ~expect:(bt_of_expr e1) (bt_of_pattern p) in
     check_expr labels e1 (fun it ->
            let@ bound_a = check_and_match_pattern p it in
            check_expr labels e2 (fun it2 ->
                let@ () = remove_as bound_a in
                k it2
              )
       )
  | M_Erun (label_sym, pes) ->
     let@ () = ensure_base_type loc ~expect Unit in
     let@ (lt,lkind) = match SymMap.find_opt label_sym labels with
       | None -> fail (fun _ -> {loc; msg = Generic (!^"undefined code label" ^/^ Sym.pp label_sym)})
       | Some (lt,lkind,_) -> return (lt,lkind)
     in
     let@ original_resources = all_resources_tagged loc in
     Spine.calltype_lt loc pes (lt,lkind) (fun False ->
     let@ () = all_empty loc original_resources in
     return ())



let check_expr_top loc labels rt e =
  let@ () = add_loc_trace loc in
  let@ () = WellTyped.ensure_base_type loc ~expect:Unit (bt_of_expr e) in
  check_expr labels e (fun lvt ->
        let (RT.Computational ((return_s, return_bt), info, lrt)) = rt in
        match return_bt with
        | Unit ->
            let lrt = LRT.subst (IT.make_subst [(return_s, lvt)]) lrt in
            let@ original_resources = all_resources_tagged loc in
            Spine.subtype loc lrt (fun () ->
                  let@ () = all_empty loc original_resources in
                  return ()
              )
        | _ ->
            let msg = "Non-void-return function does not call 'return'." in
            fail (fun _ -> {loc; msg = Generic !^msg})
    )






(* let check_pexpr_rt loc pexpr (RT.Computational ((return_s, return_bt), info, lrt)) = *)
(*   check_pexpr pexpr ~expect:return_bt (fun lvt -> *)
(*   let lrt = LRT.subst (IT.make_subst [(return_s, lvt)]) lrt in *)
(*   let@ original_resources = all_resources_tagged () in *)
(*   Spine.subtype loc lrt (fun () -> *)
(*   let@ () = all_empty loc original_resources in *)
(*   return ())) *)




let bind_arguments (loc : Loc.t) (full_args : _ mu_arguments) =

  let rec aux_l resources = function
    | M_Define ((s, it), ((loc, _) as info), args) ->
       let@ () = add_l s (IT.bt it) (fst info, lazy (Sym.pp s)) in
       let@ () = add_c (fst info) (LC.t_ (def_ s it loc)) in
       aux_l resources args
    | M_Constraint (lc, info, args) ->
       let@ () = add_c (fst info) lc in
       aux_l resources args
    | M_Resource ((s, (re, bt)), ((loc, _) as info), args) ->
       let@ () = add_l s bt (fst info, lazy (Sym.pp s)) in
       aux_l (resources @ [(re, O (sym_ (s, bt, loc)))]) args
    | M_I i ->
       return (i, resources)
  in

  let rec aux_a = function
    | M_Computational ((s, bt), info, args) ->
       let@ () = add_a s bt (fst info, lazy (Sym.pp s)) in
       aux_a args
    | M_L args ->
       aux_l [] args

  in

  aux_a full_args


let post_state_of_rt loc rt =
  let open False in
  let rt_as_at = AT.of_rt rt (LAT.I False) in
  let rt_as_args = Core_to_mucore.arguments_of_at (fun False -> False) rt_as_at in
  pure begin
     let@ False, final_resources = bind_arguments loc rt_as_args in
     let@ () = add_rs loc final_resources in
     get ()
   end




(* check_procedure: type check an (impure) procedure *)
let check_procedure
      (loc : loc)
      (fsym : Sym.t)
      (args_and_body : _ mu_proc_args_and_body)
    : unit m =
  debug 2 (lazy (headline ("checking procedure " ^ Sym.pp_string fsym)));

  pure begin

      let@ ((body, label_defs, rt), initial_resources) = bind_arguments loc args_and_body in

      let label_context = WellTyped.WProc.label_context rt label_defs in
      let label_defs = Pmap.bindings_list label_defs in

      let@ (), _mete_pre_state =
        debug 2 (lazy (headline ("checking function body " ^ Sym.pp_string fsym)));
        pure begin
            let@ () = add_rs loc initial_resources in
            let@ pre_state = get () in
            let@ () = add_label_to_trace None in
            let@ () = check_expr_top loc label_context rt body in
            return ((), pre_state)
          end
      in
      let@ _mete_post_state = post_state_of_rt loc rt in

      let@ () = ListM.iterM (fun (lsym, def) ->
        pure begin match def with
          | M_Return loc ->
             return ()
          | M_Label (loc, label_args_and_body, annots, _) ->
             debug 2 (lazy (headline ("checking label " ^ Sym.pp_string lsym ^ " " ^ Loc.to_string loc)));
             let@ (label_body, label_resources) = bind_arguments loc label_args_and_body in
             let@ () = add_rs loc label_resources in
             let (_,label_kind,loc) = SymMap.find lsym label_context in
             let@ () = add_label_to_trace (Some (loc,label_kind)) in
             check_expr_top loc label_context rt label_body
          end
        ) label_defs
      in
      return ()
    end



let skip_and_only = ref (([] : string list), ([] : string list))
let batch = ref false

let record_tagdefs tagDefs =
  PmapM.iterM (fun tag def ->
      match def with
      | M_UnionDef _ -> unsupported (Loc.other __FUNCTION__) !^"todo: union types"
      | M_StructDef layout -> add_struct_decl tag layout
    ) tagDefs

let check_tagdefs tagDefs =
  PmapM.iterM (fun tag def ->
    let open Memory in
    match def with
    | M_UnionDef _ ->
       unsupported (Loc.other __FUNCTION__) !^"todo: union types"
    | M_StructDef layout ->
       let@ _ =
         ListM.fold_rightM (fun piece have ->
             match piece.member_or_padding with
             | Some (name, _) when IdSet.mem name have ->
                (* this should have been checked earlier by the frontend *)
                assert false
             | Some (name, ct) ->
                let@ () = WellTyped.WCT.is_ct (Loc.other __FUNCTION__) ct in
                return (IdSet.add name have)
             | None ->
                return have
           ) layout IdSet.empty
       in
       return ()
  ) tagDefs



let record_and_check_logical_functions funs =

  let recursive, nonrecursive =
    List.partition (fun (_, def) ->
        LogicalFunctions.is_recursive def
      ) funs
  in

  let n_funs = List.length funs in

  (* Add all recursive functions (without their actual bodies), so that they
     can depend on themselves and each other. *)
  let@ () =
    ListM.iterM (fun (name, def) ->
        let@ simple_def = WellTyped.WLFD.welltyped {def with definition = Uninterp} in
        add_logical_function name simple_def
      ) recursive
  in

  (* Now check all functions in order. *)
  ListM.iteriM (fun i (name, def) ->
        debug 2 (lazy (headline ("checking welltypedness of function" ^
            Pp.of_total i n_funs ^ ": " ^ Sym.pp_string name)));
        let@ def = WellTyped.WLFD.welltyped def in
        add_logical_function name def
      ) funs

let record_and_check_resource_predicates preds =
  (* add the names to the context, so recursive preds check *)
  let@ () =
    ListM.iterM (fun (name, def) ->
        let@ simple_def = WellTyped.WRPD.welltyped { def with clauses = None } in
        add_resource_predicate name simple_def
      ) preds
  in
  ListM.iteriM (fun i (name, def) ->
      debug 2 (lazy (headline ("checking welltypedness of resource pred" ^
          Pp.of_total i (List.length preds) ^ ": " ^ Sym.pp_string name)));
      let@ def = WellTyped.WRPD.welltyped def in
      (* add simplified def to the context *)
      add_resource_predicate name def
    ) preds


let record_globals : 'bty. (symbol * 'bty mu_globs) list -> unit m =
  fun globs ->
  (* TODO: check the expressions *)
  ListM.iterM (fun (sym, def) ->
      match def with
      | M_GlobalDef (ct, _)
      | M_GlobalDecl ct ->
         let@ () = WellTyped.WCT.is_ct (Loc.other __FUNCTION__) ct in
         let bt = Loc in
         let info = (Loc.other __FUNCTION__, lazy (Pp.item "global" (Sym.pp sym))) in
         let@ () = add_a sym bt info in
         let here = Locations.other __FUNCTION__ in
         let@ () = add_c here (t_ (IT.good_pointer ~pointee_ct:ct (sym_ (sym, bt, here)) here)) in
         return ()
    ) globs


let register_fun_syms mu_file =
  let add fsym loc =
    (* add to context *)
    (* let lc1 = t_ (ne_ (null_, sym_ (fsym, Loc))) in *)
    let lc2 = t_ (representable_ (Pointer Void, sym_ (fsym, Loc, loc)) loc) in
    let@ () = add_l fsym Loc (loc, lazy (Pp.item "global fun-ptr" (Sym.pp fsym))) in
    let@ () = add_cs loc [(* lc1; *) lc2] in
    return ()
  in
  PmapM.iterM (fun fsym def -> match def with
      | M_Proc (loc, _, _, _) -> add fsym loc
      | M_ProcDecl (loc, _) -> add fsym loc
    ) mu_file.mu_funs


let wf_check_and_record_functions mu_funs mu_call_sigs =
  let n_syms = List.length (Pmap.bindings_list mu_funs) in
  let welltyped_ping i fsym =
    debug 2 (lazy (headline ("checking welltypedness of procedure" ^
        Pp.of_total i n_syms ^ ": " ^ Sym.pp_string fsym)))
  in
  PmapM.foldiM (fun i fsym def (trusted, checked) ->
      match def with
      | M_Proc (loc, args_and_body, tr, _parse_ast_things) ->
         welltyped_ping i fsym;
         let@ args_and_body = WellTyped.WProc.welltyped loc args_and_body in
         let ft = WellTyped.WProc.typ args_and_body in
         debug 6 (lazy (!^"function type" ^^^ Sym.pp fsym));
         debug 6 (lazy (CF.Pp_ast.pp_doc_tree (AT.dtree RT.dtree ft)));
         let@ () = add_fun_decl fsym (loc, Some ft, Pmap.find fsym mu_call_sigs) in
         begin match tr with
         | Trusted _ -> return ((fsym, (loc, ft)) :: trusted, checked)
         | Checked -> return (trusted, (fsym, (loc, args_and_body)) :: checked)
         end
      | M_ProcDecl (loc, oft) ->
         welltyped_ping i fsym;
         let@ oft = match oft with
           | None -> return None
           | Some ft ->
              let@ ft = WellTyped.WFT.welltyped "function" loc ft in
              return (Some ft)
         in
         let@ () = add_fun_decl fsym (loc, oft, Pmap.find fsym mu_call_sigs) in
         return (trusted, checked)
    ) mu_funs ([], [])




let check_c_functions funs =
  let matches_str s fsym = String.equal s (Sym.pp_string fsym) in
  let str_fsyms s = match List.filter (matches_str s) (List.map fst funs) with
    | [] ->
      Pp.warn_noloc (!^"function" ^^^ !^s ^^^ !^"not found");
      []
    | ss -> ss
  in
  let strs_fsyms ss = SymSet.of_list (List.concat_map str_fsyms ss) in
  let skip = strs_fsyms (fst (! skip_and_only)) in
  let only = strs_fsyms (snd (! skip_and_only)) in
  let only_funs = match (snd (! skip_and_only)) with
    | [] -> funs
    | ss -> List.filter (fun (fsym, _) -> SymSet.mem fsym only) funs
  in
  let selected_funs = List.filter (fun (fsym, _) -> not (SymSet.mem fsym skip)) only_funs in
  let number_entries = List.length selected_funs in
  match !batch with
  | false ->
     let@ _ =
       ListM.mapiM (fun counter (fsym, (loc, args_and_body)) ->
           let () = progress_simple (of_total (counter+1) number_entries) (Sym.pp_string fsym) in
           check_procedure loc fsym args_and_body
         ) selected_funs
     in
     return ()
  | true ->
     let@ _, pass, fail =
       ListM.fold_leftM (fun (counter,pass,fail) (fsym, (loc, args_and_body)) ->
           let@ outcome = sandbox (check_procedure loc fsym args_and_body) in
           match outcome with
           | Ok _ ->
              progress_simple (of_total (counter+1) number_entries) (Sym.pp_string fsym ^ " -- pass");
              return (counter+1, pass+1, fail)
           | Error _ ->
              progress_simple (of_total (counter+1) number_entries) (Sym.pp_string fsym ^ " -- fail");
              return (counter+1, pass, fail+1)
         ) (0, 0, 0) selected_funs
     in
     print stdout (item "summary" (int pass ^^^ !^"pass" ^^ comma ^^^ int fail ^^^ !^"fail" ));
     return ()



(* (Sym.t * (Locations.t * ArgumentTypes.lemmat)) list *)

let wf_check_and_record_lemma (lemma_s, (loc, lemma_typ)) =
  let@ lemma_typ = WellTyped.WLemma.welltyped loc lemma_s lemma_typ in
  let@ () = add_lemma lemma_s (loc, lemma_typ) in
  return (lemma_s, (loc, lemma_typ))


let ctz_proxy_ft =
  let here = Locations.other __FUNCTION__ in
  let info = (here, Some "ctz_proxy builtin ft") in
  let (n_sym, n) = IT.fresh_named (BT.(Bits (Unsigned, 32))) "n_" here in
  let (ret_sym, ret) = IT.fresh_named (BT.(Bits (Signed, 32))) "return" here in
  let neq_0 = LC.T (IT.not_ (IT.eq_ (n, IT.int_lit_ 0 (IT.bt n) here) here) here) in
  let eq_ctz = LC.T (IT.eq_ (ret, cast_ (IT.bt ret) (IT.arith_unop Terms.BWCTZNoSMT n here) here) here) in
  let rt = RT.mComputational ((ret_sym, IT.bt ret), info)
    (LRT.mConstraint (eq_ctz, info) LRT.I) in
  let ft = AT.mComputationals [(n_sym, IT.bt n, info)]
    (AT.L (LAT.mConstraint (neq_0, info) (LAT.I rt))) in
  ft

let ffs_proxy_ft sz =
  let here = Locations.other __FUNCTION__ in
  let sz_name = CF.Pp_ail.string_of_integerBaseType sz in
  let bt = Memory.bt_of_sct (Sctypes.(Integer (Signed sz))) in
  let ret_bt = Memory.bt_of_sct (Sctypes.(Integer (Signed Int_))) in
  let info = (Locations.other __FUNCTION__, Some ("ffs_proxy builtin ft: " ^ sz_name)) in
  let (n_sym, n) = IT.fresh_named bt "n_" here in
  let (ret_sym, ret) = IT.fresh_named ret_bt "return" here in
  let eq_ffs = LC.T (IT.eq_ (ret, IT.cast_ ret_bt (IT.arith_unop Terms.BWFFSNoSMT n here) here) here) in
  let rt = RT.mComputational ((ret_sym, ret_bt), info)
    (LRT.mConstraint (eq_ffs, info) LRT.I) in
  let ft = AT.mComputationals [(n_sym, bt, info)] (AT.L (LAT.I rt)) in
  ft

let add_stdlib_spec mu_call_sigs fsym =
  match Sym.has_id fsym with
  (* FIXME: change the naming, we aren't unfolding these *)
  | Some s when Setup.unfold_stdlib_name s ->
    let add ft = begin
        Pp.debug 2 (lazy (Pp.headline ("adding builtin spec for procedure " ^ Sym.pp_string fsym)));
        add_fun_decl fsym (Locations.other __FUNCTION__, Some ft, Pmap.find fsym mu_call_sigs)
      end in
    if String.equal s "ctz_proxy"
    then
      add ctz_proxy_ft
    else if String.equal s "ffs_proxy"
    then
      add (ffs_proxy_ft (Sctypes.IntegerBaseTypes.Int_))
    else if String.equal s "ffsl_proxy"
    then
      add (ffs_proxy_ft (Sctypes.IntegerBaseTypes.Long))
    else if String.equal s "ffsll_proxy"
    then
      add (ffs_proxy_ft (Sctypes.IntegerBaseTypes.LongLong))
    else
      return ()
  | _ ->
    return ()


let record_and_check_datatypes datatypes =
  (* add "empty datatypes" for checks on recursive types to succeed *)
  let@ () =
    ListM.iterM (fun (s, {loc; cases}) ->
        add_datatype s { dt_constrs = []; dt_all_params = [] }
      ) datatypes
  in
  (* check and normalise datatypes *)
  let@ datatypes = ListM.mapM WellTyped.WDT.welltyped datatypes in
  let@ sccs = WellTyped.WDT.check_recursion_ok datatypes in
  let@ () = set_datatype_order (Some sccs) in
  (* properly add datatypes *)
  ListM.iterM (fun (s, {loc; cases}) ->
      let@ () =
        add_datatype s {
            dt_constrs = List.map fst cases;
            dt_all_params = List.concat_map snd cases
          }
      in
      ListM.iterM (fun (c,c_params) ->
          add_datatype_constr c { c_params; c_datatype_tag = s }
        ) cases
    ) datatypes




let check (mu_file : unit mu_file) stmt_locs o_lemma_mode =
  Cerb_debug.begin_csv_timing () (*total*);

  Pp.debug 3 (lazy (Pp.headline "beginning type-checking mucore file."));

  (* let@ mu_file = WellTyped.BaseTyping.infer_types_file mu_file in *)

  let@ () = set_statement_locs stmt_locs in

  let@ () = record_tagdefs mu_file.mu_tagDefs in
  let@ () = check_tagdefs mu_file.mu_tagDefs in

  let@ () = record_and_check_datatypes mu_file.mu_datatypes in

  let@ () = init_solver () in

  let@ () = record_globals mu_file.mu_globs in

  let@ () = register_fun_syms mu_file in

  let@ () = ListM.iterM (add_stdlib_spec mu_file.mu_call_funinfo)
    (SymSet.elements mu_file.mu_stdlib_syms) in

  Pp.debug 3 (lazy (Pp.headline "added top-level types and constants."));

  let@ () = record_and_check_logical_functions mu_file.mu_logical_predicates in
  let@ () = record_and_check_resource_predicates mu_file.mu_resource_predicates in

  let@ lemmata = ListM.mapM wf_check_and_record_lemma mu_file.mu_lemmata in

  let@ () = CLogicalFuns.add_logical_funs_from_c mu_file.mu_call_funinfo
    mu_file.mu_mk_functions mu_file.mu_funs in

  Pp.debug 3 (lazy (Pp.headline "type-checked CN top-level declarations."));

  let@ (_trusted, checked) =
    wf_check_and_record_functions mu_file.mu_funs mu_file.mu_call_funinfo
  in

  Pp.debug 3 (lazy (Pp.headline "type-checked C functions and specifications."));

  Cerb_debug.begin_csv_timing () (*type checking functions*);
  let@ () = check_c_functions checked in
  Cerb_debug.end_csv_timing "type checking functions";

  let@ global = get_global () in
  let@ () = match o_lemma_mode with
  | Some mode -> embed_resultat (Lemmata.generate global mode lemmata)
  | None -> return ()
  in
  Cerb_debug.end_csv_timing "total";
  Pp.debug 3 (lazy (Pp.headline "done type-checking mucore file."));
  return ()












(* TODO:
   - sequencing strength
   - rem_t vs rem_f
   - check globals with expressions
   - inline TODOs
   - make sure all variables disjoint from global variables and function names
   - check datatype definition wellformedness
 *)
