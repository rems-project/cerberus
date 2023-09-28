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

open Tools
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

let bogus_cbt_to_bt (cbt : Mucore.T.cbt) = BT.Integer


let add_c loc lc =
  let@ _ = WellTyped.WLC.welltyped loc lc in
  Typing.add_c loc lc



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
         let@ () = add_c loc (LC.t_ (eq__ it (nil_ ~item_bt))) in
         return []
      | M_Ccons, [p1; p2] ->
         let@ () = ensure_base_type loc ~expect:bty (List (bt_of_pattern p1)) in
         let@ () = ensure_base_type loc ~expect:bty (bt_of_pattern p2) in
         let item_bt = bt_of_pattern p1 in
         let@ a1 = check_and_match_pattern p1 (head_ ~item_bt it) in
         let@ a2 = check_and_match_pattern p2 (tail_ it) in
         let@ () = add_c loc (LC.t_ (ne_ (it, nil_ ~item_bt))) in
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



let check_ptrval (loc : loc) ~(expect:BT.t) (ptrval : pointer_value) : IT.t m =
  let@ () = ensure_base_type loc ~expect BT.Loc in
  CF.Impl_mem.case_ptrval ptrval
    ( fun ct -> 
      let sct = Sctypes.of_ctype_unsafe loc ct in
      let@ () = WellTyped.WCT.is_ct loc sct in
      return IT.null_ )
    ( function
        | None ->
            (* FIXME(CHERI merge) *)
            (* we can now have invalid function pointer values (e.g. if someone touched the bytes in a wrong way) *)
            unsupported loc !^"invalid function pointer"
        | Some sym -> 
            (* just to make sure it exists *)
            let@ _ = get_fun_decl loc sym in
            (* the symbol of a function is the same as the symbol of its address *)
            return (sym_ (sym, BT.Loc)) ) 
    ( fun _prov p -> 
      (* TODO: Dhruv, do we want to do something with the provenance here? *)
      return (pointer_ p) )

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
      return (int_lit_ (Memory.int_of_ival iv) bt) )
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
      return (make_array_ ~item_bt values) )
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
  return (IT.struct_ (tag, member_its))

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
     let@ _ = ensure_bitvector_type loc ~expect in
     return (num_lit_ (Memory.z_of_ival iv) expect)
  | M_OVpointer p -> 
     check_ptrval loc ~expect p
  | M_OVarray items ->
     let item_bt = bt_of_object_value (List.hd items) in
     let@ () = ensure_base_type loc ~expect (Map (Integer, item_bt)) in
     let@ () = ListM.iterM (fun i -> ensure_base_type loc ~expect:item_bt (bt_of_object_value i)) items in
     let@ values = ListM.mapM (check_object_value loc) items in
     return (make_array_ ~item_bt values)
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
     return (IT.const_ctype_ ct)
  | M_Vunit ->
     let@ () = WellTyped.ensure_base_type loc ~expect Unit in
     return IT.unit_
  | M_Vtrue ->
     let@ () = WellTyped.ensure_base_type loc ~expect Bool in
     return (IT.bool_ true)
  | M_Vfalse -> 
     let@ () = WellTyped.ensure_base_type loc ~expect Bool in
     return (IT.bool_ false)
  | M_Vfunction_addr sym ->
     let@ () = ensure_base_type loc ~expect Loc in
     (* check it is a valid function address *)
     let@ _ = get_fun_decl loc sym in
     return (IT.sym_ (sym, Loc))
  | M_Vlist (_item_cbt, vals) ->
     let item_bt = bt_of_value (List.hd vals) in
     let@ () = WellTyped.ensure_base_type loc ~expect (List item_bt) in
     let@ () = ListM.iterM (fun i -> ensure_base_type loc ~expect:item_bt (bt_of_value i)) vals in
     let@ values = ListM.mapM (check_value loc) vals in
     return (list_ ~item_bt values)
  | M_Vtuple vals ->
     let item_bts = List.map bt_of_value vals in
     let@ () = ensure_base_type loc ~expect (Tuple item_bts) in
     let@ values = ListM.mapM (check_value loc) vals in
     return (tuple_ values)




(*** pure expression inference ************************************************)


(* try to follow is_representable_integer from runtime/libcore/std.core *)
let is_representable_integer arg ity = failwith "fix this"
  (* let maxInt = Memory.max_integer_type ity in *)
  (* let minInt = Memory.min_integer_type ity in *)
  (* and_ [le_ (z_ minInt, arg); le_ (arg, z_ maxInt)] *)


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
    let@ m = model_with loc (IT.bool_ true) in
    let@ m = fail_on_none "cannot get model" m in
    let@ g = get_global () in
    let@ y = fail_on_none "cannot eval term" (Solver.eval g (fst m) expr) in
    let@ _ = fail_on_none "eval to non-constant term" (IT.is_const y) in
    let eq = IT.eq_ (expr, y) in
    let@ provable = provable loc in
    begin match provable (t_ eq) with
      | `True ->
        let@ () = add_c loc (t_ eq) in
        return y
      | `False ->
        return expr
    end


let is_fun_addr global t = match IT.is_sym t with
  | Some (s, _) -> if SymMap.mem s global.Global.fun_decls
      then Some s else None
  | _ -> None

let get_loc_addrs_in_eqs () =
  (* bit of a hack, there's code down to the solver to spot equalities where
     either the lhs or rhs is a symbol *)
  let@ focused = get_solver_focused_terms () in
  let@ g = get_global () in
  let addrs = List.filter_map IT.is_eq (List.map snd focused)
    |> List.concat_map (fun (x, y) -> [x; y])
    |> List.filter_map (is_fun_addr g) in
  Pp.debug 5 (lazy (Pp.item "loc eqs for function pointer check" (Pp.list Sym.pp addrs)));
  return addrs

let check_single_ct loc expr =
  let@ pointer = WellTyped.WIT.check loc BT.CType expr in
  let@ t = try_prove_constant loc expr in
  match IT.is_const t with
    | Some (IT.CType_const ct, _) -> return ct
    | Some _ -> assert false (* should be impossible given the type *)
    | None -> fail (fun _ -> {loc;
        msg = Generic (!^ "use of non-constant ctype mucore expression")})


let get_eq_in_model loc msg x opts =
  let@ m = model_with loc (IT.bool_ true) in
  let@ m = match m with
    | None -> fail (fun _ -> {loc; msg = Generic (Pp.item "cannot get model for" msg)})
    | Some m -> return m
  in
  let@ g = get_global () in
  let ev x = Solver.eval g (fst m) x in
  let@ () = match ev x with
    | None -> fail (fun _ -> {loc; msg = Generic (Pp.item "get_eq_in_model: cannot eval in model"
        (IT.pp x ^^^ !^ "for:" ^^^ msg))})
    | Some _ -> return ()
  in
  let y = List.find_opt
    (fun y -> Option.equal IT.equal (ev (eq_ (x, y))) (Some (IT.bool_ true)))
    opts in
  match y with
    | Some y -> return y
    | None -> fail (fun _ -> {loc; msg = Generic (Pp.item "get_eq_in_model: no options are equal"
        ((Pp.typ (IT.pp x) (Pp.braces (Pp.list IT.pp opts))) ^^^ !^ "for:" ^^^ msg))})
 
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
  let@ value = match ity with
    | Bool ->
       (* TODO: can we (later) express this more efficiently without ITE? *)
       return (ite_ (eq_ (arg, num_lit_ Z.zero bt), 
                     num_lit_ Z.zero expect, 
                     num_lit_ Z.one expect))
    | _ when Sctypes.is_unsigned_integer_type ity ->
       let representable = representable_ (ct, arg) in
       (* TODO: revisit this *)
       (* TODO: this has to be fixed. The basetypes do not work out.
          The return value always has to have basetype 'expect'. *)
       (* I think: representable(ct,t) has to compare t with
          MinInt(ct) and MaxInt(ct) *in a bitvector type large enough
          for both the type of t and Min/MaxInt(ct). *)
       begin match provable (t_ representable) with
       | `True -> 
          (* some kind of cast is needed here, but one that does not change the value *)
          return arg
       | `False ->
          (* same as above, some cast is needed for 'arg', where as wrapI's type is already OK *)
          return (ite_ (representable, arg, wrapI_ (ity, arg)))
       end
    | _ ->
       begin match provable (t_ (representable_ (ct, arg))) with
       | `True -> 
          (* TODO: again, have to cast arg somehow, without changing the value *)
          return arg
       | `False -> 
          fail_unrepresentable ()
       end
  in
  return value

let _check_array_shift loc ~expect vt1 (loc_ct, ct) vt2 =
  let@ () = WellTyped.ensure_base_type loc ~expect Loc in
  let@ () = WellTyped.WCT.is_ct loc_ct ct in
  return (arrayShift_ (vt1, ct, vt2))

let check_against_core_bt loc msg2 cbt bt = 
  Typing.embed_resultat
    (CoreTypeChecks.check_against_core_bt
       (fun msg -> Resultat.fail {loc; msg = Generic (msg ^^ Pp.hardline ^^ msg2)})
       cbt bt)



let rec check_pexpr (pe : BT.t mu_pexpr) (k : IT.t -> unit m) : unit m =
  let orig_pe = pe in
  let (M_Pexpr (loc, _, expect, pe_)) = pe in
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
        k (sym_ (sym, bt))
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
        check_pexprs pes (fun values -> k (tuple_ values))
     | M_Carray, _ -> 
        let item_bt = bt_of_pexpr (List.hd pes) in
        let@ () = ensure_base_type loc ~expect (Map (Integer, item_bt)) in
        let@ () = ListM.iterM (fun i -> ensure_base_type loc ~expect:item_bt (bt_of_pexpr i)) pes in
        check_pexprs pes (fun values ->
        k (make_array_ ~item_bt values))
     | M_Cnil item_cbt, [] ->
        let@ item_bt = match expect with
          | List item_bt -> return item_bt
          | _ ->
             let msg = Mismatch {has = !^"list"; expect = BT.pp expect} in
             fail (fun _ -> {loc; msg})
        in
        let@ () = check_against_core_bt loc (!^ "checking Cnil") item_cbt item_bt in
        k (nil_ ~item_bt)
     | M_Cnil item_bt, _ -> 
        fail (fun _ -> {loc; msg = Number_arguments {has = List.length pes; expect=0}})
     | M_Ccons, [pe1; pe2] -> 
        let@ () = ensure_base_type loc ~expect (List (bt_of_pexpr pe1)) in
        let@ () = ensure_base_type loc ~expect (bt_of_pexpr pe2) in
        check_pexpr pe1 (fun vt1 ->
        check_pexpr pe2 (fun vt2 ->
        k (cons_ (vt1, vt2))))
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
     let value = arith_unop unop vt1 in
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
     let value = arith_binop binop (vt1, vt2) in
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
     k (arrayShift_ (vt1, ct, (cast_ Memory.intptr_bt vt2)))))
  | M_PEmember_shift (pe, tag, member) ->
     let@ () = WellTyped.ensure_base_type loc ~expect Loc in
     let@ () = ensure_base_type loc ~expect:Loc (bt_of_pexpr pe) in
     check_pexpr pe (fun vt ->
     let@ _ = get_struct_member_type loc tag member in
     k (memberShift_ (vt, tag, member)))
  | M_PEnot pe ->
     let@ () = WellTyped.ensure_base_type loc ~expect Bool in
     let@ () = ensure_base_type loc ~expect:Bool (bt_of_pexpr pe) in
     check_pexpr pe (fun vt ->
     k (not_ vt))
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
        k (eq_ (v1, v2))))
     | OpGt ->
        let@ () = WellTyped.ensure_base_type loc ~expect Bool in
        let@ () = check_cmp_ty (bt_of_pexpr pe1) in
        let@ () = WellTyped.ensure_base_type loc ~expect:(bt_of_pexpr pe1) (bt_of_pexpr pe2) in
        check_pexpr pe1 (fun v1 ->
        check_pexpr pe2 (fun v2 ->
        k (gt_ (v1, v2))))
     | OpLt ->
        let@ () = WellTyped.ensure_base_type loc ~expect Bool in
        let@ () = check_cmp_ty (bt_of_pexpr pe1) in
        let@ () = WellTyped.ensure_base_type loc ~expect:(bt_of_pexpr pe1) (bt_of_pexpr pe2) in
        check_pexpr pe1 (fun v1 ->
        check_pexpr pe2 (fun v2 ->
        k (lt_ (v1, v2))))
     | OpGe ->
        let@ () = WellTyped.ensure_base_type loc ~expect Bool in
        let@ () = check_cmp_ty (bt_of_pexpr pe1) in
        let@ () = WellTyped.ensure_base_type loc ~expect:(bt_of_pexpr pe1) (bt_of_pexpr pe2) in
        check_pexpr pe1 (fun v1 ->
        check_pexpr pe2 (fun v2 ->
        k (ge_ (v1, v2))))
     | OpLe ->
        let@ () = WellTyped.ensure_base_type loc ~expect Bool in
        let@ () = check_cmp_ty (bt_of_pexpr pe1) in
        let@ () = WellTyped.ensure_base_type loc ~expect:(bt_of_pexpr pe1) (bt_of_pexpr pe2) in
        check_pexpr pe1 (fun v1 ->
        check_pexpr pe2 (fun v2 ->
        k (le_ (v1, v2))))
     | OpAnd ->
        let@ () = WellTyped.ensure_base_type loc ~expect Bool in
        let@ () = WellTyped.ensure_base_type loc ~expect:Bool (bt_of_pexpr pe1) in
        let@ () = WellTyped.ensure_base_type loc ~expect:Bool (bt_of_pexpr pe2) in
        check_pexpr pe1 (fun v1 ->
        check_pexpr pe2 (fun v2 ->
        k (and_ [v1; v2])))
     | OpOr ->
        let@ () = WellTyped.ensure_base_type loc ~expect Bool in
        let@ () = WellTyped.ensure_base_type loc ~expect:Bool (bt_of_pexpr pe1) in
        let@ () = WellTyped.ensure_base_type loc ~expect:Bool (bt_of_pexpr pe2) in
        check_pexpr pe1 (fun v1 ->
        check_pexpr pe2 (fun v2 ->
        k (or_ [v1; v2])))
     | _ ->
       Pp.debug 1 (lazy (Pp.item "not yet restored" (Pp_mucore_ast.pp_pexpr orig_pe)));
       failwith "todo"
     end
  | M_PEapply_fun (fun_id, args) ->
     let@ () = ensure_base_type loc ~expect (mu_fun_return_type fun_id) in
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
     let@ args = ListM.mapM (prefer_value_with IT.is_const_val) args in
     match Mucore.evaluate_fun fun_id args with
     | Some t -> k t
     | None -> fail (fun _ -> {loc; msg = Generic (!^ "cannot evaluate function:" ^^^
           Pp.c_app (Mucore.pp_function fun_id) (List.map IT.pp args))})
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
     k (struct_ (tag, members)))
  | M_PEunion _ ->
     Cerb_debug.error "todo: PEunion"
  | M_PEcfunction pe2 ->
     let@ () = ensure_base_type loc ~expect (Tuple [CType; List CType; Bool; Bool]) in
     let@ () = ensure_base_type loc ~expect:Loc (bt_of_pexpr pe2) in
     check_pexpr pe2 (fun ptr ->
     let@ global = get_global () in
     (* function vals are just symbols the same as the names of functions *)
     let@ known = eq_value_with (is_fun_addr global) ptr in
     begin match known with
     | Some (_, sym) ->
       (* need to conjure up the characterising 4-tuple *)
       Pp.debug 5 (lazy (!^ "lookup of C function:" ^^^ Sym.pp sym));
       Pp.debug 5 (lazy (!^ "in globals:" ^^^ IT.pp (IT.bool_ (SymMap.mem sym global.Global.fun_decls))));
       let@ (_, _, c_sig) = get_fun_decl loc sym in
       begin match IT.const_of_c_sig c_sig with
         | Some it -> k it
         | None -> fail (fun _ -> {loc; msg = Generic (!^ "unsupported c-type in sig of:" ^^^
             Sym.pp sym)})
       end
     | None ->
       (* time to case split on function-pointer possibilities. *)
       let explanation = !^ "a function pointer must be explicitly enumerated" ^^^
           !^ "e.g. (in_loc_list (p, [fun1; fun2]))" in
       let@ opts = get_loc_addrs_in_eqs () in
       let@ () = if List.length opts > 0 then return ()
         else fail (fun _ -> {loc; msg = Generic (!^"no address eqs found:" ^^^ explanation)}) in
       let msg = !^ "picking function target" ^^^ Pp.parens explanation in
       let ptr_opts = List.map (fun nm -> (sym_ (nm, BT.Loc))) opts in
       let@ eq_opt = get_eq_in_model loc msg ptr ptr_opts in
       Pp.debug 5 (lazy (Pp.item "function pointer application: case splitting on" (IT.pp eq_opt)));
       let aux e cond =
         let@ () = add_c loc (t_ cond) in
         Pp.debug 5 (lazy (Pp.item "checking consistency of eq branch" (IT.pp cond)));
         let@ provable = provable loc in
         match provable (t_ (bool_ false)) with
         | `True -> return ()
         | `False -> check_pexpr e k
       in
       let@ () = pure (aux pe (eq_ (ptr, eq_opt))) in
       let@ () = pure (aux pe (not_ (eq_ (ptr, eq_opt)))) in
       return ()
    end
  )
  | M_PEmemberof _ ->
     Cerb_debug.error "todo: M_PEmemberof"
  | M_PEbool_to_integer pe ->
     let@ _ = ensure_bitvector_type loc ~expect in
     let@ () = ensure_base_type loc ~expect:Bool (bt_of_pexpr pe) in
     check_pexpr pe (fun arg ->
     k (ite_ (arg, int_lit_ 1 expect, int_lit_ 0 expect)))
  | M_PEbounded_binop (M_Bound_Wrap act, iop, pe1, pe2) ->
     (* in integers, perform this op and round. in bitvector types, just perform
        the op (for all the ops where wrapping is consistent) *)
     let@ () = WellTyped.WCT.is_ct act.loc act.ct in
     assert (match act.ct with Integer ity when is_unsigned_integer_type ity -> true | _ -> false);
     let@ () = ensure_base_type loc ~expect (Memory.bt_of_sct act.ct) in
     let@ () = ensure_base_type loc ~expect (bt_of_pexpr pe1) in
     let@ () = ensure_base_type loc ~expect (bt_of_pexpr pe2) in
     check_pexpr pe1 (fun arg1 ->
     check_pexpr pe2 (fun arg2 ->
     let x = match iop with
       | IOpAdd -> add_ (arg1, arg2)
       | IOpSub -> sub_ (arg1, arg2)
       | IOpMul -> mul_ (arg1, arg2)
     in
     k x))
  | M_PEbounded_binop (M_Bound_Except act, iop, pe1, pe2) ->
     failwith "todo"
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
  | M_PEwrapI (act, pe) -> assert false
     (* let@ () = WellTyped.WCT.is_ct act.loc act.ct in *)
     (* let@ () = WellTyped.ensure_base_type loc ~expect Integer in *)
     (* check_pexpr pe (fun arg -> *)
     (* let ity = Option.get (Sctypes.is_integer_type act.ct) in *)
     (* k (wrapI_ (ity, arg))) *)
  | M_PEcatch_exceptional_condition (act, pe) ->
     assert false
     (* let@ () = WellTyped.WCT.is_ct act.loc act.ct in *)
     (* let@ () = WellTyped.ensure_base_type loc ~expect Integer in *)
     (* let ity = Option.get (Sctypes.is_integer_type act.ct) in *)
     (* check_pexpr pe (fun arg -> *)
     (*     let@ provable = provable loc in *)
     (*     match provable (t_ (is_representable_integer arg ity)) with *)
     (*     | `True -> (k arg) *)
     (*     | `False ->  *)
     (*        let@ model = model () in *)
     (*        let ub = CF.Undefined.UB036_exceptional_condition in *)
     (*        fail (fun ctxt -> {loc; msg = Undefined_behaviour {ub; ctxt; model}}) *)
     (* ) *)
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
     let aux e cond = 
       let@ () = add_c loc (t_ cond) in
       Pp.debug 5 (lazy (Pp.item "checking consistency of if-branch" (IT.pp cond)));
       let@ provable = provable loc in
       match provable (t_ (bool_ false)) with
       | `True -> return ()
       | `False -> check_pexpr e k
     in
     let@ () = pure (aux e1 c) in
     let@ () = pure (aux e2 (not_ c)) in
     return ())
  | M_PElet (p, e1, e2) ->
     let@ fin = begin_trace_of_pure_step (Some p) e1 in
     let@ () = ensure_base_type loc ~expect (bt_of_pexpr e2) in
     let@ () = ensure_base_type loc ~expect:(bt_of_pexpr e1) (bt_of_pattern p) in
     check_pexpr e1 (fun v1 ->
     let@ bound_a = check_and_match_pattern p v1 in
     let@ () = fin () in
     check_pexpr e2 (fun lvt ->
     let@ () = remove_as bound_a in
     k lvt))
  | M_PEundef (loc, ub) ->
     let@ provable = provable loc in
     begin match provable (t_ (bool_ false)) with
     | `True -> return ()
     | `False ->
        let@ model = model () in
        fail (fun ctxt -> {loc; msg = Undefined_behaviour {ub; ctxt; model}})
     end
  | M_PEerror (err, _pe) ->
     let@ provable = provable loc in
     begin match provable (t_ (bool_ false)) with
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
    let@ original_resources = all_resources_tagged () in

    let@ rt = 
      let rec check ftyp = 
        let@ () = print_with_ctxt (fun ctxt ->
            debug 6 (lazy (item "ctxt" (Context.pp ctxt)));
            debug 6 (lazy (item "spec" (LAT.pp rt_pp ftyp)));
          )
        in
        let@ ftyp = RI.General.ftyp_args_request_step rt_subst loc (Call situation)
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

    let rec check args ftyp k = 
      match args, ftyp with
      | (arg :: args), (Computational ((s, bt), _info, ftyp)) ->
         check_arg arg ~expect:bt (fun arg ->
         check args (subst rt_subst (make_subst [(s, arg)]) ftyp) k)
      | [], (L ftyp) -> 
         k ftyp
      | _ -> 
         let expect = count_computational original_ftyp in
         let has = List.length original_args in
         fail (fun _ -> {loc; msg = Number_arguments {expect; has}})
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
open OrFalse

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
      fail_with_trace (fun trace ctxt ->
            let ctxt = { ctxt with resources = original_resources } in
            {loc; msg = Unused_resource {resource; ctxt; model; trace}})


let compute_used (prev_rs, prev_ix) (post_rs, _) =
  let post_ixs = IntSet.of_list (List.map snd post_rs) in
  (* restore previous resources that have disappeared from the context, since they
     might participate in a race *)
  let all_rs = post_rs @ List.filter (fun (_, i) -> not (IntSet.mem i post_ixs)) prev_rs in
  ListM.fold_leftM (fun (rs, ws) (r, i) ->
    let@ h = res_history i in
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
  pure begin
    let@ (point, O value), _ = 
      RI.Special.predicate_request loc (Access Load)
        ({name = Owned (ct, Init); pointer; iargs = []}, None)
    in
    return value
  end


let instantiate loc filter arg =
  let arg_s = Sym.fresh_make_uniq "instance" in
  let arg_it = sym_ (arg_s, IT.bt arg) in
  let@ () = add_l arg_s (IT.bt arg_it) (loc, lazy (Sym.pp arg_s)) in
  let@ () = add_c loc (LC.t_ (eq__ arg_it arg)) in
  let@ constraints = all_constraints () in
  let extra_assumptions = 
    List.filter_map (fun lc ->
        match lc with
        | Forall ((s, bt), t) 
             when BT.equal bt (IT.bt arg_it) && filter t ->
           Some (LC.t_ (IT.subst (IT.make_subst [(s, arg_it)]) t))
        | _ -> 
           None
      ) (LCSet.elements constraints)
  in
  if List.length extra_assumptions == 0 then Pp.warn loc (Pp.string "nothing instantiated")
  else ();
  add_cs loc extra_assumptions




let rec check_expr labels (e : BT.t mu_expr) (k: IT.t -> unit m) : unit m =
  let (M_Expr (loc, _annots, expect, e_)) = e in
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
        pointer_op eq_ pe1 pe2
     | M_PtrNe (pe1, pe2) -> 
        pointer_op ne_ pe1 pe2
     | M_PtrLt (pe1, pe2) -> 
        pointer_op ltPointer_ pe1 pe2
     | M_PtrGt (pe1, pe2) -> 
        pointer_op gtPointer_ pe1 pe2
     | M_PtrLe (pe1, pe2) -> 
        pointer_op lePointer_ pe1 pe2
     | M_PtrGe (pe1, pe2) -> 
        pointer_op gePointer_ pe1 pe2
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
        let value =
          (* TODO: here there might be a basetype mismatch: arg1 and
             arg2 are cast to intptr_t, the return value we want is of
             the basetype corresponding to ptrdiff_t (hence the
             divisor literal type). But AIUI, these don't have to be
             the same base type?*)
          div_
            (sub_ (pointerToIntegerCast_ arg1, (* intptr_t *)
                   pointerToIntegerCast_ arg2), (* intptr_t *)
             int_lit_ divisor (Memory.bt_of_sct (Integer Ptrdiff_t)))
        in
        k value))
     | M_IntFromPtr (act_from, act_to, pe) ->
        let@ () = WellTyped.WCT.is_ct act_from.loc act_from.ct in
        let@ () = WellTyped.WCT.is_ct act_to.loc act_to.ct in
        assert (match act_from.ct with Pointer _ -> true | _ -> false);
        assert (match act_to.ct with Integer _ -> true | _ -> false);
        let@ () = ensure_base_type loc ~expect (Memory.bt_of_sct act_to.ct) in
        let@ () = ensure_base_type loc ~expect:(Memory.bt_of_sct act_from.ct) (bt_of_pexpr pe) in
        check_pexpr pe (fun arg ->
        (* TODO: is this good? *)
        let test_value = cast_ Memory.intptr_bt arg in
        let actual_value = cast_ (Memory.bt_of_sct act_to.ct) arg in
        let@ () = 
          (* after discussing with Kavyan *)
          let@ provable = provable loc in
          let lc = t_ (representable_ (act_to.ct, test_value)) in
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
        assert (match act_from.ct with Integer _ -> true | _ -> false);
        assert (match act_to.ct with Pointer _ -> true | _ -> false);
        let@ () = WellTyped.ensure_base_type loc ~expect (Memory.bt_of_sct act_to.ct) in
        let@ () = WellTyped.ensure_base_type loc ~expect:(Memory.bt_of_sct act_from.ct) (bt_of_pexpr pe) in
        check_pexpr pe (fun arg ->
        (* TODO: what about unrepresentable values? If that's possible
           we to make sure our cast semantics correctly matches C's *)
        let value = integerToPointerCast_ arg in
        k value)
     | M_PtrValidForDeref (act, pe) ->
        (* TODO: provenance things? *)
        let@ () = WellTyped.WCT.is_ct act.loc act.ct in
        let@ () = WellTyped.ensure_base_type loc ~expect Bool in
        let@ () = WellTyped.ensure_base_type loc ~expect:Loc (bt_of_pexpr pe) in
        (* TODO: check. Also: this is the same as PtrWellAligned *)
        check_pexpr pe (fun arg ->
        let value = aligned_ (arg, act.ct) in
        k value)
     | M_PtrWellAligned (act, pe) ->
        let@ () = WellTyped.WCT.is_ct act.loc act.ct in
        let@ () = WellTyped.ensure_base_type loc ~expect Bool in
        let@ () = WellTyped.ensure_base_type loc ~expect:Loc (bt_of_pexpr pe) in
        (* TODO: check *)
        check_pexpr pe (fun arg ->
        let value = aligned_ (arg, act.ct) in
        k value)
     | M_PtrArrayShift (pe1, act, pe2) ->
        let@ () = ensure_base_type loc ~expect Loc in
        let@ () = ensure_base_type loc ~expect:Loc (bt_of_pexpr pe1) in
        let@ () = WellTyped.WCT.is_ct act.loc act.ct in
        let@ () = WellTyped.ensure_bits_type loc (bt_of_pexpr pe2) in
        check_pexpr pe1 (fun vt1 ->
        check_pexpr pe2 (fun vt2 ->
        k (arrayShift_ (vt1, act.ct, vt2))))
     | M_PtrMemberShift (tag_sym, memb_ident, pe) ->
        (* FIXME(CHERI merge) *)
        (* there is now an effectful variant of the member shift operator (which is UB when creating an out of bound pointer) *)
        Cerb_debug.error "todo: M_PtrMemberShift"
     | M_CopyAllocId (pe1, pe2) ->
        check_pexpr ~expect:Integer pe1 (fun vt1 ->
        check_pexpr ~expect:BT.Loc pe2 (fun vt2 ->
        let _alloc_id = pointerToAllocIdCast_ vt2 in
        let new_ptr = integerToPointerCast_ vt1 in
        k new_ptr))
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
  | M_Eaction (M_Paction (_pol, M_Action (aloc, action_))) ->
     begin match action_ with
     | M_Create (pe, act, prefix) -> 
        let@ () = WellTyped.ensure_base_type loc ~expect Loc in
        let@ () = WellTyped.WCT.is_ct act.loc act.ct in
        check_pexpr pe (fun arg ->
        let ret_s, ret = match prefix with 
          | PrefSource (_loc, syms) -> 
             let syms = List.rev syms in
             begin match syms with
             | (Symbol (_, _, SD_ObjectAddress str)) :: _ ->
                IT.fresh_named Loc ("&" ^ str)
             | _ -> 
                IT.fresh Loc
             end
          | PrefFunArg (_loc, _, n) -> 
             IT.fresh_named Loc ("&ARG" ^ string_of_int n)
          | _ -> 
             IT.fresh Loc
        in
        let@ () = add_l ret_s (IT.bt ret) (loc, lazy (Pp.string "allocation")) in
        let@ () = add_c loc (t_ (representable_ (Pointer act.ct, ret))) in
        let align_v = cast_ Memory.intptr_bt arg in
        let@ () = add_c loc (t_ (alignedI_ ~align:align_v ~t:ret)) in
        let@ () = 
          add_r loc
            (P { name = Owned (act.ct, Uninit); 
                 pointer = ret;
                 iargs = [];
               }, 
             O (default_ (Memory.bt_of_sct act.ct)))
        in
        let@ () =
          add_r loc (P (Global.mk_alloc ret), O IT.unit_) in
        k ret)
     | M_CreateReadOnly (sym1, ct, sym2, _prefix) -> 
        Cerb_debug.error "todo: CreateReadOnly"
     | M_Alloc (ct, sym, _prefix) -> 
        Cerb_debug.error "todo: Alloc"
     | M_Kill (M_Dynamic, asym) -> 
        Cerb_debug.error "todo: Free"
     | M_Kill (M_Static ct, pe) -> 
        let@ () = WellTyped.ensure_base_type loc ~expect Unit in
        let@ () = WellTyped.WCT.is_ct loc ct in
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
        k unit_)
     | M_Store (_is_locking, act, p_pe, v_pe, mo) -> 
        let@ () = WellTyped.ensure_base_type loc ~expect Unit in
        let@ () = WellTyped.WCT.is_ct act.loc act.ct in
        check_pexpr p_pe (fun parg ->
        check_pexpr v_pe (fun varg ->
        (* The generated Core program will in most cases before this
           already have checked whether the store value is
           representable and done the right thing. Pointers, as I
           understand, are an exception. *)
        let@ () = 
          let in_range_lc = representable_ (act.ct, varg) in
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
        k unit_))
     | M_Load (act, p_pe, _mo) -> 
        let@ () = WellTyped.WCT.is_ct act.loc act.ct in
        let@ () = WellTyped.ensure_base_type loc ~expect (Memory.bt_of_sct act.ct) in
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
     k unit_
  | M_Eccall (act, f_pe, pes) ->
     (* todo: do anything with act? *)
     let@ () = WellTyped.WCT.is_ct act.loc act.ct in
     check_pexpr f_pe (fun f_it ->
     let@ global = get_global () in
     let@ known = eq_value_with (is_fun_addr global) f_it in
     let@ fsym = match known with
       | Some (_, sym) -> return sym
       | _ -> unsupported loc !^"function application of function pointers"
     in
     let@ (_loc, opt_ft, _) = get_fun_decl loc fsym in
     let@ ft = match opt_ft with
       | Some ft -> return ft
       | None -> fail (fun _ -> {loc; msg = Generic (!^"Call to function with no spec:" ^^^ Sym.pp fsym)})
     in
     Spine.calltype_ft loc ~fsym pes ft (fun (Computational ((_, bt), _, _) as rt) ->
     let@ () = WellTyped.ensure_base_type loc ~expect bt in
     let@ _, members = make_return_record loc (TypeErrors.call_prefix (FunctionCall fsym)) (RT.binders rt) in
     let@ lvt = bind_return loc members rt in
     k lvt))
  | M_Eif (c_pe, e1, e2) ->
     check_pexpr c_pe (fun carg ->
     let aux lc nm e = 
       let@ () = add_c loc (t_ lc) in
       let@ provable = provable loc in
       match provable (t_ (bool_ false)) with
       | `True -> return ()
       | `False -> check_expr labels e k
     in
     let@ () = pure (aux carg "true" e1) in
     let@ () = pure (aux (not_ carg) "false" e2) in
     return ())
  | M_Ebound e ->
     check_expr labels e k
  | M_End _ ->
     Cerb_debug.error "todo: End"
  | M_Elet (p, e1, e2) ->
     let@ fin = begin_trace_of_pure_step (Some p) e1 in
     check_pexpr e1 (fun v1 ->
     let@ () = ensure_base_type loc ~expect:(IT.bt v1) (bt_of_pattern p) in
     let@ bound_a = check_and_match_pattern p v1 in
     let@ () = fin () in
     check_expr labels e2 (fun rt ->
         let@ () = remove_as bound_a in
         k rt
     ))
  | M_Eunseq es ->
     let@ item_bts = match expect with
       | Tuple bts ->
          let expect_nr = List.length bts in
          let has_nr = List.length es in
          let@ () = WellTyped.ensure_same_argument_number loc `General has_nr ~expect:expect_nr in
          return bts
       | _ -> 
          let msg = Mismatch {has = !^"tuple"; expect = BT.pp expect} in
          fail (fun _ -> {loc; msg})
     in
     let rec aux es_bts vs prev_used = match es_bts with
       | (e, bt) :: es_bts ->
          let@ pre_check = all_resources_tagged () in
          check_expr labels e (fun v ->
          let@ post_check = all_resources_tagged () in
          let@ used = compute_used pre_check post_check in
          aux es_bts (v :: vs) (used :: prev_used))
       | [] ->
          (* let@ () = check_used_distinct loc prev_used in *)
          k (tuple_ (List.rev vs))
     in
     aux (List.combine es item_bts) [] []
  | M_CN_progs (_, cn_progs) ->
     let@ () = WellTyped.ensure_base_type loc ~expect Unit in
     let rec aux = function
       | Cnprog.M_CN_let (loc, (sym, {ct; pointer}), cn_prog) ->
          let@ pointer = WellTyped.WIT.check loc Loc pointer in
          let@ () = WCT.is_ct loc ct in
          let@ value = load loc pointer ct in
          aux (Cnprog.subst (IT.make_subst [(sym, value)]) cn_prog)
       | Cnprog.M_CN_statement (loc, stmt) ->
          (* copying bits of code from elsewhere in check.ml *)
          begin match stmt with
            | M_CN_pack_unpack (pack_unpack, pt) -> 
                    warn loc !^"Explicit pack/unpack unsupported.";
                    return ()
(*                let@ pred = WRET.welltyped loc (P pt) in
               let pt = match pred with P pt -> pt | _ -> assert false in
               let@ pname, def = match pt.name with
                 | PName pname -> 
                    let@ def = Typing.get_resource_predicate_def loc pname in
                    return (pname, def)
                 | Owned _ -> 
                    fail (fun _ -> {loc; msg = Generic !^"Packing/unpacking 'Owned' currently unsupported."})
                 | Block _ -> 
                    fail (fun _ -> {loc; msg = Generic !^"Packing/unpacking 'Block' currently unsupported."})
               in
               let err_prefix = match pack_unpack with
                 | Pack -> !^ "cannot pack:" ^^^ pp_predicate_name pt.name
                 | Unpack -> !^ "cannot unpack:" ^^^ pp_predicate_name pt.name
               in
               let@ right_clause = 
                 ResourceInference.select_resource_predicate_clause def
                   loc pt.pointer pt.iargs err_prefix 
               in
               begin match pack_unpack with
               | Unpack ->
                  let@ (pred, O pred_oarg) =
                    RI.Special.predicate_request ~recursive:false
                      loc (Call (UnpackPredicate (Manual, pname))) (pt, None)
                  in
                  let lrt = ResourcePredicates.clause_lrt pred_oarg right_clause.packing_ft in
                  let@ _, members = make_return_record loc (UnpackPredicate (Manual, pname)) (LRT.binders lrt) in
                  bind_logical_return loc members lrt
               | Pack ->
                  Spine.calltype_packing loc pname right_clause.packing_ft (fun output -> 
                  add_r loc (P pt, O output)
                  )
               end *)
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
               let@ it = WIT.infer loc it in
               instantiate loc filter it
            | M_CN_extract (to_extract, it) ->
               let@ predicate_name = RI.predicate_name_of_to_extract loc to_extract in
               let@ it = WIT.infer loc it in
               add_movable_index loc (predicate_name, it)
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
                  add_c loc (LC.t_ (eq_ (pred_ f args def.return_bt, body)))
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
                  let@ () = Diagnostics.investigate model lc in
                  fail_with_trace (fun trace ctxt ->
                      {loc; msg = Unproven_constraint {constr = lc; info = (loc, None); ctxt; model; trace}}
                    )
               end
            | M_CN_inline _nms ->
               return ()
          end
     in
     let@ () = ListM.iterM aux cn_progs in
     k unit_
  | M_Ewseq (p, e1, e2)
  | M_Esseq (p, e1, e2) ->
     let@ fin = begin_trace_of_step (Some p) e1 in
     check_expr labels e1 (fun it ->
            let@ () = ensure_base_type loc ~expect:(IT.bt it) (bt_of_pattern p) in
            let@ bound_a = check_and_match_pattern p it in
            let@ () = fin () in
            check_expr labels e2 (fun it2 ->
                let@ () = remove_as bound_a in
                k it2
              )
       )
  | M_Erun (label_sym, pes) ->
     let@ (lt,lkind) = match SymMap.find_opt label_sym labels with
       | None -> fail (fun _ -> {loc; msg = Generic (!^"undefined code label" ^/^ Sym.pp label_sym)})
       | Some (lt,lkind) -> return (lt,lkind)
     in
     let@ original_resources = all_resources_tagged () in
     Spine.calltype_lt loc pes (lt,lkind) (fun False ->
     let@ () = all_empty loc original_resources in
     return ())



let check_expr_rt loc labels ~typ e = 
  let@ () = add_loc_trace loc in
  match typ with
  | Normal (RT.Computational ((return_s, return_bt), info, lrt)) ->
     let@ () = WellTyped.ensure_base_type loc ~expect:Unit (bt_of_expr e) in
     check_expr labels e (fun returned_lvt ->
         let lrt = LRT.subst (IT.make_subst [(return_s, returned_lvt)]) lrt in
         let@ original_resources = all_resources_tagged () in
         Spine.subtype loc lrt (fun () ->
         let@ () = all_empty loc original_resources in
         return ())
       )
  | False ->
     check_expr labels e (fun _ -> assert false)





(* let check_pexpr_rt loc pexpr (RT.Computational ((return_s, return_bt), info, lrt)) = *)
(*   check_pexpr pexpr ~expect:return_bt (fun lvt -> *)
(*   let lrt = LRT.subst (IT.make_subst [(return_s, lvt)]) lrt in *)
(*   let@ original_resources = all_resources_tagged () in *)
(*   Spine.subtype loc lrt (fun () -> *)
(*   let@ () = all_empty loc original_resources in *)
(*   return ())) *)




let bind_arguments (loc : Loc.t) (full_args : _ mu_arguments) =

  let rec aux_l resources = function
    | M_Define ((s, it), info, args) ->
       let@ () = add_l s (IT.bt it) (fst info, lazy (Sym.pp s)) in
       let@ () = add_c (fst info) (LC.t_ (def_ s it)) in
       aux_l resources args
    | M_Constraint (lc, info, args) ->
       let@ () = add_c (fst info) lc in
       aux_l resources args
    | M_Resource ((s, (re, bt)), info, args) ->
       let@ () = add_l s bt (fst info, lazy (Sym.pp s)) in
       aux_l (resources @ [(re, O (sym_ (s, bt)))]) args
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
            let@ () = check_expr_rt loc label_context ~typ:(Normal rt) body in
            return ((), pre_state)
          end 
      in
      let@ _mete_post_state = post_state_of_rt loc rt in

      let@ () = ListM.iterM (fun (lsym, def) ->
        pure begin match def with
          | M_Return loc ->
             return ()
          | M_Label (loc, label_args_and_body, annots, _) ->
             debug 2 (lazy (headline ("checking label " ^ Sym.pp_string lsym)));
             let@ (label_body, label_resources) = bind_arguments loc label_args_and_body in
             let@ () = add_rs loc label_resources in
             check_expr_rt loc label_context ~typ:False label_body
          end
        ) label_defs 
      in
      return ()
    end

 

let only = ref None

let record_tagdefs tagDefs = 
  PmapM.iterM (fun tag def ->
      match def with
      | M_UnionDef _ -> unsupported Loc.unknown !^"todo: union types"
      | M_StructDef layout -> add_struct_decl tag layout
    ) tagDefs

let check_tagdefs tagDefs =
  PmapM.iterM (fun tag def ->
    let open Memory in
    match def with
    | M_UnionDef _ -> 
       unsupported Loc.unknown !^"todo: union types"
    | M_StructDef layout -> 
       let@ _ = 
         ListM.fold_rightM (fun piece have ->
             match piece.member_or_padding with
             | Some (name, _) when IdSet.mem name have ->
                fail (fun _ -> {loc = Loc.unknown; msg = Duplicate_member name})
             | Some (name, ct) -> 
                let@ () = WellTyped.WCT.is_ct Loc.unknown ct in
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

  (* First check and add non-recursive functions. We check before
     adding them, because they cannot depend on themselves*)
  let@ () =
    ListM.iterM (fun (name, def) -> 
        debug 2 (lazy (headline ("checking welltypedness of function " ^ Sym.pp_string name)));
        let@ def = WellTyped.WLFD.welltyped def in
        add_logical_function name def
      ) nonrecursive
  in

  (* Then we check the recursive functions: add them all as uninterpreted, check
     welltypedness of each, then overwrite with actual (NIA-simplified) body. *)

  let@ () =
    ListM.iterM (fun (name, def) -> 
        let@ simple_def = WellTyped.WLFD.welltyped {def with definition = Uninterp} in
        add_logical_function name simple_def
      ) recursive
  in
  ListM.iterM (fun (name, def) -> 
      debug 2 (lazy (headline ("checking welltypedness of function " ^ Sym.pp_string name)));
      let@ def = WellTyped.WLFD.welltyped def in
      add_logical_function name def
    ) recursive

let record_and_check_resource_predicates preds =
  (* add the names to the context, so recursive preds check *)
  let@ () = 
    ListM.iterM (fun (name, def) ->
        let@ simple_def = WellTyped.WRPD.welltyped { def with clauses = None } in
        add_resource_predicate name simple_def
      ) preds 
  in
  ListM.iterM (fun (name, def) ->
      debug 2 (lazy (headline ("checking welltypedness of resource pred " ^ Sym.pp_string name)));
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
         let@ () = WellTyped.WCT.is_ct Loc.unknown ct in
         let bt = Loc in
         let info = (Loc.unknown, lazy (Pp.item "global" (Sym.pp sym))) in
         let@ () = add_a sym bt info in
         let@ () = add_c Loc.unknown (t_ (IT.good_pointer ~pointee_ct:ct (sym_ (sym, bt)))) in
         return ()
    ) globs 


let register_fun_syms mu_file =
  let add fsym loc =
    (* add to context *)
    (* let lc1 = t_ (ne_ (null_, sym_ (fsym, Loc))) in *)
    let lc2 = t_ (representable_ (Pointer Void, sym_ (fsym, Loc))) in
    let@ () = add_l fsym Loc (loc, lazy (Pp.item "global fun-ptr" (Sym.pp fsym))) in
    let@ () = add_cs loc [(* lc1; *) lc2] in
    return ()
  in
  PmapM.iterM (fun fsym def -> match def with
      | M_Proc (loc, _, _, _) -> add fsym loc
      | M_ProcDecl (loc, _) -> add fsym loc
    ) mu_file.mu_funs


let wf_check_and_record_functions mu_funs mu_call_sigs =
  let welltyped_ping fsym =
    debug 2 (lazy (headline ("checking welltypedness of procedure " ^ Sym.pp_string fsym)))
  in
  PmapM.foldM (fun fsym def (trusted, checked) ->
      match def with
      | M_Proc (loc, args_and_body, tr, _parse_ast_things) ->
         welltyped_ping fsym;
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
         welltyped_ping fsym;
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
  match !only with
  | Some fname ->
     let found = 
       List.find_opt (fun (fsym, _) ->
           (String.equal fname (Sym.pp_string fsym))
         ) funs
     in
     begin match found with
     | Some (fsym, (loc, args_and_body)) ->
        let () = progress_simple (of_total 1 1) (Sym.pp_string fsym) in
        check_procedure loc fsym args_and_body
     | None ->
        Pp.warn_noloc (!^"function" ^^^ !^fname ^^^ !^"not found");
        return ()
     end
  | None ->
     let number_entries = List.length funs in
     let@ _ = 
       ListM.mapiM (fun counter (fsym, (loc, args_and_body)) ->
           let () = progress_simple (of_total (counter+1) number_entries) (Sym.pp_string fsym) in
           check_procedure loc fsym args_and_body
         ) funs
     in
     return ()



(* (Sym.t * (Locations.t * ArgumentTypes.lemmat)) list *)

let wf_check_and_record_lemma (lemma_s, (loc, lemma_typ)) =
  let@ lemma_typ = WellTyped.WLemma.welltyped loc lemma_s lemma_typ in
  let@ () = add_lemma lemma_s (loc, lemma_typ) in
  return (lemma_s, (loc, lemma_typ))


let ctz_proxy_ft =
  let info = (Locations.unknown, Some "ctz_proxy builtin ft") in
  let (n_sym, n) = IT.fresh_named BT.Integer "n_" in
  let (ret_sym, ret) = IT.fresh_named BT.Integer "return" in
  let neq_0 = LC.T (IT.not_ (IT.eq_ (n, IT.int_ 0))) in
  let eq_ctz = LC.T (IT.eq_ (ret, IT.arith_unop Terms.BWCTZNoSMT n)) in
  let rt = RT.mComputational ((ret_sym, BT.Integer), info)
    (LRT.mConstraint (eq_ctz, info) LRT.I) in
  let ft = AT.mComputationals [(n_sym, BT.Integer, info)]
    (AT.L (LAT.mConstraint (neq_0, info) (LAT.I rt))) in
  ft

let ffs_proxy_ft =
  let info = (Locations.unknown, Some "ffs_proxy builtin ft") in
  let (n_sym, n) = IT.fresh_named BT.Integer "n_" in
  let (ret_sym, ret) = IT.fresh_named BT.Integer "return" in
  let eq_ffs = LC.T (IT.eq_ (ret, IT.arith_unop Terms.BWFFSNoSMT n)) in
  let rt = RT.mComputational ((ret_sym, BT.Integer), info)
    (LRT.mConstraint (eq_ffs, info) LRT.I) in
  let ft = AT.mComputationals [(n_sym, BT.Integer, info)] (AT.L (LAT.I rt)) in
  ft


let add_stdlib_spec mu_call_sigs fsym =
  match Sym.has_id fsym with
  (* FIXME: change the naming, we aren't unfolding these *)
  | Some s when Setup.unfold_stdlib_name s ->
    let add ft = begin
        Pp.debug 2 (lazy (Pp.headline ("adding builtin spec for procedure " ^ Sym.pp_string fsym)));
        add_fun_decl fsym (Locations.unknown, Some ft, Pmap.find fsym mu_call_sigs)
      end in
    if String.equal s "ctz_proxy"
    then
      add ctz_proxy_ft
    else if String.equal s "ffs_proxy"
    then
      add ffs_proxy_ft
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

  let@ () = record_globals mu_file.mu_globs in

  let@ () = register_fun_syms mu_file in

  let@ () = ListM.iterM (add_stdlib_spec mu_file.mu_call_funinfo)
    (SymSet.elements mu_file.mu_stdlib_syms) in

  Pp.debug 3 (lazy (Pp.headline "added top-level types and constants."));

  let@ () = record_and_check_logical_functions mu_file.mu_logical_predicates in
  let@ () = record_and_check_resource_predicates mu_file.mu_resource_predicates in

  let@ lemmata = ListM.mapM wf_check_and_record_lemma mu_file.mu_lemmata in

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
