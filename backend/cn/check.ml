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
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module S = Solver
module Loc = Locations
module LF = LogicalFunctions
module Mu = Mucore
module RI = ResourceInference

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




type lvt = IT.t


(* some of this is informed by impl_mem *)


type mem_value = CF.Impl_mem.mem_value
type pointer_value = CF.Impl_mem.pointer_value




(*** pattern matching *********************************************************)

let rec infer_pattern (M_Pattern (loc, _, pattern)) =
  match pattern with
  | M_CaseBase (_, has_bt) -> 
     let@ () = WellTyped.WBT.is_bt loc has_bt in
     return has_bt
  | M_CaseCtor (constructor, pats) ->
    begin match constructor, pats with
    | M_Cnil item_bt, [] -> 
       return (BT.List item_bt)
    | M_Cnil _, _ ->
       fail (fun _ -> {loc; msg = Number_arguments {has = List.length pats; expect = 0}})
    | M_Ccons, [p1; p2] -> 
       let@ bt1 = infer_pattern p1 in
       let@ bt2 = infer_pattern p2 in
       let@ () = WellTyped.ensure_base_type loc ~expect:(List bt1) bt2 in
       return (List bt1)
    | M_Ccons, _ ->
        fail (fun _ -> {loc; msg = Number_arguments {has = List.length pats; expect = 2}})
    | M_Ctuple, pats ->
        let@ bts = ListM.mapM infer_pattern pats in
        return (BT.Tuple bts)
    | M_Carray, _ ->
        Debug_ocaml.error "todo: array types"
    end





(* pattern-matches and binds *)
let rec old_pattern_match (M_Pattern (loc, _, pattern)) it =
  match pattern with
  | M_CaseBase (o_s, has_bt) ->
     begin match o_s with
     | Some s ->
        let@ () = add_a s (IT.bt it) (loc, lazy (Sym.pp s)) in
        let@ () = add_c (LC.t_ (def_ s it)) in
        return [s]
     | None -> 
        return []
     end
  | M_CaseCtor (constructor, pats) ->
     match constructor, pats with
     | M_Cnil item_bt, [] ->
        let@ () = add_c (LC.t_ (eq__ it (nil_ ~item_bt))) in
        return []
     | M_Ccons, [p1; p2] ->
        let@ item_bt = infer_pattern p1 in
        let@ a1 = old_pattern_match p1 (head_ ~item_bt it) in
        let@ a2 = old_pattern_match p2 (tail_ it) in
        let@ () = add_c (LC.t_ (ne_ (it, nil_ ~item_bt))) in
        return (a1 @ a2)
     | M_Ctuple, pats ->
        let@ all_as = ListM.mapiM (fun i p ->
          let@ item_bt = infer_pattern p in
          old_pattern_match p (nthTuple_ ~item_bt (i, it))
        ) pats in
        return (List.concat all_as)
     | M_Carray, _ ->
        Debug_ocaml.error "todo: array patterns"
     | _ -> 
        assert false

let _old_pattern_match = old_pattern_match (* for the moment keep both versions alive*)        

(* pattern-matches and binds *)
let rec pattern_match (M_Pattern (loc, _, pattern)) it =
   match pattern with
   | M_CaseBase (o_s, has_bt) ->
      begin match o_s with
      | Some s ->
         let@ () = add_a_value s it (loc, lazy (Sym.pp s)) in
         return [s]
      | None -> 
         return []
      end
   | M_CaseCtor (constructor, pats) ->
      match constructor, pats with
      | M_Cnil item_bt, [] ->
         let@ () = add_c (LC.t_ (eq__ it (nil_ ~item_bt))) in
         return []
      | M_Ccons, [p1; p2] ->
         let@ item_bt = infer_pattern p1 in
         let@ a1 = pattern_match p1 (head_ ~item_bt it) in
         let@ a2 = pattern_match p2 (tail_ it) in
         let@ () = add_c (LC.t_ (ne_ (it, nil_ ~item_bt))) in
         return (a1 @ a2)
      | M_Ctuple, pats ->
         let@ all_as = ListM.mapiM (fun i p ->
           let@ item_bt = infer_pattern p in
           pattern_match p (Simplify.IndexTerms.tuple_nth_reduce it i item_bt)
         ) pats in
         return (List.concat all_as)
      | M_Carray, _ ->
         Debug_ocaml.error "todo: array patterns"
      | _ -> 
         assert false
 






open Binding



let use_model_eqs = ref true


module InferenceEqs = struct


(* todo: what is this? Can we replace this by using the predicate_name
   + information about whether iterated or not? *)
let res_pointer_kind (res, _) = match res with
  | (RET.P ({name = Owned ct; _} as res_pt)) -> Some ((("", "Pt"), ct), res_pt.pointer)
  | (RET.Q ({name = Owned ct; _} as res_qpt)) -> Some ((("", "QPt"), ct), res_qpt.pointer)
  | (RET.P ({name = PName pn; _} as res_pd)) -> Some (((Sym.pp_string pn, "Pd"), Sctypes.Void), res_pd.pointer)
  | _ -> None

let div_groups cmp xs =
  let rec gather x xs gps ys = match ys with
    | [] -> (x :: xs) :: gps
    | (z :: zs) -> if cmp x z == 0 then gather z (x :: xs) gps zs
    else gather z [] ((x :: xs) :: gps) zs
  in
  match List.sort cmp xs with
    | [] -> []
    | (y :: ys) -> gather y [] [] ys

let div_groups_discard cmp xs =
  List.map (List.map snd) (div_groups (fun (k, _) (k2, _) -> cmp k k2) xs)

let unknown_eq_in_group simp_ctxt ptr_gp = List.find_map (fun (p, req) -> if not req then None
  else List.find_map (fun (p2, req) -> if req then None
    else if is_true (Simplify.IndexTerms.simp simp_ctxt (eq_ (p, p2))) then None
    else Some (eq_ (p, p2))) ptr_gp) ptr_gp

let upd_ptr_gps_for_model global m ptr_gps =
  let eval_f p = match Solver.eval global m p with
    | Some (IT (Const (Pointer i), _)) -> i
    | _ -> (print stderr (IT.pp p); assert false)
  in
  let eval_eqs = List.map (List.map (fun (p, req) -> (eval_f p, (p, req)))) ptr_gps in
  let ptr_gps = List.concat (List.map (div_groups_discard Z.compare) eval_eqs) in
  ptr_gps

let add_eqs_for_infer loc ftyp =
  (* TODO: tweak 'fuel'-related things *)
  if not (! use_model_eqs) then return ()
  else
  begin
  let start_eqs = time_log_start "eqs" "" in
  debug 5 (lazy (format [] "pre-inference equality discovery"));
  let reqs = LAT.r_resource_requests ftyp in
  let@ ress = map_and_fold_resources loc (fun re xs -> (Unchanged, re :: xs)) [] in
  let res_ptr_k k r = Option.map (fun (ct, p) -> (ct, (p, k))) (res_pointer_kind r) in
  let ptrs = List.filter_map (fun (_, r) -> res_ptr_k true r) reqs @
    (List.filter_map (res_ptr_k false) ress) in
  let cmp2 = Lem_basic_classes.pairCompare
        (Lem_basic_classes.pairCompare String.compare String.compare) CT.compare in
  let ptr_gps = div_groups_discard cmp2 ptrs in
  let@ ms = prev_models_with loc (bool_ true) in
  let@ global = get_global () in
  let ptr_gps = List.fold_right (upd_ptr_gps_for_model global)
        (List.map fst ms) ptr_gps in
  let@ provable = provable loc in
  let rec loop fuel ptr_gps =
    if fuel <= 0 then begin
      debug 5 (lazy (format [] "equality discovery fuel exhausted"));
      return ()
    end
    else
    let@ simp_ctxt = simp_ctxt () in
    let poss_eqs = List.filter_map (unknown_eq_in_group simp_ctxt) ptr_gps in
    debug 7 (lazy (format [] ("investigating " ^
        Int.to_string (List.length poss_eqs) ^ " possible eqs")));
    if List.length poss_eqs == 0
    then return ()
    else match provable (t_ (and_ poss_eqs)) with
      | `True ->
        debug 5 (lazy (item "adding equalities" (IT.pp (and_ poss_eqs))));
        let@ () = add_cs (List.map t_ poss_eqs) in
        loop (fuel - 1) ptr_gps
      | `False ->
        let (m, _) = Solver.model () in
        debug 7 (lazy (format [] ("eqs refuted, processing model")));
        let ptr_gps = upd_ptr_gps_for_model global m ptr_gps in
        loop (fuel - 1) ptr_gps
  in
  let@ () = loop 10 ptr_gps in
  debug 5 (lazy (format [] "finished equality discovery"));
  time_log_end start_eqs;
  return ()
  end

(*
    let exact_match () =
      let@ global = get_global () in
      let@ all_lcs = all_constraints () in
      return begin fun (request, resource) -> match (request, resource) with
      | (RER.Point req_p, RE.Point res_p) ->
        let simp t = Simplify.simp global.struct_decls all_lcs t in
        let pmatch = eq_ (req_p.pointer, res_p.pointer) in
        let more_perm = impl_ (req_p.permission, res_p.permission) in
        (* FIXME: simp of Impl isn't all that clever *)
        (is_true (simp pmatch) && is_true (simp more_perm))
      | _ -> false
      end
*)


end






(*** function call typing, subtyping, and resource inference *****************)

(* spine is parameterised so it can be used both for function and
   label types (which don't have a return type) *)







(*** pure value inference *****************************************************)


let check_computational_bound loc s = 
  let@ is_bound = bound_a s in
  if is_bound 
  then return () 
  else fail (fun _ -> {loc; msg = Unknown_variable s})



let check_ptrval (loc : loc) ~(expect:BT.t) (ptrval : pointer_value) : (lvt) m =
  let@ () = ensure_base_type loc ~expect BT.Loc in
  CF.Impl_mem.case_ptrval ptrval
    ( fun ct -> 
      let sct = Sctypes.of_ctype_unsafe loc ct in
      let@ () = WellTyped.WCT.is_ct loc sct in
      return IT.null_ )
    ( fun sym -> 
      (* just to make sure it exists *)
      let@ _ = get_fun_decl loc sym in
      (* the symbol of a function is the same as the symbol of its address *)
      return (sym_ (sym, BT.Loc)) ) 
    ( fun _prov p -> 
      return (pointer_ p) )

let rec check_mem_value (loc : loc) ~(expect:BT.t) (mem : mem_value) : (lvt) m =
  CF.Impl_mem.case_mem_value mem
    ( fun ct -> 
      let@ () = WellTyped.WCT.is_ct loc (Sctypes.of_ctype_unsafe loc ct) in
      fail (fun _ -> {loc; msg = Unspecified ct}) )
    ( fun _ _ -> 
      unsupported loc !^"infer_mem_value: concurrent read case" )
    ( fun ity iv -> 
      (* TODO: do anything with ity? *)
      let@ () = WellTyped.ensure_base_type loc ~expect Integer in
      return (int_ (Memory.int_of_ival iv)) )
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
           let msg = Mismatch {has = !^"Array"; expect = BT.pp expect} in
           fail (fun _ -> {loc; msg})
      in
      assert (BT.equal index_bt Integer);
      let@ values = ListM.mapM (check_mem_value loc ~expect:item_bt) mem_values in
      return (make_array_ ~item_bt values) )
    ( fun tag mvals -> 
      let@ () = WellTyped.ensure_base_type loc ~expect (Struct tag) in
      let mvals = List.map (fun (member, _, mv) -> (member, mv)) mvals in
      check_struct loc tag mvals )
    ( fun tag id mv -> 
      check_union loc tag id mv )

and check_struct (loc : loc) (tag : Sym.t) 
                 (member_values : (Id.t * mem_value) list) : (lvt) m =
  (* might have to make sure the fields are ordered in the same way as
     in the struct declaration *)
  let@ layout = get_struct_decl loc tag in
  let rec check fields spec =
    match fields, spec with
    | ((member, mv) :: fields), ((smember, sct) :: spec) 
         when Id.equal member smember ->
       let@ member_lvt = check_mem_value loc ~expect:(BT.of_sct sct) mv in
       let@ member_its = check fields spec in
       return ((member, member_lvt) :: member_its)
    | [], [] -> 
       return []
    | ((id, mv) :: fields), ((smember, sbt) :: spec) ->
       Debug_ocaml.error "mismatch in fields in infer_struct"
    | [], ((member, _) :: _) ->
       fail (fun _ -> {loc; msg = Generic (!^"field" ^/^ Id.pp member ^^^ !^"missing")})
    | ((member,_) :: _), [] ->
       fail (fun _ -> {loc; msg = Generic (!^"supplying unexpected field" ^^^ Id.pp member)})
  in
  let@ member_its = check member_values (Memory.member_types layout) in
  return (IT.struct_ (tag, member_its))

and check_union (loc : loc) (tag : Sym.t) (id : Id.t) 
                (mv : mem_value) : (lvt) m =
  Debug_ocaml.error "todo: union types"

let rec check_object_value (loc : loc) ~(expect: BT.t)
          (ov : 'bty mu_object_value) : (lvt) m =
  match ov with
  | M_OVinteger iv ->
     let@ () = WellTyped.ensure_base_type loc ~expect Integer in
     return (z_ (Memory.z_of_ival iv))
  | M_OVpointer p -> 
     check_ptrval loc ~expect p
  | M_OVarray items ->
     let@ index_bt, item_bt = match expect with
       | BT.Map (index_bt, item_bt) -> return (index_bt, item_bt)
       | _ -> 
          let msg = Mismatch {has = !^"Array"; expect = BT.pp expect} in
          fail (fun _ -> {loc; msg})
     in
     assert (BT.equal index_bt Integer);
     let@ values = ListM.mapM (check_object_value loc ~expect:item_bt) items in
     return (make_array_ ~item_bt values)
  | M_OVstruct (tag, fields) -> 
     let mvals = List.map (fun (member,_,mv) -> (member, mv)) fields in
     check_struct loc tag mvals       
  | M_OVunion (tag, id, mv) -> 
     check_union loc tag id mv
  | M_OVfloating iv ->
     unsupported loc !^"floats"

(* and check_loaded_value loc ~expect (M_LVspecified ov) = *)
(*   check_object_value loc ~expect ov *)






let rec check_value (loc : loc) ~(expect:BT.t) (v : 'bty mu_value) : (lvt) m = 
  match v with
  | M_Vobject ov ->
     check_object_value loc ~expect ov
  | M_Vctype ct ->
     let@ () = WellTyped.ensure_base_type loc ~expect CType in
     let@ ct = match Sctypes.of_ctype ct with
       | Some ct -> return ct
       | None -> fail (fun _ -> {loc; msg = Generic (!^ "unsupported ctype:" ^^^
            Cerb_frontend.Pp_core_ctype.pp_ctype ct)})
     in
     return (IT.const_ctype_ ct)
  (* | M_Vloaded lv -> *)
  (*    check_loaded_value loc ~expect lv *)
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
     (* check it is a valid function address *)
     let@ _ = get_fun_decl loc sym in
     return (IT.sym_ (sym, Loc))
  | M_Vlist (item_bt, vals) ->
     let@ () = WellTyped.WBT.is_bt loc item_bt in
     let@ () = WellTyped.ensure_base_type loc ~expect (List item_bt) in
     let@ values = ListM.mapM (check_value loc ~expect:item_bt) vals in
     return (list_ ~item_bt values)
  | M_Vtuple vals ->
     let@ item_bts = match expect with
       | Tuple bts -> 
          let expect_nr = List.length bts in
          let has_nr = List.length vals in
          let@ () = WellTyped.ensure_same_argument_number loc `General 
                      has_nr ~expect:expect_nr in
          return bts
       | _ -> 
          let msg = Mismatch {has = !^"tuple"; expect = BT.pp expect} in
          fail (fun _ -> {loc; msg})
     in
     let@ values = ListM.map2M (fun v expect -> check_value loc ~expect v) vals item_bts in
     return (tuple_ values)




(*** pure expression inference ************************************************)


let warn_uf loc operation = 
  let msg = 
    !^"This expression includes non-linear integer arithmetic." ^^^
    !^"Generating uninterpreted-function constraint:" ^^^
    squotes (!^operation)
  in
  Pp.warn loc msg



let wrapI loc ity arg =
  (* try to follow wrapI from runtime/libcore/std.core *)
  let maxInt = Memory.max_integer_type ity in
  let minInt = Memory.min_integer_type ity in
  let dlt = Z.add (Z.sub maxInt minInt) (Z.of_int 1) in
  let r = rem_f_ (arg, z_ dlt) in
  ite_ (le_ (r, z_ maxInt), r, sub_ (r, z_ dlt))


(* try to follow is_representable_integer from runtime/libcore/std.core *)
let is_representable_integer arg ity = 
  let maxInt = Memory.max_integer_type ity in
  let minInt = Memory.min_integer_type ity in
  and_ [le_ (z_ minInt, arg); le_ (arg, z_ maxInt)]


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

let is_fun_addr global t = match IT.is_sym t with
  | Some (s, _) -> if SymMap.mem s global.Global.fun_decls
      then Some s else None
  | _ -> None



let check_single_ct loc expr =
  let@ pointer = WellTyped.WIT.check loc BT.CType expr in
  let@ known = eq_value_with IT.is_const expr in
  match known with
  | Some (_, (IT.CType_const ct, _)) -> return ct
  | Some _ -> assert false (* should be impossible given the type *)
  | None ->
    (* backup strategy, try to figure out the single value *)
    let@ m = model_with loc (IT.bool_ false) in
    let fail2 = (fun msg -> fail (fun _ -> {loc; msg = Generic (!^ "no known value for ctype:"
        ^^^ (!^ msg))})) in
    let@ m = match m with
      | None -> fail2 "cannot get model"
      | Some m -> return m
    in
    let@ g = get_global () in
    let@ y = match Solver.eval g (fst m) expr with
      | None -> fail2 "cannot eval term"
      | Some y -> return y
    in
    let@ ct = match IT.is_const y with
      | Some (IT.CType_const ct, _) -> return ct
      | _ -> fail2 "cannot eval to constant term"
    in
    let eq = IT.eq_ (expr, y) in
    let@ provable = provable loc in
    begin match provable (t_ eq) with
      | `True ->
        let@ () = add_c (t_ eq) in
        return ct
       | `False ->
        (* TODO: this is the most likely case, give a better error *)
        fail2 "cannot prove type is constant"
    end


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
 
let check_conv_int loc ~expect (ct : Sctypes.ctype) arg =
  let@ () = WellTyped.ensure_base_type loc ~expect Integer in 
  let@ () = WellTyped.WCT.is_ct loc ct in
  (* let@ arg = check_pexpr ~expect:Integer pe in *)
  (* try to follow conv_int from runtime/libcore/std.core *)
  let ity = match ct with
    | Integer ity -> ity
    | _ -> Debug_ocaml.error "conv_int applied to non-integer type"
  in
  let@ provable = provable loc in
  let fail_unrepresentable () = 
    let@ model = model () in
    fail (fun ctxt ->
        let msg = Int_unrepresentable 
                    {value = arg; ict = ct; ctxt; model} in
        {loc; msg}
      )
  in
  let@ value = match ity with
    | Bool ->
       return (ite_ (eq_ (arg, int_ 0), int_ 0, int_ 1))
    | _ when Sctypes.is_unsigned_integer_type ity ->
       let representable = representable_ (ct, arg) in
       (* TODO: revisit this *)
       begin match provable (t_ representable) with
       | `True -> return arg
       | `False ->
          return (ite_ (representable, arg, wrapI loc ity arg))
       end
    | _ ->
       begin match provable (t_ (representable_ (ct, arg))) with
       | `True -> return arg
       | `False -> fail_unrepresentable ()
       end
  in
  return value

let check_array_shift loc ~expect vt1 (loc_ct, ct) vt2 =
  let@ () = WellTyped.ensure_base_type loc ~expect Loc in
  let@ () = WellTyped.WCT.is_ct loc_ct ct in
  return (arrayShift_ (vt1, ct, vt2))


(* could potentially return a vt instead of an RT.t *)
let rec check_pexpr (pe : 'bty mu_pexpr) ~(expect:BT.t) 
        (k : lvt -> (unit) m) : (unit) m =
  let (M_Pexpr (loc, _, _, pe_)) = pe in
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
  (* | M_PEimpl i -> *)
  (*    let@ global = get_global () in *)
  (*    let value = Global.get_impl_constant global i in *)
  (*    return {loc; value} *)
  | M_PEval v ->
     let@ vt = check_value loc ~expect v in
     k vt
  | M_PEconstrained _ ->
     Debug_ocaml.error "todo: PEconstrained"
  | M_PEctor (ctor, pes) ->
     begin match ctor, pes with
     | M_Ctuple, _ -> 
        let@ item_bts = match expect with
          | Tuple bts -> 
             let expect_nr = List.length bts in
             let has_nr = List.length pes in
             let@ () = WellTyped.ensure_same_argument_number loc `General 
                         has_nr ~expect:expect_nr in
             return bts
          | _ -> 
             let msg = Mismatch {has = !^"tuple"; expect = BT.pp expect} in
             fail (fun _ -> {loc; msg})
        in
        check_pexprs (List.combine pes item_bts) (fun values ->
        k (tuple_ values))
     | M_Carray, _ -> 
        let@ item_bt = match expect with
          | Map (index_bt, item_bt) -> return item_bt
          | _ -> 
             let msg = Mismatch {has = !^"array"; expect = BT.pp expect} in
             fail (fun _ -> {loc; msg})
        in
        assert (BT.equal item_bt Integer);
        check_pexprs (List.map (fun pe -> (pe, item_bt)) pes) (fun values ->
        k (make_array_ ~item_bt values))
     | M_Cnil item_bt, [] -> 
        let@ () = WellTyped.WBT.is_bt loc item_bt in
        let@ () = WellTyped.ensure_base_type loc ~expect (List item_bt) in
        k (nil_ ~item_bt)
     | M_Cnil item_bt, _ -> 
        fail (fun _ -> {loc; msg = Number_arguments {has = List.length pes; expect=0}})
     | M_Ccons, [pe1; pe2] -> 
        let@ item_bt = match expect with
          | List item_bt -> return item_bt
          | _ -> 
             let msg = Mismatch {has = !^"list"; expect = BT.pp expect} in
             fail (fun _ -> {loc; msg})
        in
        check_pexpr ~expect:item_bt pe1 (fun vt1 ->
        check_pexpr ~expect pe2 (fun vt2 ->
        k (cons_ (vt1, vt2))))
     | M_Ccons, _ ->
        fail (fun _ -> {loc; msg = Number_arguments {has = List.length pes; expect = 2}})
     end
  | M_CivCOMPL _ ->
     Debug_ocaml.error "todo: CivCOMPL"
  | M_CivAND _ ->
     Debug_ocaml.error "todo: CivAND"
  | M_CivOR _ ->
     Debug_ocaml.error "todo: CivOR"
  | M_CivXOR (act, pe1, pe2) -> 
     let@ () = WellTyped.ensure_base_type loc ~expect Integer in
     let _ity = match act.ct with
       | Integer ity -> ity
       | _ -> Debug_ocaml.error "M_CivXOR with non-integer c-type"
     in
     check_pexpr ~expect:Integer pe1 (fun vt1 ->
     check_pexpr ~expect:Integer pe2 (fun vt2 ->
     let value = warn_uf loc "xor_uf"; xor_no_smt_ (vt1, vt2) in
     k value))
  | M_Cfvfromint _ -> 
     unsupported loc !^"floats"
  | M_Civfromfloat (act, _) -> 
     let@ () = WellTyped.WCT.is_ct act.loc act.ct in
     unsupported loc !^"floats"
  | M_PEarray_shift (pe1, ct, pe2) ->
     let@ () = WellTyped.ensure_base_type loc ~expect Loc in
     check_pexpr ~expect:BT.Loc pe1 (fun vt1 ->
     check_pexpr ~expect:Integer pe2 (fun vt2 ->
     let@ vt = check_array_shift loc ~expect vt1 (loc, ct) vt2 in
     k vt))
  | M_PEmember_shift (pe, tag, member) ->
     let@ () = WellTyped.ensure_base_type loc ~expect Loc in
     check_pexpr ~expect:Loc pe (fun vt ->
     let@ layout = get_struct_decl loc tag in
     let@ _member_bt = get_member_type loc tag member layout in
     k (memberShift_ (vt, tag, member)))
  | M_PEnot pe ->
     let@ () = WellTyped.ensure_base_type loc ~expect Bool in
     check_pexpr ~expect:Bool pe (fun vt ->
     k (not_ vt))
  | M_PEop (op, pe1, pe2) ->
     let check_args_and_ret abt1 abt2 rbt k' = 
       check_pexpr ~expect:abt1 pe1 (fun v1 ->
       check_pexpr ~expect:abt2 pe2 (fun v2 ->
       let@ () = WellTyped.ensure_base_type loc ~expect rbt in
       k' (v1, v2)))
     in
     begin match op with
     | OpAdd -> 
        check_args_and_ret Integer Integer Integer (fun (v1, v2) ->
        k (add_ (v1, v2)))
     | OpSub ->
        check_args_and_ret Integer Integer Integer (fun (v1, v2) ->
        k (sub_ (v1, v2)))
     | OpMul ->
        check_args_and_ret Integer Integer Integer (fun (v1, v2) ->
        k (if (is_z_ v1 || is_z_ v2) then mul_ (v1, v2) 
           else (warn_uf loc "mul_uf"; mul_no_smt_ (v1, v2))))
     | OpDiv ->
        check_args_and_ret Integer Integer Integer (fun (v1, v2) ->
        k (if is_z_ v2 then div_ (v1, v2) 
           else (warn_uf loc "div_uf"; div_no_smt_ (v1, v2))))
     | OpRem_f ->
        check_args_and_ret Integer Integer Integer (fun (v1, v2) ->
        k (if is_z_ v2 then rem_ (v1, v2) 
           else (warn_uf loc "rem_uf"; rem_no_smt_ (v1, v2))))
     | OpRem_t ->
        check_args_and_ret Integer Integer Integer (fun (v1, v2) ->
        let@ provable = provable loc in
        begin match provable (LC.T (and_ [le_ (int_ 0, v1); le_ (int_ 0, v2)])) with
        | `True ->
           (* If the arguments are non-negative, then rem or mod should be sound to use for rem_t *)
           (* If not it throws a type error, but we should instead
              map that to an uninterpreted function eventually. *)
           k (if (is_z_ v2) then IT.mod_ (v1, v2) 
              else (warn_uf loc "mod_uf"; IT.mod_no_smt_ (v1, v2)))
        | `False ->
           let@ model = model () in
           let err = !^"Unsupported: rem_t applied to negative arguments" in
           fail (fun ctxt ->
               let msg = Generic_with_model {err; model; ctxt} in
               {loc; msg}
             )
        end)
     | OpExp ->
        check_args_and_ret Integer Integer Integer (fun (v1, v2) ->
        begin match is_z v1, is_z v2 with
        | Some z, Some z' ->
           let it = exp_ (v1, v2) in
           if Z.lt z' Z.zero then
             (* we should relax this and map to exp_no_smt_ if we
                can handle negative exponents there *)
             fail (fun ctxt -> {loc; msg = NegativeExponent {it; ctxt}})
           else if Z.fits_int32 z' then
             k it
           else 
             (* we can probably just relax this and map to exp_no_smt_ *)
             fail (fun ctxt -> {loc; msg = TooBigExponent {it; ctxt}})
        | _ ->
           k (warn_uf loc "power_uf"; exp_no_smt_ (v1, v2))
        end)
     | OpEq ->
        (* eventually we have to also support floats here *)
        check_args_and_ret Integer Integer Bool (fun (v1, v2) ->
        k (eq_ (v1, v2)))
     | OpGt ->
        (* eventually we have to also support floats here *)
        check_args_and_ret Integer Integer Bool (fun (v1, v2) ->
        k (gt_ (v1, v2)))
     | OpLt ->
        check_args_and_ret Integer Integer Bool (fun (v1, v2) ->
        k (lt_ (v1, v2)))
     | OpGe ->
        check_args_and_ret Integer Integer Bool (fun (v1, v2) ->
        k (ge_ (v1, v2)))
     | OpLe -> 
        check_args_and_ret Integer Integer Bool (fun (v1, v2) ->
        k (le_ (v1, v2)))
     | OpAnd ->
        check_args_and_ret Bool Bool Bool (fun (v1, v2) ->
        k (and_ [v1; v2]))
     | OpOr -> 
        check_args_and_ret Bool Bool Bool (fun (v1, v2) ->
        k (or_ [v1; v2]))
     end
  | M_PEapply_fun (fun_id, args) ->
     let expect_args = Mucore.mu_fun_param_types fun_id in
     let@ () = if List.length expect_args = List.length args then return ()
       else fail (fun _ -> {loc; msg = Number_arguments {has = List.length args;
                expect = List.length expect_args}}) in
     check_pexprs (List.combine args expect_args) (fun args ->
     let@ args = ListM.mapM (prefer_value_with IT.is_const_val) args in
     match Mucore.evaluate_fun fun_id args with
     | Some t -> k t
     | None -> fail (fun _ -> {loc; msg = Generic (!^ "cannot evaluate function:" ^^^
           Pp.c_app (Mucore.pp_function fun_id) (List.map IT.pp args))})
     )
  | M_PEstruct (tag, xs) ->
     let@ layout = get_struct_decl loc tag in
     let@ xs_with_expects = ListM.mapM (fun (nm, expr) ->
       let@ ty = get_member_type loc tag nm layout in
       return (expr, BT.of_sct ty)) xs in
     check_pexprs xs_with_expects (fun vs ->
     let v = struct_ (tag, List.map2 (fun (nm, _) v -> (nm, v)) xs vs) in
     k v)
  | M_PEunion _ ->
     Debug_ocaml.error "todo: PEunion"
  | M_PEcfunction pe2 ->
     check_pexpr ~expect:Loc pe2 (fun ptr ->
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
         let@ () = add_c (t_ cond) in
         Pp.debug 5 (lazy (Pp.item "checking consistency of eq branch" (IT.pp cond)));
         let@ provable = provable loc in
         match provable (t_ (bool_ false)) with
         | `True -> return ()
         | `False -> check_pexpr ~expect e k
       in
       let@ () = pure (aux pe (eq_ (ptr, eq_opt))) in
       let@ () = pure (aux pe (not_ (eq_ (ptr, eq_opt)))) in
       return ()
    end
  )
  | M_PEmemberof _ ->
     Debug_ocaml.error "todo: M_PEmemberof"
  | M_PEbool_to_integer pe ->
     let@ () = WellTyped.ensure_base_type loc ~expect Integer in
     check_pexpr ~expect:Bool pe (fun arg ->
     k (ite_ (arg, int_ 1, int_ 0)))
  | M_PEconv_int (ct_expr, pe)
  | M_PEconv_loaded_int (ct_expr, pe) ->
     check_pexpr ~expect:BT.CType ct_expr (fun ct_it ->
     let@ ct = check_single_ct loc ct_it in
     check_pexpr ~expect:Integer pe (fun lvt ->
     let@ vt = check_conv_int loc ~expect ct lvt in
     k vt))
  | M_PEwrapI (act, pe) ->
     let@ () = WellTyped.ensure_base_type loc ~expect Integer in
     check_pexpr ~expect:Integer pe (fun arg ->
     let ity = Option.get (Sctypes.is_integer_type act.ct) in
     k (wrapI loc ity arg))
  | M_PEcatch_exceptional_condition (act, pe) ->
     let@ () = WellTyped.ensure_base_type loc ~expect Integer in
     let ity = Option.get (Sctypes.is_integer_type act.ct) in
     check_pexpr ~expect:Integer pe (fun arg ->
         let@ provable = provable loc in
         match provable (t_ (is_representable_integer arg ity)) with
         | `True -> (k arg)
         | `False -> 
            let@ model = model () in
            let ub = CF.Undefined.UB036_exceptional_condition in
            fail (fun ctxt -> {loc; msg = Undefined_behaviour {ub; ctxt; model}})
     )
  | M_PEis_representable_integer (pe, act) ->
     let@ () = WellTyped.ensure_base_type loc ~expect Bool in
     let ity = Option.get (Sctypes.is_integer_type act.ct) in
     check_pexpr ~expect:Integer pe (fun arg ->
         k (is_representable_integer arg ity)
       )
  | M_PEif (pe, e1, e2) ->
     check_pexpr ~expect:Bool pe (fun c ->
     let aux e cond = 
       let@ () = add_c (t_ cond) in
       Pp.debug 5 (lazy (Pp.item "checking consistency of if-branch" (IT.pp cond)));
       let@ provable = provable loc in
       match provable (t_ (bool_ false)) with
       | `True -> return ()
       | `False -> check_pexpr ~expect e k
     in
     let@ () = pure (aux e1 c) in
     let@ () = pure (aux e2 (not_ c)) in
     return ())
  | M_PElet (M_Pat p, e1, e2) ->
     let@ fin = begin_trace_of_pure_step (Some (Mu.M_Pat p)) e1 in
     let@ p_bt = infer_pattern p in
     check_pexpr ~expect:p_bt e1 (fun v1 ->
     let@ bound_a = pattern_match p v1 in
     let@ () = fin () in
     check_pexpr ~expect e2 (fun lvt ->
     let@ () = remove_as bound_a in
     k lvt))
  (* | M_PEdone pe -> *)
  (*    let@ arg = infer_pexpr pe in *)
  (*    Spine.subtype loc arg typ *)
  | M_PEundef (_loc, ub) ->
     let@ provable = provable loc in
     begin match provable (t_ (bool_ false)) with
     | `True -> return ()
     | `False ->
        let@ model = model () in
        fail (fun ctxt -> {loc; msg = Undefined_behaviour {ub; ctxt; model}})
     end
  | M_PEerror (err, pe) ->
     let@ provable = provable loc in
     begin match provable (t_ (bool_ false)) with
     | `True -> return ()
     | `False ->
        let@ model = model () in
        fail (fun ctxt -> {loc; msg = StaticError {err; ctxt; model}})
     end


and check_pexprs (pes_expects : (_ mu_pexpr * BT.t) list)
(k : lvt list -> (unit) m) : (unit) m =
  match pes_expects with
  | [] -> k []
  | (pe, expect) :: pes_expects ->
     check_pexpr pe ~expect (fun lvt ->
     check_pexprs pes_expects (fun lvts ->
     k (lvt :: lvts)))






module Spine : sig

  val calltype_ft : 
    Loc.t -> fsym:Sym.t -> _ mu_pexpr list -> AT.ft -> (RT.t -> (unit) m) -> (unit) m
  val calltype_lt : 
    Loc.t -> _ mu_pexpr list -> AT.lt * label_kind -> (False.t -> (unit) m) -> (unit) m
  val calltype_lemma :
    Loc.t -> lemma:Sym.t -> (Loc.t * IT.t) list -> AT.lemmat -> (LRT.t -> unit m) -> unit m
  val calltype_packing : 
    Loc.t -> Sym.t -> LAT.packing_ft -> (IT.t -> (unit) m) -> (unit) m
  val subtype : 
    Loc.t -> LRT.t -> (unit -> (unit) m) -> (unit) m
end = struct


  let spine_l rt_subst rt_pp loc (situation : call_situation) ftyp k = 

    let start_spine = time_log_start "spine_l" "" in

    (* record the resources now, so errors are raised with all
       the resources present, rather than those that remain after some
       arguments are claimed *)
    let@ original_resources = all_resources_tagged () in

    let@ () =
      time_f_logs loc 9 "pre_inf_eqs"
        (InferenceEqs.add_eqs_for_infer loc) ftyp
    in

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


  let calltype_ft loc ~fsym args (ftyp : AT.ft) k =
    spine check_pexpr RT.subst RT.pp loc (FunctionCall fsym) args ftyp k


  let calltype_lt loc args ((ltyp : AT.lt), label_kind) k =
    spine check_pexpr False.subst False.pp 
      loc (LabelCall label_kind) args ltyp k

  let calltype_lemma loc ~lemma args lemma_typ k =
    let check_it_arg (loc, it_arg) ~(expect:LS.t) k =
      let@ it_arg = WellTyped.WIT.check loc expect it_arg in
      k it_arg
    in
    spine check_it_arg LRT.subst LRT.pp
      loc (LemmaApplication lemma) args lemma_typ k

  let calltype_packing loc (name : Sym.t) (ft : LAT.packing_ft) k =
    spine_l IT.subst IT.pp 
      loc (PackPredicate name) ft k

  (* The "subtyping" judgment needs the same resource/lvar/constraint
     inference as the spine judgment. So implement the subtyping
     judgment 'arg <: LRT' by type checking 'f()' for 'f: LRT -> False'. *)
  let subtype (loc : loc) (rtyp : LRT.t) k =
    let lft = LAT.of_lrt rtyp (LAT.I False.False) in
    spine_l False.subst False.pp loc Subtyping lft (fun False.False ->
    k ())


end




(*** impure expression inference **********************************************)



(* `t` is used for the type of Run/Goto: Goto has no return type
   (because the control flow does not return there), but instead
   returns `False`. Type inference of impure expressions returns
   either a return type and a typing context or `False` *)
type 'a orFalse = 
  | Normal of 'a
  | False

(* let pp_or_false (ppf : 'a -> Pp.document) (m : 'a orFalse) : Pp.document =  *)
(*   match m with *)
(*   | Normal a -> ppf a *)
(*   | False -> parens !^"no return" *)


let filter_empty_resources loc =
  let@ provable = provable loc in
  map_and_fold_resources loc (fun resource xs ->
      let constr = match resource with
        | (P p, _) -> t_ (not_ p.permission)
        | (Q p, _) -> forall_ (p.q, BT.Integer) (not_ p.permission)
      in
      match provable constr with
      | `True -> (Deleted, xs)
      | `False ->
        let model = Solver.model () in
        (Unchanged, ((resource, constr, model) :: xs))
  ) []

let all_empty loc original_resources =
  let@ remaining_resources = filter_empty_resources loc in
  (* there will be a model available if at least one resource persisted *)
  let@ provable = provable loc in
  let@ global = get_global () in
  let@ () = ListM.iterM (fun (resource, _, model) ->
      match Spans.null_resource_check (fst model) global (RE.request resource) with
        | None -> return ()
        | Some (pt, ok) ->
          let uiinfo = (Access Free, (Some (RET.P pt), None)) in
          begin match provable (t_ ok) with
            | `True ->
              debug 6 (lazy (Pp.item "remaining resource null, trying to unpack"
                  (RET.pp_predicate_type pt)));
              let@ _ = ResourceInference.General.do_unpack loc uiinfo pt in
              return ()
            | `False -> return ()
          end
  ) remaining_resources in
  let@ remaining_resources = filter_empty_resources loc in
  match remaining_resources with
    | [] -> return ()
    | ((resource, constr, model) :: _) ->
         let@ global = get_global () in
         let@ simp_ctxt = simp_ctxt () in
         RI.debug_constraint_failure_diagnostics 6 model global simp_ctxt constr;
         fail_with_trace (fun trace -> fun ctxt ->
             let ctxt = { ctxt with resources = original_resources } in
             {loc; msg = Unused_resource {resource; ctxt; model; trace}})


(*type labels = (AT.lt * label_kind) SymMap.t*)


let load loc pointer ct =
  let@ (point, O value) = 
    (RI.Special.predicate_request ~recursive:true loc (Access (Load None)) ({ 
           name = Owned ct;
           pointer = pointer;
           permission = bool_ true;
           iargs = [];
         }, None))
  in
  let@ () = add_r (P point, O value) in
  return value


let instantiate loc filter arg =
  let arg_s = Sym.fresh_make_uniq "instance" in
  let arg_it = sym_ (arg_s, IT.bt arg) in
  let@ () = add_l arg_s (IT.bt arg_it) (loc, lazy (Sym.pp arg_s)) in
  let@ () = add_c (LC.t_ (eq__ arg_it arg)) in
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
  add_cs extra_assumptions




let rec check_expr labels ~(typ:BT.t orFalse) (e : 'bty mu_expr) 
      (k: lvt -> (unit) m)
    : (unit) m =
  let (M_Expr (loc, _annots, e_)) = e in
  let@ () = add_loc_trace loc in
  let@ locs = get_loc_trace () in
  let@ () = print_with_ctxt (fun ctxt ->
       debug 3 (lazy (action "inferring expression"));
       debug 3 (lazy (item "expr" (group (Pp_mucore.pp_expr e))));
       debug 3 (lazy (item "ctxt" (Context.pp ctxt)));
    )
  in
  match typ, e_ with
  | Normal expect, M_Epure pe -> 
     check_pexpr ~expect pe (fun lvt ->
     k lvt)
  | Normal expect, M_Ememop memop ->
     let pointer_op op pe1 pe2 = 
       check_pexpr ~expect:Loc pe1 (fun arg1 ->
       check_pexpr ~expect:Loc pe2 (fun arg2 ->
       let lvt = op (arg1, arg2) in
       let@ () = WellTyped.ensure_base_type loc ~expect (IT.bt lvt) in
       k lvt))
     in
     begin match memop with
     | M_PtrEq (asym1, asym2) -> 
        pointer_op eq_ asym1 asym2
     | M_PtrNe (asym1, asym2) -> 
        pointer_op ne_ asym1 asym2
     | M_PtrLt (asym1, asym2) -> 
        pointer_op ltPointer_ asym1 asym2
     | M_PtrGt (asym1, asym2) -> 
        pointer_op gtPointer_ asym1 asym2
     | M_PtrLe (asym1, asym2) -> 
        pointer_op lePointer_ asym1 asym2
     | M_PtrGe (asym1, asym2) -> 
        pointer_op gePointer_ asym1 asym2
     | M_Ptrdiff (act, pe1, pe2) -> 
        let@ () = WellTyped.WCT.is_ct act.loc act.ct in
        check_pexpr ~expect:Loc pe1 (fun arg1 ->
        check_pexpr ~expect:Loc pe2 (fun arg2 ->
        (* copying and adapting from memory/concrete/impl_mem.ml *)
        let divisor = match act.ct with
          | Array (item_ty, _) -> Memory.size_of_ctype item_ty
          | ct -> Memory.size_of_ctype ct
        in
        let value =
          div_
            (sub_ (pointerToIntegerCast_ arg1,
                   pointerToIntegerCast_ arg2),
             int_ divisor)
        in
        k value))
     | M_IntFromPtr (act_from, act_to, pe) ->
        let@ () = WellTyped.ensure_base_type loc ~expect Integer in
        let@ () = WellTyped.WCT.is_ct act_from.loc act_from.ct in
        let@ () = WellTyped.WCT.is_ct act_to.loc act_to.ct in
        check_pexpr ~expect:Loc pe (fun arg ->
        let value = pointerToIntegerCast_ arg in
        let@ () = 
          (* after discussing with Kavyan *)
          let@ provable = provable loc in
          let lc = t_ (representable_ (act_to.ct, value)) in
          begin match provable lc with
          | `True -> return () 
          | `False ->
             let@ model = model () in
             fail (fun ctxt ->
                 let ict = act_to.ct in
                 {loc; msg = Int_unrepresentable {value = arg; ict; ctxt; model}}
               )
          end
        in
        k value)
     | M_PtrFromInt (act_from, act2_to, pe) ->
        let@ () = WellTyped.ensure_base_type loc ~expect Loc in
        let@ () = WellTyped.WCT.is_ct act_from.loc act_from.ct in
        let@ () = WellTyped.WCT.is_ct act2_to.loc act2_to.ct in
        check_pexpr ~expect:Integer pe (fun arg ->
        let value = integerToPointerCast_ arg in
        k value)
     | M_PtrValidForDeref (act, pe) ->
        let@ () = WellTyped.ensure_base_type loc ~expect Bool in
        (* check *)
        let@ () = WellTyped.WCT.is_ct act.loc act.ct in
        check_pexpr ~expect:Loc pe (fun arg ->
        let value = aligned_ (arg, act.ct) in
        k value)
     | M_PtrWellAligned (act, pe) ->
        let@ () = WellTyped.ensure_base_type loc ~expect Bool in
        let@ () = WellTyped.WCT.is_ct act.loc act.ct in
        check_pexpr ~expect:Loc pe (fun arg ->
        let value = aligned_ (arg, act.ct) in
        k value)
     | M_PtrArrayShift (pe1, act, pe2) ->
        check_pexpr ~expect:BT.Loc pe1 (fun vt1 ->
        check_pexpr ~expect:Integer pe2 (fun vt2 ->
        let@ lvt = check_array_shift loc ~expect vt1 (act.loc, act.ct) vt2 in
        k lvt))
     | M_Memcpy _ (* (asym 'bty * asym 'bty * asym 'bty) *) ->
        Debug_ocaml.error "todo: M_Memcpy"
     | M_Memcmp _ (* (asym 'bty * asym 'bty * asym 'bty) *) ->
        Debug_ocaml.error "todo: M_Memcmp"
     | M_Realloc _ (* (asym 'bty * asym 'bty * asym 'bty) *) ->
        Debug_ocaml.error "todo: M_Realloc"
     | M_Va_start _ (* (asym 'bty * asym 'bty) *) ->
        Debug_ocaml.error "todo: M_Va_start"
     | M_Va_copy _ (* (asym 'bty) *) ->
        Debug_ocaml.error "todo: M_Va_copy"
     | M_Va_arg _ (* (asym 'bty * actype 'bty) *) ->
        Debug_ocaml.error "todo: M_Va_arg"
     | M_Va_end _ (* (asym 'bty) *) ->
        Debug_ocaml.error "todo: M_Va_end"
     end
  | Normal expect, M_Eaction (M_Paction (_pol, M_Action (aloc, action_))) ->
     begin match action_ with
     | M_Create (pe, act, prefix) -> 
        let@ () = WellTyped.ensure_base_type loc ~expect Loc in
        let@ () = WellTyped.WCT.is_ct act.loc act.ct in
        check_pexpr ~expect:Integer pe (fun arg ->
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
        let@ () = add_c (t_ (representable_ (Pointer act.ct, ret))) in
        let@ () = add_c (t_ (alignedI_ ~align:arg ~t:ret)) in
        let@ () = 
          add_r
            (P { name = Block act.ct; 
                 pointer = ret;
                 permission = bool_ true;
                 iargs = [];
               }, 
             O unit_)
        in
        k ret)
     | M_CreateReadOnly (sym1, ct, sym2, _prefix) -> 
        Debug_ocaml.error "todo: CreateReadOnly"
     | M_Alloc (ct, sym, _prefix) -> 
        Debug_ocaml.error "todo: Alloc"
     | M_Kill (M_Dynamic, asym) -> 
        Debug_ocaml.error "todo: Free"
     | M_Kill (M_Static ct, pe) -> 
        let@ () = WellTyped.ensure_base_type loc ~expect Unit in
        let@ () = WellTyped.WCT.is_ct loc ct in
        check_pexpr ~expect:Loc pe (fun arg ->
        let@ _ = 
          RI.Special.predicate_request ~recursive:true loc (Access Kill) ({
            name = Block ct;
            pointer = arg;
            permission = bool_ true;
            iargs = [];
          }, None)
        in
        k unit_)
     | M_Store (_is_locking, act, p_pe, v_pe, mo) -> 
        let@ () = WellTyped.ensure_base_type loc ~expect Unit in
        let@ () = WellTyped.WCT.is_ct act.loc act.ct in
        check_pexpr ~expect:Loc p_pe (fun parg ->
        check_pexpr ~expect:(BT.of_sct act.ct) v_pe (fun varg ->
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
          RI.Special.predicate_request ~recursive:true loc (Access (Store None)) ({
              name = Block act.ct; 
              pointer = parg;
              permission = bool_ true;
              iargs = [];
            }, None)
        in
        let@ () = 
          add_r
            (P { name = Owned act.ct;
                 pointer = parg;
                 permission = bool_ true;
                 iargs = [];
               },
             O varg)
        in
        k unit_))
     | M_Load (act, p_pe, _mo) -> 
        let@ () = WellTyped.WCT.is_ct act.loc act.ct in
        let@ () = WellTyped.ensure_base_type loc ~expect (BT.of_sct act.ct) in
        check_pexpr ~expect:Loc p_pe (fun pointer ->
        let@ value = load loc pointer act.ct in
        k value)
     | M_RMW (ct, sym1, sym2, sym3, mo1, mo2) -> 
        Debug_ocaml.error "todo: RMW"
     | M_Fence mo -> 
        Debug_ocaml.error "todo: Fence"
     | M_CompareExchangeStrong (ct, sym1, sym2, sym3, mo1, mo2) -> 
        Debug_ocaml.error "todo: CompareExchangeStrong"
     | M_CompareExchangeWeak (ct, sym1, sym2, sym3, mo1, mo2) -> 
        Debug_ocaml.error "todo: CompareExchangeWeak"
     | M_LinuxFence mo -> 
        Debug_ocaml.error "todo: LinuxFemce"
     | M_LinuxLoad (ct, sym1, mo) -> 
        Debug_ocaml.error "todo: LinuxLoad"
     | M_LinuxStore (ct, sym1, sym2, mo) -> 
        Debug_ocaml.error "todo: LinuxStore"
     | M_LinuxRMW (ct, sym1, sym2, mo) -> 
        Debug_ocaml.error "todo: LinuxRMW"
     end
  | Normal expect, M_Eskip -> 
     let@ () = WellTyped.ensure_base_type loc ~expect Unit in
     k unit_
  | Normal expect, M_Eccall (act, f_pe, pes) ->
     (* todo: do anything with act? *)
     let@ () = WellTyped.WCT.is_ct act.loc act.ct in
     check_pexpr ~expect:Loc f_pe (fun f_it ->
     let@ global = get_global () in
     let@ known = eq_value_with (is_fun_addr global) f_it in
     let@ fsym = match known with
       | Some (_, sym) -> return sym
       | _ -> unsupported loc !^"function application of function pointers"
     in
     let@ (_loc, ft, _) = get_fun_decl loc fsym in

     Spine.calltype_ft loc ~fsym pes ft (fun (Computational ((_, bt), _, _) as rt) ->
     let@ () = WellTyped.ensure_base_type loc ~expect bt in
     let@ _, members = make_return_record loc (FunctionCall fsym) (RT.binders rt) in
     let@ lvt = bind_return loc members rt in
     k lvt))
  (* | M_Eproc (fname, pes) -> *)
  (*    let@ (_, decl_typ) = match fname with *)
  (*      | CF.Core.Impl impl ->  *)
  (*         let@ global = get_global () in *)
  (*         let ift = Global.get_impl_fun_decl global impl in *)
  (*         let ft = AT.map (fun value -> rt_of_lvt {loc = Loc.unknown; value}) ift in *)
  (*         return (loc, ft) *)
  (*      | CF.Core.Sym sym ->  *)
  (*         let@ (loc, fun_decl, _) = get_fun_decl loc sym in *)
  (*         return (loc, fun_decl) *)
  (*    in *)
  (*    let@ args = ListM.mapM infer_pexpr pes in *)
  (*    Spine.calltype_ft loc args decl_typ *)

  | _, M_Eif (c_pe, e1, e2) ->
     check_pexpr ~expect:Bool c_pe (fun carg ->
     let aux lc nm e = 
       let@ () = add_c (t_ lc) in
       let@ provable = provable loc in
       match provable (t_ (bool_ false)) with
       | `True -> return ()
       | `False -> check_expr labels ~typ e k
     in
     let@ () = pure (aux carg "true" e1) in
     let@ () = pure (aux (not_ carg) "false" e2) in
     return ())
  | _, M_Ebound e ->
     check_expr labels ~typ e k
  | _, M_End _ ->
     Debug_ocaml.error "todo: End"
  | _, M_Elet (M_Pat p, e1, e2) ->
     let@ fin = begin_trace_of_pure_step (Some (Mu.M_Pat p)) e1 in
     let@ p_bt = infer_pattern p in
     check_pexpr ~expect:p_bt e1 (fun v1 ->
     let@ bound_a = pattern_match p v1 in
     let@ () = fin () in
     check_expr labels ~typ e2 (fun rt ->
         let@ () = remove_as bound_a in
         k rt
     ))
  | Normal expect, M_Eunseq es ->
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
     let rec aux es_bts k = match es_bts with
       | [] -> k []
       | (e, bt) :: es_bts ->
          check_expr labels ~typ:(Normal bt) e (fun v ->
          aux es_bts (fun vs ->
          k (v :: vs)
          ))
     in
     aux (List.combine es item_bts) (fun vts ->
     let lvt = tuple_ vts in
     k lvt
     )
  | Normal expect, M_CN_progs (_, cn_progs) ->
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
               let@ pred = WRET.welltyped loc (P pt) in
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
                  add_r (P pt, O output)
                  )
               end
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
               let@ it = WIT.check loc Integer it in
               instantiate loc filter it
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
                  add_c (LC.t_ (eq_ (pred_ f args def.return_bt, body)))
               end
            | M_CN_apply (lemma, args) ->
               let@ (_loc, lemma_typ) = get_lemma loc lemma in
               let args = List.map (fun arg -> (loc, arg)) args in
               Spine.calltype_lemma loc ~lemma args lemma_typ (fun lrt ->
                   let@ _, members = make_return_record loc (LemmaApplication lemma) (LRT.binders lrt) in
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
                  fail_with_trace (fun trace ctxt ->
                      {loc; msg = Unproven_constraint {constr = lc; info = (loc, None); ctxt; model; trace}}
                    )
               end
          end
     in
     let@ () = ListM.iterM aux cn_progs in
     k unit_
     

  | _, M_Ewseq (p, e1, e2)
  | _, M_Esseq (p, e1, e2) ->
     let@ fin = begin_trace_of_step (Some (Mu.M_Pat p)) e1 in
     let@ p_bt = infer_pattern p in
     check_expr labels ~typ:(Normal p_bt) e1 (fun it ->
            let@ bound_a = pattern_match p it in
            let@ () = fin () in
            check_expr labels ~typ e2 (fun it2 ->
                let@ () = remove_as bound_a in
                k it2
              )
       )
  | _, M_Erun (label_sym, pes) ->
     let@ (lt,lkind) = match SymMap.find_opt label_sym labels with
       | None -> fail (fun _ -> {loc; msg = Generic (!^"undefined code label" ^/^ Sym.pp label_sym)})
       | Some (lt,lkind) -> return (lt,lkind)
     in
     let@ original_resources = all_resources_tagged () in
     Spine.calltype_lt loc pes (lt,lkind) (fun False ->
     let@ () = all_empty loc original_resources in
     return ())
  | False, _ ->
     let err = 
       "This expression returns but is expected "^
         "to have non-return type."
     in
     fail (fun _ -> {loc; msg = Generic !^err})



let check_expr_rt loc labels ~typ e = 
  let@ () = add_loc_trace loc in
  match typ with
  | Normal (RT.Computational ((return_s, return_bt), info, lrt)) ->
     check_expr labels ~typ:(Normal return_bt) e (fun returned_lvt ->
         let lrt = LRT.subst (IT.make_subst [(return_s, returned_lvt)]) lrt in
         let@ original_resources = all_resources_tagged () in
         Spine.subtype loc lrt (fun () ->
         let@ () = all_empty loc original_resources in
         return ())
       )
  | False ->
     check_expr labels ~typ:False e (fun _ -> assert false)





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
       let@ () = add_c (LC.t_ (def_ s it)) in
       aux_l resources args
    | M_Constraint (lc, info, args) ->
       let@ () = add_c lc in
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

     



(* check_procedure: type check an (impure) procedure *)
let check_procedure 
      (loc : loc) 
      (fsym : Sym.t)
      (args_and_body : 'bty mu_proc_args_and_body)
    : (unit) m =
  debug 2 (lazy (headline ("checking procedure " ^ Sym.pp_string fsym)));

  pure begin 

      let@ ((body, label_defs, rt), initial_resources) = bind_arguments loc args_and_body in

      let@ label_defs, label_context =
        PmapM.foldM (fun sym def (label_defs, label_context) ->
            let@ lt, def, kind =
              pure begin match def with
                | M_Return loc ->
                   return (AT.of_rt rt (LAT.I False.False), M_Return loc, Return)
                | M_Label (loc, label_args_and_body, annots, parsed_spec) ->
                   let@ label_args_and_body, lt = 
                     WellTyped.WLabel.welltyped loc label_args_and_body in
                   let kind = match CF.Annot.get_label_annot annots with
                     | Some (LAloop_body loop_id) -> Loop
                     | Some (LAloop_continue loop_id) -> Loop
                     | _ -> Other
                   in
                   return (lt, M_Label (loc, label_args_and_body, annots, parsed_spec), kind)
                end
            in
            debug 6 (lazy (!^"label type within function" ^^^ Sym.pp fsym));
            debug 6 (lazy (CF.Pp_ast.pp_doc_tree (AT.dtree False.dtree lt)));
            return ((sym, def) :: label_defs, SymMap.add sym (lt, kind) label_context)
          ) label_defs ([], SymMap.empty)
      in

      let@ () = 
        debug 2 (lazy (headline ("checking function body " ^ Sym.pp_string fsym)));
        pure begin
            let@ () = add_rs initial_resources in 
            check_expr_rt loc label_context ~typ:(Normal rt) body
          end 
      in
      let@ () = ListM.iterM (fun (lsym, def) ->
        pure begin match def with
          | M_Return loc ->
             return ()
          | M_Label (loc, label_args_and_body, annots, _) ->
             debug 2 (lazy (headline ("checking label " ^ Sym.pp_string lsym)));
             let@ (label_body, label_resources) = bind_arguments loc label_args_and_body in
             let@ () = add_rs label_resources in
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
       ListM.iterM (fun piece ->
           match piece.member_or_padding with
           | Some (name, ct) -> WellTyped.WCT.is_ct Loc.unknown ct
           | None -> return ()
         ) layout
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
        let@ def = WellTyped.WLFD.welltyped def in
        add_logical_function name def
      ) nonrecursive
  in

  (* Then we check the recursive functions: add them all, check
     welltypedness of each, then overwrite (post-NIA-simplification --
     a bit ugly). *)

  let@ () =
    ListM.iterM (fun (name, def) -> 
        add_logical_function name def
      ) recursive
  in
  ListM.iterM (fun (name, def) -> 
      let@ def = WellTyped.WLFD.welltyped def in
      add_logical_function name def
    ) recursive

let record_and_check_resource_predicates preds =
  let@ simp_preds = pure begin
    (* add the names to the context, so recursive preds check *)
    let@ () = ListM.iterM (fun (name, def) ->
        add_resource_predicate name { def with clauses = None }) preds in
    ListM.mapM (fun (name, def) ->
      let@ def = WellTyped.WRPD.welltyped def in
      return (name, def)) preds
  end in
  ListM.iterM (fun (name, def) ->
      (* add simplified def to the context *)
      add_resource_predicate name def
    ) simp_preds


let record_globals globs =
  (* TODO: check the expressions *)
  ListM.iterM (fun (sym, def) ->
      match def with
      | M_GlobalDef ((gbt, ct), _)
      | M_GlobalDecl ((gbt, ct)) ->
         let@ () = WellTyped.WBT.is_bt Loc.unknown gbt in
         let@ () = WellTyped.WCT.is_ct Loc.unknown ct in
         let bt = Loc in
         let info = (Loc.unknown, lazy (Pp.item "global" (Sym.pp sym))) in
         let@ () = add_a sym bt info in
         let@ () = add_c (t_ (IT.good_pointer ~pointee_ct:ct (sym_ (sym, bt)))) in
         return ()
    ) globs 


let wf_check_and_record_functions mu_funs mu_call_sigs =
  let add fsym loc ft =
    (* add to context *)
    (* let lc1 = t_ (ne_ (null_, sym_ (fsym, Loc))) in *)
    let lc2 = t_ (representable_ (Pointer Void, sym_ (fsym, Loc))) in
    let@ () = add_l fsym Loc (loc, lazy (Pp.item "global fun-ptr" (Sym.pp fsym))) in
    let@ () = add_cs [(* lc1; *) lc2] in
    add_fun_decl fsym (loc, ft, Pmap.find fsym mu_call_sigs)
  in
  let welltyped_ping fsym =
    debug 2 (lazy (headline ("checking welltypedness of procedure " ^ Sym.pp_string fsym)))
  in
  PmapM.foldM (fun fsym def (trusted, checked) ->
      match def with
      | M_Proc (loc, args_and_body, tr, _) ->
         welltyped_ping fsym;
         let@ args_and_body, ft = WellTyped.WProc.welltyped loc args_and_body in
         debug 6 (lazy (!^"function type" ^^^ Sym.pp fsym));
         debug 6 (lazy (CF.Pp_ast.pp_doc_tree (AT.dtree RT.dtree ft)));
         let@ () = add fsym loc ft in
         begin match tr with
         | Trusted _ -> return ((fsym, (loc, ft)) :: trusted, checked)
         | Checked -> return (trusted, (fsym, (loc, args_and_body)) :: checked)
         end
      | M_ProcDecl (loc, ft) ->
         welltyped_ping fsym;
         let@ ft = WellTyped.WFT.welltyped "function" loc ft in
         let@ () = add fsym loc ft in
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





let check mu_file stmt_locs o_lemma_mode = 
  let@ () = set_statement_locs stmt_locs in

  let@ () = record_tagdefs mu_file.mu_tagDefs in
  let@ () = check_tagdefs mu_file.mu_tagDefs in

  let@ () = ListM.iterM (fun (s,dt) -> add_datatype s dt) 
              mu_file.mu_datatypes in
  let@ () = ListM.iterM (fun (s,pd) -> add_datatype_constr s pd)
              mu_file.mu_constructors in

  let@ () = record_and_check_logical_functions mu_file.mu_logical_predicates in
  let@ () = record_and_check_resource_predicates mu_file.mu_resource_predicates in
  let@ () = record_globals mu_file.mu_globs in
  let@ lemmata = ListM.mapM wf_check_and_record_lemma mu_file.mu_lemmata in
  let@ (_trusted, checked) = wf_check_and_record_functions mu_file.mu_funs
            mu_file.mu_call_funinfo in
  let@ () = check_c_functions checked in

  let@ global = get_global () in
  let@ () = match o_lemma_mode with
  | Some mode -> embed_resultat (Lemmata.generate global mode lemmata)
  | None -> return ()
  in
  return ()


  









(* TODO: 
   - sequencing strength
   - rem_t vs rem_f
   - check globals with expressions
   - inline TODOs
   - make sure all variables disjoint from global variables and function names
   - check datatype definition wellformedness
 *)
