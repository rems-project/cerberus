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
module LP = LogicalPredicates
module Mu = NewMu.New
module RI = ResourceInference

open Tools
open Sctypes
open Context
open Global
open IT
open TypeErrors
open CF.Mucore
open Mu
open Pp
open BT
open Resources
open ResourceTypes
open ResourcePredicates
open LogicalConstraints
open List
open Typing
open Effectful.Make(Typing)




(* some of this is informed by impl_mem *)


type mem_value = CF.Impl_mem.mem_value
type pointer_value = CF.Impl_mem.pointer_value




(*** pattern matching *********************************************************)


(* pattern-matches and binds *)
let pattern_match = 
  let rec aux pat : (IT.t * ((Sym.t * BT.t) list * (Sym.t * (BT.t * Sym.t)) list), type_error) m = 
    let (M_Pattern (loc, _, pattern) : mu_pattern) = pat in
    match pattern with
    | M_CaseBase (o_s, has_bt) ->
       let@ () = WellTyped.WBT.is_bt loc has_bt in
       let lsym = Sym.fresh () in 
       begin match o_s with
       | Some s -> 
          return (sym_ (lsym, has_bt), ([(lsym, has_bt)], [(s, (has_bt, lsym))]))
       | None -> 
          return (sym_ (lsym, has_bt), ([(lsym, has_bt)], []))
       end
    | M_CaseCtor (constructor, pats) ->
       match constructor, pats with
       | M_Cnil item_bt, [] ->
          let@ () = WellTyped.WBT.is_bt loc item_bt in
          return (IT.nil_ ~item_bt, ([], []))
       | M_Cnil item_bt, _ ->
          let@ () = WellTyped.WBT.is_bt loc item_bt in
          fail (fun _ -> {loc; msg = Number_arguments {has = List.length pats; expect = 0}})
       | M_Ccons, [p1; p2] ->
          let@ it1, (l1, a1) = aux p1 in
          let@ it2, (l2, a2) = aux p2 in
          let@ () = WellTyped.ensure_base_type loc ~expect:(List (IT.bt it1)) (IT.bt it2) in
          return (cons_ (it1, it2), (l1@l2, a1@a2))
       | M_Ccons, _ -> 
          fail (fun _ -> {loc; msg = Number_arguments {has = List.length pats; expect = 2}})
       | M_Ctuple, pats ->
          let@ its_l_a = ListM.mapM aux pats in
          let its, l_a = List.split its_l_a in
          let l, a = List.split l_a in
          return (tuple_ its, (List.concat l, List.concat a))
       | M_Cspecified, [pat] ->
          aux pat
       | M_Cspecified, _ ->
          fail (fun _ -> {loc; msg = Number_arguments {expect = 1; has = List.length pats}})
       | M_Carray, _ ->
          Debug_ocaml.error "todo: array types"
  in
  fun pat -> aux pat
  (* fun to_match ((M_Pattern (loc, _, _)) as pat : mu_pattern) -> *)
  (* let@ it = aux pat in *)
  (* let@ () = WellTyped.ensure_base_type loc ~expect:(IT.bt to_match) (IT.bt it) in *)
  (* add_c (t_ (eq_ (it, to_match))) *)



module PrefixHash = 
  Hashtbl.Make(struct
      type t = String.t
      let equal = String.equal
      let hash = String.length
    end)

let prefixes = PrefixHash.create 20

let prefixed str =
  let next = match PrefixHash.find_opt prefixes str with
    | None -> 0
    | Some i -> i + 1
  in
  PrefixHash.add prefixes str next;
  str ^ string_of_int next


let fresh_same_id_with_prefix oprefix s = 
  match oprefix, Sym.description s with
  | Some prefix, SD_CN_Id name -> 
     Sym.fresh_named (name ^ "__" ^ prefixed prefix)
  | _ -> Sym.fresh ()

let fresh_return_with_prefix oprefix = 
  match oprefix with
  | Some prefix -> Sym.fresh_named (prefixed prefix)
  | None -> Sym.fresh ()

let fresh_call_with_prefix call_situation s = 
  match Sym.description s with
  | SD_CN_Id name -> 
     Sym.fresh_named (name ^ "__" ^ prefixed (call_prefix call_situation))
  | _ -> Sym.fresh ()


let rec bind_logical (oprefix,where) (lrt : LRT.t) = 
  match lrt with
  | Define ((s, it), oinfo, rt) ->
     let s, rt = 
       let s' = fresh_same_id_with_prefix oprefix s in
       LRT.alpha_rename_ s' (s, IT.bt it) rt 
     in
     let@ () = add_l s (IT.bt it) in
     let@ () = add_c (LC.t_ (IT.def_ s it)) in
     bind_logical (oprefix, where) rt
  | Resource ((s, (re, oarg_spec)), _oinfo, rt) -> 
     let s, rt = 
       let s' = fresh_same_id_with_prefix oprefix s in
       LRT.alpha_rename_ s' (s, oarg_spec) rt 
     in
     let@ () = add_l s oarg_spec in
     let@ () = add_r where (re, O (sym_ (s, oarg_spec))) in
     bind_logical (oprefix, where) rt
  | Constraint (lc, _oinfo, rt) -> 
     let@ () = add_c lc in
     bind_logical (oprefix, where) rt
  | I -> 
     return ()

let bind_computational (oprefix, where) (name : Sym.t) (rt : RT.t) =
  let Computational ((s, bt), _oinfo, rt) = rt in
  let s' = fresh_return_with_prefix oprefix in
  let rt' = LRT.subst (IT.make_subst [(s, IT.sym_ (s', bt))]) rt in
  let@ () = add_l s' bt in
  let@ () = add_a name (bt, s') in
  bind_logical (oprefix, where) rt'


let bind (oprefix, where) (name : Sym.t) (rt : RT.t) =
  bind_computational (oprefix, where) name rt

let bind_logically (oprefix, where) (rt : RT.t) : ((BT.t * Sym.t), type_error) m =
  let Computational ((s, bt), _oinfo, rt) = rt in
  let s' = fresh_return_with_prefix oprefix in
  let rt' = LRT.subst (IT.make_subst [(s, IT.sym_ (s', bt))]) rt in
  let@ () = add_l s' bt in
  let@ () = bind_logical (oprefix, where) rt' in
  return (bt, s')

type lvt = IT.t



let rt_of_lvt lvt = 
  let sym = Sym.fresh () in
  RT.Computational ((sym, IT.bt lvt), (Loc.unknown, None),
  LRT.Constraint (t_ (def_ sym lvt), (Loc.unknown, None),
  LRT.I))



(* (\* The pattern-matching might de-struct 'bt'. For easily making *)
(*    constraints carry over to those values, record (lname,bound) as a *)
(*    logical variable and record constraints about how the variables *)
(*    introduced in the pattern-matching relate to (lname,bound). *\) *)
(* let pattern_match_rt loc (pat : mu_pattern) (rt : RT.t) : (unit, type_error) m = *)
(*   let@ (bt, s') = bind_logically (Some loc) rt in *)
(*   pattern_match (sym_ (s', bt)) pat *)





module InferenceEqs = struct

let use_model_eqs = ref true

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

let unknown_eq_in_group simp ptr_gp = List.find_map (fun (p, req) -> if not req then None
  else List.find_map (fun (p2, req) -> if req then None
    else if is_true (simp (eq_ (p, p2))) then None
    else Some (eq_ (p, p2))) ptr_gp) ptr_gp

let upd_ptr_gps_for_model global m ptr_gps =
  let eval_f p = match Solver.eval global m p with
    | Some (IT (Lit (Pointer i), _)) -> i
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
    let@ values, equalities, lcs = simp_constraints () in
    let simp t = Simplify.simp global.struct_decls values equalities lcs t in
    let poss_eqs = List.filter_map (unknown_eq_in_group simp) ptr_gps in
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
  if is_bound then return () 
  else fail (fun _ -> {loc; msg = Unknown_variable s})



let check_ptrval (loc : loc) ~(expect:BT.t) (ptrval : pointer_value) : (lvt, type_error) m =
  let@ () = WellTyped.ensure_base_type loc ~expect BT.Loc in
  CF.Impl_mem.case_ptrval ptrval
    ( fun ct -> 
      let sct = Retype.ct_of_ct loc ct in
      let@ () = WellTyped.WCT.is_ct loc sct in
      return IT.null_ )
    ( fun sym -> 
      (* just to make sure it exists *)
      let@ _ = get_fun_decl loc sym in
      return (sym_ (sym, BT.Loc)) ) 
    ( fun _prov p -> 
      return (pointer_ p) )

let rec check_mem_value (loc : loc) ~(expect:BT.t) (mem : mem_value) : (lvt, type_error) m =
  CF.Impl_mem.case_mem_value mem
    ( fun ct -> 
      let@ () = WellTyped.WCT.is_ct loc (Retype.ct_of_ct loc ct) in
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
      let@ () = WellTyped.WCT.is_ct loc (Retype.ct_of_ct loc ct) in
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

and check_struct (loc : loc) (tag : tag) 
                 (member_values : (member * mem_value) list) : (lvt, type_error) m =
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

and check_union (loc : loc) (tag : tag) (id : Id.t) 
                (mv : mem_value) : (lvt, type_error) m =
  Debug_ocaml.error "todo: union types"

let rec check_object_value (loc : loc) ~(expect: BT.t)
          (ov : 'bty mu_object_value) : (lvt, type_error) m =
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
     let@ values = ListM.mapM (check_loaded_value loc ~expect:item_bt) items in
     return (make_array_ ~item_bt values)
  | M_OVstruct (tag, fields) -> 
     let mvals = List.map (fun (member,_,mv) -> (member, mv)) fields in
     check_struct loc tag mvals       
  | M_OVunion (tag, id, mv) -> 
     check_union loc tag id mv
  | M_OVfloating iv ->
     unsupported loc !^"floats"

and check_loaded_value loc ~expect (M_LVspecified ov) =
  check_object_value loc ~expect ov

let rec check_value (loc : loc) ~(expect:BT.t) (v : 'bty mu_value) : (lvt, type_error) m = 
  match v with
  | M_Vobject ov ->
     check_object_value loc ~expect ov
  | M_Vloaded lv ->
     check_loaded_value loc ~expect lv
  | M_Vunit ->
     let@ () = WellTyped.ensure_base_type loc ~expect Unit in
     return IT.unit_
  | M_Vtrue ->
     let@ () = WellTyped.ensure_base_type loc ~expect Bool in
     return (IT.bool_ true)
  | M_Vfalse -> 
     let@ () = WellTyped.ensure_base_type loc ~expect Bool in
     return (IT.bool_ false)
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




let rec check_conv_int loc ~expect (act : _ act) pe = 
  let@ () = WellTyped.ensure_base_type loc ~expect Integer in 
  let@ () = WellTyped.WCT.is_ct act.loc act.ct in
  let@ arg = check_pexpr ~expect:Integer pe in
  (* try to follow conv_int from runtime/libcore/std.core *)
  let ity = match act.ct with
    | Integer ity -> ity
    | _ -> Debug_ocaml.error "conv_int applied to non-integer type"
  in
  let@ provable = provable loc in
  let fail_unrepresentable () = 
    let@ model = model () in
    fail (fun ctxt ->
        let msg = Int_unrepresentable 
                    {value = arg; ict = act.ct; ctxt; model} in
        {loc; msg}
      )
  in
  let@ value = match ity with
    | Bool ->
       return (ite_ (eq_ (arg, int_ 0), int_ 0, int_ 1))
    | _ when Sctypes.is_unsigned_integer_type ity ->
       (* TODO: revisit this *)
       (* begin match provable (t_ (representable_ (act.ct, arg))) with *)
       (* | `True -> return arg *)
       (* | `False -> *)
          return (ite_ (representable_ (act.ct, arg), arg, wrapI loc ity arg))
       (* end *)
    | _ ->
       begin match provable (t_ (representable_ (act.ct, arg))) with
       | `True -> return arg
       | `False -> fail_unrepresentable ()
       end
  in
  return value

and check_array_shift loc ~expect pe1 (loc_ct, ct) pe2 =
  let@ () = WellTyped.ensure_base_type loc ~expect Loc in
  let@ () = WellTyped.WCT.is_ct loc_ct ct in
  let@ vt1 = check_pexpr ~expect:BT.Loc pe1 in
  let@ vt2 = check_pexpr ~expect:Integer pe2 in
  return (arrayShift_ (vt1, ct, vt2))



(* could potentially return a vt instead of an RT.t *)
and check_pexpr (pe : 'bty mu_pexpr) ~(expect:BT.t) : (lvt, type_error) m =
  let (M_Pexpr (loc, _, _, pe_)) = pe in
  let@ () = print_with_ctxt (fun ctxt ->
      debug 3 (lazy (action "inferring pure expression"));
      debug 3 (lazy (item "expr" (NewMu.pp_pexpr pe)));
      debug 3 (lazy (item "ctxt" (Context.pp ctxt)))
    )
  in
  let@ lvt = match pe_ with
    | M_PEsym sym ->
       let@ () = check_computational_bound loc sym in
       let@ (bt,lname) = get_a sym in
       let@ () = WellTyped.ensure_base_type loc ~expect bt in
       return (sym_ (lname, bt))
    (* | M_PEimpl i -> *)
    (*    let@ global = get_global () in *)
    (*    let value = Global.get_impl_constant global i in *)
    (*    return {loc; value} *)
    | M_PEval v ->
       check_value loc ~expect v
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
          let@ values = ListM.map2M (fun pe bt -> check_pexpr ~expect:bt pe)
                          pes item_bts in
          return (tuple_ values)
       | M_Carray, _ -> 
          let@ item_bt = match expect with
            | Map (index_bt, item_bt) -> return item_bt
            | _ -> 
               let msg = Mismatch {has = !^"array"; expect = BT.pp expect} in
               fail (fun _ -> {loc; msg})
          in
          assert (BT.equal item_bt Integer);
          let@ values = ListM.mapM (check_pexpr ~expect:item_bt) pes in
          return (make_array_ ~item_bt values)
       | M_Cspecified, [pe] ->
          check_pexpr ~expect pe
       | M_Cspecified, _ ->
          fail (fun _ -> {loc; msg = Number_arguments {has = List.length pes; expect = 1}})
       | M_Cnil item_bt, [] -> 
          let@ () = WellTyped.WBT.is_bt loc item_bt in
          let@ () = WellTyped.ensure_base_type loc ~expect (List item_bt) in
          return (nil_ ~item_bt)
       | M_Cnil item_bt, _ -> 
          fail (fun _ -> {loc; msg = Number_arguments {has = List.length pes; expect=0}})
       | M_Ccons, [pe1; pe2] -> 
          let@ item_bt = match expect with
            | List item_bt -> return item_bt
            | _ -> 
               let msg = Mismatch {has = !^"list"; expect = BT.pp expect} in
               fail (fun _ -> {loc; msg})
          in
          let@ vt1 = check_pexpr ~expect:item_bt pe1 in
          let@ vt2 = check_pexpr ~expect pe2 in
          return (cons_ (vt1, vt2))
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
       let@ vt1 = check_pexpr ~expect:Integer pe1 in
       let@ vt2 = check_pexpr ~expect:Integer pe2 in
       let value = warn_uf loc "xor_uf"; xor_no_smt_ (vt1, vt2) in
       return value
    | M_Cfvfromint _ -> 
       unsupported loc !^"floats"
    | M_Civfromfloat (act, _) -> 
       let@ () = WellTyped.WCT.is_ct act.loc act.ct in
       unsupported loc !^"floats"
    | M_PEarray_shift (pe1, ct, pe2) ->
       let@ () = WellTyped.ensure_base_type loc ~expect Loc in
       check_array_shift loc ~expect pe1 (loc, ct) pe2
    | M_PEmember_shift (pe, tag, member) ->
       let@ () = WellTyped.ensure_base_type loc ~expect Loc in
       let@ vt = check_pexpr ~expect:Loc pe in
       let@ layout = get_struct_decl loc tag in
       let@ _member_bt = get_member_type loc tag member layout in
       return (memberShift_ (vt, tag, member))
    | M_PEnot pe ->
       let@ () = WellTyped.ensure_base_type loc ~expect Bool in
       let@ vt = check_pexpr ~expect:Bool pe in
       return (not_ vt)
    | M_PEop (op, pe1, pe2) ->
       let check_args_and_ret abt1 abt2 rbt = 
         let@ v1 = check_pexpr ~expect:abt1 pe1 in
         let@ v2 = check_pexpr ~expect:abt2 pe2 in
         let@ () = WellTyped.ensure_base_type loc ~expect rbt in
         return (v1, v2)
       in
       begin match op with
       | OpAdd -> 
          let@ v1, v2 = check_args_and_ret Integer Integer Integer in
          return (add_ (v1, v2))
       | OpSub ->
          let@ v1, v2 = check_args_and_ret Integer Integer Integer in
          return (sub_ (v1, v2))
       | OpMul ->
          let@ v1, v2 = check_args_and_ret Integer Integer Integer in
          return (if (is_z_ v1 || is_z_ v2) then mul_ (v1, v2) 
                  else (warn_uf loc "mul_uf"; mul_no_smt_ (v1, v2)))
       | OpDiv ->
          let@ v1, v2 = check_args_and_ret Integer Integer Integer in
          return (if is_z_ v2 then div_ (v1, v2) 
                  else (warn_uf loc "div_uf"; div_no_smt_ (v1, v2)))
       | OpRem_f ->
          let@ v1, v2 = check_args_and_ret Integer Integer Integer in
          return (if is_z_ v2 then rem_ (v1, v2) 
                  else (warn_uf loc "rem_uf"; rem_no_smt_ (v1, v2)))
       | OpRem_t ->
          let@ v1, v2 = check_args_and_ret Integer Integer Integer in
          let@ provable = provable loc in
          begin match provable (LC.T (and_ [le_ (int_ 0, v1); le_ (int_ 0, v2)])) with
          | `True ->
             (* If the arguments are non-negative, then rem or mod should be sound to use for rem_t *)
             (* If not it throws a type error, but we should instead
                map that to an uninterpreted function eventually. *)
             return (if (is_z_ v2) then IT.mod_ (v1, v2) 
                     else (warn_uf loc "mod_uf"; IT.mod_no_smt_ (v1, v2)))
          | `False ->
             let@ model = model () in
             let err = !^"Unsupported: rem_t applied to negative arguments" in
             fail (fun ctxt ->
                 let msg = Generic_with_model {err; model; ctxt} in
                 {loc; msg}
               )
          end
       | OpExp ->
          let@ v1, v2 = check_args_and_ret Integer Integer Integer in
          begin match is_z v1, is_z v2 with
          | Some z, Some z' ->
             let it = exp_ (v1, v2) in
             if Z.lt z' Z.zero then
               (* we should relax this and map to exp_no_smt_ if we
                  can handle negative exponents there *)
               fail (fun ctxt -> {loc; msg = NegativeExponent {context = it; it; ctxt}})
             else if Z.fits_int32 z' then
               return it
             else 
               (* we can probably just relax this and map to exp_no_smt_ *)
               fail (fun ctxt -> {loc; msg = TooBigExponent {context =it; it; ctxt}})
          | _ ->
             return (warn_uf loc "power_uf"; exp_no_smt_ (v1, v2))
          end 
       | OpEq ->
          (* eventually we have to also support floats here *)
          let@ v1, v2 = check_args_and_ret Integer Integer Bool in
          return (eq_ (v1, v2))
       | OpGt ->
          (* eventually we have to also support floats here *)
          let@ v1, v2 = check_args_and_ret Integer Integer Bool in
          return (gt_ (v1, v2))
       | OpLt ->
          let@ v1, v2 = check_args_and_ret Integer Integer Bool in
          return (lt_ (v1, v2))
       | OpGe ->
          let@ v1, v2 = check_args_and_ret Integer Integer Bool in
          return (ge_ (v1, v2))
       | OpLe -> 
          let@ v1, v2 = check_args_and_ret Integer Integer Bool in
          return (le_ (v1, v2))
       | OpAnd ->
          let@ v1, v2 = check_args_and_ret Bool Bool Bool in
          return (and_ [v1; v2])
       | OpOr -> 
          let@ v1, v2 = check_args_and_ret Bool Bool Bool in
          return (or_ [v1; v2])
       end
    | M_PEstruct _ ->
       Debug_ocaml.error "todo: PEstruct"
    | M_PEunion _ ->
       Debug_ocaml.error "todo: PEunion"
    | M_PEmemberof _ ->
       Debug_ocaml.error "todo: M_PEmemberof"
    | M_PEassert_undef (pe, _uloc, ub) ->
       let@ () = WellTyped.ensure_base_type loc ~expect Unit in
       let@ arg = check_pexpr ~expect:Bool pe in
       let@ provable = provable loc in
       begin match provable (t_ arg) with
       | `True -> 
          return unit_
       | `False ->
          let@ model = model () in
          fail (fun ctxt -> {loc; msg = Undefined_behaviour {ub; ctxt; model}})
       end
    | M_PEbool_to_integer pe ->
       let@ () = WellTyped.ensure_base_type loc ~expect Integer in
       let@ arg = check_pexpr ~expect:Bool pe in
       return (ite_ (arg, int_ 1, int_ 0))
    | M_PEconv_int (act, pe) ->
       check_conv_int loc ~expect act pe
    | M_PEconv_loaded_int (act, pe) ->
       check_conv_int loc ~expect act pe
    | M_PEwrapI (act, pe) ->
       let@ () = WellTyped.ensure_base_type loc ~expect Integer in
       let@ arg = check_pexpr ~expect:Integer pe in
       let ity = match act.ct with
         | Integer ity -> ity
         | _ -> Debug_ocaml.error "wrapI applied to non-integer type"
       in
       return (wrapI loc ity arg)
    | M_PEif (pe, e1, e2) ->
       let@ c = check_pexpr ~expect:Bool pe in
       let aux e cond = 
         pure begin
             let@ () = add_c (t_ cond) in
             let@ provable = provable loc in
             match provable (t_ (bool_ false)) with
             | `True -> return (default_ expect)
             | `False -> check_pexpr ~expect e
           end
       in
       let@ v1 = aux e1 c in
       let@ v2 = aux e2 (not_ c) in
       return (ite_ (c, v1, v2))
    | M_PElet (M_Pat p, e1, e2) ->
       let@ fin = begin_trace_of_pure_step (Some (Mu.M_Pat p)) e1 in
       let@ patv, (l, a) = pattern_match p in
       let@ v1 = check_pexpr ~expect:(IT.bt patv) e1 in
       let@ () = add_ls l in
       let@ () = add_as a in
       let@ () = add_c (t_ (eq__ patv v1)) in
       let@ () = fin () in
       let@ lvt = check_pexpr ~expect e2 in
       let@ () = remove_as (List.map fst a) in
       return lvt
    (* | M_PEdone pe -> *)
    (*    let@ arg = infer_pexpr pe in *)
    (*    Spine.subtype loc arg typ *)
    | M_PEundef (_loc, ub) ->
       let@ provable = provable loc in
       begin match provable (t_ (bool_ false)) with
       | `True -> return (default_ expect)
       | `False ->
          let@ model = model () in
          fail (fun ctxt -> {loc; msg = Undefined_behaviour {ub; ctxt; model}})
       end
    | M_PEerror (err, pe) ->
       let@ provable = provable loc in
       begin match provable (t_ (bool_ false)) with
       | `True -> return (default_ expect)
       | `False ->
          let@ model = model () in
          fail (fun ctxt -> {loc; msg = StaticError {err; ctxt; model}})
       end
  in
  debug 3 (lazy (item "type" (IT.pp lvt)));
  return lvt


let unpack_def global name args =
    Option.bind (Global.get_logical_predicate_def global name)
    (fun def ->
    match def.definition with
    | Def body ->
       Some (LogicalPredicates.open_pred def.args body args)
    | Uninterp -> None
    )

let debug_constraint_failure_diagnostics model global c =
  if ! Pp.print_level == 0 then () else
  let split tm = match IT.term tm with
    | IT.Bool_op (IT.And xs) -> Some ("and", xs)
    | IT.Bool_op (IT.Or xs) -> Some ("or", xs)
    | IT.Bool_op (IT.Not x) -> Some ("not", [x])
    | IT.Bool_op (IT.EQ (x, y)) -> Some ("eq", [x; y])
    | IT.Pred (name, args) when Option.is_some (unpack_def global name args) ->
        Some (Sym.pp_string name, [Option.get (unpack_def global name args)])
    | _ -> None
  in
  let rec diag_rec i tm =
    let pt = !^ "-" ^^^ Pp.int i ^^ Pp.colon in
    begin match Solver.eval global (fst model) tm with
      | None -> Pp.debug 6 (lazy (pt ^^^ !^ "cannot eval:" ^^^ IT.pp tm))
      | Some v -> Pp.debug 6 (lazy (pt ^^^ IT.pp v ^^^ !^"<-" ^^^ IT.pp tm))
    end;
    match split tm with
      | None -> ()
      | Some (nm, ts) -> List.iter (diag_rec (i + 1)) ts
  in
  begin match c with
  | LC.T tm ->
    Pp.debug 6 (lazy (Pp.item "counterexample, expanding" (IT.pp tm)));
    diag_rec 0 tm
  | _ -> ()
  end

module Spine : sig

  val calltype_ft : 
    Loc.t -> (_ mu_pexpr) list -> AT.ft -> (RT.t, type_error) m
  val calltype_lt : 
    Loc.t -> (_ mu_pexpr) list -> AT.lt * label_kind -> (unit, type_error) m
  val calltype_packing : 
    Loc.t -> Sym.t -> LAT.packing_ft -> (OutputDef.t, type_error) m
  val subtype : 
    Loc.t -> LRT.t -> (unit, type_error) m
end = struct


  let has_exact loc (r : RET.t) =
    let@ is_ex = RI.General.exact_match () in
    map_and_fold_resources loc (fun re found -> (Unchanged, found || is_ex (RE.request re, r))) false

  let prioritise_resource loc rt_subst pred ftyp = 
    let open LAT in
    let rec aux names ft_so_far ft = 
      match ft with
      | Define ((s, it), info, t) ->
         let ft_so_far' ft = ft_so_far (Define ((s, it), info, ft)) in
         aux (SymSet.add s names) ft_so_far' t
      | Resource ((name, (re, bt)), info, t) ->
         let continue () = 
           let ft_so_far' ft = ft_so_far (Resource ((name, (re, bt)), info, ft)) in
           aux (SymSet.add name names) ft_so_far' t 
         in
         if not (SymSet.is_empty (SymSet.inter (RET.free_vars re) names)) then 
           continue ()
         else
           let@ pred_holds = pred loc re in
           if pred_holds then 
             let name, t = LAT.alpha_rename rt_subst (name, bt) t in
             return (Resource ((name, (re, bt)), info, (ft_so_far t)))
           else 
             continue ()
      | Constraint (lc, info, t) -> 
         let ft_so_far' ft = ft_so_far (Constraint (lc, info, ft)) in
         aux names ft_so_far' t
      | I rt ->
         return (ft_so_far (I rt))         
    in
    aux SymSet.empty (fun ft -> ft) ftyp

  let prefer_exact loc rt_subst ftyp =
    if !RI.reorder_points 
    then prioritise_resource loc rt_subst has_exact ftyp
    else return ftyp 




  let spine_l rt_subst rt_pp loc (situation : call_situation) ftyp = 

    let start_spine = time_log_start "spine_l" "" in

    (* record the resources now, so we can later re-construct the
       memory state "before" running spine *)
    let@ original_resources = all_resources_tagged () in

    let@ () = 
      let@ trace_length = get_trace_length () in
      time_f_logs loc 9 "pre_inf_eqs" trace_length
        (InferenceEqs.add_eqs_for_infer loc) ftyp
    in

    let@ rt, cs = 
      let rec check cs ftyp = 
        let@ () = print_with_ctxt (fun ctxt ->
            debug 6 (lazy (item "ctxt" (Context.pp ctxt)));
            debug 6 (lazy (item "spec" (LAT.pp rt_pp ftyp)));
          )
        in
        let@ ftyp = prefer_exact loc rt_subst ftyp in
        match ftyp with
        | LAT.Resource ((s, (resource, bt)), info, ftyp) -> 
           let uiinfo = (situation, (Some resource, Some info)) in
           let@ o_re_oarg = RI.General.resource_request ~recursive:true loc uiinfo resource in
           let@ oargs = match o_re_oarg with
             | None ->
                let@ model = model () in
                fail_with_trace (fun trace -> fun ctxt ->
                    let ctxt = { ctxt with resources = original_resources } in
                    let msg = Missing_resource_request 
                                {orequest = Some resource; 
                                 situation = Call situation; 
                                 oinfo = Some info; model; trace; ctxt} in
                    {loc; msg}
                  )

             | Some (re, O oargs) ->
                assert (ResourceTypes.equal re resource);
                return oargs
           in
           check cs (LAT.subst rt_subst (IT.make_subst [(s, oargs)]) ftyp)
        | Define ((s, it), info, ftyp) ->
           let s' = fresh_call_with_prefix situation s in
           let bt = IT.bt it in
           let@ () = add_l s' bt in
           let@ () = add_c (LC.t_ (def_ s' it)) in
           check cs (LAT.subst rt_subst (IT.make_subst [(s, sym_ (s', bt))]) ftyp)
        | Constraint (c, info, ftyp) -> 
           let@ () = return (debug 9 (lazy (item "checking constraint" (LC.pp c)))) in
           let@ provable = provable loc in
           let res = provable c in
           begin match res with
           | `True -> check (c :: cs) ftyp
           | `False ->
              let@ model = model () in
              let@ global = get_global () in
              debug_constraint_failure_diagnostics model global c;
              fail_with_trace (fun trace -> fun ctxt ->
                  let ctxt = { ctxt with resources = original_resources } in
                  {loc; msg = Unsat_constraint {constr = c; info; ctxt; model; trace}}
                )
           end
        | I rt ->
           return (rt, cs)
      in
      check [] ftyp
    in

    let@ () = return (debug 9 (lazy !^"done")) in
    time_log_end start_spine;
    return rt


  let spine rt_subst rt_pp loc (situation : call_situation) args ftyp =

    let open ArgumentTypes in

    let original_ftyp = ftyp in
    let original_args = args in

    let@ () = print_with_ctxt (fun ctxt ->
        debug 6 (lazy (call_situation situation));
        debug 6 (lazy (item "ctxt" (Context.pp ctxt)));
        debug 6 (lazy (item "spec" (pp rt_pp ftyp)))
      )
    in

    let@ ftyp = 
      let rec check args ftyp = 
        match args, ftyp with
        | ((arg : _ mu_pexpr) :: args), (Computational ((s, bt), _info, ftyp)) ->
           let@ arg = check_pexpr ~expect:bt arg in
           check args (subst rt_subst (make_subst [(s, arg)]) ftyp)
        | [], (L ftyp) -> 
           return ftyp
        | _ -> 
           let expect = count_computational original_ftyp in
           let has = List.length original_args in
           fail (fun _ -> {loc; msg = Number_arguments {expect; has}})
      in
      check args ftyp 
    in
    
    spine_l rt_subst rt_pp loc situation ftyp


  let calltype_ft loc args (ftyp : AT.ft) : (RT.t, type_error) m =
    spine RT.subst RT.pp loc FunctionCall args ftyp


  let calltype_lt loc args ((ltyp : AT.lt), label_kind) : (unit, type_error) m =
    let@ (False.False) =
      spine False.subst False.pp 
        loc (LabelCall label_kind) args ltyp
    in
    return ()

  let calltype_packing loc (name : Sym.t) (ft : LAT.packing_ft)
        : (OutputDef.t, type_error) m =
    spine_l OutputDef.subst OutputDef.pp 
      loc (PackPredicate name) ft

  (* The "subtyping" judgment needs the same resource/lvar/constraint
     inference as the spine judgment. So implement the subtyping
     judgment 'arg <: LRT' by type checking 'f()' for 'f: LRT -> False'. *)
  let subtype (loc : loc) (rtyp : LRT.t) : (unit, type_error) m =
    let lft = LAT.of_lrt rtyp (LAT.I False.False) in
    let@ (False.False) =
      spine_l False.subst False.pp loc Subtyping lft in
    return ()


end




(*** impure expression inference **********************************************)



(* `t` is used for the type of Run/Goto: Goto has no return type
   (because the control flow does not return there), but instead
   returns `False`. Type inference of impure expressions returns
   either a return type and a typing context or `False` *)
type 'a orFalse = 
  | Normal of 'a
  | False

let pp_or_false (ppf : 'a -> Pp.document) (m : 'a orFalse) : Pp.document = 
  match m with
  | Normal a -> ppf a
  | False -> parens !^"no return"



let all_empty loc = 
  let@ provable = provable loc in
  let@ all_resources = all_resources () in
  ListM.iterM (fun resource ->
      let constr = match resource with
        | (P p, _) -> t_ (not_ p.permission)
        | (Q p, _) -> forall_ (p.q, BT.Integer) (not_ p.permission)
      in
      match provable constr with
      | `True -> return () 
      | `False -> 
         let@ model = model () in 
         fail_with_trace (fun trace -> fun ctxt ->
             {loc; msg = Unused_resource {resource; ctxt; model; trace}})
    ) all_resources


type labels = (AT.lt * label_kind) SymMap.t


let check_expr labels ~(expect:BT.t) (e : 'bty mu_expr) : (RT.t, type_error) m =
  let (M_Expr (loc, _annots, e_)) = e in
  let@ () = print_with_ctxt (fun ctxt ->
       debug 3 (lazy (action "inferring expression"));
       debug 3 (lazy (item "expr" (group (NewMu.pp_expr e))));
       debug 3 (lazy (item "ctxt" (Context.pp ctxt)));
    )
  in
  let@ result = match e_ with
    | M_Epure pe -> 
       let@ lvt = check_pexpr ~expect pe in
       return (rt_of_lvt lvt)
    | M_Ememop memop ->
       let pointer_op op pe1 pe2 = 
         let@ arg1 = check_pexpr ~expect:Loc pe1 in
         let@ arg2 = check_pexpr ~expect:Loc pe2 in
         let lvt = op (arg1, arg2) in
         let@ () = WellTyped.ensure_base_type loc ~expect (IT.bt lvt) in
         return (rt_of_lvt lvt)
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
          let@ arg1 = check_pexpr ~expect:Loc pe1 in
          let@ arg2 = check_pexpr ~expect:Loc pe2 in
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
          return (rt_of_lvt value)


       | M_IntFromPtr (act_from, act_to, pe) ->
          let@ () = WellTyped.ensure_base_type loc ~expect Integer in
          let@ () = WellTyped.WCT.is_ct act_from.loc act_from.ct in
          let@ () = WellTyped.WCT.is_ct act_to.loc act_to.ct in
          let@ arg = check_pexpr ~expect:Loc pe in
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
          return (rt_of_lvt value)
       | M_PtrFromInt (act_from, act2_to, pe) ->
          let@ () = WellTyped.ensure_base_type loc ~expect Loc in
          let@ () = WellTyped.WCT.is_ct act_from.loc act_from.ct in
          let@ () = WellTyped.WCT.is_ct act2_to.loc act2_to.ct in
          let@ arg = check_pexpr ~expect:Integer pe in
          let value = integerToPointerCast_ arg in
          return (rt_of_lvt value)
       | M_PtrValidForDeref (act, pe) ->
          let@ () = WellTyped.ensure_base_type loc ~expect Bool in
          (* check *)
          let@ () = WellTyped.WCT.is_ct act.loc act.ct in
          let@ arg = check_pexpr ~expect:Loc pe in
          let value = aligned_ (arg, act.ct) in
          return (rt_of_lvt value)
       | M_PtrWellAligned (act, pe) ->
          let@ () = WellTyped.ensure_base_type loc ~expect Bool in
          let@ () = WellTyped.WCT.is_ct act.loc act.ct in
          let@ arg = check_pexpr ~expect:Loc pe in
          let value = aligned_ (arg, act.ct) in
          return (rt_of_lvt value)
       | M_PtrArrayShift (pe1, act, pe2) ->
          let@ lvt = check_array_shift loc ~expect pe1 (act.loc, act.ct) pe2 in
          return (rt_of_lvt lvt)
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
    | M_Eaction (M_Paction (_pol, M_Action (aloc, action_))) ->
       begin match action_ with
       | M_Create (pe, act, _prefix) -> 
          let@ () = WellTyped.ensure_base_type loc ~expect Loc in
          let@ () = WellTyped.WCT.is_ct act.loc act.ct in
          let@ arg = check_pexpr ~expect:Integer pe in
          let ret = Sym.fresh () in
          let oarg_s, oarg = IT.fresh_named (Resources.block_oargs) "Uninit" in
          let resource = 
            (oarg_s, (P {
                name = Block act.ct; 
                pointer = sym_ (ret, Loc);
                permission = bool_ true;
                iargs = [];
              },
             IT.bt oarg))
          in
          let rt = 
            RT.Computational ((ret, Loc), (loc, None),
            LRT.Constraint (t_ (representable_ (pointer_ct act.ct, sym_ (ret, Loc))), (loc, None),
            LRT.Constraint (t_ (alignedI_ ~align:arg ~t:(sym_ (ret, Loc))), (loc, None),
            LRT.Resource (resource, (loc, None), 
            LRT.I))))
          in
          return (rt)
       | M_CreateReadOnly (sym1, ct, sym2, _prefix) -> 
          Debug_ocaml.error "todo: CreateReadOnly"
       | M_Alloc (ct, sym, _prefix) -> 
          Debug_ocaml.error "todo: Alloc"
       | M_Kill (M_Dynamic, asym) -> 
          Debug_ocaml.error "todo: Free"
       | M_Kill (M_Static ct, pe) -> 
          let@ () = WellTyped.ensure_base_type loc ~expect Unit in
          let@ () = WellTyped.WCT.is_ct loc ct in
          let@ arg = check_pexpr ~expect:Loc pe in
          let@ _ = 
            RI.Special.predicate_request ~recursive:true loc (Access Kill) ({
              name = Owned ct;
              pointer = arg;
              permission = bool_ true;
              iargs = [];
            }, None)
          in
          return (rt_of_lvt unit_)
       | M_Store (_is_locking, act, p_pe, v_pe, mo) -> 
          let@ () = WellTyped.ensure_base_type loc ~expect Unit in
          let@ () = WellTyped.WCT.is_ct act.loc act.ct in
          let@ parg = check_pexpr ~expect:Loc p_pe in
          let@ varg = check_pexpr ~expect:(BT.of_sct act.ct) v_pe in
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
          let oarg_s, oarg = IT.fresh_named (owned_oargs act.ct) "Stored" in
          let resource = 
            (oarg_s, (P {
                name = Owned act.ct;
                pointer = parg;
                permission = bool_ true;
                iargs = [];
               },
             IT.bt oarg))
          in
          let value_constr = 
            t_ (eq_ (recordMember_ ~member_bt:(BT.of_sct act.ct) (oarg, value_sym),
                     varg))
          in
          let rt = 
            RT.Computational ((Sym.fresh (), Unit), (loc, None),
            Resource (resource, (loc, None),
            Constraint (value_constr, (loc, None),
            LRT.I)))
          in
          return (rt)
       | M_Load (act, p_pe, _mo) -> 
          let@ () = WellTyped.WCT.is_ct act.loc act.ct in
          let@ () = WellTyped.ensure_base_type loc ~expect (BT.of_sct act.ct) in
          let@ parg = check_pexpr ~expect:Loc p_pe in
          let@ (point, point_oargs) = 
            restore_resources 
              (RI.Special.predicate_request ~recursive:true loc (Access (Load None)) ({ 
                     name = Owned act.ct;
                     pointer = parg;
                     permission = bool_ true;
                     iargs = [];
                   }, None))
          in
          let value = snd (List.hd (RI.oargs_list point_oargs)) in
          (* let@ () =  *)
          (*   let@ provable = provable loc in *)
          (*   match provable (t_ init) with *)
          (*   | `True -> return ()  *)
          (*   | `False -> *)
          (*      let@ model = model () in *)
          (*      fail (fun ctxt -> {loc; msg = Uninitialised_read {ctxt; model}}) *)
          (* in *)
          let ret = Sym.fresh () in
          let rt = 
            RT.Computational ((ret, IT.bt value), (loc, None),
            Constraint (t_ (def_ ret value), (loc, None),
                        (* TODO: check *)
            LRT.I))
          in
          return (rt)
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
    | M_Eskip -> 
       let@ () = WellTyped.ensure_base_type loc ~expect Unit in
       return (rt_of_lvt unit_)
    | M_Eccall (act, f_pe, pes) ->
       (* todo: do anything with act? *)
       let@ () = WellTyped.WCT.is_ct act.loc act.ct in
       let fsym = match f_pe with
         | M_Pexpr (_, _, _, M_PEsym fsym) -> fsym
         | _ -> unsupported loc !^"function application of function pointers"
       in
       let@ (_loc, ft, _) = get_fun_decl loc fsym in
       Spine.calltype_ft loc pes ft
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
    | M_Erpredicate (pack_unpack, TPU_Predicate pname, pes) ->
       let@ () = WellTyped.ensure_base_type loc ~expect Unit in
       let@ global = get_global () in
       let@ pname, def = Typing.todo_get_resource_predicate_def_s loc (Id.s pname) in
       let@ pointer_pe, iarg_pes = match pes with
         | pointer_asym :: iarg_asyms -> return (pointer_asym, iarg_asyms)
         | _ -> fail (fun _ -> {loc; msg = Generic !^"pointer argument to predicate missing"})
       in
       let@ () = 
         (* "+1" because of pointer argument *)
         let has, expect = List.length iarg_pes + 1, List.length def.iargs + 1 in
         if has = expect then return ()
         else fail (fun _ -> {loc; msg = Number_arguments {has; expect}})
       in
       let@ pointer_arg = check_pexpr ~expect:Loc pointer_pe in
       let@ iargs = 
         ListM.map2M (fun arg expect ->
             check_pexpr ~expect arg
           ) iarg_pes (List.map snd def.iargs)
       in
       let@ instantiated_clauses = match def.clauses with
         | Some clauses ->
             let subst = 
               make_subst (
                   (def.pointer, pointer_arg) ::
                   List.map2 (fun (def_ia, _) ia -> (def_ia, ia)) def.iargs iargs
                 )
             in
             return (List.map (ResourcePredicates.subst_clause subst) clauses)
         | None ->
            let action = match pack_unpack with 
              | Pack -> "pack" 
              | Unpack -> "unpack"
            in
            let msg = "Cannot "^action^" uninterpreted predicate" in
            fail (fun _ -> {loc; msg = Generic !^msg})
       in
       let@ provable = provable loc in
       let@ right_clause = 
         let rec try_clauses negated_guards clauses = 
           match clauses with
           | clause :: clauses -> 
              begin match provable (t_ (and_ (clause.guard :: negated_guards))) with
              | `True -> return clause.packing_ft
              | `False -> try_clauses (not_ clause.guard :: negated_guards) clauses
              end
           | [] -> 
              let err = 
                !^"do not have enough information for" ^^^
                (match pack_unpack with Pack -> !^"packing" | Unpack -> !^"unpacking") ^^^
                Sym.pp pname
              in
              fail (fun _ -> {loc; msg = Generic err})
         in
         try_clauses [] instantiated_clauses
       in
       begin match pack_unpack with
       | Unpack ->
          let@ (pred, O pred_oargs) =
            RI.Special.predicate_request ~recursive:false
              loc (Call (UnpackPredicate pname)) ({
                name = PName pname;
                pointer = pointer_arg;
                permission = bool_ true;
                iargs = iargs;
              }, None)
          in
          let condition, outputs = LAT.logical_arguments_and_return right_clause in
          let lc = 
            eq_ (pred_oargs, 
                 record_ (List.map (fun (o : OutputDef.entry) -> (o.name, o.value)) outputs))
          in
          let lrt = LRT.concat condition (Constraint (t_ lc, (loc, None), I)) in
          return (RT.Computational ((Sym.fresh (), BT.Unit), (loc, None), lrt))
       | Pack ->
          let@ (output_assignment) = Spine.calltype_packing loc pname right_clause in
          let output = record_ (List.map (fun (o : OutputDef.entry) -> (o.name, o.value)) output_assignment) in
          let oarg_s, oarg = IT.fresh_named (IT.bt output) "Packed" in
          let resource = 
            (oarg_s, (P {
              name = PName pname;
              pointer = pointer_arg;
              permission = bool_ true;
              iargs = iargs;
            }, IT.bt oarg))
          in
          let rt =
            (RT.Computational ((Sym.fresh (), BT.Unit), (loc, None),
             Resource (resource, (loc, None),
             Constraint (t_ (eq_ (oarg, output)), (loc, None), 
             LRT.I))))
          in
          return (rt)
       end
    | M_Erpredicate (pack_unpack, TPU_Struct tag, pes) ->
       let@ () = WellTyped.ensure_base_type loc ~expect Unit in
       let@ _layout = get_struct_decl loc tag in
       let@ () = 
         (* "+1" because of pointer argument *)
         let has = List.length pes in
         if has = 1 then return ()
         else fail (fun _ -> {loc; msg = Number_arguments {has; expect = 1}})
       in
       let@ pointer_arg = check_pexpr ~expect:Loc (List.hd pes) in
       begin match pack_unpack with
       | Pack ->
          let situation = Call (TypeErrors.PackStruct tag) in
          let@ (resource, O resource_oargs) = 
            RI.Special.fold_struct ~recursive:true loc situation tag 
              pointer_arg (bool_ true) 
          in
          let oargs_s, oargs = IT.fresh_named (IT.bt resource_oargs) "Packed" in
          let rt = 
            RT.Computational ((Sym.fresh (), BT.Unit), (loc, None),
            LRT.Resource ((oargs_s, (P resource, IT.bt oargs)), (loc, None), 
            LRT.Constraint (t_ (eq_ (oargs, resource_oargs)), (loc, None),
            LRT.I)))
          in
          return (rt)
       | Unpack ->
          let situation = Call (TypeErrors.UnpackStruct tag) in
          let@ resources = 
            RI.Special.unfold_struct ~recursive:true loc situation tag 
              pointer_arg (bool_ true) 
          in
          let constraints, resources = 
            List.fold_left_map (fun acc (r, O o) -> 
                let oarg_s, oarg = IT.fresh (IT.bt o) in
                let acc = acc @ [(t_ (eq_ (oarg, o)), (loc, None))] in
                acc, ((oarg_s, (r, IT.bt oarg)), (loc, None))
              ) [] resources in
          let lrt = LRT.mResources resources (LRT.mConstraints constraints LRT.I) in
          let rt = RT.Computational ((Sym.fresh (), BT.Unit), (loc, None), lrt) in
          return (rt)
       end
    | M_Elpredicate (have_show, pname, asyms) ->
       unsupported loc !^"have/show"
    | M_Einstantiate (oid, pe) ->
       let@ () = WellTyped.ensure_base_type loc ~expect Unit in
       let@ arg = check_pexpr ~expect:Integer pe in
       let@ constraints = all_constraints () in
       let omentions_pred it = match oid with
         | Some id -> IT.mentions_pred id it
         | None -> true
       in
       let extra_assumptions = 
         List.filter_map (fun lc ->
             match lc with
             | Forall ((s, bt), t) 
                  when BT.equal bt (IT.bt arg) && omentions_pred t ->
                Some (LC.t_ (IT.subst (IT.make_subst [(s, arg)]) t), (loc, None))
             | _ -> 
                None
           ) (LCSet.elements constraints)
       in
       if List.length extra_assumptions == 0 then Pp.warn loc (Pp.string "nothing instantiated")
       else ();
       let lrt = LRT.mConstraints extra_assumptions LRT.I in
       return (RT.Computational ((Sym.fresh (), Unit), (loc, None), lrt))
  in
  debug 3 (lazy (RT.pp result));
  return result

(* check_expr: type checking for impure epressions; type checks `e`
   against `typ`, which is either a return type or `False`; returns
   either an updated environment, or `False` in case of Goto *)
let rec check_texpr labels (e : 'bty mu_texpr) (typ : RT.t orFalse) 
        : (unit, type_error) m =

  let@ () = increase_trace_length () in
  let (M_TExpr (loc, _annots, e_)) = e in
  let@ () = print_with_ctxt (fun ctxt ->
      debug 3 (lazy (action "checking expression"));
      debug 3 (lazy (item "expr" (group (NewMu.pp_texpr e))));
      debug 3 (lazy (item "type" (pp_or_false RT.pp typ)));
      debug 3 (lazy (item "ctxt" (Context.pp ctxt)));
    )
  in
  let@ result = match e_ with
    | M_Eif (c_pe, e1, e2) ->
       let@ carg = check_pexpr ~expect:Bool c_pe in
       let aux lc nm e = 
           pure begin
               let@ () = add_c (t_ lc) in
               let@ provable = provable loc in
               match provable (t_ (bool_ false)) with
               | `True -> return ()
               | `False ->
                  let start = time_log_start (nm ^ " branch") (Locations.to_string loc) in
                  let@ () = check_texpr_in [loc_of_texpr e; loc] labels e typ in
                  time_log_end start;
                  return ()
             end
       in
       let@ () = aux carg "true" e1 in
       let@ () = aux (not_ carg) "false" e2 in
       return ()
    | M_Ebound e ->
       check_texpr labels e typ 
    | M_End _ ->
       Debug_ocaml.error "todo: End"
    | M_Elet (M_Pat p, e1, e2) ->
(*       let@ fin = begin_trace_of_step (Some (Mu.M_Pat p)) e1 in *)
       let@ patv, (l, a) = pattern_match p in
       let@ v1 = check_pexpr ~expect:(IT.bt patv) e1 in
       let@ () = add_ls l in
       let@ () = add_as a in
       let@ () = add_c (t_ (eq__ patv v1)) in
(*       let@ () = fin () in *)
       check_texpr labels e2 typ
    | M_Ewseq (p, e1, e2)
    | M_Esseq (p, e1, e2) ->
       let@ patv, (l, a) = pattern_match p in
       let@ fin = begin_trace_of_step (Some (Mu.M_Pat p)) e1 in
       let@ rt1 = check_expr labels ~expect:(IT.bt patv) e1 in
       let oprefix = match e1 with
         | M_Expr (_, _, M_Eccall (_, M_Pexpr (_, _, _, M_PEsym fsym), _)) -> 
            Sym.has_id fsym
         (* | M_Expr (_, _, M_Eaction (M_Paction (_, M_Action (_, M_Store _)))) -> *)
         (*    Some "store" *)
         (* | M_Expr (_, _, M_Eaction (M_Paction (_, M_Action (_, M_Load _)))) -> *)
         (*    Some "load" *)
         (* | M_Expr (_, _, M_Eaction (M_Paction (_, M_Action (_, M_Create _)))) -> *)
         (*    Some "create" *)
         | _ -> None
       in
       let@ (bt, s') = bind_logically (oprefix, Some (Loc loc)) rt1 in
       let@ () = add_ls l in
       let@ () = add_as a in
       let@ () = add_c (t_ (def_ s' patv)) in
       let@ () = fin () in
       let@ () = check_texpr labels e2 typ in
       return ()
    | M_Edone e ->
       begin match typ with
       | Normal (Computational ((return_s, return_bt), info, lrt)) ->
          let@ (returned_rt) = check_expr labels ~expect:return_bt e in
          let@ (arg_bt, arg_s) = bind_logically (None, Some (Loc loc)) returned_rt in
          let lrt = LRT.subst (IT.make_subst [(return_s, sym_ (arg_s, arg_bt))]) lrt in
          let@ () = Spine.subtype loc lrt in
          let@ () = all_empty loc in
          return ()
       | False ->
          let err = 
            "This expression returns but is expected "^
              "to have non-return type."
          in
          fail (fun _ -> {loc; msg = Generic !^err})
       end
    | M_Erun (label_sym, pes) ->
       let@ (lt,lkind) = match SymMap.find_opt label_sym labels with
         | None -> fail (fun _ -> {loc; msg = Generic (!^"undefined code label" ^/^ Sym.pp label_sym)})
         | Some (lt,lkind) -> return (lt,lkind)
       in
       let@ () = Spine.calltype_lt loc pes (lt,lkind) in
       let@ () = all_empty loc in
       return ()

  in
  return result


and check_texpr_in locs labels e typ =
  let@ loc_trace = get_loc_trace () in
  in_loc_trace (locs @ loc_trace) (fun () -> check_texpr labels e typ)


let check_pexpr_rt loc pexpr (RT.Computational ((return_s, return_bt), info, lrt)) =
  let@ lvt = check_pexpr pexpr ~expect:return_bt in
  let lrt = LRT.subst (IT.make_subst [(return_s, lvt)]) lrt in
  let@ () = Spine.subtype loc lrt in
  let@ () = all_empty loc in
  return ()


let check_and_bind_arguments rt_subst loc arguments (function_typ : 'rt AT.t) = 
  let rec check args (ftyp : 'rt AT.t) =
    match args, ftyp with
    | ((aname, abt) :: args), (AT.Computational ((lname, sbt), _info, ftyp)) ->
       if BT.equal abt sbt then
         let new_lname = Sym.fresh_same aname in
         let subst = make_subst [(lname, sym_ (new_lname, sbt))] in
         let ftyp' = AT.subst rt_subst subst ftyp in
         let@ () = add_l new_lname abt in
         let@ () = add_a aname (abt,new_lname) in
         check args ftyp'
       else
         fail (fun _ -> {loc; msg = Mismatch {has = BT.pp abt; expect = BT.pp sbt}})
    | [], (AT.Computational (_, _, _))
    | (_ :: _), (AT.L _) ->
       let expect = AT.count_computational function_typ in
       let has = List.length arguments in
       fail (fun _ -> {loc; msg = Number_arguments {expect; has}})
    | [], AT.L ftyp ->
       let open LAT in
       let rec bind resources = function
         | Define ((sname, it), _, ftyp) ->
            let@ () = add_l sname (IT.bt it) in
            let@ () = add_c (t_ (def_ sname it)) in
            bind resources ftyp
         | Resource ((s, (re, bt)), _, ftyp) ->
            let@ () = add_l s bt in
            bind ((re, O (sym_ (s, bt))) :: resources) ftyp
         | Constraint (lc, _, ftyp) ->
            let@ () = add_c lc in
            bind resources ftyp
         | I rt ->
            return (rt, resources)
       in
       bind [] ftyp
  in
  check arguments function_typ


(* let do_post_typing info = *)
(*   let eqs_data = List.filter_map (function *)
(*     | SuggestEqsData x -> Some x) info *)
(*   in *)
(*   SuggestEqs.warn_missing_spec_eqs eqs_data; *)
(*   return () *)


(* check_function: type check a (pure) function *)
let check_function 
      (loc : loc) 
      (info : string) 
      (arguments : (Sym.t * BT.t) list) 
      (rbt : BT.t) 
      (body : 'bty mu_pexpr) 
      (function_typ : AT.ft)
    : (unit, type_error) Typing.m =
  debug 2 (lazy (headline ("checking function " ^ info)));
  pure begin
      let@ (rt, resources) = 
        check_and_bind_arguments RT.subst loc arguments function_typ 
      in
      let@ () = ListM.iterM (add_r (Some (Label "start"))) resources in
      (* rbt consistency *)
      let@ () = 
        let Computational ((sname, sbt), _info, t) = rt in
        WellTyped.ensure_base_type loc ~expect:sbt rbt
      in
      check_pexpr_rt loc body rt
    end

(* check_procedure: type check an (impure) procedure *)
let check_procedure 
      (loc : loc) 
      (fsym : Sym.t)
      (arguments : (Sym.t * BT.t) list)
      (rbt : BT.t) 
      (body : 'bty mu_texpr)
      (function_typ : AT.ft) 
      (label_defs : 'bty mu_label_defs)
    : (unit, type_error) Typing.m =
  debug 2 (lazy (headline ("checking procedure " ^ Sym.pp_string fsym)));
  debug 2 (lazy (item "type" (AT.pp RT.pp function_typ)));

  pure begin 
      (* check and bind the function arguments *)
      let@ ((rt, label_defs), resources) = 
        let function_typ = AT.map (fun rt -> (rt, label_defs)) function_typ in
        let rt_and_label_defs_subst substitution (rt, label_defs) = 
          (RT.subst substitution rt, 
           subst_label_defs (AT.subst False.subst) substitution label_defs)
        in
        check_and_bind_arguments rt_and_label_defs_subst
          loc arguments function_typ 
      in
      (* rbt consistency *)
      let@ () = 
        let Computational ((sname, sbt), _info, t) = rt in
        WellTyped.ensure_base_type loc ~expect:sbt rbt
      in
      (* check well-typedness of labels and record their types *)
      let@ labels = 
        PmapM.foldM (fun sym def acc ->
            pure begin 
                match def with
                | M_Return (loc, lt) ->
                   let@ () = WellTyped.WLT.welltyped "return label" loc lt in
                   return (SymMap.add sym (lt, Return) acc)
                | M_Label (loc, lt, _, _, annots) -> 
                   let label_kind = match CF.Annot.get_label_annot annots with
                     | Some (LAloop_body loop_id) -> Loop
                     | Some (LAloop_continue loop_id) -> Loop
                     | _ -> Other
                   in
                   let@ () = WellTyped.WLT.welltyped "label" loc lt in
                   return (SymMap.add sym (lt, label_kind) acc)
              end
          ) label_defs SymMap.empty 
      in
      (* check each label *)
      let check_label lsym def =
        pure begin 
          match def with
          | M_Return (loc, lt) ->
             return ()
          | M_Label (loc, lt, args, body, annots) ->
             debug 2 (lazy (headline ("checking label " ^ Sym.pp_string lsym)));
             debug 2 (lazy (item "type" (AT.pp False.pp lt)));
             let label_name = match Sym.description lsym with
               | Sym.SD_Id l -> l
               | _ -> Debug_ocaml.error "label without name"
             in
             let@ (rt, resources) = 
               check_and_bind_arguments False.subst loc args lt 
             in
             let@ () = ListM.iterM (add_r (Some (Label label_name))) resources in
             let@ () = check_texpr_in [loc] labels body False in
             return ()
          end
      in
      let check_body () = 
        pure begin 
            debug 2 (lazy (headline ("checking function body " ^ Sym.pp_string fsym)));
            let@ () = ListM.iterM (add_r (Some (Label "start"))) resources in
            check_texpr labels body (Normal rt)
          end
      in
      let@ () = check_body () in
      let@ () = PmapM.iterM check_label label_defs in
      return ()
    end

 

let only = ref None


let check mu_file = 
  let () = Debug_ocaml.begin_csv_timing "total" in

  let () = Debug_ocaml.begin_csv_timing "tagDefs" in
  let@ () = 
    (* check and record tagDefs *)
    let@ () = 
      PmapM.iterM (fun tag def ->
          match def with
          | M_UnionDef _ -> unsupported Loc.unknown !^"todo: union types"
          | M_StructDef layout -> add_struct_decl tag layout
        ) mu_file.mu_tagDefs
    in
    let@ () = 
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
        ) mu_file.mu_tagDefs
    in
    return ()
  in
  let () = Debug_ocaml.end_csv_timing "tagDefs" in


  let () = Debug_ocaml.begin_csv_timing "impls" in
  (* let@ () =  *)
  (*   (\* check and record impls *\) *)
  (*   let open Global in *)
  (*   PmapM.iterM (fun impl impl_decl -> *)
  (*       let descr = CF.Implementation.string_of_implementation_constant impl in *)
  (*       match impl_decl with *)
  (*       | M_Def (rt, rbt, pexpr) ->  *)
  (*          let@ () = WellTyped.WRT.welltyped Loc.unknown rt in *)
  (*          let@ () = WellTyped.WBT.is_bt Loc.unknown rbt in *)
  (*          let@ () = check_function Loc.unknown descr [] rbt pexpr (AT.L (LAT.I rt)) in *)
  (*          add_impl_constant impl rt *)
  (*       | M_IFun (ft, rbt, args, pexpr) -> *)
  (*          let@ () = WellTyped.WFT.welltyped "implementation-defined function" Loc.unknown ft in *)
  (*          let@ () = WellTyped.WBT.is_bt Loc.unknown rbt in *)
  (*          let@ () = check_function Loc.unknown descr args rbt pexpr ft in *)
  (*          add_impl_fun_decl impl ft *)
  (*     ) mu_file.mu_impl *)
  (* in *)
  (* let () = Debug_ocaml.end_csv_timing "impls" in *)
  

  let () = Debug_ocaml.begin_csv_timing "logical predicates" in
  (* check and record logical predicate defs *)
  Pp.progress_simple "checking specifications" "logical predicate welltypedness";
  let@ () =
    ListM.iterM (fun (name, def) -> add_logical_predicate name def)
        mu_file.mu_logical_predicates
  in
  let@ () =
    ListM.iterM (fun (name,(def : LP.definition)) -> 
        let@ () = WellTyped.WLPD.welltyped def in
        Pp.debug 1 (lazy (Pp.item "logical predicate" (LP.pp_def (Sym.pp name) def)));
        return ()
      ) mu_file.mu_logical_predicates
  in
  let () = Debug_ocaml.end_csv_timing "logical predicates" in

  let () = Debug_ocaml.begin_csv_timing "resource predicates" in
  let@ () = 
    (* check and record resource predicate defs *)
    let@ () = 
      ListM.iterM (fun (name, def) -> add_resource_predicate name def)
        mu_file.mu_resource_predicates
    in
    Pp.progress_simple "checking specifications" "resource predicate welltypedness";
    let@ () = 
      ListM.iterM (fun (name,def) -> WellTyped.WRPD.welltyped def)
        mu_file.mu_resource_predicates
    in
    return ()
  in
  let () = Debug_ocaml.end_csv_timing "resource predicates" in


  let () = Debug_ocaml.begin_csv_timing "globals" in
  let@ () = 
    (* record globals *)
    (* TODO: check the expressions *)
    ListM.iterM (fun (sym, def) ->
        match def with
        | M_GlobalDef (lsym, (gbt, ct), _)
        | M_GlobalDecl (lsym, (gbt, ct)) ->
           let@ () = WellTyped.WBT.is_bt Loc.unknown gbt in
           let@ () = WellTyped.WCT.is_ct Loc.unknown ct in
           let bt = Loc in
           let@ () = add_l lsym bt in
           let@ () = add_a sym (bt, lsym) in
           let@ () = add_c (t_ (IT.good_pointer ~pointee_ct:ct (sym_ (lsym, bt)))) in
           return ()
      ) mu_file.mu_globs 
  in
  let () = Debug_ocaml.end_csv_timing "globals" in

  let@ () =
    PmapM.iterM
      (fun fsym (M_funinfo (loc, _attrs, ftyp, trusted, _has_proto)) ->
        (* let lc1 = t_ (ne_ (null_, sym_ (fsym, Loc))) in *)
        (* let lc2 = t_ (representable_ (Pointer Void, sym_ (fsym, Loc))) in *)
        (* let@ () = add_l fsym Loc in *)
        (* let@ () = add_cs [lc1; lc2] in *)
        add_fun_decl fsym (loc, ftyp, trusted)
      ) mu_file.mu_funinfo
  in

  let () = Debug_ocaml.begin_csv_timing "welltypedness" in
  let@ () =
    Pp.progress_simple "checking specifications" "function welltypedness";
    PmapM.iterM
      (fun fsym (M_funinfo (loc, _attrs, ftyp, _trusted, _has_proto)) ->
        match !only with
        | Some fname when not (String.equal fname (Sym.pp_string fsym)) ->
           return ()
        | _ ->
           let () = debug 2 (lazy (headline ("checking welltypedness of procedure " ^ Sym.pp_string fsym))) in
           let () = debug 2 (lazy (item "type" (AT.pp RT.pp ftyp))) in
           WellTyped.WFT.welltyped "global" loc ftyp
      ) mu_file.mu_funinfo
  in
  let () = Debug_ocaml.end_csv_timing "welltypedness" in

  let check_function =
    fun fsym fn ->
    let@ (loc, ftyp, trusted) = get_fun_decl Locations.unknown fsym in
    let () = Debug_ocaml.begin_csv_timing "functions" in
    let start = time_log_start "function" (CF.Pp_symbol.to_string fsym) in
    let@ () = match trusted, fn with
      | Trusted _, _ -> 
         return ()
      | Checked, M_Fun (rbt, args, body) ->
         check_function loc (Sym.pp_string fsym) args rbt body ftyp
      | Checked, M_Proc (loc', rbt, args, body, labels) ->
         check_procedure loc fsym args rbt body ftyp labels
      | _, (M_ProcDecl _ | M_BuiltinDecl _) -> (* TODO: ? *) 
         return ()
    in
    Debug_ocaml.end_csv_timing "functions";
    time_log_end start;
    return ()
  in

  let () = Debug_ocaml.begin_csv_timing "check stdlib" in
  let@ () = PmapM.iterM check_function mu_file.mu_stdlib in
  let () = Debug_ocaml.end_csv_timing "check stdlib" in
  let () = Debug_ocaml.begin_csv_timing "check functions" in
  let@ () = 
    let number_entries = List.length (Pmap.bindings_list mu_file.mu_funs) in
    let ping = Pp.progress "checking function" number_entries in
    PmapM.iterM (fun fsym fn ->
        match !only with
        | Some fname when not (String.equal fname (Sym.pp_string fsym)) ->
           return ()
        | _ ->
        let@ () = return (ping (Sym.pp_string fsym)) in
        let@ () = check_function fsym fn in
        return ()
      ) mu_file.mu_funs 
  in
  let () = Debug_ocaml.end_csv_timing "check functions" in


  let () = Debug_ocaml.end_csv_timing "total" in

  return ()





(* TODO: 
   - sequencing strength
   - rem_t vs rem_f
   - check globals with expressions
   - inline TODOs
 *)
