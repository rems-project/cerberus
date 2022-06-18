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
  let rec aux pat : (IT.t, type_error) m = 
    let (M_Pattern (loc, _, pattern) : mu_pattern) = pat in
    match pattern with
    | M_CaseBase (o_s, has_bt) ->
       let@ () = WellTyped.WBT.is_bt loc has_bt in
       let lsym = Sym.fresh () in 
       let@ () = add_l lsym has_bt in
       begin match o_s with
       | Some s -> 
          let@ () = add_a s (has_bt, lsym) in
          return (sym_ (lsym, has_bt))
       | None -> 
          return (sym_ (lsym, has_bt))
       end
    | M_CaseCtor (constructor, pats) ->
       match constructor, pats with
       | M_Cnil item_bt, [] ->
          let@ () = WellTyped.WBT.is_bt loc item_bt in
          return (IT.nil_ ~item_bt)
       | M_Cnil item_bt, _ ->
          let@ () = WellTyped.WBT.is_bt loc item_bt in
          fail (fun _ -> {loc; msg = Number_arguments {has = List.length pats; expect = 0}})
       | M_Ccons, [p1; p2] ->
          let@ it1 = aux p1 in
          let@ it2 = aux p2 in
          let@ () = WellTyped.ensure_base_type loc ~expect:(List (IT.bt it1)) (IT.bt it2) in
          return (cons_ (it1, it2))
       | M_Ccons, _ -> 
          fail (fun _ -> {loc; msg = Number_arguments {has = List.length pats; expect = 2}})
       | M_Ctuple, pats ->
          let@ its = ListM.mapM aux pats in
          return (tuple_ its)
       | M_Cspecified, [pat] ->
          aux pat
       | M_Cspecified, _ ->
          fail (fun _ -> {loc; msg = Number_arguments {expect = 1; has = List.length pats}})
       | M_Carray, _ ->
          Debug_ocaml.error "todo: array types"
  in
  fun to_match ((M_Pattern (loc, _, _)) as pat : mu_pattern) ->
  let@ it = aux pat in
  let@ () = WellTyped.ensure_base_type loc ~expect:(IT.bt to_match) (IT.bt it) in
  add_c (t_ (eq_ (it, to_match)))





let rec bind_logical where (lrt : LRT.t) = 
  match lrt with
  | Define ((s, it), oinfo, rt) ->
     let s, rt = LRT.alpha_rename (s, IT.bt it) rt in
     let@ () = add_l s (IT.bt it) in
     let@ () = add_c (LC.t_ (IT.def_ s it)) in
     bind_logical where rt
  | Resource ((s, (re, oarg_spec)), _oinfo, rt) -> 
     let s, rt = LRT.alpha_rename (s, oarg_spec) rt in
     let@ () = add_l s oarg_spec in
     let@ () = add_r where (re, O (sym_ (s, oarg_spec))) in
     bind_logical where rt
  | Constraint (lc, _oinfo, rt) -> 
     let@ () = add_c lc in
     bind_logical where rt
  | I -> 
     return ()

let bind_computational where (name : Sym.t) (rt : RT.t) =
  let Computational ((s, bt), _oinfo, rt) = rt in
  let s' = Sym.fresh () in
  let rt' = LRT.subst (IT.make_subst [(s, IT.sym_ (s', bt))]) rt in
  let@ () = add_l s' bt in
  let@ () = add_a name (bt, s') in
  bind_logical where rt'


let bind where (name : Sym.t) (rt : RT.t) =
  bind_computational where name rt

let bind_logically where (rt : RT.t) : ((BT.t * Sym.t), type_error) m =
  let Computational ((s, bt), _oinfo, rt) = rt in
  let s' = Sym.fresh () in
  let rt' = LRT.subst (IT.make_subst [(s, IT.sym_ (s', bt))]) rt in
  let@ () = add_l s' bt in
  let@ () = bind_logical where rt' in
  return (bt, s')

type lvt = {loc : Loc.t; value : IT.t}
type lvts = lvt list


let bind_lvt sym lvt = 
  let s' = Sym.fresh () in
  let@ () = add_l s' (IT.bt lvt.value) in
  let@ () = add_a sym (IT.bt lvt.value, s') in
  add_c (t_ (def_ s' lvt.value))



let rt_of_lvt lvt = 
  let sym = Sym.fresh () in
  RT.Computational ((sym, IT.bt lvt.value), (Loc.unknown, None),
  LRT.Constraint (t_ (def_ sym lvt.value), (Loc.unknown, None),
  LRT.I))



(* The pattern-matching might de-struct 'bt'. For easily making
   constraints carry over to those values, record (lname,bound) as a
   logical variable and record constraints about how the variables
   introduced in the pattern-matching relate to (lname,bound). *)
let pattern_match_rt loc (pat : mu_pattern) (rt : RT.t) : (unit, type_error) m =
  let@ (bt, s') = bind_logically (Some loc) rt in
  pattern_match (sym_ (s', bt)) pat





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




(* info gathered during spine judgements, per path through a
   function/procedure, which are only useful once this has completed
   for all paths *)
type per_path_info_entry =
  SuggestEqsData of SuggestEqs.constraint_analysis
type per_path = per_path_info_entry list


module Spine : sig
  val calltype_ft : 
    Loc.t -> lvts -> AT.ft -> (RT.t * per_path, type_error) m
  val calltype_ift : 
    Loc.t -> lvts -> AT.ift -> (IT.t * per_path, type_error) m
  val calltype_lft : 
    Loc.t -> LAT.lft -> (LRT.t * per_path, type_error) m
  val calltype_lt : 
    Loc.t -> lvts -> AT.lt * label_kind -> (per_path, type_error) m
  val calltype_packing : 
    Loc.t -> Sym.t -> LAT.packing_ft -> (OutputDef.t * per_path, type_error) m
  val subtype : 
    Loc.t -> lvt -> RT.t -> (per_path, type_error) m
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




  let spine_l rt_subst rt_pp loc situation ftyp = 

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
      let@ provable = provable loc in
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
                                 situation; oinfo = Some info; model; trace; ctxt} in
                    {loc; msg}
                  )

             | Some (re, O oargs) ->
                assert (ResourceTypes.equal re resource);
                return oargs
           in
           check cs (LAT.subst rt_subst (IT.make_subst [(s, oargs)]) ftyp)
        | Define ((s, it), info, ftyp) ->
           let s' = Sym.fresh () in
           let bt = IT.bt it in
           let@ () = add_l s' bt in
           let@ () = add_c (LC.t_ (def_ s' it)) in
           check cs (LAT.subst rt_subst (IT.make_subst [(s, sym_ (s', bt))]) ftyp)
        | Constraint (c, info, ftyp) -> 
           let@ () = return (debug 9 (lazy (item "checking constraint" (LC.pp c)))) in
           let res = provable c in
           begin match res with
           | `True -> check (c :: cs) ftyp
           | `False ->
              let@ model = model () in
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

    let@ constraints = all_constraints () in
    let per_path = SuggestEqs.eqs_from_constraints (LCSet.elements constraints) cs
      |> Option.map (fun x -> SuggestEqsData x) |> Option.to_list in

    let@ () = return (debug 9 (lazy !^"done")) in
    time_log_end start_spine;
    return (rt, per_path)


  let spine rt_subst rt_pp loc situation args ftyp =

    let open ArgumentTypes in

    let original_ftyp = ftyp in
    let original_args = args in

    let@ () = print_with_ctxt (fun ctxt ->
        debug 6 (lazy (checking_situation situation));
        debug 6 (lazy (item "ctxt" (Context.pp ctxt)));
        debug 6 (lazy (item "spec" (pp rt_pp ftyp)))
      )
    in

    let@ ftyp = 
      let rec check args ftyp = 
        match args, ftyp with
        | (arg :: args), (Computational ((s, bt), _info, ftyp)) ->
           if BT.equal (IT.bt arg.value) bt then
             check args (subst rt_subst (make_subst [(s, arg.value)]) ftyp)
           else
             fail (fun _ -> {loc = arg.loc; msg = Mismatch {has = IT.bt arg.value; expect = bt}})
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


  let calltype_ft loc args (ftyp : AT.ft) : (RT.t * per_path, type_error) m =
    spine RT.subst RT.pp loc FunctionCall args ftyp

  let calltype_ift loc args (ftyp : AT.ift) : (IT.t * per_path, type_error) m =
    spine IT.subst IT.pp loc FunctionCall args ftyp

  let calltype_lft loc (ftyp : LAT.lft) : (LRT.t * per_path, type_error) m =
    spine_l LRT.subst LRT.pp loc FunctionCall ftyp

  let calltype_lt loc args ((ltyp : AT.lt), label_kind) : (per_path, type_error) m =
    let@ (False.False, per_path) =
      spine False.subst False.pp 
        loc (LabelCall label_kind) args ltyp
    in
    return per_path

  let calltype_packing loc (name : Sym.t) (ft : LAT.packing_ft)
        : (OutputDef.t * per_path, type_error) m =
    spine_l OutputDef.subst OutputDef.pp 
      loc (PackPredicate name) ft

  (* The "subtyping" judgment needs the same resource/lvar/constraint
     inference as the spine judgment. So implement the subtyping
     judgment 'arg <: RT' by type checking 'f(arg)' for 'f: RT -> False'. *)
  let subtype (loc : loc) arg (rtyp : RT.t) : (per_path, type_error) m =
    let ft = AT.of_rt rtyp (LAT.I False.False) in
    let@ (False.False, per_path) =
      spine False.subst False.pp loc Subtyping [arg] ft in
    return per_path


end


(*** pure value inference *****************************************************)


let check_computational_bound loc s = 
  let@ is_bound = bound_a s in
  if is_bound then return () 
  else fail (fun _ -> {loc; msg = Unknown_variable s})

(* let arg_of_sym (loc : loc) (sym : Sym.t) : (arg, type_error) m =  *)
(*   let@ () = check_computational_bound loc sym in *)
(*   let@ (bt,lname) = get_a sym in *)
(*   return {value = sym_ (lname, bt); loc} *)


let infer_array loc (args : lvts) : (lvt, type_error) m = 
  let item_bt = match args with
    | [] -> Debug_ocaml.error "todo: empty arrays"
    | arg :: _ -> IT.bt arg.value
  in
  let@ (_, value) = 
    ListM.fold_leftM (fun (index,it) arg -> 
        let@ () = WellTyped.ensure_base_type arg.loc 
                    ~expect:item_bt (IT.bt arg.value) in
        return (index + 1, map_set_ it (int_ index, arg.value))
         ) (0, const_map_ Integer (default_ item_bt)) args
  in
  return {value;loc}


let infer_constructor (loc : loc) (constructor : mu_ctor) 
                      (args : lvts) : (lvt, type_error) m = 
  match constructor, args with
  | M_Ctuple, _ -> 
     return {loc; value = tuple_ (List.map (fun arg -> arg.value) args)}
  | M_Carray, args -> 
     infer_array loc args
  | M_Cspecified, [arg] ->
     return {loc; value = arg.value}
  | M_Cspecified, _ ->
     fail (fun _ -> {loc; msg = Number_arguments {has = List.length args; expect = 1}})
  | M_Cnil item_bt, [] -> 
     let@ () = WellTyped.WBT.is_bt loc item_bt in
     return {loc; value = nil_ ~item_bt}
  | M_Cnil item_bt, _ -> 
     fail (fun _ -> {loc; msg = Number_arguments {has = List.length args; expect=0}})
  | M_Ccons, [arg1; arg2] -> 
     let@ () = WellTyped.ensure_base_type arg2.loc 
                 ~expect:(BT.List (IT.bt arg1.value)) (IT.bt arg2.value) in
     return {loc; value = cons_ (arg1.value, arg2.value)}
  | M_Ccons, _ ->
     fail (fun _ -> {loc; msg = Number_arguments {has = List.length args; expect = 2}})



let infer_ptrval (loc : loc) (ptrval : pointer_value) : (lvt, type_error) m =
  CF.Impl_mem.case_ptrval ptrval
    ( fun ct -> 
      let sct = Retype.ct_of_ct loc ct in
      let@ () = WellTyped.WCT.is_ct loc sct in
      return {loc; value = IT.null_} )
    ( fun sym -> 
      (* just to make sure it exists *)
      let@ _ = get_fun_decl loc sym in
      return {loc; value = sym_ (sym, BT.Loc)} ) 
    ( fun _prov p -> 
      return {loc; value = pointer_ p} )

let rec infer_mem_value (loc : loc) (mem : mem_value) : (lvt, type_error) m =
  CF.Impl_mem.case_mem_value mem
    ( fun ct -> 
      let@ () = WellTyped.WCT.is_ct loc (Retype.ct_of_ct loc ct) in
      fail (fun _ -> {loc; msg = Unspecified ct}) )
    ( fun _ _ -> 
      unsupported loc !^"infer_mem_value: concurrent read case" )
    ( fun ity iv -> 
      (* TODO: do anything with ity? *)
      return {loc; value = int_ (Memory.int_of_ival iv)} )
    ( fun ft fv -> 
      unsupported loc !^"floats" )
    ( fun ct ptrval -> 
      (* TODO: do anything else with ct? *)
      let@ () = WellTyped.WCT.is_ct loc (Retype.ct_of_ct loc ct) in
      infer_ptrval loc ptrval  )
    ( fun mem_values -> 
      let@ vts = ListM.mapM (infer_mem_value loc) mem_values in
      infer_array loc vts )
    ( fun tag mvals -> 
      let mvals = List.map (fun (member, _, mv) -> (member, mv)) mvals in
      infer_struct loc tag mvals )
    ( fun tag id mv -> 
      infer_union loc tag id mv )

and infer_struct (loc : loc) (tag : tag) 
                 (member_values : (member * mem_value) list) : (lvt, type_error) m =
  (* might have to make sure the fields are ordered in the same way as
     in the struct declaration *)
  let@ layout = get_struct_decl loc tag in
  let rec check fields spec =
    match fields, spec with
    | ((member, mv) :: fields), ((smember, sct) :: spec) 
         when Id.equal member smember ->
       let@ member_lvt = infer_mem_value loc mv in
       let@ () = WellTyped.ensure_base_type loc 
                   ~expect:(BT.of_sct sct) (IT.bt member_lvt.value) in
       let@ member_its = check fields spec in
       return ((member, member_lvt.value) :: member_its)
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
  return {loc; value = IT.struct_ (tag, member_its)}

and infer_union (loc : loc) (tag : tag) (id : Id.t) 
                (mv : mem_value) : (lvt, type_error) m =
  Debug_ocaml.error "todo: union types"

let rec infer_object_value (loc : loc)
                       (ov : 'bty mu_object_value) : (lvt, type_error) m =
  match ov with
  | M_OVinteger iv ->
     return {loc; value = z_ (Memory.z_of_ival iv)}
  | M_OVpointer p -> 
     infer_ptrval loc p
  | M_OVarray items ->
     let@ vts = ListM.mapM (infer_loaded_value loc) items in
     infer_array loc vts
  | M_OVstruct (tag, fields) -> 
     let mvals = List.map (fun (member,_,mv) -> (member, mv)) fields in
     infer_struct loc tag mvals       
  | M_OVunion (tag, id, mv) -> 
     infer_union loc tag id mv
  | M_OVfloating iv ->
     unsupported loc !^"floats"

and infer_loaded_value loc (M_LVspecified ov) =
  infer_object_value loc ov

let rec infer_value (loc : loc) (v : 'bty mu_value) : (lvt, type_error) m = 
  match v with
  | M_Vobject ov ->
     infer_object_value loc ov
  | M_Vloaded lv ->
     infer_loaded_value loc lv
  | M_Vunit ->
     return {loc; value = IT.unit_}
  | M_Vtrue ->
     return {loc; value = IT.bool_ true}
  | M_Vfalse -> 
     return {loc; value = IT.bool_ false}
  | M_Vlist (bt, vals) ->
     let@ () = WellTyped.WBT.is_bt loc bt in
     let@ its = 
       ListM.mapM (fun v -> 
           let@ i_lvt = infer_value loc v in
           let@ () = WellTyped.ensure_base_type i_lvt.loc 
                       ~expect:bt (IT.bt i_lvt.value) in
           return i_lvt.value
         ) vals
     in
     return {loc; value = list_ ~item_bt:bt its}
  | M_Vtuple vals ->
     let@ lvts = ListM.mapM (infer_value loc) vals in
     let value = tuple_ (List.map (fun lvt -> lvt.value) lvts) in
     return {loc; value}




(*** pure expression inference ************************************************)


let infer_array_shift loc arg1 (loc_ct, ct) arg2 =
  let@ () = WellTyped.WCT.is_ct loc_ct ct in
  let@ () = WellTyped.ensure_base_type arg1.loc ~expect:Loc (IT.bt arg1.value) in
  let@ () = WellTyped.ensure_base_type arg2.loc ~expect:Integer (IT.bt arg2.value) in
  let value = arrayShift_ (arg1.value, ct, arg2.value) in
  return {loc; value}


let wrapI loc ity arg =
  (* try to follow wrapI from runtime/libcore/std.core *)
  let maxInt = Memory.max_integer_type ity in
  let minInt = Memory.min_integer_type ity in
  let dlt = Z.add (Z.sub maxInt minInt) (Z.of_int 1) in
  let r = rem_f_ (arg, z_ dlt) in
  let value = ite_ (le_ (r, z_ maxInt), r, sub_ (r, z_ dlt)) in
  {value; loc}



let conv_int loc (act : _ act) arg = 
  let@ () = WellTyped.WCT.is_ct act.loc act.ct in
  let@ () = WellTyped.ensure_base_type arg.loc ~expect:Integer (IT.bt arg.value) in
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
                    {value = arg.value; ict = act.ct; ctxt; model} in
        {loc; msg}
      )
  in
  let@ value = match ity with
    | Bool ->
       return (ite_ (eq_ (arg.value, int_ 0), int_ 0, int_ 1))
    | _ when Sctypes.is_unsigned_integer_type ity ->
       begin match provable (t_ (representable_ (act.ct, arg.value))) with
       | `True -> return arg.value
       | `False ->
          return
            (ite_ (representable_ (act.ct, arg.value),
                   arg.value, 
                   (wrapI loc ity arg.value).value))
       end
    | _ ->
       begin match provable (t_ (representable_ (act.ct, arg.value))) with
       | `True -> return arg.value
       | `False -> fail_unrepresentable ()
       end
  in
  return {loc; value}


(* could potentially return a vt instead of an RT.t *)
let rec infer_pexpr (pe : 'bty mu_pexpr) : (lvt, type_error) m =
  let (M_Pexpr (loc, _annots, _bty, pe_)) = pe in
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
       return {loc; value = sym_ (lname, bt)}
    (* | M_PEimpl i -> *)
    (*    let@ global = get_global () in *)
    (*    let value = Global.get_impl_constant global i in *)
    (*    return {loc; value} *)
    | M_PEval v ->
       infer_value loc v
    | M_PEconstrained _ ->
       Debug_ocaml.error "todo: PEconstrained"
    | M_PEctor (ctor, pes) ->
       let@ args = ListM.mapM infer_pexpr pes in
       infer_constructor loc ctor args
    | M_CivCOMPL _ ->
       Debug_ocaml.error "todo: CivCOMPL"
    | M_CivAND _ ->
       Debug_ocaml.error "todo: CivAND"
    | M_CivOR _ ->
       Debug_ocaml.error "todo: CivOR"
    | M_CivXOR (act, pe1, pe2) -> 
       (* let ity = match act.ct with *)
       (*   | Integer ity -> ity *)
       (*   | _ -> Debug_ocaml.error "M_CivXOR with non-integer c-type" *)
       (* in *)
       let@ arg1 = infer_pexpr pe1 in
       let@ arg2 = infer_pexpr pe2 in
       let@ () = WellTyped.ensure_base_type arg1.loc ~expect:Integer (IT.bt arg1.value) in
       let@ () = WellTyped.ensure_base_type arg2.loc ~expect:Integer (IT.bt arg2.value) in
       let value = xor_ (arg1.value, arg2.value) in
       (* let result = wrapI ity xor_unbounded in *)
       return {loc; value}
    | M_Cfvfromint _ -> 
       unsupported loc !^"floats"
    | M_Civfromfloat (act, _) -> 
       let@ () = WellTyped.WCT.is_ct act.loc act.ct in
       unsupported loc !^"floats"
    | M_PEarray_shift (pe1, ct, pe2) ->
       let@ arg1 = infer_pexpr pe1 in
       let@ arg2 = infer_pexpr pe2 in
       infer_array_shift loc arg1 (loc, ct) arg2
    | M_PEmember_shift (pe, tag, member) ->
       let@ arg = infer_pexpr pe in
       let@ () = WellTyped.ensure_base_type arg.loc ~expect:Loc (IT.bt arg.value) in
       let@ layout = get_struct_decl loc tag in
       let@ _member_bt = get_member_type loc tag member layout in
       let value = memberShift_ (arg.value, tag, member) in
       return {loc; value}
    | M_PEnot pe ->
       let@ arg = infer_pexpr pe in
       let@ () = WellTyped.ensure_base_type arg.loc ~expect:Bool (IT.bt arg.value) in
       let value = not_ arg.value in
       return {loc; value}
    | M_PEop (op, pe1, pe2) ->
       let@ arg1 = infer_pexpr pe1 in
       let@ arg2 = infer_pexpr pe2 in
       let v1 = arg1.value in
       let v2 = arg2.value in
       let@ ((ebt1, ebt2), value) = match op with
         | OpAdd ->   return ((Integer, Integer), IT.add_ (v1, v2))
         | OpSub ->   return ((Integer, Integer), IT.sub_ (v1, v2))
         | OpMul ->   return ((Integer, Integer), IT.mul_ (v1, v2))
         | OpDiv ->   return ((Integer, Integer), IT.div_ (v1, v2))
         | OpRem_f -> return ((Integer, Integer), IT.rem_f_ (v1, v2))
         | OpExp ->   return ((Integer, Integer), IT.exp_no_smt_ (v1, v2))
         | OpEq ->    return ((Integer, Integer), IT.eq_ (v1, v2))
         | OpGt ->    return ((Integer, Integer), IT.gt_ (v1, v2))
         | OpLt ->    return ((Integer, Integer), IT.lt_ (v1, v2))
         | OpGe ->    return ((Integer, Integer), IT.ge_ (v1, v2))
         | OpLe ->    return ((Integer, Integer), IT.le_ (v1, v2))
         | OpAnd ->   return ((Bool, Bool), IT.and_ [v1; v2])
         | OpOr ->    return ((Bool, Bool), IT.or_ [v1; v2])
         | OpRem_t -> 
            let@ provable = provable loc in
            begin match provable (LC.T (and_ [le_ (int_ 0, v1); le_ (int_ 0, v2)])) with
            | `True ->
               (* if the arguments are non-negative, then rem or mod should be sound to use for rem_t *)
               return ((Integer, Integer), IT.mod_ (v1, v2))
            | `False ->
               let@ model = model () in
               let err = !^"Unsupported: rem_t applied to negative arguments" in
               fail (fun ctxt ->
                   let msg = Generic_with_model {err; model; ctxt} in
                   {loc; msg}
                 )
            end
       in
       let@ () = WellTyped.ensure_base_type arg1.loc ~expect:ebt1 (IT.bt arg1.value) in
       let@ () = WellTyped.ensure_base_type arg2.loc ~expect:ebt2 (IT.bt arg2.value) in
       return {loc; value}
    | M_PEstruct _ ->
       Debug_ocaml.error "todo: PEstruct"
    | M_PEunion _ ->
       Debug_ocaml.error "todo: PEunion"
    | M_PEmemberof _ ->
       Debug_ocaml.error "todo: M_PEmemberof"
    | M_PEassert_undef (pe, _uloc, ub) ->
       let@ arg = infer_pexpr pe in
       let@ () = WellTyped.ensure_base_type arg.loc ~expect:Bool (IT.bt arg.value) in
       let@ provable = provable loc in
       begin match provable (t_ arg.value) with
       | `True -> 
          return {loc; value = unit_}
       | `False ->
          let@ model = model () in
          fail (fun ctxt -> {loc; msg = Undefined_behaviour {ub; ctxt; model}})
       end
    | M_PEbool_to_integer pe ->
       let@ arg = infer_pexpr pe in
       let@ () = WellTyped.ensure_base_type arg.loc ~expect:Bool (IT.bt arg.value) in
       let value = ite_ (arg.value, int_ 1, int_ 0) in
       return {loc; value}
    | M_PEconv_int (act, pe) ->
       let@ arg = infer_pexpr pe in
       conv_int loc act arg
    | M_PEconv_loaded_int (act, pe) ->
       let@ arg = infer_pexpr pe in
       conv_int loc act arg
    | M_PEwrapI (act, pe) ->
       let@ arg = infer_pexpr pe in
       let@ () = WellTyped.ensure_base_type arg.loc ~expect:Integer (IT.bt arg.value) in
       let ity = match act.ct with
         | Integer ity -> ity
         | _ -> Debug_ocaml.error "wrapI applied to non-integer type"
       in
       let value = wrapI loc ity arg.value in
       return value
  in
  debug 3 (lazy (item "type" (IT.pp lvt.value)));
  return lvt


let rec check_tpexpr (e : 'bty mu_tpexpr) (typ : RT.t) : (per_path, type_error) m =
  let (M_TPexpr (loc, _annots, _, e_)) = e in
  let@ () = print_with_ctxt (fun ctxt ->
      debug 3 (lazy (action "checking pure expression"));
      debug 3 (lazy (item "expr" (group (NewMu.pp_tpexpr e))));
      debug 3 (lazy (item "type" (RT.pp typ)));
      debug 3 (lazy (item "ctxt" (Context.pp ctxt)));
    )
  in
  match e_ with
  | M_PEif (pe, e1, e2) ->
     let@ carg = infer_pexpr pe in
     let@ () = WellTyped.ensure_base_type carg.loc ~expect:Bool (IT.bt carg.value) in
     let@ per_paths = ListM.mapM (fun (lc, e) ->
         pure begin
             let@ () = add_c (t_ lc) in
             let@ provable = provable loc in
             match provable (t_ (bool_ false)) with
             | `True -> return []
             | `False -> check_tpexpr_in [loc_of_tpexpr e; loc] e typ
           end
       ) [(carg.value, e1); (not_ carg.value, e2)] in
     return (List.concat per_paths)
  | M_PEcase (pe, pats_es) ->
     let@ arg = infer_pexpr pe in
     let@ per_paths = ListM.mapM (fun (pat, pe) ->
         pure begin
             let@ () = pattern_match arg.value pat in
             let@ provable = provable loc in
             match provable (t_ (bool_ false)) with
             | `True -> return []
             | `False -> check_tpexpr_in [loc_of_tpexpr pe; loc] pe typ
           end
       ) pats_es in
     return (List.concat per_paths)
  | M_PElet (p, e1, e2) ->
     let@ fin = begin_trace_of_pure_step (Some p) e1 in
     let@ arg1 = infer_pexpr e1 in
     let@ () = match p with
       | M_Symbol sym -> bind_lvt sym arg1
       | M_Pat pat -> pattern_match arg1.value pat
     in
     let@ () = fin () in
     check_tpexpr e2 typ
  | M_PEdone pe ->
     let@ arg = infer_pexpr pe in
     Spine.subtype loc arg typ
  | M_PEundef (_loc, ub) ->
     let@ provable = provable loc in
     begin match provable (t_ (bool_ false)) with
     | `True -> return []
     | `False ->
        let@ model = model () in
        fail (fun ctxt -> {loc; msg = Undefined_behaviour {ub; ctxt; model}})
     end
  | M_PEerror (err, pe) ->
     let@ arg = infer_pexpr pe in
     let@ provable = provable loc in
     begin match provable (t_ (bool_ false)) with
     | `True -> return []
     | `False ->
        let@ model = model () in
        fail (fun ctxt -> {loc; msg = StaticError {err; ctxt; model}})
     end


and check_tpexpr_in locs e typ =
  let@ loc_trace = get_loc_trace () in
  in_loc_trace (locs @ loc_trace) (fun () -> check_tpexpr e typ)

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
         fail (fun ctxt -> {loc; msg = Unused_resource {resource; ctxt; model}})
    ) all_resources


type labels = (AT.lt * label_kind) SymMap.t


let infer_expr labels (e : 'bty mu_expr) : (RT.t * per_path, type_error) m =
  let (M_Expr (loc, _annots, e_)) = e in
  let@ () = print_with_ctxt (fun ctxt ->
       debug 3 (lazy (action "inferring expression"));
       debug 3 (lazy (item "expr" (group (NewMu.pp_expr e))));
       debug 3 (lazy (item "ctxt" (Context.pp ctxt)));
    )
  in
  let@ result = match e_ with
    | M_Epure pe -> 
       let@ lvt = infer_pexpr pe in
       return (rt_of_lvt lvt, [])
    | M_Ememop memop ->
       let pointer_op op pe1 pe2 = 
         let@ arg1 = infer_pexpr pe1 in
         let@ arg2 = infer_pexpr pe2 in
         let@ () = WellTyped.ensure_base_type arg1.loc ~expect:Loc (IT.bt arg1.value) in
         let@ () = WellTyped.ensure_base_type arg2.loc ~expect:Loc (IT.bt arg2.value) in
         let lvt = {loc; value = op (arg1.value, arg2.value)} in
         return (rt_of_lvt lvt, [])
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
          let@ arg1 = infer_pexpr pe1 in
          let@ arg2 = infer_pexpr pe2 in
          let@ () = WellTyped.ensure_base_type arg1.loc ~expect:Loc (IT.bt arg1.value) in
          let@ () = WellTyped.ensure_base_type arg2.loc ~expect:Loc (IT.bt arg2.value) in
          (* copying and adapting from memory/concrete/impl_mem.ml *)
          let divisor = match act.ct with
            | Array (item_ty, _) -> Memory.size_of_ctype item_ty
            | ct -> Memory.size_of_ctype ct
          in
          let value =
            div_
              (sub_ (pointerToIntegerCast_ arg1.value,
                     pointerToIntegerCast_ arg2.value),
               int_ divisor)
          in
          return (rt_of_lvt {loc; value}, [])
       | M_IntFromPtr (act_from, act_to, pe) ->
          let@ () = WellTyped.WCT.is_ct act_from.loc act_from.ct in
          let@ () = WellTyped.WCT.is_ct act_to.loc act_to.ct in
          let@ arg = infer_pexpr pe in
          let@ () = WellTyped.ensure_base_type arg.loc ~expect:Loc (IT.bt arg.value) in
          let value = pointerToIntegerCast_ arg.value in
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
                   {loc; msg = Int_unrepresentable 
                                 {value = arg.value; ict; ctxt; model}}
                 )
            end
          in
          return (rt_of_lvt {loc; value}, [])
       | M_PtrFromInt (act_from, act2_to, pe) ->
          let@ () = WellTyped.WCT.is_ct act_from.loc act_from.ct in
          let@ () = WellTyped.WCT.is_ct act2_to.loc act2_to.ct in
          let@ arg = infer_pexpr pe in
          let@ () = WellTyped.ensure_base_type arg.loc ~expect:Integer (IT.bt arg.value) in
          let value = integerToPointerCast_ arg.value in
          return (rt_of_lvt {loc; value}, [])
       | M_PtrValidForDeref (act, pe) ->
          (* check *)
          let@ () = WellTyped.WCT.is_ct act.loc act.ct in
          let@ arg = infer_pexpr pe in
          let@ () = WellTyped.ensure_base_type arg.loc ~expect:Loc (IT.bt arg.value) in
          let value = aligned_ (arg.value, act.ct) in
          return (rt_of_lvt {loc; value}, [])
       | M_PtrWellAligned (act, pe) ->
          let@ () = WellTyped.WCT.is_ct act.loc act.ct in
          let@ arg = infer_pexpr pe in
          let@ () = WellTyped.ensure_base_type arg.loc ~expect:Loc (IT.bt arg.value) in
          let value = aligned_ (arg.value, act.ct) in
          return (rt_of_lvt {loc; value}, [])
       | M_PtrArrayShift (pe1, act, pe2) ->
          let@ arg1 = infer_pexpr pe1 in
          let@ arg2 = infer_pexpr pe2 in
          let@ lvt = infer_array_shift loc arg1 (act.loc, act.ct) arg2 in
          return (rt_of_lvt lvt, [])
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
          let@ () = WellTyped.WCT.is_ct act.loc act.ct in
          let@ arg = infer_pexpr pe in
          let@ () = WellTyped.ensure_base_type arg.loc ~expect:Integer (IT.bt arg.value) in
          let ret = Sym.fresh () in
          let oarg_s, oarg = IT.fresh (Resources.block_oargs) in
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
            LRT.Constraint (t_ (alignedI_ ~align:arg.value ~t:(sym_ (ret, Loc))), (loc, None),
            LRT.Resource (resource, (loc, None), 
            LRT.I))))
          in
          return (rt, [])
       | M_CreateReadOnly (sym1, ct, sym2, _prefix) -> 
          Debug_ocaml.error "todo: CreateReadOnly"
       | M_Alloc (ct, sym, _prefix) -> 
          Debug_ocaml.error "todo: Alloc"
       | M_Kill (M_Dynamic, asym) -> 
          Debug_ocaml.error "todo: Free"
       | M_Kill (M_Static ct, pe) -> 
          let@ () = WellTyped.WCT.is_ct loc ct in
          let@ arg = infer_pexpr pe in
          let@ () = WellTyped.ensure_base_type arg.loc ~expect:Loc (IT.bt arg.value) in
          let@ _ = 
            RI.Special.predicate_request ~recursive:true loc (Access Kill) ({
              name = Owned ct;
              pointer = arg.value;
              permission = bool_ true;
              iargs = [];
            }, None)
          in
          return (rt_of_lvt {loc; value = unit_}, [])
       | M_Store (_is_locking, act, p_pe, v_pe, mo) -> 
          let@ () = WellTyped.WCT.is_ct act.loc act.ct in
          let@ parg = infer_pexpr p_pe in
          let@ varg = infer_pexpr v_pe in
          let@ () = WellTyped.ensure_base_type loc ~expect:(BT.of_sct act.ct) (IT.bt varg.value) in
          let@ () = WellTyped.ensure_base_type loc ~expect:Loc (IT.bt parg.value) in
          (* The generated Core program will in most cases before this
             already have checked whether the store value is
             representable and done the right thing. Pointers, as I
             understand, are an exception. *)
          let@ () = 
            let in_range_lc = good_ (act.ct, varg.value) in
            let@ provable = provable loc in
            let holds = provable (t_ in_range_lc) in
            match holds with
            | `True -> return () 
            | `False ->
               let@ model = model () in
               fail (fun ctxt ->
                   let msg = 
                     Write_value_bad {
                         ct = act.ct; 
                         location = parg.value; 
                         value = varg.value; 
                         ctxt;
                         model}
                   in
                   {loc; msg}
                 )
          in
          let@ _ = 
            RI.Special.predicate_request ~recursive:true loc (Access (Store None)) ({
                name = Block act.ct; 
                pointer = parg.value;
                permission = bool_ true;
                iargs = [];
              }, None)
          in
          let oarg_s, oarg = IT.fresh (owned_oargs act.ct) in
          let resource = 
            (oarg_s, (P {
                name = Owned act.ct;
                pointer = parg.value;
                permission = bool_ true;
                iargs = [];
               },
             IT.bt oarg))
          in
          let value_constr = 
            t_ (eq_ (recordMember_ ~member_bt:(BT.of_sct act.ct) (oarg, value_sym),
                     varg.value))
          in
          let rt = 
            RT.Computational ((Sym.fresh (), Unit), (loc, None),
            Resource (resource, (loc, None),
            Constraint (value_constr, (loc, None),
            LRT.I)))
          in
          return (rt, [])
       | M_Load (act, p_pe, _mo) -> 
          let@ () = WellTyped.WCT.is_ct act.loc act.ct in
          let@ parg = infer_pexpr p_pe in
          let@ () = WellTyped.ensure_base_type parg.loc ~expect:Loc (IT.bt parg.value) in
          let@ (point, point_oargs) = 
            restore_resources 
              (RI.Special.predicate_request ~recursive:true loc (Access (Load None)) ({ 
                     name = Owned act.ct;
                     pointer = parg.value;
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
            Constraint (t_ (good_ (act.ct, value)), (loc, None),
            LRT.I)))
          in
          return (rt, [])
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
       let rt = RT.Computational ((Sym.fresh (), Unit), (loc, None), I) in
       return (rt, [])
    | M_Eccall (act, f_pe, pes) ->
       (* todo: do anything with act? *)
       let@ () = WellTyped.WCT.is_ct act.loc act.ct in
       let@ args = ListM.mapM infer_pexpr pes in
       let fsym = match f_pe with
         | M_Pexpr (_, _, _, M_PEsym fsym) -> fsym
         | _ -> unsupported loc !^"function application of function pointers"
       in
       let@ (_loc, ft, _) = get_fun_decl loc fsym in
       Spine.calltype_ft loc args ft
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
       let@ global = get_global () in
       let@ pname, def = Typing.todo_get_resource_predicate_def_s loc (Id.s pname) in
       let@ pointer_pe, iarg_pes = match pes with
         | pointer_asym :: iarg_asyms -> return (pointer_asym, iarg_asyms)
         | _ -> fail (fun _ -> {loc; msg = Generic !^"pointer argument to predicate missing"})
       in
       let@ pointer_arg = infer_pexpr pointer_pe in
       let@ iargs = ListM.mapM infer_pexpr iarg_pes in
       let@ () = 
         (* "+1" because of pointer argument *)
         let has, expect = List.length iargs + 1, List.length def.iargs + 1 in
         if has = expect then return ()
         else fail (fun _ -> {loc; msg = Number_arguments {has; expect}})
       in
       let@ () = WellTyped.ensure_base_type pointer_arg.loc ~expect:Loc (IT.bt pointer_arg.value) in
       let@ () = 
         ListM.iterM (fun (arg, expected_sort) ->
             WellTyped.ensure_base_type arg.loc ~expect:expected_sort (IT.bt arg.value)
           ) (List.combine iargs (List.map snd def.iargs))
       in
       let instantiated_clauses = 
         let subst = 
           make_subst (
               (def.pointer, pointer_arg.value) ::
               List.map2 (fun (def_ia, _) ia -> (def_ia, ia.value)) def.iargs iargs
             )
         in
         List.map (ResourcePredicates.subst_clause subst) def.clauses
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
              loc (UnpackPredicate pname) ({
                name = PName pname;
                pointer = pointer_arg.value;
                permission = bool_ true;
                iargs = List.map (fun arg -> arg.value) iargs;
              }, None)
          in
          let condition, outputs = LAT.logical_arguments_and_return right_clause in
          let lc = 
            eq_ (pred_oargs, 
                 record_ (List.map (fun (o : OutputDef.entry) -> (o.name, o.value)) outputs))
          in
          let lrt = LRT.concat condition (Constraint (t_ lc, (loc, None), I)) in
          return (RT.Computational ((Sym.fresh (), BT.Unit), (loc, None), lrt), [])
       | Pack ->
          let@ (output_assignment, per_path) = Spine.calltype_packing loc pname right_clause in
          let output = record_ (List.map (fun (o : OutputDef.entry) -> (o.name, o.value)) output_assignment) in
          let oarg_s, oarg = IT.fresh (IT.bt output) in
          let resource = 
            (oarg_s, (P {
              name = PName pname;
              pointer = pointer_arg.value;
              permission = bool_ true;
              iargs = List.map (fun arg -> arg.value) iargs;
            }, IT.bt oarg))
          in
          let rt =
            (RT.Computational ((Sym.fresh (), BT.Unit), (loc, None),
             Resource (resource, (loc, None),
             Constraint (t_ (eq_ (oarg, output)), (loc, None), 
             LRT.I))))
          in
          return (rt, per_path)
       end
    | M_Erpredicate (pack_unpack, TPU_Struct tag, pes) ->
       let@ _layout = get_struct_decl loc tag in
       let@ args = ListM.mapM infer_pexpr pes in
       let@ () = 
         (* "+1" because of pointer argument *)
         let has = List.length args in
         if has = 1 then return ()
         else fail (fun _ -> {loc; msg = Number_arguments {has; expect = 1}})
       in
       let pointer_arg = List.hd args in
       let@ () = WellTyped.ensure_base_type pointer_arg.loc ~expect:Loc (IT.bt pointer_arg.value) in
       begin match pack_unpack with
       | Pack ->
          let situation = TypeErrors.PackStruct tag in
          let@ (resource, O resource_oargs) = 
            RI.Special.fold_struct ~recursive:true loc situation tag 
              pointer_arg.value (bool_ true) 
          in
          let oargs_s, oargs = IT.fresh (IT.bt resource_oargs) in
          let rt = 
            RT.Computational ((Sym.fresh (), BT.Unit), (loc, None),
            LRT.Resource ((oargs_s, (P resource, IT.bt oargs)), (loc, None), 
            LRT.Constraint (t_ (eq_ (oargs, resource_oargs)), (loc, None),
            LRT.I)))
          in
          return (rt, [])
       | Unpack ->
          let situation = TypeErrors.UnpackStruct tag in
          let@ resources = 
            RI.Special.unfold_struct ~recursive:true loc situation tag 
              pointer_arg.value (bool_ true) 
          in
          let constraints, resources = 
            List.fold_left_map (fun acc (r, O o) -> 
                let oarg_s, oarg = IT.fresh (IT.bt o) in
                let acc = acc @ [(t_ (eq_ (oarg, o)), (loc, None))] in
                acc, ((oarg_s, (r, IT.bt oarg)), (loc, None))
              ) [] resources in
          let lrt = LRT.mResources resources (LRT.mConstraints constraints LRT.I) in
          let rt = RT.Computational ((Sym.fresh (), BT.Unit), (loc, None), lrt) in
          return (rt, [])
       end
    | M_Elpredicate (have_show, pname, asyms) ->
       unsupported loc !^"have/show"
    | M_Einstantiate (oid, pe) ->
       let@ arg = infer_pexpr pe in
       let@ constraints = all_constraints () in
       let omentions_pred it = match oid with
         | Some id -> IT.mentions_pred id it
         | None -> true
       in
       let extra_assumptions = 
         List.filter_map (fun lc ->
             match lc with
             | Forall ((s, bt), t) 
                  when BT.equal bt (IT.bt arg.value) && omentions_pred t ->
                Some (LC.t_ (IT.subst (IT.make_subst [(s, arg.value)]) t), (loc, None))
             | _ -> 
                None
           ) (LCSet.elements constraints)
       in
       let lrt = LRT.mConstraints extra_assumptions LRT.I in
       return (RT.Computational ((Sym.fresh (), Unit), (loc, None), lrt), [])
  in
  debug 3 (lazy (RT.pp (fst result)));
  return result

(* check_expr: type checking for impure epressions; type checks `e`
   against `typ`, which is either a return type or `False`; returns
   either an updated environment, or `False` in case of Goto *)
let rec check_texpr labels (e : 'bty mu_texpr) (typ : RT.t orFalse) 
        : (per_path, type_error) m =

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
       let@ carg = infer_pexpr c_pe in
       let@ () = WellTyped.ensure_base_type carg.loc ~expect:Bool (IT.bt carg.value) in
       let@ per_paths = ListM.mapM (fun (lc, nm, e) ->
           pure begin
               let@ () = add_c (t_ lc) in
               let@ provable = provable loc in
               match provable (t_ (bool_ false)) with
               | `True -> return []
               | `False ->
                 let start = time_log_start (nm ^ " branch") (Locations.to_string loc) in
                 let@ per_path = check_texpr_in [loc_of_texpr e; loc] labels e typ in
                 time_log_end start;
                 return per_path
             end
         ) [(carg.value, "true", e1); (not_ carg.value, "false", e2)] in
       return (List.concat per_paths)
    | M_Ebound e ->
       check_texpr labels e typ 
    | M_End _ ->
       Debug_ocaml.error "todo: End"
    | M_Ecase (c_pe, pats_es) ->
       let@ arg = infer_pexpr c_pe in
       let@ per_paths = ListM.mapM (fun (pat, pe) ->
           pure begin
               let@ () = pattern_match arg.value pat in
               let@ provable = provable loc in
               match provable (t_ (bool_ false)) with
               | `True -> return []
               | `False -> check_texpr_in [loc_of_texpr pe; loc] labels pe typ
             end
         ) pats_es in
       return (List.concat per_paths)
    | M_Elet (p, e1, e2) ->
       let@ fin = begin_trace_of_pure_step (Some p) e1 in
       let@ lvt = infer_pexpr e1 in
       let@ () = match p with 
         | M_Symbol sym -> bind_lvt sym lvt
         | M_Pat pat -> pattern_match lvt.value pat
       in
       let@ () = fin () in
       check_texpr labels e2 typ
    | M_Ewseq (pat, e1, e2) ->
       let@ fin = begin_trace_of_step (Some (Mu.M_Pat pat)) e1 in
       let@ (rt, per_path1) = infer_expr labels e1 in
       let@ () = pattern_match_rt (Loc (loc_of_expr e1)) pat rt in
       let@ () = fin () in
       let@ per_path2 = check_texpr labels e2 typ in
       return (per_path1 @ per_path2)
    | M_Esseq (pat, e1, e2) ->
       let@ fin = begin_trace_of_step (Some pat) e1 in
       let@ (rt, per_path1) = infer_expr labels e1 in
       let@ () = match pat with
         | M_Symbol sym -> bind (Some (Loc (loc_of_expr e1))) sym rt
         | M_Pat pat -> pattern_match_rt (Loc (loc_of_expr e1)) pat rt
       in
       let@ () = fin () in
       let@ per_path2 = check_texpr labels e2 typ in
       return (per_path1 @ per_path2)
    | M_Edone pe ->
       begin match typ with
       | Normal typ ->
          let@ arg = infer_pexpr pe in
          let@ per_path = Spine.subtype loc arg typ in
          let@ () = all_empty loc in
          return per_path
       | False ->
          let err = 
            "This expression returns but is expected "^
              "to have non-return type."
          in
          fail (fun _ -> {loc; msg = Generic !^err})
       end
    | M_Eundef (_loc, ub) ->
       let@ provable = provable loc in
       begin match provable (t_ (bool_ false)) with
       | `True -> return []
       | `False ->
          let@ model = model () in
          fail (fun ctxt -> {loc; msg = Undefined_behaviour {ub; ctxt; model}})
       end
  | M_Eerror (err, pe) ->
     let@ arg = infer_pexpr pe in
     let@ provable = provable loc in
     begin match provable (t_ (bool_ false)) with
     | `True -> return []
     | `False ->
        let@ model = model () in
        fail (fun ctxt -> {loc; msg = StaticError {err; ctxt; model}})
     end
    | M_Erun (label_sym, pes) ->
       let@ (lt,lkind) = match SymMap.find_opt label_sym labels with
         | None -> fail (fun _ -> {loc; msg = Generic (!^"undefined code label" ^/^ Sym.pp label_sym)})
         | Some (lt,lkind) -> return (lt,lkind)
       in
       let@ args = ListM.mapM infer_pexpr pes in
       let@ per_path = Spine.calltype_lt loc args (lt,lkind) in
       let@ () = all_empty loc in
       return per_path

  in
  return result


and check_texpr_in locs labels e typ =
  let@ loc_trace = get_loc_trace () in
  in_loc_trace (locs @ loc_trace) (fun () -> check_texpr labels e typ)



let check_and_bind_arguments rt_subst loc arguments (function_typ : 'rt AT.t) = 
  let rec check args (ftyp : 'rt AT.t) =
    match args, ftyp with
    | ((aname, abt) :: args), (AT.Computational ((lname, sbt), _info, ftyp)) ->
       if BT.equal abt sbt then
         let new_lname = Sym.fresh () in
         let subst = make_subst [(lname, sym_ (new_lname, sbt))] in
         let ftyp' = AT.subst rt_subst subst ftyp in
         let@ () = add_l new_lname abt in
         let@ () = add_a aname (abt,new_lname) in
         check args ftyp'
       else
         fail (fun _ -> {loc; msg = Mismatch {has = abt; expect = sbt}})
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
      (body : 'bty mu_tpexpr) 
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
      let@ per_path = check_tpexpr_in [loc] body rt in
      (* let@ () = do_post_typing per_path in *)
      return ()
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
      let check_label lsym def per_path1 =
        pure begin 
          match def with
          | M_Return (loc, lt) ->
             return per_path1
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
             let@ per_path2 = check_texpr_in [loc] labels body False in
             return (per_path1 @ per_path2)
          end
      in
      let check_body () = 
        pure begin 
            debug 2 (lazy (headline ("checking function body " ^ Sym.pp_string fsym)));
            let@ () = ListM.iterM (add_r (Some (Label "start"))) resources in
            check_texpr labels body (Normal rt)
          end
      in
      let@ per_path = check_body () in
      let@ per_path = PmapM.foldM check_label label_defs per_path in
      (* let@ () = do_post_typing per_path in *)
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
  let@ () = 
    (* check and record logical predicate defs *)
    Pp.progress_simple "checking specifications" "logical predicate welltypedness";
    ListM.iterM (fun (name,(def : LP.definition)) -> 
        let@ () = WellTyped.WLPD.welltyped def in
        add_logical_predicate name def
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
