module CF=Cerb_frontend
module RE = Resources.RE
module RER = Resources.Requests
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts
module LRT = LogicalReturnTypes
module RT = ReturnTypes
module AT = ArgumentTypes
module TE = TypeErrors
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module S = Solver
module Loc = Locations
module LP = LogicalPredicates

open Tools
open Sctypes
open Context
open Global

open IT
open TypeErrors
module Mu = Retype.New
open CF.Mucore
open Mu

open Pp
open BT
open Resources
open Resources.RE
open ResourcePredicates
open LogicalConstraints

open List





(* some of this is informed by impl_mem *)



(*** mucore pp setup **********************************************************)

module PP_TYPS = struct
  module T = Retype.SR_Types
  let pp_bt = BT.pp 
  let pp_ct ct = Sctypes.pp ct
  let pp_ft = AT.pp RT.pp
  let pp_gt = pp_ct
  let pp_lt = AT.pp False.pp
  let pp_ut _ = Pp.string "todo: implement union type printer"
  let pp_st _ = Pp.string "todo: implement struct type printer"
end

module PP_MUCORE = CF.Pp_mucore.Make(CF.Pp_mucore.Basic)(PP_TYPS)
(* let pp_budget () = Some !debug_level *)
let pp_budget () = Some (!print_level*5)
let pp_pexpr e = PP_MUCORE.pp_pexpr e
let pp_tpexpr e = PP_MUCORE.pp_tpexpr (pp_budget ()) e
let pp_expr e = PP_MUCORE.pp_expr e
let pp_texpr e = PP_MUCORE.pp_texpr (pp_budget ()) e


open Typing
open Effectful.Make(Typing)



type mem_value = CF.Impl_mem.mem_value
type pointer_value = CF.Impl_mem.pointer_value


(*** auxiliaries **************************************************************)

let ensure_logical_sort (loc : loc) ~(expect : LS.t) (has : LS.t) : (unit, type_error) m =
  if LS.equal has expect 
  then return () 
  else fail (fun _ -> {loc; msg = Mismatch {has; expect}})

let ensure_base_type (loc : loc) ~(expect : BT.t) (has : BT.t) : (unit, type_error) m =
  ensure_logical_sort loc ~expect has


let check_computational_bound loc s = 
  let@ is_bound = bound_a s in
  if is_bound then return () 
  else fail (fun _ -> {loc; msg = Unknown_variable s})

let get_struct_decl loc tag = 
  let@ global = get_global () in
  match SymMap.find_opt tag global.struct_decls with
  | Some decl -> return decl
  | None -> fail (fun _ -> {loc; msg = Unknown_struct tag})

let get_member_type loc tag member layout = 
  match List.assoc_opt Id.equal member (Memory.member_types layout) with
  | Some membertyp -> return membertyp
  | None -> fail (fun _ -> {loc; msg = Unknown_member (tag, member)})

let get_fun_decl loc fsym = 
  let@ global = get_global () in
  match Global.get_fun_decl global fsym with
  | Some t -> return t
  | None -> fail (fun _ -> {loc = Loc.unknown; msg = Unknown_function fsym})





(*** pattern matching *********************************************************)


let pattern_match = 

  let rec aux pat : (IT.t, type_error) m = 
    let (M_Pattern (loc, _, pattern) : mu_pattern) = pat in
    match pattern with
    | M_CaseBase (o_s, has_bt) ->
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
          return (IT.nil_ ~item_bt)
       | M_Cnil item_bt, _ ->
          fail (fun _ -> {loc; msg = Number_arguments {has = List.length pats; expect = 0}})
       | M_Ccons, [p1; p2] ->
          let@ it1 = aux p1 in
          let@ it2 = aux p2 in
          let@ () = ensure_base_type loc ~expect:(List (IT.bt it1)) (IT.bt it2) in
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
  let@ () = ensure_base_type loc ~expect:(IT.bt to_match) (IT.bt it) in
  add_c (t_ (eq_ (it, to_match)))





let rec bind_logical where (lrt : LRT.t) = 
  match lrt with
  | Logical ((s, ls), _oinfo, rt) ->
     let s' = Sym.fresh () in
     let rt' = LRT.subst (IT.make_subst [(s, IT.sym_ (s', ls))]) rt in
     let@ () = add_l s' ls in
     bind_logical where rt'
  | Define ((s, it), oinfo, rt) ->
     let s' = Sym.fresh () in
     let bt = IT.bt it in
     let rt' = LRT.subst (IT.make_subst [(s, IT.sym_ (s', bt))]) rt in
     let constr = LC.t_ (IT.def_ s' it) in
     let@ () = add_l s' bt in
     let@ () = add_c constr in
     bind_logical where rt'
  | Resource (re, _oinfo, rt) -> 
     let@ lcs = add_r where re in
     let@ () = add_cs lcs in
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






(* The pattern-matching might de-struct 'bt'. For easily making
   constraints carry over to those values, record (lname,bound) as a
   logical variable and record constraints about how the variables
   introduced in the pattern-matching relate to (lname,bound). *)
let pattern_match_rt loc (pat : mu_pattern) (rt : RT.t) : (unit, type_error) m =
  let@ (bt, s') = bind_logically (Some loc) rt in
  pattern_match (sym_ (s', bt)) pat





(* resource inference *)



module ResourceInference = struct 

  let reorder_points = ref true

  module General = struct

    type 'a cases = C of 'a list


    let unfold_array_request item_ct base_pointer_t length permission_t = 
      Resources.Requests.{
          ct = array_ct item_ct (Some length);
          pointer = base_pointer_t;
          value = of_sct (array_ct item_ct (Some length));
          init = BT.Bool;
          permission = permission_t;
      }

    let unfold_struct_request tag pointer_t permission_t = 
      Resources.Requests.{
          ct = struct_ct tag;
          pointer = pointer_t;
          value = BT.of_sct (struct_ct tag);
          init = BT.Bool;
          permission = permission_t;
      }

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

    let rec point_request loc failure (requested : Resources.Requests.point) = 
      debug 7 (lazy (item "point request" (RER.pp (Point requested))));
      let@ is_ex = exact_match () in
      let is_exact_re re = !reorder_points && (is_ex (RER.Point requested, re)) in
      let@ global = get_global () in
      let@ all_lcs = all_constraints () in
      let simp t = Simplify.simp global.struct_decls all_lcs t in
      let needed = requested.permission in 
      let sub_resource_if = fun cond re (needed, C value, C init) ->
            let continue = (re, (needed, C value, C init)) in
            if not (cond re) || is_false needed then continue else
            match re with
            | Point p' when Sctypes.equal requested.ct p'.ct ->
               debug 15 (lazy (item "point/point sub at ptr" (IT.pp p'.pointer)));
               let pmatch = eq_ (requested.pointer, p'.pointer) in
               let took = and_ [pmatch; p'.permission; needed] in
               let value = value @ [(took, p'.value)] in
               let init = init @ [(took, p'.init)] in
               let needed' = and_ [needed; not_ (and_ [pmatch; p'.permission])] in
               let permission' = and_ [p'.permission; not_ (and_ [pmatch; needed])] in
               Point {p' with permission = permission'}, (simp needed', C value, C init)
            | QPoint p' when Sctypes.equal requested.ct p'.ct ->
               let base = p'.pointer in
               debug 15 (lazy (item "point/qpoint sub at base ptr" (IT.pp base)));
               let item_size = int_ (Memory.size_of_ctype p'.ct) in
               let offset = array_offset_of_pointer ~base ~pointer:requested.pointer in
               let index = array_pointer_to_index ~base ~item_size ~pointer:requested.pointer in
               let pre_match =
                 (* adapting from RE.subarray_condition *)
                 and_ [lePointer_ (base, requested.pointer);
                       eq_ (rem_ (offset, item_size), int_ 0)]
               in
               let subst = IT.make_subst [(p'.q, index)] in
               let took = and_ [pre_match; IT.subst subst p'.permission; needed] in
               let value = value @ [(took, IT.subst subst p'.value)] in
               let init = init @ [(took, IT.subst subst p'.init)] in
               let needed' = and_ [needed; not_ (and_ [pre_match; IT.subst subst p'.permission])] in
               let permission' = 
                 and_ [p'.permission; 
                       not_ (and_ [eq_ (sym_ (p'.q, Integer), index); pre_match; needed])] 
               in
               QPoint {p' with permission = permission'}, (simp needed', C value, C init)
            | _ ->
               continue
      in
      let@ (needed, C value, C init) =
        map_and_fold_resources (sub_resource_if is_exact_re)
          (needed, C [], C [])
      in
      let@ (needed, C value, C init) =
        map_and_fold_resources (sub_resource_if (fun re -> not (is_exact_re re)))
          (needed, C value, C init) in
      let@ provable = provable in
      begin match provable (t_ (not_ needed)) with
      | `True ->
         let v_s, v = IT.fresh requested.value in
         let i_s, i = IT.fresh requested.init in
         let@ () = add_ls [(v_s, IT.bt v); (i_s, IT.bt i)] in
         let constr x (guard, x_v) = t_ (impl_ (guard, eq_ (x, x_v))) in
         let@ () = add_cs (map (constr v) value @ map (constr i) init) in
         let r = { 
             ct = requested.ct;
             pointer = requested.pointer;
             value = v;
             init = i;
             permission = requested.permission 
           }
         in
         (* let r = RE.simp_point ~only_outputs:true global.struct_decls all_lcs r in *)
         return r
      | `False ->
         let@ resource = match requested.ct with
           | Array (act, Some length) ->
              fold_array loc failure act requested.pointer length 
                requested.permission
           | Struct tag ->
              fold_struct loc failure tag requested.pointer 
                requested.permission
           | _ -> 
              let@ model = model () in
              fail (failure model)
         in
         let@ lcs = add_r (Some (Loc loc)) resource in
         let@ () = add_cs lcs in
         point_request loc failure requested
      end


    and qpoint_request loc failure (requested : Resources.Requests.qpoint) = 
      debug 7 (lazy (item "qpoint request" (RER.pp (QPoint requested))));
      let@ global = get_global () in
      let@ all_lcs = all_constraints () in
      let simp t = Simplify.simp global.struct_decls all_lcs t in
      let needed = requested.permission in
      let@ (needed, C value, C init) =
        map_and_fold_resources (fun re (needed, C value, C init) ->
            let continue = (re, (needed, C value, C init)) in
            if is_false needed then continue else
            match re with
            | Point p' when Sctypes.equal requested.ct p'.ct ->
               let base = requested.pointer in
               let item_size = int_ (Memory.size_of_ctype requested.ct) in
               let offset = array_offset_of_pointer ~base ~pointer:p'.pointer in
               let index = array_pointer_to_index ~base ~item_size ~pointer:p'.pointer in
               let pre_match = 
                 and_ [lePointer_ (base, p'.pointer);
                       eq_ (rem_ (offset, item_size), int_ 0)]
               in
               let subst = IT.make_subst [(requested.q, index)] in
               let took = and_ [pre_match; IT.subst subst needed; p'.permission] in
               let i_match = eq_ (sym_ (requested.q, Integer), index) in
               let value = value @ [(and_ [took; i_match], p'.value)] in
               let init = init @ [(and_ [took; i_match], p'.init)] in
               let needed' = and_ [needed; not_ (and_ [pre_match; p'.permission; i_match])] in
               let permission' = and_ [p'.permission; not_ (and_ [pre_match; IT.subst subst needed])] in
               Point {p' with permission = permission'}, (simp needed', C value, C init)
            | QPoint p' when Sctypes.equal requested.ct p'.ct ->
               let p' = alpha_rename_qpoint requested.q p' in
               let pmatch = eq_ (requested.pointer, p'.pointer) in
               let took = and_ [pmatch; needed; p'.permission] in
               let value = value @ [(took, p'.value)] in
               let init = init @ [(took, p'.init)] in
               let needed' = and_ [needed; not_ (and_ [pmatch; p'.permission])] in
               let permission' = and_ [p'.permission; not_ (and_ [pmatch; needed])] in
               QPoint {p' with permission = permission'}, (simp needed', C value, C init)
            | re ->
               continue
          ) (needed, C [], C [])
      in
      let@ provable = provable in
      let holds = provable (forall_ (requested.q, BT.Integer) (not_ needed)) in
      begin match holds with
      | `True ->
         let q_s, q = requested.q, sym_ (requested.q, BT.Integer) in
         let v_s, v = IT.fresh (Map (IT.bt q, requested.value)) in
         let i_s, i = IT.fresh (Map (IT.bt q, requested.init)) in
         let@ () = add_ls [(v_s, IT.bt v); (i_s, IT.bt i)] in
         let constr a (guard, a_v) =
           forall_ (q_s, IT.bt q)
             (impl_ (guard, eq_ (map_get_ a q, a_v)))
         in
         let@ () = add_cs (map (constr v) value @ (map (constr i) init)) in
         let r = { 
             ct = requested.ct;
             pointer = requested.pointer;
             q = requested.q;
             value = map_get_ v q;
             init = map_get_ i q;
             permission = requested.permission;
           } 
         in
         (* let r = RE.simp_qpoint ~only_outputs:true global.struct_decls all_lcs r in *)
         return r
      | `False ->
         let@ model = model () in
         fail (failure model)
      end




    and predicate_request loc failure (requested : Resources.Requests.predicate) = 
      debug 7 (lazy (item "predicate request" (RER.pp (Predicate requested))));
      let@ global = get_global () in
      let@ all_lcs = all_constraints () in
      let simp t = Simplify.simp global.struct_decls all_lcs t in
      let needed = requested.permission in 
      let@ (needed, oargs) =
        map_and_fold_resources (fun re (needed, oargs) ->
            let continue = (re, (needed, oargs)) in
            if is_false needed then continue else
            match re with
            | Predicate p' when String.equal requested.name p'.name ->
               let pmatch = 
                 eq_ (requested.pointer, p'.pointer)
                 :: List.map2 eq__ requested.iargs p'.iargs
               in
               let took = and_ (needed :: p'.permission :: pmatch) in
               let oargs = List.map2 (fun (C oa) oa' -> C (oa @ [(took, oa')])) oargs p'.oargs in
               let needed' = and_ [needed; not_ (and_ (p'.permission :: pmatch))] in
               let permission' = and_ [p'.permission; not_ (and_ (needed :: pmatch))] in
               Predicate {p' with permission = permission'}, (simp needed', oargs)
            | QPredicate p' when String.equal requested.name p'.name ->
               let base = p'.pointer in
               let item_size = int_ p'.step in
               let offset = array_offset_of_pointer ~base ~pointer:requested.pointer in
               let index = array_pointer_to_index ~base ~item_size ~pointer:requested.pointer in
               let subst = IT.make_subst [(p'.q, index)] in
               let pre_match = 
                 (* adapting from RE.subarray_condition *)
                 and_ (lePointer_ (base, requested.pointer)
                       :: eq_ (rem_ (offset, item_size), int_ 0)
                       :: List.map2 (fun ia ia' -> eq_ (ia, IT.subst subst ia')) requested.iargs p'.iargs)
               in
               let took = and_ [pre_match; needed; IT.subst subst p'.permission] in
               let oargs = List.map2 (fun (C oa) oa' -> C (oa @ [(took, IT.subst subst oa')])) oargs p'.oargs in
               let needed' = and_ [needed; not_ (and_ [pre_match; IT.subst subst p'.permission])] in
               let i_match = eq_ (sym_ (p'.q, Integer), index) in
               let permission' = and_ [p'.permission; not_ (and_ [pre_match; needed; i_match])] in
               QPredicate {p' with permission = permission'}, (simp needed', oargs)
            | re ->
               continue
          ) (needed, List.map (fun _ -> C []) requested.oargs)
      in
      let@ provable = provable in
      begin match provable (t_ (not_ needed)) with
      | `True ->
         let constr x (guard, v_x) = t_ (impl_ (guard, eq_ (x, v_x))) in
         let@ oas = 
           ListM.map2M (fun (C oa) oa_bt ->
               let o_s, o = IT.fresh oa_bt in
               let@ () = add_l o_s (IT.bt o) in
               let@ () = add_cs (List.map (constr o) oa) in
               return o
             ) oargs requested.oargs
         in
         let r = { 
             name = requested.name;
             pointer = requested.pointer;
             permission = requested.permission;
             iargs = requested.iargs; 
             oargs = oas
           }
         in
         (* let r = RE.simp_predicate ~only_outputs:true global.struct_decls all_lcs r in *)
         return r
      | `False ->
         let@ model = model () in
         fail (failure model)
      end


    and qpredicate_request loc failure (requested : Resources.Requests.qpredicate) = 
      debug 7 (lazy (item "qpredicate request" (RER.pp (QPredicate requested))));
      let@ global = get_global () in
      let@ all_lcs = all_constraints () in
      let simp it = Simplify.simp global.struct_decls all_lcs it in
      let needed = requested.permission in
      let@ (needed, oargs) =
        map_and_fold_resources (fun re (needed, oargs) ->
            let continue = (re, (needed, oargs)) in
            if is_false needed then continue else
            match re with
            | Predicate p' when String.equal requested.name p'.name ->
               let base = requested.pointer in
               let item_size = int_ requested.step in
               let offset = array_offset_of_pointer ~base ~pointer:p'.pointer in
               let index = array_pointer_to_index ~base ~item_size ~pointer:p'.pointer in
               let subst = IT.make_subst [(requested.q, index)] in
               let pre_match = 
                 and_ (lePointer_ (base, p'.pointer)
                       :: eq_ (rem_ (offset, item_size), int_ 0)
                       :: List.map2 (fun ia ia' -> eq_ (IT.subst subst ia, ia')) requested.iargs p'.iargs
                   )
               in
               let took = and_ [pre_match; IT.subst subst needed; p'.permission] in
               let i_match = eq_ (sym_ (requested.q, Integer), index) in
               let oargs = List.map2 (fun (C oa) oa' -> C (oa @ [(and_ [took; i_match], oa')])) oargs p'.oargs in
               let needed' = and_ [needed; not_ (and_ [pre_match; p'.permission; i_match])] in
               let permission' = and_ [p'.permission; not_ (and_ [pre_match; IT.subst subst needed; p'.permission])] in
               Predicate {p' with permission = permission'}, (simp needed', oargs)
            | QPredicate p' when String.equal requested.name p'.name 
                                 && requested.step = p'.step ->
               let p' = alpha_rename_qpredicate requested.q p' in
               let pmatch = 
                 and_ (eq_ (requested.pointer, p'.pointer)
                       :: List.map2 eq__ requested.iargs p'.iargs)
               in
               let took = and_ [pmatch; needed; p'.permission] in
               let needed' = and_ [needed; not_ (and_ [pmatch; p'.permission])] in
               let permission' = and_ [p'.permission; not_ (and_ [pmatch; needed])] in
               let oargs = List.map2 (fun (C oa) oa' -> C (oa @ [(took, oa')])) oargs p'.oargs in
               QPredicate {p' with permission = permission'}, (simp needed', oargs)
            | re ->
               continue
          ) (needed, List.map (fun _ -> C []) requested.oargs)
      in
      let@ provable = provable in
      let holds = provable (forall_ (requested.q, BT.Integer) (not_ needed)) in
      begin match holds with
      | `True ->
         let q_s, q = requested.q, sym_ (requested.q, Integer) in
         (* let constr a (guard, a_v) =  *)
         (*   forall_ (q_s, IT.bt q) *)
         (*     (impl_ (guard , _)) *)
         (* in *)
         let constr a (guard, a_v) = 
           forall_ (q_s, IT.bt q)
             (impl_ (guard, eq_ (map_get_ a q, a_v)))
         in
         let@ oas = 
           ListM.map2M (fun (C oa) (oa_bt) ->
               let o_s, o = IT.fresh (Map (IT.bt q, oa_bt)) in
               let@ () = add_l o_s (IT.bt o) in
               let@ () = add_cs (List.map (constr o) oa) in
               return (map_get_ o q)
             ) oargs requested.oargs
         in
         let r = { 
             name = requested.name;
             pointer = requested.pointer;
             q = requested.q;
             step = requested.step;
             permission = requested.permission;
             iargs = requested.iargs; 
             oargs = oas;
           } 
         in
         (* let r = RE.simp_qpredicate ~only_outputs:true global.struct_decls all_lcs r in *)
         return r
      | `False ->
         let@ model = model () in
         fail (failure model)
      end


    and fold_array loc failure item_ct base length permission =
      debug 7 (lazy (item "fold array" Pp.empty));
      debug 7 (lazy (item "item_ct" (Sctypes.pp item_ct)));
      debug 7 (lazy (item "base" (IT.pp base)));
      debug 7 (lazy (item "length" (IT.pp (int_ length))));
      debug 7 (lazy (item "permission" (IT.pp permission)));
      if length > 20 then warn !^"generating point-wise constraints for big array";
      let@ qpoint = 
        let q_s, q = IT.fresh Integer in
        qpoint_request loc failure {
          ct = item_ct;
          pointer = base;
          q = q_s;
          value = BT.of_sct item_ct;
          init = BT.Bool;
          permission = and_ [permission; (int_ 0) %<= q; q %< (int_ length)];
        }
      in
      let folded_value_s, folded_value = 
        IT.fresh (Map (Integer, BT.of_sct item_ct)) in
      let folded_value_constr = 
        let q_s, q = qpoint.q, sym_ (qpoint.q, Integer) in
        forall_ (q_s, IT.bt q) (
            eq_ (map_get_ folded_value q,
                 qpoint.value)
          )
      in
      let@ () = add_l folded_value_s (IT.bt folded_value) in
      let@ () = add_c folded_value_constr in
      (* let folded_value =  *)
      (*   let empty = const_map_ Integer (default_ (BT.of_sct item_ct)) in *)
      (*   let rec update value i =  *)
      (*     if i >= length then value else *)
      (*       let subst = IT.make_subst [(qpoint.q, int_ i)] in *)
      (*       let cell_value = IT.subst subst qpoint.value in *)
      (*       let value' = map_set_ value (int_ i, cell_value) in *)
      (*       update value' (i + 1) *)
      (*   in *)
      (*   update empty 0 *)
      (* in *)
      let folded_init = 
        let q_s, q = qpoint.q, sym_ (qpoint.q, Integer) in
        eachI_ (0, q_s, length - 1) qpoint.init
      in
      let folded_resource = 
        Point {
            ct = array_ct item_ct (Some length);
            pointer = base;
            value = folded_value;
            init = folded_init;
            permission = permission;
          }
      in
      return folded_resource



    and fold_struct loc failure tag pointer_t permission_t =
      debug 7 (lazy (item "fold struct" Pp.empty));
      debug 7 (lazy (item "tag" (Sym.pp tag)));
      debug 7 (lazy (item "pointer" (IT.pp pointer_t)));
      debug 7 (lazy (item "permission" (IT.pp permission_t)));
      let open Memory in
      let@ global = get_global () in
      let layout = SymMap.find tag global.struct_decls in
      let@ (values, inits) = 
        ListM.fold_leftM (fun (values, inits) {offset; size; member_or_padding} ->
            let member_p = integerToPointerCast_ (add_ (pointerToIntegerCast_ pointer_t, int_ offset)) in
            match member_or_padding with
            | Some (member, sct) ->
               let@ point = 
                 point_request loc failure {
                   ct = sct;
                   pointer = member_p;
                   value = BT.of_sct sct;
                   init = BT.Bool;
                   permission = permission_t;
                 }
               in
               return (values @ [(member, point.value)], inits @ [point.init])
            | None ->
               let rec bytes i =
                 if i = size then return () else
                   let@ _ = 
                     point_request loc failure {
                         ct = integer_ct Char;
                         pointer = integerToPointerCast_ (add_ (pointerToIntegerCast_ member_p, int_ i));
                         permission = permission_t;
                         value = BT.Integer;
                         init = BT.Bool;
                       } 
                   in
                   bytes (i + 1)
               in
               let@ () = bytes 0 in
               return (values, inits)
       ) ([], []) layout
      in
      let folded_resource = 
        Point {
            ct = struct_ct tag;
            pointer = pointer_t;
            value = IT.struct_ (tag, values); 
            init = and_ inits;
            permission = permission_t;
          }
      in
      return folded_resource

    let unfolded_array item_ct base length permission value init =
      let q_s, q = IT.fresh_named Integer "i" in
      QPoint {
          ct = item_ct;
          pointer = base;
          q = q_s;
          value = (map_get_ value q); 
          init = init;
          permission = and_ [permission; (int_ 0) %<= q; q %< (int_ length)]
        }

    (* actually actually here *)
    let unfold_array loc failure item_ct base length permission =   
      debug 7 (lazy (item "unfold array" Pp.empty));
      debug 7 (lazy (item "item_ct" (Sctypes.pp item_ct)));
      debug 7 (lazy (item "base" (IT.pp base)));
      debug 7 (lazy (item "length" (IT.pp (int_ length))));
      debug 7 (lazy (item "permission" (IT.pp permission)));
      let@ point = 
        point_request loc failure 
          (unfold_array_request item_ct base length permission) 
      in
      let qpoint =
        unfolded_array item_ct base length permission 
          point.value point.init
      in
      return qpoint

    let unfold_struct loc failure tag pointer_t permission_t = 
      debug 7 (lazy (item "unfold struct" Pp.empty));
      debug 7 (lazy (item "tag" (Sym.pp tag)));
      debug 7 (lazy (item "pointer" (IT.pp pointer_t)));
      debug 7 (lazy (item "permission" (IT.pp permission_t)));
      let@ global = get_global () in
      let@ point = 
        point_request loc failure 
          (unfold_struct_request tag pointer_t permission_t)
      in
      let layout = SymMap.find tag global.struct_decls in
      let lrt = 
        let open Memory in
        List.fold_right (fun {offset; size; member_or_padding} lrt ->
            let member_p = integerToPointerCast_ (add_ (pointerToIntegerCast_ pointer_t, int_ offset)) in
            match member_or_padding with
            | Some (member, sct) ->
               let resource = 
                 Point {
                     ct = sct;
                     pointer = member_p;
                     permission = permission_t;
                     value = member_ ~member_bt:(BT.of_sct sct) (tag, point.value, member);
                     init = point.init
                   } 
               in
               let lrt = LRT.Resource (resource, (loc, None), lrt) in
               lrt
            | None ->
               let rec bytes i =
                 if i = size then LRT.I else
                   let member_p = integerToPointerCast_ (add_ (pointerToIntegerCast_ member_p, int_ i)) in
                   let padding_s, padding_t = IT.fresh BT.Integer in
                   let resource = 
                     Point {
                         ct = integer_ct Char;
                         pointer = member_p;
                         permission = permission_t;
                         value = padding_t;
                         init = bool_ false
                       } 
                   in
                   LRT.Logical ((padding_s, IT.bt padding_t), (loc, None),
                   LRT.Resource (resource, (loc, None),
                   bytes (i + 1)))
               in
               let lrt = LRT.concat (bytes 0) lrt in
               lrt
          ) layout LRT.I
      in
      return lrt

    let resource_request loc failure (request : RER.t) : (RE.t, type_error) m = 
      match request with
      | Point request ->
         let@ point = point_request loc failure request in
         return (Point point)
      | QPoint request ->
         let@ qpoint = qpoint_request loc failure request in
         return (QPoint qpoint)
      | Predicate request ->
         let@ predicate = predicate_request loc failure request in
         return (Predicate predicate)
      | QPredicate request ->
         let@ qpredicate = qpredicate_request loc failure request in
         return (QPredicate qpredicate)

  end

  module Special = struct

    let missing_resource_failure loc situation (orequest, oinfo) = 
      fun model ctxt ->
      let msg = Missing_resource_request {orequest; situation; oinfo; model; ctxt} in
      {loc; msg}

    let point_request loc situation (request, oinfo) = 
      let failure = missing_resource_failure loc situation 
                      (Some (Point request), oinfo) in
      General.point_request loc failure request

    let qpoint_request loc situation (request, oinfo) = 
      let failure = missing_resource_failure loc situation 
                      (Some (QPoint request), oinfo) in
      General.qpoint_request loc failure request

    let predicate_request loc situation (request, oinfo) = 
      let failure = missing_resource_failure loc situation 
                      (Some (Predicate request), oinfo) in
      General.predicate_request loc failure request

    let qpredicate_request loc situation (request, oinfo) = 
      let failure = missing_resource_failure loc situation 
                      (Some (QPredicate request), oinfo) in
      General.qpredicate_request loc failure request

    let unfold_array loc situation ct base_pointer_t length permission_t = 
      let request = General.unfold_array_request ct base_pointer_t length permission_t in
      let failure = missing_resource_failure loc situation 
                      (Some (RER.Point request), None) in
      General.unfold_array loc failure ct base_pointer_t length permission_t

    let unfold_struct loc situation tag pointer_t permission_t = 
      let request = General.unfold_struct_request tag pointer_t permission_t in
      let failure = missing_resource_failure loc situation 
                      (Some (RER.Point request), None) in
      General.unfold_struct loc failure tag pointer_t permission_t

    let fold_struct loc situation tag pointer_t permission_t = 
      let failure = missing_resource_failure loc situation (None, None) in
      General.fold_struct loc failure tag pointer_t permission_t

  end


end



module InferenceEqs = struct

let use_model_eqs = ref true

let res_pointer_kind res = match res with
  | (RE.Point res_pt) -> Some ((true, res_pt.ct), res_pt.pointer)
  | (RE.QPoint res_qpt) -> Some ((false, res_qpt.ct), res_qpt.pointer)
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

let add_eqs_for_infer ftyp =
  if not (! use_model_eqs) then return ()
  else
  begin
  debug 5 (lazy (format [] "pre-inference equality discovery"));
  let reqs = NormalisedArgumentTypes.r_resource_requests ftyp in
  let@ ress = map_and_fold_resources (fun re xs -> (re, re :: xs)) [] in
  let res_ptr_k k r = Option.map (fun (ct, p) -> (ct, (p, k))) (res_pointer_kind r) in
  let ptrs = List.filter_map (res_ptr_k true) reqs @
    (List.filter_map (res_ptr_k false) ress) in
  let cmp2 = Lem_basic_classes.pairCompare Bool.compare CT.compare in
  let ptr_gps = div_groups_discard cmp2 ptrs in
  let@ provable = provable in
  let rec loop ptr_gps =
    let@ global = get_global () in
    let@ all_lcs = all_constraints () in
    let simp t = Simplify.simp global.struct_decls all_lcs t in
    let poss_eqs = List.filter_map (unknown_eq_in_group simp) ptr_gps in
    debug 7 (lazy (format [] ("investigating " ^
        Int.to_string (List.length poss_eqs) ^ " possible eqs")));
    if List.length poss_eqs == 0
    then return ()
    else match provable (t_ (and_ poss_eqs)) with
      | `True ->
        debug 5 (lazy (item "adding equalities" (IT.pp (and_ poss_eqs))));
        let@ () = add_cs (List.map t_ poss_eqs) in
        loop ptr_gps
      | `False ->
        let (m, _) = Solver.model () in
        debug 7 (lazy (format [] ("eqs refuted, processing model")));
        let eval_f p = match Solver.eval global.struct_decls m p with
          | Some (IT (Lit (Pointer i), _)) -> i
          | _ -> (print stderr (IT.pp p); assert false)
        in
        let eval_eqs = List.map (List.map (fun (p, req) -> (eval_f p, (p, req)))) ptr_gps in
        let ptr_gps = List.concat (List.map (div_groups_discard Z.compare) eval_eqs) in
        loop ptr_gps
  in
  let@ () = loop ptr_gps in
  debug 5 (lazy (format [] "finished equality discovery"));
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



module RI = ResourceInference






(*** function call typing, subtyping, and resource inference *****************)

(* spine is parameterised so it can be used both for function and
   label types (which don't have a return type) *)



type arg = {lname : Sym.t; bt : BT.t; loc : loc}
type args = arg list
let it_of_arg arg = sym_ (arg.lname, arg.bt)

let arg_of_sym (loc : loc) (sym : Sym.t) : (arg, type_error) m = 
  let@ () = check_computational_bound loc sym in
  let@ (bt,lname) = get_a sym in
  return {lname; bt; loc}

let arg_of_asym (asym : 'bty asym) : (arg, type_error) m = 
  arg_of_sym asym.loc asym.sym

let args_of_asyms (asyms : 'bty asyms) : (args, type_error) m = 
  ListM.mapM arg_of_asym asyms


module Spine : sig
  val calltype_ft : 
    Loc.t -> args -> AT.ft -> (RT.t, type_error) m
  val calltype_lft : 
    Loc.t -> AT.lft -> (LRT.t, type_error) m
  val calltype_lt : 
    Loc.t -> args -> AT.lt * label_kind -> (unit, type_error) m
  val calltype_packing : 
    Loc.t -> Id.t -> AT.packing_ft -> (OutputDef.t, type_error) m
  val calltype_lpred_argument_inference : 
    Loc.t -> Id.t -> args -> AT.packing_ft -> (IT.t list, type_error) m
  val subtype : 
    Loc.t -> arg -> RT.t -> (unit, type_error) m
end = struct

  let pp_unis (unis : (LS.t * Locations.info) SymMap.t) : Pp.document = 
   Pp.list (fun (sym, (ls, _)) ->
     Sym.pp sym ^^^ !^"unresolved" ^^^ parens (LS.pp ls)
     ) (SymMap.bindings unis)



  (* requires equality on inputs *)
  (* could optimise to delay checking the constraints until later *)
  let match_resources loc failure =

    let ls_matches_spec unis uni_var instantiation = 
      let (expect, info) = SymMap.find uni_var unis in
      if LS.equal (IT.bt instantiation) expect 
      then return ()
      else fail (fun _ -> {loc; msg = Mismatch_lvar { has = IT.bt instantiation; expect; spec_info = info}})
    in

    let unify_or_constrain (unis, subst, constrs) (output_spec, output_have) =
      match IT.subst (make_subst subst) output_spec with
      | IT (Lit (Sym s), _) when SymMap.mem s unis ->
         let@ () = ls_matches_spec unis s output_have in
         return (SymMap.remove s unis, (s, output_have) :: subst, constrs)
      | _ ->
         return (unis, subst, eq_ (output_spec, output_have) :: constrs)
    in
    let unify_or_constrain_list = ListM.fold_leftM unify_or_constrain in

    (* ASSUMES unification variables and quantifier q_s are disjoint,
       and that resource inference has produced a resource with value/oargs v[q] *)
    let unify_or_constrain_q (q_s,q_bt) condition (unis, subst, constrs) (output_spec, output_have) = 
      let q = sym_ (q_s, q_bt) in
      match is_map_get (IT.subst (make_subst subst) output_spec) with
      | Some (IT (Lit (Sym s), _), IT (Lit (Sym q'_s), q'_bt)) 
           when Sym.equal q'_s q_s && SymMap.mem s unis ->
         let@ () = ensure_logical_sort loc ~expect:q_bt q'_bt in
         let (output_have_body, q') = Option.get (is_map_get output_have) in
         assert (IT.equal q' q);
         let@ () = ls_matches_spec unis s output_have_body in
         return (SymMap.remove s unis, (s, output_have_body) :: subst, constrs)
      | _ ->
         return (unis, subst, eq_ (output_spec, output_have) :: constrs)
    in
    let unify_or_constrain_q_list q condition = 
      ListM.fold_leftM (unify_or_constrain_q q condition) in

    fun (unis : (LS.t * Locations.info) SymMap.t) r_spec r_have ->

    debug 9 (lazy (item "matching resource" (RE.pp r_have ^^^ !^"against" ^^^ (RE.pp r_spec))));

    match r_spec, r_have with
    | Point p_spec, Point p_have ->
       assert (Sctypes.equal p_spec.ct p_have.ct
               && IT.equal p_spec.pointer p_have.pointer
               && IT.equal p_spec.permission p_have.permission);
       let@ (unis, subst, constrs) = 
         unify_or_constrain_list (unis, [], []) 
           [(p_spec.value, p_have.value); 
            (p_spec.init, p_have.init)] 
       in
       let@ provable = provable in
       let result = provable (t_ (impl_ (p_have.permission, and_ constrs))) in
       begin match result with
       | `True -> return (unis, make_subst subst) 
       | `False -> let@ model = model () in fail (failure model)
       end
    | QPoint p_spec, QPoint p_have ->
       let p_spec, p_have = 
         let q = Sym.fresh_same p_spec.q in
         RE.alpha_rename_qpoint q p_spec,
         RE.alpha_rename_qpoint q p_have
       in
       assert (Sctypes.equal p_spec.ct p_have.ct
               && IT.equal p_spec.pointer p_have.pointer
               && Sym.equal p_spec.q p_have.q
               && IT.equal p_spec.permission p_have.permission);
       let@ (unis, subst, constrs) = 
         unify_or_constrain_q_list (p_have.q, Integer) p_have.permission
           (unis, [], []) 
           [(p_spec.value, p_have.value); 
            (p_spec.init, p_have.init)] 
       in         
       let@ provable = provable in
       let result = 
         provable
           (forall_ (p_have.q, BT.Integer)
              (impl_ (p_have.permission, and_ constrs)))
       in
       begin match result with
       | `True -> return (unis, make_subst subst) 
       | `False -> let@ model = model () in fail (failure model)
       end
    | Predicate p_spec, Predicate p_have ->
       assert (String.equal p_spec.name p_have.name
               && IT.equal p_spec.pointer p_have.pointer
               && IT.equal p_spec.permission p_have.permission
               && List.equal IT.equal p_spec.iargs p_have.iargs);
       let@ (unis, subst, constrs) = 
         unify_or_constrain_list (unis, [], [])
           (List.combine p_spec.oargs p_have.oargs) 
       in
       let@ provable = provable in
       let result = provable (t_ (impl_ (p_have.permission, and_ constrs))) in
       begin match result with
       | `True -> return (unis, make_subst subst) 
       | `False -> let@ model = model () in fail (failure model)
       end
    | QPredicate p_spec, QPredicate p_have ->
       let p_spec, p_have = 
         let q = Sym.fresh_same p_spec.q in
         RE.alpha_rename_qpredicate q p_spec,
         RE.alpha_rename_qpredicate q p_have 
       in
       assert (String.equal p_spec.name p_have.name
               && IT.equal p_spec.pointer p_have.pointer
               && Sym.equal p_spec.q p_have.q
               && p_spec.step = p_have.step
               && IT.equal p_spec.permission p_have.permission
               && List.equal IT.equal p_spec.iargs p_have.iargs);
       let@ (unis, subst, constrs) = 
         unify_or_constrain_q_list (p_have.q, Integer) p_have.permission
           (unis, [], []) 
           (List.combine p_spec.oargs p_have.oargs) 
       in
       let@ provable = provable in
       let result =
         provable
           (forall_ (p_have.q, BT.Integer)
              (impl_ (p_have.permission, and_ constrs)))
       in
       begin match result with
       | `True -> return (unis, make_subst subst) 
       | `False -> let@ model = model () in fail (failure model)
       end
    | _ -> 
       Debug_ocaml.error "resource inference has inferred mismatched resources"

  let prefer_req i ftyp =
    let open NormalisedArgumentTypes in
    let rec grab i ftyp = match ftyp with
      | Resource (resource, info, ftyp) -> if i = 0
          then (resource, info)
          else grab (i - 1) ftyp
      | _ -> assert false
    in
    let rec del i ftyp = match ftyp with
      | Resource (resource, info, ftyp) -> if i = 0
          then ftyp
          else Resource (resource, info, del (i - 1) ftyp)
      | _ -> assert false
    in
    let (resource, info) = grab i ftyp in
    let ftyp = del i ftyp in
    Resource (resource, info, ftyp)

  let has_exact r =
    let@ is_ex = RI.General.exact_match () in
    map_and_fold_resources (fun re found -> (re, found || is_ex (RE.request re, r))) false

  let prefer_exact unis ftyp =
    if ! RI.reorder_points then return ftyp
    else
    let reqs1 = NormalisedArgumentTypes.r_resource_requests ftyp in
    let reqs = List.mapi (fun i res -> (i, res)) reqs1 in
    let res_free_vars r = match r with
      | Point p -> IT.free_vars p.pointer
      | QPoint p -> IT.free_vars p.pointer
      | _ -> SymSet.empty
    in
    let no_unis r = SymSet.for_all (fun x -> not (SymMap.mem x unis)) (res_free_vars r) in
    let reqs = List.filter (fun (_, r) -> no_unis r) reqs in
    let@ reqs = ListM.filterM (fun (_, r) -> has_exact r) reqs in
    (* just need an actual preference function *)
    match List.rev reqs with
      | ((i, _) :: _) -> return (prefer_req i ftyp)
      | [] -> return ftyp


  let spine :
        'rt. 
        (IT.t Subst.t -> 'rt -> 'rt) ->
        ('rt -> Pp.doc) ->
        Loc.t ->
        situation ->
        arg list ->
        'rt AT.t ->
        ('rt, type_error) m
    =
    fun rt_subst rt_pp
        loc situation arguments ftyp ->

    (* record the resources now, so we can later re-construct the
       memory state "before" running spine *)
    let@ original_resources = all_resources () in

    let open NormalisedArgumentTypes in

    let ftyp = normalise rt_subst ftyp in

    let@ () = print_with_ctxt (fun ctxt ->
        debug 6 (lazy (checking_situation situation));
        debug 6 (lazy (item "ctxt" (Context.pp ctxt)));
        debug 6 (lazy (item "spec" (pp rt_pp ftyp)))
      )
    in

    let@ ftyp_l = 
      let rec check_computational args ftyp = 
        match args, ftyp with
        | (arg :: args), (Computational ((s, bt), _info, ftyp))
             when BT.equal arg.bt bt ->
           check_computational args 
             (subst rt_subst (make_subst [(s, sym_ (arg.lname, bt))]) ftyp)
        | (arg :: _), (Computational ((_, bt), _info, _))  ->
           fail (fun _ -> {loc = arg.loc; msg = Mismatch {has = arg.bt; expect = bt}})
        | [], (L ftyp) -> 
           return ftyp
        | _ -> 
           let expect = count_computational ftyp in
           let has = List.length arguments in
           fail (fun _ -> {loc; msg = Number_arguments {expect; has}})
      in
      check_computational arguments ftyp 
    in

    let@ (unis, ftyp_r) = 
      let rec delay_logical unis ftyp =
        let@ () = print_with_ctxt (fun ctxt ->
            debug 6 (lazy (item "ctxt" (Context.pp ctxt)));
            debug 6 (lazy (item "spec" (pp_l rt_pp ftyp)))
          )
        in
        match ftyp with
        | Logical ((s, ls), info, ftyp) ->
           let s' = Sym.fresh () in
           delay_logical (SymMap.add s' (ls, info) unis) 
             (subst_l rt_subst (make_subst [(s, sym_ (s', ls))]) ftyp)
        | R ftyp -> 
           return (unis, ftyp)
      in
      delay_logical SymMap.empty ftyp_l
    in

    let@ () = InferenceEqs.add_eqs_for_infer ftyp_r in

    let@ (unis, ftyp_c) = 
      let rec infer_resources unis ftyp = 
        let@ () = print_with_ctxt (fun ctxt ->
            debug 6 (lazy (item "ctxt" (Context.pp ctxt)));
            debug 6 (lazy (item "spec" (pp_r rt_pp ftyp)));
            debug 6 (lazy (item "unis" (pp_unis unis)))
          )
        in
        let@ ftyp = prefer_exact unis ftyp in
        match ftyp with
        | Resource (resource, info, ftyp) -> 
           let request = RE.request resource in
           let@ resource' = 
             let failure model ctxt = 
               let ctxt = { ctxt with resources = original_resources } in
               let msg = Missing_resource_request {orequest = Some request; situation; oinfo = Some info; model; ctxt} in
               {loc; msg}
             in
             RI.General.resource_request loc failure request 
           in
           let@ (unis, new_subst) = 
             let failure model ctxt = 
               let ctxt = { ctxt with resources = original_resources } in
               let expect = resource in
               let has = resource' in
               {loc = loc; msg = Resource_mismatch {expect; has; situation; ctxt; model}}
             in
             match_resources loc failure unis resource resource' 
           in
           infer_resources unis (subst_r rt_subst new_subst ftyp)
        | C ftyp ->
           return (unis, ftyp)
      in
      infer_resources unis ftyp_r
    in
    debug 9 (lazy (!^"finished inferring resource"));

    let () = match SymMap.min_binding_opt unis with
      | Some (s, _) ->
         Debug_ocaml.error ("Unconstrained_logical_variable " ^ Sym.pp_string s)
      | None ->
         ()
    in

    let@ rt = 
      let@ provable = provable in
      let@ () = return (debug 9 (lazy !^"checking constraints")) in
      let rec check_logical_constraints = function
        | Constraint (c, info, ftyp) -> 
           let@ () = return (debug 9 (lazy (item "checking constraint" (LC.pp c)))) in
           begin match provable c with
           | `True -> check_logical_constraints ftyp 
           | `False ->
              let@ model = model () in
              fail (fun ctxt ->
                  let ctxt = { ctxt with resources = original_resources } in
                  {loc; msg = Unsat_constraint {constr = c; info; ctxt; model}}
                )
           end
        | I rt ->
           return rt
      in
      check_logical_constraints ftyp_c
    in
    let@ () = return (debug 9 (lazy !^"done")) in
    return rt

  let calltype_ft loc args (ftyp : AT.ft) : (RT.t, type_error) m =
    spine RT.subst RT.pp loc FunctionCall args ftyp

  let calltype_lft loc (ftyp : AT.lft) : (LRT.t, type_error) m =
    spine LRT.subst LRT.pp loc FunctionCall [] ftyp

  let calltype_lt loc args ((ltyp : AT.lt), label_kind) : (unit, type_error) m =
    let@ False.False = 
      spine False.subst False.pp 
        loc (LabelCall label_kind) args ltyp
    in
    return ()

  let calltype_packing loc (name : Id.t) (ft : AT.packing_ft) : (OutputDef.t, type_error) m =
    spine OutputDef.subst OutputDef.pp 
      loc (Pack (TPU_Predicate name)) [] ft

  let calltype_lpred_argument_inference loc (name : Id.t) 
        supplied_args (ft : AT.packing_ft) : (IT.t list, type_error) m =
    let@ output_assignment = 
      spine OutputDef.subst OutputDef.pp 
        loc (ArgumentInference name) supplied_args ft
    in
    return (List.map (fun o -> o.OutputDef.value) output_assignment)


  (* The "subtyping" judgment needs the same resource/lvar/constraint
     inference as the spine judgment. So implement the subtyping
     judgment 'arg <: RT' by type checking 'f(arg)' for 'f: RT -> False'. *)
  let subtype (loc : loc) arg (rtyp : RT.t) : (unit, type_error) m =
    let ft = AT.of_rt rtyp (AT.I False.False) in
    let@ False.False = 
      spine False.subst False.pp loc Subtyping [arg] ft in
    return ()


end


(*** pure value inference *****************************************************)

type vt = BT.t * IT.t
let vt_of_arg arg = (arg.bt, it_of_arg arg)

let rt_of_vt loc (bt,it) = 
  let s = Sym.fresh () in 
  RT.Computational ((s, bt), (loc, None),
  LRT.Constraint (t_ (def_ s it), (loc, None),
  LRT.I))


let infer_tuple (loc : loc) (vts : vt list) : (vt, type_error) m = 
  let bts, its = List.split vts in
  return (Tuple bts, IT.tuple_ its)

let infer_array (loc : loc) (vts : vt list) = 
  let item_bt = match vts with
    | [] -> Debug_ocaml.error "todo: empty arrays"
    | (item_bt, _) :: _ -> item_bt
  in
  let@ (_, it) = 
    ListM.fold_leftM (fun (index,it) (arg_bt, arg_it) -> 
        let@ () = ensure_base_type loc ~expect:item_bt arg_bt in
        return (index + 1, map_set_ it (int_ index, arg_it))
         ) (0, const_map_ Integer (default_ item_bt)) vts
  in
  return (BT.Map (Integer, item_bt), it)


let infer_constructor (loc : loc) (constructor : mu_ctor) 
                      (args : arg list) : (vt, type_error) m = 
  match constructor, args with
  | M_Ctuple, _ -> 
     infer_tuple loc (List.map vt_of_arg args)
  | M_Carray, args -> 
     infer_array loc (List.map vt_of_arg args)
  | M_Cspecified, [arg] ->
     return (vt_of_arg arg)
  | M_Cspecified, _ ->
     fail (fun _ -> {loc; msg = Number_arguments {has = List.length args; expect = 1}})
  | M_Cnil item_bt, [] -> 
     let bt = List item_bt in
     return (bt, nil_ ~item_bt)
  | M_Cnil item_bt, _ -> 
     fail (fun _ -> {loc; msg = Number_arguments {has = List.length args; expect=0}})
  | M_Ccons, [arg1; arg2] -> 
     let bt = List arg1.bt in
     let@ () = ensure_base_type arg2.loc ~expect:bt arg2.bt in
     let list_it = cons_ (it_of_arg arg1, it_of_arg arg2) in
     return (arg2.bt, list_it)
  | M_Ccons, _ ->
     fail (fun _ -> {loc; msg = Number_arguments {has = List.length args; expect = 2}})



let infer_ptrval (loc : loc) (ptrval : pointer_value) : (vt, type_error) m =
  CF.Impl_mem.case_ptrval ptrval
    ( fun ct -> 
      return (Loc, IT.null_) )
    ( fun sym -> 
      return (Loc, sym_ (sym, BT.Loc)) )
    ( fun _prov loc -> 
      return (Loc, pointer_ loc) )
    ( fun () -> 
      Debug_ocaml.error "unspecified pointer value" )

let rec infer_mem_value (loc : loc) (mem : mem_value) : (vt, type_error) m =
  let open BT in
  CF.Impl_mem.case_mem_value mem
    ( fun ct -> 
      fail (fun _ -> {loc; msg = Unspecified ct}) )
    ( fun _ _ -> 
      unsupported loc !^"infer_mem_value: concurrent read case" )
    ( fun it iv -> 
      return (Integer, int_ (Memory.int_of_ival iv)) )
    ( fun ft fv -> 
      unsupported loc !^"floats" )
    ( fun _ ptrval -> 
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
                 (member_values : (member * mem_value) list) : (vt, type_error) m =
  (* might have to make sure the fields are ordered in the same way as
     in the struct declaration *)
  let@ layout = get_struct_decl loc tag in
  let rec check fields spec =
    match fields, spec with
    | ((member, mv) :: fields), ((smember, sct) :: spec) 
         when member = smember ->
       let@ (member_bt, member_it) = infer_mem_value loc mv in
       let@ () = ensure_base_type loc ~expect:(BT.of_sct sct) member_bt in
       let@ member_its = check fields spec in
       return ((member, member_it) :: member_its)
    | [], [] -> 
       return []
    | ((id, mv) :: fields), ((smember, sbt) :: spec) ->
       Debug_ocaml.error "mismatch in fields in infer_struct"
    | [], ((member, _) :: _) ->
       fail (fun _ -> {loc; msg = Generic (!^"field" ^/^ Id.pp member ^^^ !^"missing")})
    | ((member,_) :: _), [] ->
       fail (fun _ -> {loc; msg = Generic (!^"supplying unexpected field" ^^^ Id.pp member)})
  in
  let@ it = check member_values (Memory.member_types layout) in
  return (BT.Struct tag, IT.struct_ (tag, it))

and infer_union (loc : loc) (tag : tag) (id : Id.t) 
                (mv : mem_value) : (vt, type_error) m =
  Debug_ocaml.error "todo: union types"

let rec infer_object_value (loc : loc)
                       (ov : 'bty mu_object_value) : (vt, type_error) m =
  match ov with
  | M_OVinteger iv ->
     let i = Memory.z_of_ival iv in
     return (Integer, z_ i)
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

let rec infer_value (loc : loc) (v : 'bty mu_value) : (vt, type_error) m = 
  match v with
  | M_Vobject ov ->
     infer_object_value loc ov
  | M_Vloaded lv ->
     infer_loaded_value loc lv
  | M_Vunit ->
     return (Unit, IT.unit_)
  | M_Vtrue ->
     return (Bool, IT.bool_ true)
  | M_Vfalse -> 
     return (Bool, IT.bool_ false)
  | M_Vlist (bt, vals) ->
     let@ its = 
       ListM.mapM (fun v -> 
           let@ (i_bt, i_it) = infer_value loc v in
           let@ () = ensure_base_type loc ~expect:bt i_bt in
           return i_it
         ) vals
     in
     return (BT.List bt, list_ ~item_bt:bt its)
  | M_Vtuple vals ->
     let@ vts = ListM.mapM (infer_value loc) vals in
     let bts, its = List.split vts in
     return (Tuple bts, tuple_ its)






(*** pure expression inference ************************************************)

let infer_array_shift loc asym1 ct asym2 =
  let@ arg1 = arg_of_asym asym1 in
  let@ arg2 = arg_of_asym asym2 in
  let@ () = ensure_base_type arg1.loc ~expect:Loc arg1.bt in
  let@ () = ensure_base_type arg2.loc ~expect:Integer arg2.bt in
  let@ provable = provable in
  (* let element_size = Memory.size_of_ctype ct in *)
  let v = arrayShift_ (it_of_arg arg1, ct, it_of_arg arg2) in
  (*   integerToPointerCast_
   *     (add_ (pointerToIntegerCast_ (it_of_arg arg1), 
   *            mul_ (int_ element_size, it_of_arg arg2)))
   * in *)
  let@ o_folded_length =
    map_and_fold_resources (fun re found ->
        match found, re with
        | Some _, _ -> 
           (re, found)
        | None, Point {ct = Array (_, Some length); pointer; _} ->
           begin match provable (t_ (eq__ pointer (it_of_arg arg1))) with
           | `True -> (re, Some length)
           | `False -> (re, found)
           end
        | _ -> 
           (re, found)
      ) None
  in
  match o_folded_length with
  | None -> 
     return (rt_of_vt loc (BT.Loc, v))
  | Some length ->
     (* TODO: this is unnecessary: we could have just unfolded the
        array in the loop above *)
     let@ unfolded_array = 
       RI.Special.unfold_array loc ArrayShift ct (it_of_arg arg1) 
         length (bool_ true) 
     in
     return (
       RT.concat (rt_of_vt loc (BT.Loc, v)) 
       (LRT.Resource (unfolded_array, (loc, None), LRT.I))
     )


let wrapI ity arg =
  (* try to follow wrapI from runtime/libcore/std.core *)
  let maxInt = Memory.max_integer_type ity in
  let minInt = Memory.min_integer_type ity in
  let dlt = Z.add (Z.sub maxInt minInt) (Z.of_int 1) in
  let r = rem_f___ (arg, z_ dlt) in
  ite_ (le_ (r, z_ maxInt), r, sub_ (r, z_ dlt))



let infer_pexpr (pe : 'bty mu_pexpr) : (RT.t, type_error) m = 
  let (M_Pexpr (loc, _annots, _bty, pe_)) = pe in
  let@ () = print_with_ctxt (fun ctxt ->
      debug 3 (lazy (action "inferring pure expression"));
      debug 3 (lazy (item "expr" (pp_pexpr pe)));
      debug 3 (lazy (item "ctxt" (Context.pp ctxt)))
    )
  in
  let@ rt = match pe_ with
    | M_PEsym sym ->
       let@ arg = arg_of_sym loc sym in
       return (rt_of_vt loc (vt_of_arg arg))
    | M_PEimpl i ->
       let@ global = get_global () in
       let rt = Global.get_impl_constant global i in
       return rt
    | M_PEval v ->
       let@ vt = infer_value loc v in
       return (rt_of_vt loc vt)
    | M_PEconstrained _ ->
       Debug_ocaml.error "todo: PEconstrained"
    | M_PEerror (err, asym) ->
       let@ arg = arg_of_asym asym in
       let@ provable = provable in
       begin match provable (t_ (bool_ false)) with
       | `True -> assert false
       | `False ->
          let@ model = model () in
          fail (fun ctxt -> {loc; msg = StaticError {err; ctxt; model}})
       end
    | M_PEctor (ctor, asyms) ->
       let@ args = args_of_asyms asyms in
       let@ vt = infer_constructor loc ctor args in
       return (rt_of_vt loc vt)
    | M_CivCOMPL _ ->
       Debug_ocaml.error "todo: CivCOMPL"
    | M_CivAND _ ->
       Debug_ocaml.error "todo: CivAND"
    | M_CivOR _ ->
       Debug_ocaml.error "todo: CivOR"
    | M_CivXOR (act, asym1, asym2) -> 
       let ity = match act.ct with
         | Integer ity -> ity
         | _ -> Debug_ocaml.error "M_CivXOR with non-integer c-type"
       in
       let@ arg1 = arg_of_asym asym1 in
       let@ arg2 = arg_of_asym asym2 in
       let@ () = ensure_base_type arg1.loc ~expect:Integer arg1.bt in
       let@ () = ensure_base_type arg2.loc ~expect:Integer arg2.bt in
       let vt = (Integer, xor_ ity (it_of_arg arg1, it_of_arg arg2)) in
       return (rt_of_vt loc vt)
    | M_Cfvfromint _ -> 
       unsupported loc !^"floats"
    | M_Civfromfloat _ -> 
       unsupported loc !^"floats"
    | M_PEarray_shift (asym1, ct, asym2) ->
       infer_array_shift loc asym1 ct asym2
    | M_PEmember_shift (asym, tag, member) ->
       let@ arg = arg_of_asym asym in
       let@ () = ensure_base_type arg.loc ~expect:Loc arg.bt in
       let@ provable = provable in
       let@ found =
         map_and_fold_resources (fun re found ->
             match found, re with
             | true, _ -> 
                (re, found)
             | false, Point {ct = Struct tag'; pointer; permission; _} 
                  when Sym.equal tag tag' ->
                begin match provable (t_ (and_ [eq__ pointer (it_of_arg arg);
                                                permission])) with
                | `True -> (re, true)
                | `False -> (re, found)
                end
             | _ -> 
                (re, found)
           ) false
       in
       let@ lrt = 
         if found then
           (* TODO: this is unecessary: we could have unfolded the
              struct in the loop above *)
           RI.Special.unfold_struct loc MemberShift tag (it_of_arg arg) (bool_ true) 
         else 
           return LRT.I
       in
       let@ layout = get_struct_decl loc tag in
       let@ _member_bt = get_member_type loc tag member layout in
       let@ offset = match Memory.member_offset layout member with
         | Some offset -> return offset
         | None -> fail (fun _ -> {loc; msg = Unknown_member (tag, member)})
       in
       let vt = (Loc, integerToPointerCast_ (add_ (pointerToIntegerCast_ (it_of_arg arg), int_ offset))) in
       return (RT.concat (rt_of_vt loc vt) lrt)
    | M_PEnot asym ->
       let@ arg = arg_of_asym asym in
       let@ () = ensure_base_type arg.loc ~expect:Bool arg.bt in
       let vt = (Bool, not_ (it_of_arg arg)) in
       return (rt_of_vt loc vt)
    | M_PEop (op, asym1, asym2) ->
       let@ arg1 = arg_of_asym asym1 in
       let@ arg2 = arg_of_asym asym2 in
       let v1 = it_of_arg arg1 in
       let v2 = it_of_arg arg2 in
       let (((ebt1, ebt2), rbt), result_it) =
         match op with
         | OpAdd ->   (((Integer, Integer), Integer), IT.add_ (v1, v2))
         | OpSub ->   (((Integer, Integer), Integer), IT.sub_ (v1, v2))
         | OpMul ->   (((Integer, Integer), Integer), IT.mul_ (v1, v2))
         | OpDiv ->   (((Integer, Integer), Integer), IT.div_ (v1, v2))
         | OpRem_t -> (((Integer, Integer), Integer), IT.rem_t___ (v1, v2))
         | OpRem_f -> (((Integer, Integer), Integer), IT.rem_f___ (v1, v2))
         | OpExp ->   (((Integer, Integer), Integer), IT.exp_ (v1, v2))
         | OpEq ->    (((Integer, Integer), Bool), IT.eq_ (v1, v2))
         | OpGt ->    (((Integer, Integer), Bool), IT.gt_ (v1, v2))
         | OpLt ->    (((Integer, Integer), Bool), IT.lt_ (v1, v2))
         | OpGe ->    (((Integer, Integer), Bool), IT.ge_ (v1, v2))
         | OpLe ->    (((Integer, Integer), Bool), IT.le_ (v1, v2))
         | OpAnd ->   (((Bool, Bool), Bool), IT.and_ [v1; v2])
         | OpOr ->    (((Bool, Bool), Bool), IT.or_ [v1; v2])
       in
       let@ () = ensure_base_type arg1.loc ~expect:ebt1 arg1.bt in
       let@ () = ensure_base_type arg2.loc ~expect:ebt2 arg2.bt in
       return (rt_of_vt loc (rbt, result_it))
    | M_PEstruct _ ->
       Debug_ocaml.error "todo: PEstruct"
    | M_PEunion _ ->
       Debug_ocaml.error "todo: PEunion"
    | M_PEmemberof _ ->
       Debug_ocaml.error "todo: M_PEmemberof"
    | M_PEcall (called, asyms) ->
       let@ global = get_global () in
       let@ decl_typ = match called with
         | CF.Core.Impl impl -> 
            return (Global.get_impl_fun_decl global impl )
         | CF.Core.Sym sym -> 
            let@ (_, t, _) = get_fun_decl loc sym in
            return t
       in
       let@ args = args_of_asyms asyms in
       Spine.calltype_ft loc args decl_typ
    | M_PEassert_undef (asym, _uloc, ub) ->
       let@ arg = arg_of_asym asym in
       let@ () = ensure_base_type arg.loc ~expect:Bool arg.bt in
       let@ provable = provable in
       begin match provable (t_ (it_of_arg arg)) with
       | `True -> return (rt_of_vt loc (Unit, unit_))
       | `False ->
          let@ model = model () in
          fail (fun ctxt -> {loc; msg = Undefined_behaviour {ub; ctxt; model}})
       end
    | M_PEbool_to_integer asym ->
       let@ arg = arg_of_asym asym in
       let@ () = ensure_base_type arg.loc ~expect:Bool arg.bt in
       let vt = (Integer, (ite_ (it_of_arg arg, int_ 1, int_ 0))) in
       return (rt_of_vt loc vt)
    | M_PEconv_int (act, asym) ->
       let@ arg = arg_of_asym asym in
       let@ () = ensure_base_type arg.loc ~expect:Integer arg.bt in
       (* try to follow conv_int from runtime/libcore/std.core *)
       let arg_it = it_of_arg arg in
       let ity = match act.ct with
         | Integer ity -> ity
         | _ -> Debug_ocaml.error "conv_int applied to non-integer type"
       in
       let@ provable = provable in
       begin match ity with
       | Bool ->
          let vt = (Integer, ite_ (eq_ (arg_it, int_ 0), int_ 0, int_ 1)) in
          return (rt_of_vt loc vt)
       | _
            when Sctypes.is_unsigned_integer_type ity ->
          let result = match provable (t_ (representable_ (act.ct, arg_it))) with
            | `True -> arg_it
            | `False ->
               ite_ (representable_ (act.ct, arg_it),
                     arg_it,
                     wrapI ity arg_it)
          in
          return (rt_of_vt loc (Integer, result))
       | _ ->
          begin match provable (t_ (representable_ (act.ct, arg_it))) with
          | `True -> return (rt_of_vt loc (Integer, arg_it))
          | `False ->
             let value = arg_it in
             let ict = act.ct in
             let@ model = model () in
             fail (fun ctxt ->
                 let msg = Int_unrepresentable {value; ict; ctxt; model} in
                 {loc; msg}
               )
          end
       end
    | M_PEwrapI (act, asym) ->
       let@ arg = arg_of_asym asym in
       let@ () = ensure_base_type arg.loc ~expect:Integer arg.bt in
       let ity = match act.ct with
         | Integer ity -> ity
         | _ -> Debug_ocaml.error "wrapI applied to non-integer type"
       in
       let result = wrapI ity (it_of_arg arg) in
       return (rt_of_vt loc (Integer, result))
  in  
  debug 3 (lazy (item "type" (RT.pp rt)));
  return rt


let rec check_tpexpr (e : 'bty mu_tpexpr) (typ : RT.t) : (unit, type_error) m = 
  let (M_TPexpr (loc, _annots, _, e_)) = e in
  let@ () = print_with_ctxt (fun ctxt ->
      debug 3 (lazy (action "checking pure expression"));
      debug 3 (lazy (item "expr" (group (pp_tpexpr e))));
      debug 3 (lazy (item "type" (RT.pp typ)));
      debug 3 (lazy (item "ctxt" (Context.pp ctxt)));
    )
  in
  match e_ with
  | M_PEif (casym, e1, e2) ->
     let@ carg = arg_of_asym casym in
     let@ () = ensure_base_type carg.loc ~expect:Bool carg.bt in
     ListM.iterM (fun (lc, e) ->
         pure begin
             let@ () = add_c (t_ lc) in
             let@ provable = provable in
             match provable (t_ (bool_ false)) with
             | `True -> return ()
             | `False -> check_tpexpr e typ
           end
       ) [(it_of_arg carg, e1); (not_ (it_of_arg carg), e2)]
  | M_PEcase (asym, pats_es) ->
     let@ arg = arg_of_asym asym in
     ListM.iterM (fun (pat, pe) ->
         pure begin 
             let@ () = pattern_match (it_of_arg arg) pat in
             let@ provable = provable in
             match provable (t_ (bool_ false)) with
             | `True -> return ()
             | `False -> check_tpexpr e typ
           end
       ) pats_es
  | M_PElet (p, e1, e2) ->
     let@ rt = infer_pexpr e1 in
     let@ () = match p with
       | M_Symbol sym -> bind (Some (Loc (loc_of_pexpr e1))) sym rt
       | M_Pat pat -> pattern_match_rt (Loc (loc_of_pexpr e1)) pat rt
     in
     check_tpexpr e2 typ
  | M_PEdone asym ->
     let@ arg = arg_of_asym asym in
     let@ () = Spine.subtype loc arg typ in
     return ()
  | M_PEundef (_loc, ub) ->
     let@ provable = provable in
     begin match provable (t_ (bool_ false)) with
     | `True -> assert false;
     | `False ->
        let@ model = model () in
        fail (fun ctxt -> {loc; msg = Undefined_behaviour {ub; ctxt; model}})
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
  let@ provable = provable in
  let@ all_resources = all_resources () in
  ListM.iterM (fun resource ->
      let constr = match resource with
        | Point p -> t_ (not_ p.permission)
        | QPoint p -> forall_ (p.q, BT.Integer) (not_ p.permission)
        | Predicate p -> t_ (not_ p.permission)
        | QPredicate p -> forall_ (p.q, BT.Integer) (not_ p.permission)
      in
      match provable constr with
      | `True -> return () 
      | `False -> 
         let@ model = model () in 
         fail (fun ctxt -> {loc; msg = Unused_resource {resource; ctxt; model}})
    ) all_resources


type labels = (AT.lt * label_kind) SymMap.t


let infer_expr labels (e : 'bty mu_expr) : (RT.t, type_error) m = 
  let (M_Expr (loc, _annots, e_)) = e in
  let@ () = print_with_ctxt (fun ctxt ->
       debug 3 (lazy (action "inferring expression"));
       debug 3 (lazy (item "expr" (group (pp_expr e))));
       debug 3 (lazy (item "ctxt" (Context.pp ctxt)));
    )
  in
  let@ result = match e_ with
    | M_Epure pe -> 
       infer_pexpr pe
    | M_Ememop memop ->
       let pointer_op op asym1 asym2 = 
         let@ arg1 = arg_of_asym asym1 in
         let@ arg2 = arg_of_asym asym2 in
         let@ () = ensure_base_type arg1.loc ~expect:Loc arg1.bt in
         let@ () = ensure_base_type arg2.loc ~expect:Loc arg2.bt in
         let vt = (Bool, op (it_of_arg arg1, it_of_arg arg2)) in
         return (rt_of_vt loc vt)
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
       | M_Ptrdiff (act, asym1, asym2) -> 
          let@ arg1 = arg_of_asym asym1 in
          let@ arg2 = arg_of_asym asym2 in
          let@ () = ensure_base_type arg1.loc ~expect:Loc arg1.bt in
          let@ () = ensure_base_type arg2.loc ~expect:Loc arg2.bt in
          (* copying and adapting from memory/concrete/impl_mem.ml *)
          let divisor = match act.ct with
            | Array (item_ty, _) -> Memory.size_of_ctype item_ty
            | ct -> Memory.size_of_ctype ct
          in
          let v =
            div_
              (sub_ (pointerToIntegerCast_ (it_of_arg arg1),
                     pointerToIntegerCast_ (it_of_arg arg2)),
               int_ divisor)
          in
          let vt = (Integer, v) in
          return (rt_of_vt loc vt)
       | M_IntFromPtr (act_from, act_to, asym) ->
          let@ arg = arg_of_asym asym in
          let@ () = ensure_base_type arg.loc ~expect:Loc arg.bt in
          let v = pointerToIntegerCast_ (it_of_arg arg) in
          let@ () = 
            (* after discussing with Kavyan *)
            let@ provable = provable in
            let lc = t_ (representable_ (act_to.ct, v)) in
            begin match provable lc with
            | `True -> return () 
            | `False ->
               let@ model = model () in
               fail (fun ctxt ->
                   let ict = act_to.ct in
                   let value = it_of_arg arg in
                   {loc; msg = Int_unrepresentable {value; ict; ctxt; model}}
                 )
            end
          in
          let vt = (Integer, v) in
          return (rt_of_vt loc vt)
       | M_PtrFromInt (act_from, act2_to, asym) ->
          let@ arg = arg_of_asym asym in
          let@ () = ensure_base_type arg.loc ~expect:Integer arg.bt in
          let vt = (Loc, integerToPointerCast_ (it_of_arg arg)) in
          return (rt_of_vt loc vt)
       | M_PtrValidForDeref (act, asym) ->
          (* check *)
          let@ arg = arg_of_asym asym in
          let@ () = ensure_base_type arg.loc ~expect:Loc arg.bt in
          let vt = (Bool, aligned_ (it_of_arg arg, act.ct)) in
          return (rt_of_vt loc vt)
       | M_PtrWellAligned (act, asym) ->
          let@ arg = arg_of_asym asym in
          let@ () = ensure_base_type arg.loc ~expect:Loc arg.bt in
          let vt = (Bool, aligned_ (it_of_arg arg, act.ct)) in
          return (rt_of_vt loc vt)
       | M_PtrArrayShift (asym1, act, asym2) ->
          infer_array_shift loc asym1 act.ct asym2
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
       | M_Create (asym, act, _prefix) -> 
          let@ arg = arg_of_asym asym in
          let@ () = ensure_base_type arg.loc ~expect:Integer arg.bt in
          let ret = Sym.fresh () in
          let value_s, value_t = IT.fresh (BT.of_sct act.ct) in
          let resource = 
            RE.Point {
                ct = act.ct; 
                pointer = sym_ (ret, Loc);
                permission = bool_ true;
                value = value_t; 
                init = bool_ false;
              }
          in
          let rt = 
            RT.Computational ((ret, Loc), (loc, None),
            LRT.Constraint (t_ (representable_ (pointer_ct act.ct, sym_ (ret, Loc))), (loc, None),
            LRT.Constraint (t_ (alignedI_ ~align:(it_of_arg arg) ~t:(sym_ (ret, Loc))), (loc, None),
            LRT.Logical ((value_s, BT.of_sct act.ct), (loc, None), 
            LRT.Resource (resource, (loc, None), 
            LRT.I)))))
          in
          return rt
       | M_CreateReadOnly (sym1, ct, sym2, _prefix) -> 
          Debug_ocaml.error "todo: CreateReadOnly"
       | M_Alloc (ct, sym, _prefix) -> 
          Debug_ocaml.error "todo: Alloc"
       | M_Kill (M_Dynamic, asym) -> 
          Debug_ocaml.error "todo: Free"
       | M_Kill (M_Static ct, asym) -> 
          let@ arg = arg_of_asym asym in
          let@ () = ensure_base_type arg.loc ~expect:Loc arg.bt in
          let@ _ = 
            RI.Special.point_request loc (Access Kill) ({
              ct = ct;
              pointer = it_of_arg arg;
              permission = bool_ true;
              value = BT.of_sct ct; 
              init = BT.Bool;
            }, None)
          in
          let rt = RT.Computational ((Sym.fresh (), Unit), (loc, None), I) in
          return rt
       | M_Store (_is_locking, act, pasym, vasym, mo) -> 
          let@ parg = arg_of_asym pasym in
          let@ varg = arg_of_asym vasym in
          let@ () = ensure_base_type loc ~expect:(BT.of_sct act.ct) varg.bt in
          let@ () = ensure_base_type loc ~expect:Loc parg.bt in
          (* The generated Core program will in most cases before this
             already have checked whether the store value is
             representable and done the right thing. Pointers, as I
             understand, are an exception. *)
          let@ () = 
            let in_range_lc = representable_ (act.ct, it_of_arg varg) in
            let@ provable = provable in
            let holds = provable (t_ in_range_lc) in
            match holds with
            | `True -> return () 
            | `False ->
               let@ model = model () in
               fail (fun ctxt ->
                   let msg = 
                     Write_value_unrepresentable {
                         ct = act.ct; 
                         location = it_of_arg parg; 
                         value = it_of_arg varg; 
                         ctxt;
                         model}
                   in
                   {loc; msg}
                 )
          in
          let@ _ = 
            RI.Special.point_request loc (Access (Store None)) ({
                ct = act.ct; 
                pointer = it_of_arg parg;
                permission = bool_ true;
                value = BT.of_sct act.ct; 
                init = BT.Bool;
              }, None)
          in
          let resource = 
            RE.Point {
                ct = act.ct;
                pointer = it_of_arg parg;
                permission = bool_ true;
                value = it_of_arg varg; 
                init = bool_ true;
              }
          in
          let rt = 
            RT.Computational ((Sym.fresh (), Unit), (loc, None),
            Resource (resource, (loc, None),
            LRT.I)) 
          in
          return rt
       | M_Load (act, pasym, _mo) -> 
          let@ parg = arg_of_asym pasym in
          let@ () = ensure_base_type parg.loc ~expect:Loc parg.bt in
          let@ point = 
            restore_resources 
              (RI.Special.point_request loc (Access (Load None)) ({ 
                     ct = act.ct;
                     pointer = it_of_arg parg;
                     permission = bool_ true; (* fix *)
                     value = BT.of_sct act.ct; 
                     init = BT.Bool;
                   }, None))
          in
          let@ () = 
            let@ provable = provable in
            match provable (t_ point.init) with
            | `True -> return () 
            | `False ->
               let@ model = model () in
               fail (fun ctxt -> {loc; msg = Uninitialised_read {ctxt; model}})
          in
          let ret = Sym.fresh () in
          let constr = def_ ret point.value in
          let rt = 
            RT.Computational ((ret, IT.bt point.value), (loc, None),
            Constraint (t_ constr, (loc, None),
            LRT.I)) 
          in
          return rt
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
       return rt
    | M_Eccall (_ctype, afsym, asyms) ->
       let@ args = args_of_asyms asyms in
       let@ (_loc, ft, _) = get_fun_decl loc afsym.sym in
       Spine.calltype_ft loc args ft
    | M_Eproc (fname, asyms) ->
       let@ (_, decl_typ) = match fname with
         | CF.Core.Impl impl -> 
            let@ global = get_global () in
            return (loc, Global.get_impl_fun_decl global impl)
         | CF.Core.Sym sym -> 
            let@ (loc, fun_decl, _) = get_fun_decl loc sym in
            return (loc, fun_decl)
       in
       let@ args = args_of_asyms asyms in
       Spine.calltype_ft loc args decl_typ
    | M_Erpredicate (pack_unpack, TPU_Predicate pname, asyms) ->
       let@ global = get_global () in
       let@ def = match Global.get_resource_predicate_def global (Id.s pname) with
         | Some def -> return def
         | None -> fail (fun _ -> {loc; msg = Unknown_resource_predicate (Id.s pname)})
       in
       let@ pointer_asym, iarg_asyms = match asyms with
         | pointer_asym :: iarg_asyms -> return (pointer_asym, iarg_asyms)
         | _ -> fail (fun _ -> {loc; msg = Generic !^"pointer argument to predicate missing"})
       in
       let@ pointer_arg = arg_of_asym pointer_asym in
       (* todo: allow other permission amounts *)
       let permission = bool_ true in
       let@ iargs = args_of_asyms iarg_asyms in
       let@ () = 
         (* "+1" because of pointer argument *)
         let has, expect = List.length iargs + 1, List.length def.iargs + 1 in
         if has = expect then return ()
         else fail (fun _ -> {loc; msg = Number_arguments {has; expect}})
       in
       let@ () = ensure_base_type pointer_arg.loc ~expect:Loc pointer_arg.bt in
       let@ () = ensure_base_type loc ~expect:Bool (IT.bt permission) in
       let@ () = 
         ListM.iterM (fun (arg, expected_sort) ->
             ensure_base_type arg.loc ~expect:expected_sort arg.bt
           ) (List.combine iargs (List.map snd def.iargs))
       in
       let instantiated_clauses = 
         let subst = 
           make_subst (
               (def.pointer, it_of_arg pointer_arg) ::
               (def.permission, permission) ::
               List.combine (List.map fst def.iargs) (List.map it_of_arg iargs)
             )
         in
         List.map (ResourcePredicates.subst_clause subst) def.clauses
       in
       let@ provable = provable in
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
                Id.pp pname
              in
              fail (fun _ -> {loc; msg = Generic err})
         in
         try_clauses [] instantiated_clauses
       in
       begin match pack_unpack with
       | Unpack ->
          let@ pred =
            RI.Special.predicate_request loc (Unpack (TPU_Predicate pname)) ({
                name = Id.s pname;
                pointer = it_of_arg pointer_arg;
                permission = permission;
                iargs = List.map it_of_arg iargs;
                oargs = List.map snd def.oargs;
              }, None)
          in
          let condition, outputs = AT.logical_arguments_and_return right_clause in
          let lc = and_ (List.map2 (fun it (o : OutputDef.entry) -> eq__ it o.value) pred.oargs outputs) in
          let lrt = LRT.concat condition (Constraint (t_ lc, (loc, None), I)) in
          return (RT.Computational ((Sym.fresh (), BT.Unit), (loc, None), lrt))
       | Pack ->
          let@ output_assignment = Spine.calltype_packing loc pname right_clause in
          let resource = 
            Predicate {
              name = Id.s pname;
              pointer = it_of_arg pointer_arg;
              permission = bool_ true;
              iargs = List.map it_of_arg iargs;
              oargs = List.map (fun (o : OutputDef.entry) -> o.value) output_assignment;
            }
          in
          let rt =
            (RT.Computational ((Sym.fresh (), BT.Unit), (loc, None),
             Resource (resource, (loc, None),
             LRT.I)))
          in
          return rt
       end
    | M_Erpredicate (pack_unpack, TPU_Struct tag, asyms) ->
       let@ args = args_of_asyms asyms in
       let@ () = 
         (* "+1" because of pointer argument *)
         let has = List.length args in
         if has = 1 then return ()
         else fail (fun _ -> {loc; msg = Number_arguments {has; expect = 1}})
       in
       let pointer_arg = List.hd args in
       let@ () = ensure_base_type pointer_arg.loc ~expect:Loc pointer_arg.bt in
       begin match pack_unpack with
       | Pack ->
          let situation = TypeErrors.Pack (TPU_Struct tag) in
          let@ resource = RI.Special.fold_struct loc situation tag 
                            (it_of_arg pointer_arg) (bool_ true) in
          let rt = 
            RT.Computational ((Sym.fresh (), BT.Unit), (loc, None),
            LRT.Resource (resource, (loc, None), 
            LRT.I))
          in
          return rt
       | Unpack ->
          let situation = TypeErrors.Unpack (TPU_Struct tag) in
          let@ lrt = 
            RI.Special.unfold_struct loc situation tag 
              (it_of_arg pointer_arg) (bool_ true) 
          in
          let rt = RT.Computational ((Sym.fresh (), BT.Unit), (loc, None), lrt) in
          return rt

       end
    | M_Elpredicate (have_show, pname, asyms) ->
       let@ global = get_global () in
       let@ def = match Global.get_logical_predicate_def global (Id.s pname) with
         | Some def -> return def
         | None -> fail (fun _ -> {loc; msg = Unknown_logical_predicate (Id.s pname)})
       in
       let@ args = 
         restore_resources begin 
           let@ supplied_args = args_of_asyms asyms in
           Spine.calltype_lpred_argument_inference loc pname 
             supplied_args def.infer_arguments 
           end
       in
       (* let@ () = 
        *   let has, expect = List.length args, List.length def.args in
        *   if has = expect then return ()
        *   else fail (fun _ -> {loc; msg = Number_arguments {has; expect}})
        * in
        * let@ () = 
        *   ListM.iterM (fun (arg, expected_sort) ->
        *       ensure_base_type arg.loc ~expect:expected_sort arg.bt
        *     ) (List.combine args (List.map snd def.args))
        * in *)
       let rt = 
         RT.Computational ((Sym.fresh (), BT.Unit), (loc, None), 
         LRT.Constraint (Pred {name = Id.s pname; args}, (loc, None),
         LRT.I))
       in
       begin match have_show with
       | Have ->
          let@ qarg = match def.qarg with
            | Some n -> return (List.nth args n)
            | None ->
               let err = 
                 "Cannot use predicate " ^ Id.s pname ^ 
                   " with 'Have' because it \
                    has no index/quantifier argument."
               in
               fail (fun _ -> {loc; msg = Generic !^err})
          in
          let@ provable = provable in
          let@ constraints = all_constraints () in
          let to_check = 
            let body = LP.open_pred global def args in
            let assumptions = 
              List.filter_map (function
                  | LC.QPred qpred' when String.equal qpred'.pred.name (Id.s pname) ->
                     let su = make_subst [(fst qpred'.q, qarg)] in
                     let condition' = IT.subst su qpred'.condition in
                     let pred_args' = List.map (IT.subst su) qpred'.pred.args in
                     Some (impl_ (condition', LP.open_pred global def pred_args'))
                  | _ -> 
                     None
                ) constraints
            in
            impl_ (and_ assumptions, body)
          in
          let@ () = match provable (t_ to_check) with
            | `True -> return ()
            | `False ->
               let@ model = model () in
               fail (fun ctxt -> {loc; msg = No_quantified_constraints {to_check; ctxt; model}})
          in
          return rt
       | Show ->
          let@ provable = provable in
          let lc = Pred {name = Id.s pname; args} in
          begin match provable lc with
          | `True -> return rt
          | `False ->
             let@ model = model () in
             fail (fun ctxt -> {loc; msg = Unsat_constraint {constr = lc; info = (loc, None); ctxt; model}})
          end
       end
  in
  debug 3 (lazy (RT.pp result));
  return result

(* check_expr: type checking for impure epressions; type checks `e`
   against `typ`, which is either a return type or `False`; returns
   either an updated environment, or `False` in case of Goto *)
let rec check_texpr labels (e : 'bty mu_texpr) (typ : RT.t orFalse) 
        : (unit, type_error) m = 

  let (M_TExpr (loc, _annots, e_)) = e in
  let@ () = print_with_ctxt (fun ctxt ->
      debug 3 (lazy (action "checking expression"));
      debug 3 (lazy (item "expr" (group (pp_texpr e))));
      debug 3 (lazy (item "type" (pp_or_false RT.pp typ)));
      debug 3 (lazy (item "ctxt" (Context.pp ctxt)));
    )
  in
  let@ result = match e_ with
    | M_Eif (casym, e1, e2) ->
       let@ carg = arg_of_asym casym in
       let@ () = ensure_base_type carg.loc ~expect:Bool carg.bt in
       ListM.iterM (fun (lc, e) ->
           pure begin 
               let@ () = add_c (t_ lc) in
               let@ provable = provable in
               match provable (t_ (bool_ false)) with
               | `True -> return ()
               | `False -> check_texpr labels e typ 
             end
         ) [(it_of_arg carg, e1); (not_ (it_of_arg carg), e2)]
    | M_Ebound (_, e) ->
       check_texpr labels e typ 
    | M_End _ ->
       Debug_ocaml.error "todo: End"
    | M_Ecase (asym, pats_es) ->
       let@ arg = arg_of_asym asym in
       ListM.iterM (fun (pat, pe) ->
           pure begin 
               let@ () = pattern_match (it_of_arg arg) pat in
               let@ provable = provable in
               match provable (t_ (bool_ false)) with
               | `True -> return ()
               | `False -> check_texpr labels e typ
             end
         ) pats_es
    | M_Elet (p, e1, e2) ->
       let@ rt = infer_pexpr e1 in
       let@ () = match p with 
         | M_Symbol sym -> bind (Some (Loc (loc_of_pexpr e1))) sym rt
         | M_Pat pat -> pattern_match_rt (Loc (loc_of_pexpr e1)) pat rt
       in
       check_texpr labels e2 typ
    | M_Ewseq (pat, e1, e2) ->
       let@ rt = infer_expr labels e1 in
       let@ () = pattern_match_rt (Loc (loc_of_expr e1)) pat rt in
       check_texpr labels e2 typ
    | M_Esseq (pat, e1, e2) ->
       let@ rt = infer_expr labels e1 in
       let@ () = match pat with
         | M_Symbol sym -> bind (Some (Loc (loc_of_expr e1))) sym rt
         | M_Pat pat -> pattern_match_rt (Loc (loc_of_expr e1)) pat rt
       in
       check_texpr labels e2 typ
    | M_Edone asym ->
       begin match typ with
       | Normal typ ->
          let@ arg = arg_of_asym asym in
          let@ () = Spine.subtype loc arg typ in
          all_empty loc
       | False ->
          let err = 
            "This expression returns but is expected "^
              "to have non-return type."
          in
          fail (fun _ -> {loc; msg = Generic !^err})
       end
    | M_Eundef (_loc, ub) ->
       let@ provable = provable in
       begin match provable (t_ (bool_ false)) with
       | `True -> assert false
       | `False ->
          let@ model = model () in
          fail (fun ctxt -> {loc; msg = Undefined_behaviour {ub; ctxt; model}})
       end
    | M_Erun (label_sym, asyms) ->
       let@ (lt,lkind) = match SymMap.find_opt label_sym labels with
         | None -> fail (fun _ -> {loc; msg = Generic (!^"undefined code label" ^/^ Sym.pp label_sym)})
         | Some (lt,lkind) -> return (lt,lkind)
       in
       let@ args = args_of_asyms asyms in
       let@ () = Spine.calltype_lt loc args (lt,lkind) in
       let@ () = all_empty loc in
       return ()

  in
  return result




let check_and_bind_arguments rt_subst loc arguments (function_typ : 'rt AT.t) = 
  let rec check resources args (ftyp : 'rt AT.t) =
    match args, ftyp with
    | ((aname,abt) :: args), (AT.Computational ((lname, sbt), _info, ftyp))
         when BT.equal abt sbt ->
       let new_lname = Sym.fresh () in
       let subst = make_subst [(lname, sym_ (new_lname, sbt))] in
       let ftyp' = AT.subst rt_subst subst ftyp in
       let@ () = add_l new_lname abt in
       let@ () = add_a aname (abt,new_lname) in
       check resources args ftyp'
    | ((aname, abt) :: args), (AT.Computational ((sname, sbt), _info, ftyp)) ->
       fail (fun _ -> {loc; msg = Mismatch {has = abt; expect = sbt}})
    | [], (AT.Computational (_, _, _))
    | (_ :: _), (AT.I _) ->
       let expect = AT.count_computational function_typ in
       let has = List.length arguments in
       fail (fun _ -> {loc; msg = Number_arguments {expect; has}})
    | args, (AT.Logical ((sname, sls), _, ftyp)) ->
       let@ () = add_l sname sls in
       check resources args ftyp
    | args, (AT.Define ((sname, it), _, ftyp)) ->
       let@ () = add_l sname (IT.bt it) in
       let@ () = add_c (t_ (def_ sname it)) in
       check resources args ftyp
    | args, (AT.Resource (re, _, ftyp)) ->
       check (re :: resources) args ftyp
    | args, (AT.Constraint (lc, _, ftyp)) ->
       let@ () = add_c lc in
       check resources args ftyp
    | [], (AT.I rt) ->
       return (rt, resources)
  in
  check [] arguments function_typ


(* check_function: type check a (pure) function *)
let check_function 
      (loc : loc) 
      (info : string) 
      (arguments : (Sym.t * BT.t) list) 
      (rbt : BT.t) 
      (body : 'bty mu_tpexpr) 
      (function_typ : AT.ft)
      (ctxt: Context.t)
    : (unit, type_error) Resultat.t =
  debug 2 (lazy (headline ("checking function " ^ info)));
  run ctxt begin
      let@ (rt, resources) = 
        check_and_bind_arguments RT.subst loc arguments function_typ 
      in
      let@ () = 
        ListM.iterM (fun r -> 
            let@ lcs = add_r (Some (Label "start")) r in
            add_cs lcs
          ) resources in
      (* rbt consistency *)
      let@ () = 
        let Computational ((sname, sbt), _info, t) = rt in
        ensure_base_type loc ~expect:sbt rbt
      in
      let@ () = check_tpexpr body rt in
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
      (ctxt: Context.t)
    : (unit, type_error) Resultat.t =
  debug 2 (lazy (headline ("checking procedure " ^ Sym.pp_string fsym)));
  debug 2 (lazy (item "type" (AT.pp RT.pp function_typ)));

  run ctxt begin 
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
        ensure_base_type loc ~expect:sbt rbt
      in
      (* check well-typedness of labels and record their types *)
      let@ labels = 
        PmapM.foldM (fun sym def acc ->
            pure begin 
                match def with
                | M_Return (loc, lt) ->
                   let@ () = WellTyped.WLT.good "return label" loc lt in
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
      let check_label lsym def () = 
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
             let@ () = 
               ListM.iterM (fun r ->
                   let@ lcs = add_r (Some (Label label_name)) r in
                   add_cs lcs
                 ) resources in
             let@ () = check_texpr labels body False in
             return ()
          end
      in
      let@ () = PmapM.foldM check_label label_defs () in
      (* check the function body *)
      debug 2 (lazy (headline ("checking function body " ^ Sym.pp_string fsym)));
      let@ () = 
        ListM.iterM (fun r -> 
            let@ lcs = add_r (Some (Label "start")) r in
            add_cs lcs
          ) resources 
      in
      check_texpr labels body (Normal rt)
    end

 


let check mu_file = 
  let open Resultat in
  let open Effectful.Make(Resultat) in

  let () = Debug_ocaml.begin_csv_timing "total" in

  let ctxt = Context.empty Global.empty in
  
  let () = Debug_ocaml.begin_csv_timing "tagDefs" in
  let@ ctxt = 
    (* check and record tagDefs *)
    let open Memory in
    PmapM.foldM (fun tag def ctxt ->
        match def with
        | M_UnionDef _ -> 
           unsupported Loc.unknown !^"todo: union types"
        | M_StructDef layout -> 
           let@ () =
             ListM.iterM (fun piece ->
                 match piece.member_or_padding with
                 | Some (_, Sctypes.Struct sym2) ->
                    if SymMap.mem sym2 ctxt.global.struct_decls then return ()
                    else fail {loc = Loc.unknown; msg = Unknown_struct sym2}
                 | _ -> return ()
               ) layout
           in
           let struct_decls = SymMap.add tag layout ctxt.global.struct_decls in
           let global = { ctxt.global with struct_decls } in
           return { ctxt with global }
      ) mu_file.mu_tagDefs ctxt
  in
  let () = Debug_ocaml.end_csv_timing "tagDefs" in

  let () = Debug_ocaml.begin_csv_timing "impls" in
  let@ ctxt = 
    (* check and record impls *)
    let open Global in
    PmapM.foldM (fun impl impl_decl ctxt ->
        let descr = CF.Implementation.string_of_implementation_constant impl in
        match impl_decl with
        | M_Def (rt, rbt, pexpr) -> 
           let@ () = Typing.run ctxt (WellTyped.WRT.good Loc.unknown rt) in
           let@ () = check_function Loc.unknown descr [] rbt pexpr (AT.I rt) ctxt in
           let ctxt = 
             let impl_constants = ImplMap.add impl rt ctxt.global.impl_constants in
             let global = { ctxt.global with impl_constants } in
             { ctxt with global }                           
           in
           return ctxt
        | M_IFun (ft, rbt, args, pexpr) ->
           let@ () = 
             let descr = "implementation-defined function" in
             Typing.run ctxt (WellTyped.WFT.good descr Loc.unknown ft)
           in
           let@ () = 
             let descr = (CF.Implementation.string_of_implementation_constant impl) in
             check_function Loc.unknown descr args rbt pexpr ft ctxt
           in
           let impl_fun_decls = ImplMap.add impl ft ctxt.global.impl_fun_decls in
           let global = { ctxt.global with impl_fun_decls } in
           return { ctxt with global }
      ) mu_file.mu_impl ctxt
  in
  let () = Debug_ocaml.end_csv_timing "impls" in
  

  let () = Debug_ocaml.begin_csv_timing "logical predicates" in
  let@ ctxt = 
    (* check and record logical predicate defs *)
    let number_entries = List.length (mu_file.mu_logical_predicates) in
    let ping = Pp.progress "logical predicate welltypedness" number_entries in
    ListM.fold_leftM (fun ctxt (name,(def : LP.definition)) -> 
        let@ () = return (ping name) in
        let@ () = Typing.run ctxt (WellTyped.WLPD.good def) in
        let logical_predicates =
          StringMap.add name def ctxt.global.logical_predicates in
        let global = { ctxt.global with logical_predicates } in
        return { ctxt with global }
      ) ctxt mu_file.mu_logical_predicates
  in
  let () = Debug_ocaml.end_csv_timing "logical predicates" in

  let () = Debug_ocaml.begin_csv_timing "resource predicates" in
  let@ ctxt = 
    (* check and record resource predicate defs *)
    let number_entries = List.length (mu_file.mu_resource_predicates) in
    let ping = Pp.progress "resource predicate welltypedness" number_entries in
    ListM.fold_leftM (fun ctxt (name,def) -> 
        let@ () = return (ping name) in
        let@ () = Typing.run ctxt (WellTyped.WRPD.good def) in
        let resource_predicates =
          StringMap.add name def ctxt.global.resource_predicates in
        let global = { ctxt.global with resource_predicates } in
        return { ctxt with global }
      ) ctxt mu_file.mu_resource_predicates
  in
  let () = Debug_ocaml.end_csv_timing "resource predicates" in


  let () = Debug_ocaml.begin_csv_timing "globals" in
  let@ ctxt = 
    (* record globals *)
    (* TODO: check the expressions *)
    ListM.fold_leftM (fun ctxt (sym, def) ->
        match def with
        | M_GlobalDef (lsym, (_, ct), _)
        | M_GlobalDecl (lsym, (_, ct)) ->
           let bt = Loc in
           let ctxt = Context.add_l lsym bt ctxt in
           let ctxt = Context.add_a sym (bt, lsym) ctxt in
           let ctxt = Context.add_c (t_ (IT.good_pointer ~pointee_ct:ct (sym_ (lsym, bt)))) ctxt in
           return ctxt
      ) ctxt mu_file.mu_globs 
  in
  let () = Debug_ocaml.end_csv_timing "globals" in

  let@ ctxt =
    PmapM.foldM
      (fun fsym (M_funinfo (loc, _attrs, ftyp, trusted, _has_proto)) ctxt ->
        let ctxt = 
          let lc1 = t_ (ne_ (null_, sym_ (fsym, Loc))) in
          let lc2 = t_ (representable_ (pointer_ct void_ct, sym_ (fsym, Loc))) in
          let ctxt = Context.add_l fsym Loc ctxt in
          let ctxt = Context.add_c lc1 ctxt in
          let ctxt = Context.add_c lc2 ctxt in
          ctxt
        in
        let fun_decls = SymMap.add fsym (loc, ftyp, trusted) ctxt.global.fun_decls in
        let global = { ctxt.global with fun_decls = fun_decls } in
        return {ctxt with global}
      ) mu_file.mu_funinfo ctxt
  in

  let () = Debug_ocaml.begin_csv_timing "welltypedness" in
  let@ () =
    let number_entries = List.length (Pmap.bindings_list mu_file.mu_funinfo) in
    let ping = Pp.progress "function welltypedness" number_entries in
    PmapM.iterM
      (fun fsym (M_funinfo (loc, _attrs, ftyp, _trusted, _has_proto)) ->
        let@ () = return (ping (Sym.pp_string fsym)) in
        let () = debug 2 (lazy (headline ("checking welltypedness of procedure " ^ Sym.pp_string fsym))) in
        let () = debug 2 (lazy (item "type" (AT.pp RT.pp ftyp))) in
        Typing.run ctxt (WellTyped.WFT.good "global" loc ftyp)
      ) mu_file.mu_funinfo
  in
  let () = Debug_ocaml.end_csv_timing "welltypedness" in

  let check_function =
    fun fsym fn ->
    let decl = Global.get_fun_decl ctxt.global fsym in
    let () = Debug_ocaml.begin_csv_timing "functions" in
    let@ () = match fn, decl with
      | M_Fun (rbt, args, body), Some (loc, ftyp, trusted) ->
         begin match trusted with
         | CF.Mucore.Trusted _ -> return ()
         | CF.Mucore.Checked -> 
            check_function loc (Sym.pp_string fsym) args rbt body ftyp ctxt
         end
      | M_Fun (rbt, args, body), None ->
         fail {loc = Loc.unknown; msg = Unknown_function fsym}
      | M_Proc (loc, rbt, args, body, labels), Some (loc', ftyp, trusted) ->
         begin match trusted with
         | CF.Mucore.Trusted _ -> return ()
         | CF.Mucore.Checked -> 
            check_procedure loc' fsym args rbt body ftyp labels ctxt
         end
      | M_Proc (loc, rbt, args, body, labels), None ->
         fail {loc; msg = Unknown_function fsym}
      | M_ProcDecl _, _ -> 
         return ()
      | M_BuiltinDecl _, _ -> 
         return ()
    in
    let () = Debug_ocaml.end_csv_timing "functions" in
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
