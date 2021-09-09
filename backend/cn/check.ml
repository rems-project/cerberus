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
open Tools

open IT
open TypeErrors
module Mu = Retype.New
open CF.Mucore
open Mu

open Pp
open BT
open Resources
open Resources.RE
open Predicates
open LogicalConstraints








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


module Make 
         (G : sig val global : Global.t end)
         (S : Solver.S) 
         (L : Local.S)
  = struct
  module WT = WellTyped.Make(G)(S)(L)
  module E = Explain.Make(G)(S)(L)


  module Typing = Typing.Make(L)
  open Typing
  open Effectful.Make(Typing)



  (*** meta types ***************************************************************)
  type mem_value = CF.Impl_mem.mem_value
  type pointer_value = CF.Impl_mem.pointer_value


  (*** auxiliaries **************************************************************)

  let ensure_logical_sort (loc : loc) ~(expect : LS.t) (has : LS.t) : unit m =
    if LS.equal has expect 
    then return () 
    else fail loc (Mismatch {has; expect})

  let ensure_base_type (loc : loc) ~(expect : BT.t) (has : BT.t) : unit m =
    ensure_logical_sort loc ~expect has


  let check_computational_bound loc s = 
    let@ is_bound = bound s KComputational in
    if is_bound then return ()
    else fail loc (Unbound_name (Sym s))

  let get_struct_decl loc tag = 
    let open Global in
    match SymMap.find_opt tag G.global.struct_decls with
      | Some decl -> return decl
      | None -> fail loc (Missing_struct tag)

  let get_member_type loc tag member layout = 
    match List.assoc_opt Id.equal member (Memory.member_types layout) with
    | Some membertyp -> return membertyp
    | None -> fail loc (Missing_member (tag, member))






  (*** pattern matching *********************************************************)


  let pattern_match = 

    let rec aux pat : IT.t m = 
      let (M_Pattern (loc, _, pattern) : mu_pattern) = pat in
      match pattern with
      | M_CaseBase (o_s, has_bt) ->
         let lsym = Sym.fresh () in 
         let@ () = add_l lsym has_bt in
         begin match o_s with
         | Some s -> 
            (* let@ is_bound = bound s KComputational in
             * if is_bound 
             * then fail loc (Name_bound_twice (Sym s))
             * else *)
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
            fail loc (Number_arguments {has = List.length pats; expect = 0})
         | M_Ccons, [p1; p2] ->
            let@ it1 = aux p1 in
            let@ it2 = aux p2 in
            let@ () = ensure_base_type loc ~expect:(List (IT.bt it1)) (IT.bt it2) in
            return (cons_ (it1, it2))
         | M_Ccons, _ -> 
            fail loc (Number_arguments {has = List.length pats; expect = 2})
         | M_Ctuple, pats ->
            let@ its = ListM.mapM aux pats in
            return (tuple_ its)
         | M_Cspecified, [pat] ->
            aux pat
         | M_Cspecified, _ ->
            fail loc (Number_arguments {expect = 1; has = List.length pats})
         | M_Carray, _ ->
            Debug_ocaml.error "todo: array types"
    in
    
    fun to_match ((M_Pattern (loc, _, _)) as pat : mu_pattern) ->
    let@ it = aux pat in
    let@ () = ensure_base_type loc ~expect:(IT.bt to_match) (IT.bt it) in
    add_c (t_ (eq_ (it, to_match)))
    


  (* The pattern-matching might de-struct 'bt'. For easily making
     constraints carry over to those values, record (lname,bound) as a
     logical variable and record constraints about how the variables
     introduced in the pattern-matching relate to (lname,bound). *)
  let pattern_match_rt loc (pat : mu_pattern) (rt : RT.t) : unit m =
    let@ (bt, s') = logically_bind_return_type (Some loc) rt in
    pattern_match (sym_ (s', bt)) pat





  (* resource inference *)



  module ResourceInference = struct 


    let missing_resource_failure situation (request, oinfo) = 
      fun local ->
      let model = S.get_model (L.solver local) in
      let (resource, state) = E.resource_request local model request in
      Missing_resource {resource; state; situation; oinfo}
    

    let unfold_array_request ct base_pointer_t length_t permission_t = 
      Resources.Requests.{
          ct = Sctype ([], Array (ct, Some length_t));
          pointer = base_pointer_t;
          value = BT.Array (Integer, of_sct ct);
          init = BT.Bool;
          permission = permission_t;
      }

    let unfold_struct_request tag pointer_t permission_t = 
      Resources.Requests.{
          ct = Sctype ([], Struct tag);
          pointer = pointer_t;
          value = Struct tag;
          init = BT.Bool;
          permission = permission_t;
      }

    let rec point_request loc (failure : failure) (requested : Resources.Requests.point) = 
      let needed = requested.permission in 
      let@ all_lcs = all_constraints () in
      let@ provable = provable in
      let@ (needed, value, init) =
        map_and_fold_resources (fun re (needed, value, init) ->
            match re with
            | Point p' 
                 when Sctypes.equal requested.ct p'.ct &&
                        provable (t_ (eq_ (requested.pointer, p'.pointer))) ->
                 let can_take = min_ (p'.permission, needed) in
                 let took = gt_ (can_take, q_ (0, 1)) in
                 let value = ite_ (took, p'.value, value) in
                 let init = ite_ (took, p'.init, init) in
                 let needed = sub_ (needed, can_take) in
                 let permission' = sub_ (p'.permission, can_take) in
                 Point {p' with permission = permission'}, (needed, value, init)
            | QPoint p' 
                 when Sctypes.equal requested.ct p'.ct &&
                      let subst = [(p'.qpointer, requested.pointer)] in
                      provable (t_ (gt_ (IT.subst subst p'.permission, q_ (0, 1)))) ->
               let subst = [(p'.qpointer, requested.pointer)] in
               let can_take = min_ (IT.subst subst p'.permission, needed) in
               let took = gt_ (can_take, q_ (0, 1)) in
               let value =  ite_ (took, IT.subst subst p'.value, value) in
               let init = ite_ (took, IT.subst subst p'.init, init) in
               let needed = sub_ (needed, can_take) in
               let permission' =
                 ite_ (eq_ (sym_ (p'.qpointer, BT.Loc), requested.pointer),
                       sub_ (IT.subst subst p'.permission, can_take),
                       p'.permission)
               in
               QPoint {p' with permission = permission'}, (needed, value, init)
            | re ->
               (re, (needed, value, init))
          ) (needed, default_ requested.value, default_ BT.Bool)
      in
      let holds = provable (t_ (eq_ (needed, q_ (0, 1)))) in
      if holds then
        let r = 
          { ct = requested.ct;
            pointer = requested.pointer;
            value = Simplify.simp all_lcs value;
            init = Simplify.simp all_lcs init;
            permission = requested.permission }
        in
        return r
      else 
        let@ lrt = match requested.ct with
          | Sctype (_, Array (act, Some length)) ->
             fold_array loc failure act requested.pointer length (q_ (1, 1))
          | Sctype (_, Struct tag) ->
             fold_struct loc failure tag requested.pointer (q_ (1, 1))
          | _ -> 
             failS loc failure
        in
        let@ () = bind_logical_return_type (Some (Local.Loc loc)) lrt in
        point_request loc failure requested


    and qpoint_request loc failure (requested : Resources.Requests.qpoint) = 
      let needed = requested.permission in
      let@ all_lcs = all_constraints () in
      let@ provable = provable in
      let@ (needed, value, init) =
        map_and_fold_resources (fun re (needed, value, init) ->
            match re with
            | Point p' 
                 when Sctypes.equal requested.ct p'.ct &&
                      let subst = [(requested.qpointer, p'.pointer)] in
                      provable (t_ (gt_ (IT.subst subst needed, q_ (0, 1)))) ->
               let subst = [(requested.qpointer, p'.pointer)] in
               let can_take = min_ (p'.permission, IT.subst subst needed) in
               let pmatch = eq_ (sym_ (requested.qpointer, BT.Loc), p'.pointer) in
               let needed = ite_ (pmatch, sub_ (IT.subst subst needed, can_take), needed) in
               let took = gt_ (can_take, q_ (0, 1)) in
               let value = ite_ (and_ [pmatch;took], p'.value, value) in
               let init = ite_ (and_ [pmatch;took], p'.init, init) in
               let permission' = sub_ (p'.permission, can_take) in
               (Point {p' with permission = permission'}, (needed, value, init))
            | QPoint p' 
                 when Sctypes.equal requested.ct p'.ct ->
               let subst = [(p'.qpointer, sym_ (requested.qpointer, Loc))] in
               let can_take = min_ (IT.subst subst p'.permission, needed) in
               let took = gt_ (can_take, q_ (0, 1)) in
               let needed = sub_ (needed, can_take) in
               let value = ite_ (took, IT.subst subst p'.value, value) in
               let init = ite_ (took, IT.subst subst p'.init, init) in
               let permission' = 
                 sub_ (p'.permission, 
                       IT.subst [(requested.qpointer, sym_ (p'.qpointer, Loc))] can_take)
               in
               (QPoint {p' with permission = permission'}, (needed, value, init))
            | re ->
               (re, (needed, value, init))
          ) (needed, default_ requested.value, default_ BT.Bool)
      in
      let holds =
        provable (forall_ (requested.qpointer, BT.Loc) None
                    (eq_ (needed, q_ (0, 1))))
      in
      if holds then
        let r = 
          { ct = requested.ct;
            qpointer = requested.qpointer;
            value = Simplify.simp all_lcs value; 
            init = Simplify.simp all_lcs init;
            permission = requested.permission;
          } 
        in
        return r
      else 
        failS loc failure


    and predicate_request loc failure (requested : Resources.Requests.predicate) = 
      let needed = requested.permission in 
      let@ all_lcs = all_constraints () in
      let@ provable = provable in
      let@ (needed, oargs) =
        map_and_fold_resources (fun re (needed, oargs) ->
            match re with
            | Predicate p' 
                 when String.equal requested.name p'.name &&
                      provable 
                        (t_ (and_ (eq_ (requested.pointer, p'.pointer) ::
                                     List.map2 eq__ requested.iargs p'.iargs)))  ->
               let can_take = min_ (p'.permission, needed) in
               let took = gt_ (can_take, q_ (0, 1)) in
               let oargs = List.map2 (fun oarg oarg' -> ite_ (took, oarg', oarg)) oargs p'.oargs in
               let needed = sub_ (needed, can_take) in
               let permission' = sub_ (p'.permission, can_take) in
               Predicate {p' with permission = permission'}, (needed, oargs)
            | QPredicate p' 
                 when String.equal requested.name p'.name && 
                      let subst = [(p'.qpointer, requested.pointer)] in
                      provable
                        (t_ (and_ (List.map2 (fun iarg iarg' -> 
                                       eq__ iarg (IT.subst subst iarg')
                                     ) requested.iargs p'.iargs))) ->
               let subst = [(p'.qpointer, requested.pointer)] in
               let can_take = min_ (IT.subst subst p'.permission, needed) in
               let took = gt_ (can_take, q_ (0, 1)) in
               let oargs = List.map2 (fun oarg oarg' -> ite_ (took, oarg', oarg)) oargs p'.oargs in
               let permission' =
                 ite_ (eq_ (sym_ (p'.qpointer, BT.Loc), requested.pointer),
                       sub_ (IT.subst subst p'.permission, can_take),
                       p'.permission)
               in
               QPredicate {p' with permission = permission'}, (needed, oargs)
            | re ->
               (re, (needed, oargs))
          ) (needed, List.map (fun oarg -> default_ oarg) requested.oargs)
      in
      let holds = provable (t_ (eq_ (needed, q_ (0, 1)))) in
      if holds then
        let r = 
          { name = requested.name;
            pointer = requested.pointer;
            permission = requested.permission;
            iargs = requested.iargs; 
            oargs = List.map (Simplify.simp all_lcs) oargs
          }
        in
        return r
      else 
        failS loc failure

    and qpredicate_request loc failure (requested : Resources.Requests.qpredicate) = 
      let needed = requested.permission in
      let@ all_lcs = all_constraints () in
      let@ provable = provable in
      let@ (needed, oargs) =
        map_and_fold_resources (fun re (needed, oargs) ->
            match re with
            | Predicate p' 
                 when String.equal requested.name p'.name &&
                      let subst = [(requested.qpointer, p'.pointer)] in
                      provable
                        (t_ (and_ (List.map2 (fun iarg iarg' -> 
                                       eq__ (IT.subst subst iarg) iarg'
                                     ) requested.iargs p'.iargs))) ->
               let subst = [(requested.qpointer, p'.pointer)] in
               let can_take = min_ (p'.permission, IT.subst subst needed) in
               let pmatch = eq_ (sym_ (requested.qpointer, BT.Loc), p'.pointer) in
               let needed = ite_ (pmatch, sub_ (IT.subst subst needed, can_take), needed) in
               let took = gt_ (can_take, q_ (0, 1)) in
               let oargs = List.map2 (fun oarg oarg' -> ite_ (and_ [pmatch;took], oarg', oarg)) oargs p'.oargs in
               let permission' = sub_ (p'.permission, can_take) in
               (Predicate {p' with permission = permission'}, (needed, oargs))
            | QPredicate p' 
                 when String.equal requested.name p'.name &&
                      let subst = [(p'.qpointer, sym_ (requested.qpointer, Loc))] in
                      provable
                        (t_ (and_ (List.map2 (fun iarg iarg' -> 
                                       eq__ iarg (IT.subst subst iarg')
                                     ) requested.iargs p'.iargs))) ->
               let subst = [(p'.qpointer, sym_ (requested.qpointer, Loc))] in
               let can_take = min_ (IT.subst subst p'.permission, needed) in
               let took = gt_ (can_take, q_ (0, 1)) in
               let needed = sub_ (needed, can_take) in
               let oargs = List.map2 (fun oarg oarg' -> ite_ (took, IT.subst subst oarg', oarg)) oargs p'.oargs in
               let permission' = 
                 sub_ (p'.permission, 
                       IT.subst [(requested.qpointer, sym_ (p'.qpointer, Loc))] can_take)
               in
               (QPredicate {p' with permission = permission'}, (needed, oargs))
            | re ->
               (re, (needed, oargs))
          ) (needed, List.map default_ requested.oargs)
      in
      let holds =
        provable
          (forall_ (requested.qpointer, BT.Loc) None
             (eq_ (needed, q_ (0, 1))))
      in
      if holds then
        let r = 
          { name = requested.name;
            qpointer = requested.qpointer;
            permission = requested.permission;
            iargs = requested.iargs; 
            oargs = List.map (Simplify.simp all_lcs) oargs;
          } 
        in
        return r
      else  
        failS loc failure


    and fold_array loc failure ct base_pointer_t length_t permission_t =
      let element_size = int_ (Memory.size_of_ctype ct) in
      let@ qpoint = 
        let qp_s, qp_t = IT.fresh Loc in
        qpoint_request loc failure {
          ct = ct;
          qpointer = qp_s;
          value = BT.of_sct ct;
          init = BT.Bool;
          permission = 
            array_permission qp_t base_pointer_t (int_ length_t)
              element_size permission_t;
        }
      in
      let@ provable = provable in
      let folded_init_t = 
        bool_ (provable (
          forall_ (qpoint.qpointer, Loc) None
            (impl_ (gt_ (qpoint.permission, q_ (0, 1)), qpoint.init))
          ))
      in
      let folded_value_s, folded_value_t = 
        IT.fresh (Array (Integer, BT.of_sct ct)) in
      let folded_resource = 
        Point {
             ct = Sctype ([], Array (ct, Some length_t));
             pointer = base_pointer_t;
             value = folded_value_t;
             init = folded_init_t;
             permission = permission_t;
           }
      in
      let fold_value_constr = 
        let i_s, i_t = IT.fresh Integer in
        let i_pointer = 
          array_index_to_pointer base_pointer_t element_size i_t in
        forall_ (i_s, IT.bt i_t) None
          (impl_ 
             (array_index_in_range i_t (int_ length_t),
              eq__ 
                (app_ folded_value_t i_t)
                (IT.subst [(qpoint.qpointer, i_pointer)] 
                   qpoint.value)))
      in
      let lrt = 
        LRT.Logical ((folded_value_s, IT.bt folded_value_t), (loc, None),
        LRT.Resource (folded_resource, (loc, None),
        LRT.Constraint (fold_value_constr, (loc, None),
        LRT.I)))
      in
      return lrt

    and unfold_array loc failure ct base_pointer_t length_t permission_t =   
      let element_size = int_ (Memory.size_of_ctype ct) in
      let@ point = 
        point_request loc failure 
          (unfold_array_request
             ct base_pointer_t length_t permission_t) 
      in
      let unfolded_resource = 
        let qp_s, qp_t = IT.fresh Loc in
        QPoint {
            ct = ct;
            qpointer = qp_s;
            value = 
              app_ point.value 
                (array_pointer_to_index base_pointer_t element_size qp_t); 
            init = point.init;
            permission = 
              array_permission qp_t base_pointer_t (int_ length_t) 
                element_size permission_t;
          }
      in
      let lrt = LRT.Resource (unfolded_resource, (loc, None), LRT.I) in
      return lrt


    and fold_struct loc failure tag pointer_t permission_t =
      let open Memory in
      let layout = SymMap.find tag G.global.struct_decls in
      let@ (values, inits) = 
        ListM.fold_rightM (fun {offset; size; member_or_padding} (values, inits) ->
            let member_p = addPointer_ (pointer_t, int_ offset) in
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
               return ((member, point.value) :: values, point.init :: inits)
            | None ->
               let rec bytes i =
                 if i = size then return () else
                   let@ _ = 
                     point_request loc failure {
                         ct = Sctype ([], Integer Char);
                         pointer = addPointer_ (member_p, int_ i);
                         permission = permission_t;
                         value = BT.Integer;
                         init = BT.Bool;
                       } 
                   in
                   bytes (i + 1)
               in
               let@ () = bytes 0 in
               return (values, inits)
       ) layout ([], [])
      in
      let folded_resource = 
        Point {
            ct = Sctype ([], Struct tag);
            pointer = pointer_t;
            value = IT.struct_ (tag, values); 
            init = and_ inits;
            permission = permission_t;
          }
      in
      return (LRT.Resource (folded_resource, (loc, None), LRT.I))

    and unfold_struct loc failure tag pointer_t permission_t = 
      let@ point = 
        point_request loc failure 
          (unfold_struct_request tag pointer_t permission_t)
      in
      let layout = SymMap.find tag G.global.struct_decls in
      let lrt = 
        let open Memory in
        List.fold_right (fun {offset; size; member_or_padding} lrt ->
            let member_p = addPointer_ (pointer_t, int_ offset) in
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
                   let member_p = addPointer_ (member_p, int_ i) in
                   let padding_s, padding_t = IT.fresh BT.Integer in
                   let resource = 
                     Point {
                         ct = Sctype ([], Integer Char);
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



    let point_request loc situation (request, oinfo) = 
      point_request loc 
        (missing_resource_failure situation (Point request, oinfo))
        request
            

    let qpoint_request loc situation (request, oinfo) = 
      qpoint_request loc
        (missing_resource_failure situation (QPoint request, oinfo))
        request

    let predicate_request loc situation (request, oinfo) = 
      predicate_request loc 
        (missing_resource_failure situation (Predicate request, oinfo))
        request

    let qpredicate_request loc situation (request, oinfo) = 
      qpredicate_request loc 
        (missing_resource_failure situation (QPredicate request, oinfo))
        request

    let resource_request loc situation ((request : Resources.Requests.t), oinfo) : RE.t m = 
      match request with
      | Point requested ->
         let@ point = point_request loc situation (requested, oinfo) in
         return (Point point)
      | QPoint requested ->
         let@ qpoint = qpoint_request loc situation (requested, oinfo) in
         return (QPoint qpoint)
      | Predicate requested ->
         let@ predicate = predicate_request loc situation (requested, oinfo) in
         return (Predicate predicate)
      | QPredicate requested ->
         let@ qpredicate = qpredicate_request loc situation (requested, oinfo) in
         return (QPredicate qpredicate)

    let unfold_array loc situation ct base_pointer_t length_t permission_t = 
      unfold_array loc 
        (missing_resource_failure situation 
           (Point (unfold_array_request ct base_pointer_t length_t permission_t), None))
         ct base_pointer_t length_t permission_t

    let unfold_struct loc situation tag pointer_t permission_t = 
      unfold_struct loc 
        (missing_resource_failure situation 
           (Point (unfold_struct_request tag pointer_t permission_t), None))
         tag pointer_t permission_t

  end


  module RI = ResourceInference


  (*** function call typing, subtyping, and resource inference *****************)

  (* spine is parameterised so it can be used both for function and
     label types (which don't have a return type) *)



  type arg = {lname : Sym.t; bt : BT.t; loc : loc}
  type args = arg list
  let it_of_arg arg = sym_ (arg.lname, arg.bt)

  let arg_of_sym (loc : loc) (sym : Sym.t) : arg m = 
    let@ () = check_computational_bound loc sym in
    let@ (bt,lname) = get_a sym in
    return {lname; bt; loc}

  let arg_of_asym (asym : 'bty asym) : arg m = 
    arg_of_sym asym.loc asym.sym

  let args_of_asyms (asyms : 'bty asyms) : args m = 
    ListM.mapM arg_of_asym asyms



  module Spine : sig
    val calltype_ft : 
      Loc.t -> args -> AT.ft -> RT.t m
    val calltype_lft : 
      Loc.t -> AT.lft -> LRT.t m
    val calltype_lt : 
      Loc.t -> args -> AT.lt * label_kind -> unit m
    val calltype_packing : 
      Loc.t -> Id.t -> AT.packing_ft -> OutputDef.t m
    val subtype : 
      Loc.t -> arg -> RT.t -> unit m
  end = struct

    let pp_unis (unis : (LS.t * Loc.info) SymMap.t) : Pp.document = 
     Pp.list (fun (sym, (ls, _)) ->
       Sym.pp sym ^^^ !^"unresolved" ^^^ parens (LS.pp ls)
       ) (SymMap.bindings unis)



    (* requires equality on inputs *)
    (* could optimise to delay checking the constraints until later *)
    let match_resources loc failure =

      let make_array quantifier body = 
        let body, ls, cs = RE.make_array quantifier body in
        let@ () = add_ls ls in
        let@ cs = add_cs cs in
        return body
      in

      let ls_matches_spec unis uni_var instantiation = 
        let (expect, info) = SymMap.find uni_var unis in
        if LS.equal (IT.bt instantiation) expect 
        then return ()
        else fail loc (Mismatch_lvar { has = IT.bt instantiation; expect; spec_info = info})
      in

      let unify_or_constrain (unis, subst, constrs) (output_spec, output_have) =
        match IT.subst subst output_spec with
        | IT (Lit (Sym s), _) when SymMap.mem s unis ->
           let@ () = ls_matches_spec unis s output_have in
           return (SymMap.remove s unis, (s, output_have) :: subst, constrs)
        | _ ->
           return (unis, subst, eq_ (output_spec, output_have) :: constrs)
      in
      let unify_or_constrain_list = ListM.fold_leftM unify_or_constrain in

      (* ASSUMES unification variables and quantifier q_s are disjoint  *)
      let unify_or_constrain_q (q_s,q_bt) (unis, subst, constrs) (output_spec, output_have) = 
        match IT.subst subst output_spec with
        | IT (Array_op (App (IT (Lit (Sym s), _), IT (Lit (Sym q'), _))), _) 
             when Sym.equal q' q_s && SymMap.mem s unis ->
           let@ output_have_body = make_array (q_s, q_bt) output_have in
           let@ () = ls_matches_spec unis s output_have_body in
           return (SymMap.remove s unis, (s, output_have_body) :: subst, constrs)
        | _ ->
           return (unis, subst, eq_ (output_spec, output_have) :: constrs)
      in
      let unify_or_constrain_q_list q = ListM.fold_leftM (unify_or_constrain_q q) in

      fun (unis : (LS.t * Loc.info) SymMap.t) r_spec r_have ->

      match r_spec, r_have with
      | Point p_spec, Point p_have
           when Sctypes.equal p_spec.ct p_have.ct &&
                IT.equal p_spec.pointer p_have.pointer &&
                IT.equal p_spec.permission p_have.permission ->
         let@ (unis, subst, constrs) = 
           unify_or_constrain_list (unis, [], []) 
             [(p_spec.value, p_have.value); (p_spec.init, p_have.init)] 
         in
         let@ provable = provable in
         let result = 
           provable (t_ (impl_ (gt_ (p_have.permission, q_ (0, 1)), and_ constrs)))
         in
         if result then return (unis, subst) else failS loc failure
      | QPoint p_spec, QPoint p_have
           when Sctypes.equal p_spec.ct p_have.ct &&
                Sym.equal p_spec.qpointer p_have.qpointer &&
                IT.equal p_spec.permission p_have.permission ->
         let p_spec, p_have = 
           let qpointer = Sym.fresh_same p_spec.qpointer in
           RE.alpha_rename_qpoint qpointer p_spec,
           RE.alpha_rename_qpoint qpointer p_have
         in

         let@ (unis, subst, constrs) = 
           unify_or_constrain_q_list (p_have.qpointer, Loc) (unis, [], []) 
             [(p_spec.value, p_have.value); (p_spec.init, p_have.init)] 
         in

         let@ provable = provable in
         let result = 
           provable
              (forall_ (p_have.qpointer, BT.Loc) None
                 (impl_ (gt_ (p_have.permission, q_ (0, 1)), and_ constrs)))
         in
         if result then return (unis, subst) else failS loc failure
      | Predicate p_spec, Predicate p_have 
           when predicate_name_equal p_spec.name p_have.name &&
                IT.equal p_spec.pointer p_have.pointer &&
                IT.equal p_spec.permission p_have.permission &&
                List.equal IT.equal p_spec.iargs p_have.iargs ->
         let@ (unis, subst, constrs) = 
           unify_or_constrain_list (unis, [], [])
             (List.combine p_spec.oargs p_have.oargs) in
         let@ provable = provable in
         let result =
           provable (t_ (impl_ (gt_ (p_have.permission, q_ (0, 1)), and_ constrs)))
         in
         if result then return (unis, subst) else failS loc failure
      | QPredicate p_spec, QPredicate p_have 
           when predicate_name_equal p_spec.name p_have.name &&
                Sym.equal p_spec.qpointer p_have.qpointer &&
                IT.equal p_spec.permission p_have.permission &&
                List.equal IT.equal p_spec.iargs p_have.iargs ->
         let p_spec, p_have = 
           let qpointer = (Sym.fresh_same p_spec.qpointer) in
           RE.alpha_rename_qpredicate qpointer p_spec,
           RE.alpha_rename_qpredicate qpointer p_have 
         in
         let@ (unis, subst, constrs) = 
           unify_or_constrain_q_list (p_have.qpointer, Loc)
             (unis, [], []) (List.combine p_spec.oargs p_have.oargs) 
         in
         let@ provable = provable in
         let result =
           provable
             (forall_ (p_have.qpointer, BT.Loc) None
                (impl_ (gt_ (p_have.permission, q_ (0, 1)), and_ constrs)))
         in
         if result then return (unis, subst) else failS loc failure
      | _ -> 
         Debug_ocaml.error "resource inference has inferred mismatched resources"





    


    let resource_mismatch_failure situation resource resource' =
      fun local ->
      let model = S.get_model (L.solver local) in
      let ((expect,has), state) = 
        E.resources local model (resource, resource') in
      (Resource_mismatch {expect; has; state; situation})
  

    let spine :
          'rt. 
          (IT.t Subst.t -> 'rt -> 'rt) ->
          ('rt -> Pp.doc) ->
          Loc.t ->
          situation ->
          arg list ->
          'rt AT.t ->
          'rt m
      =
      fun rt_subst rt_pp
          loc situation arguments ftyp ->

      let open NormalisedArgumentTypes in

      let ftyp = normalise ftyp in

      let@ () = print_with_local (fun l ->
          debug 6 (lazy (checking_situation situation));
          debug 6 (lazy (item "local" (L.pp l)));
          debug 6 (lazy (item "spec" (pp rt_pp ftyp)))
        )
      in

      let@ ftyp_l = 
        let rec check_computational args ftyp = 
          match args, ftyp with
          | (arg :: args), (Computational ((s, bt), _info, ftyp))
               when BT.equal arg.bt bt ->
             check_computational args 
               (subst rt_subst [(s, sym_ (arg.lname, bt))] ftyp)
          | (arg :: _), (Computational ((_, bt), _info, _))  ->
             fail arg.loc (Mismatch {has = arg.bt; expect = bt})
          | [], (L ftyp) -> 
             return ftyp
          | _ -> 
             let expect = count_computational ftyp in
             let has = List.length arguments in
             fail loc (Number_arguments {expect; has})
        in
        check_computational arguments ftyp 
      in

      let@ (unis, ftyp_r) = 
        let rec delay_logical unis ftyp =
          let@ () = print_with_local (fun l ->
              debug 6 (lazy (item "local" (L.pp l)));
              debug 6 (lazy (item "spec" (pp_l rt_pp ftyp)))
            )
          in
          match ftyp with
          | Logical ((s, ls), info, ftyp) ->
             let s' = Sym.fresh () in
             delay_logical (SymMap.add s' (ls, info) unis) 
               (subst_l rt_subst [(s, sym_ (s', ls))] ftyp)
          | R ftyp -> 
             return (unis, ftyp)
        in
        delay_logical SymMap.empty ftyp_l
      in

      let@ (unis, ftyp_c) = 
        let rec infer_resources unis ftyp = 
          let@ () = print_with_local (fun l ->
              debug 6 (lazy (item "local" (L.pp l)));
              debug 6 (lazy (item "spec" (pp_r rt_pp ftyp)));
              debug 6 (lazy (item "unis" (pp_unis unis)))
            )
          in
          match ftyp with
          | Resource (resource, info, ftyp) -> 
             let request = RE.request resource in
             let@ resource' = RI.resource_request loc situation (request, Some info) in
             let@ (unis, new_subst) = 
               match_resources loc (resource_mismatch_failure situation resource resource')
                 unis resource resource' in
             infer_resources unis (subst_r rt_subst new_subst ftyp)
          | C ftyp ->
             return (unis, ftyp)
        in
        infer_resources unis ftyp_r
      in

      let () = match SymMap.min_binding_opt unis with
        | Some (s, _) ->
           Debug_ocaml.error ("Unconstrained_logical_variable " ^ Sym.pp_string s)
        | None ->
           ()
      in

      let@ rt = 
        let@ provable = provable in
        let rec check_logical_constraints = function
          | Constraint (c, info, ftyp) -> 
             if provable c then check_logical_constraints ftyp else
               failS loc (fun local ->
                   let (constr,state) = 
                     E.unsatisfied_constraint local 
                       (L.get_model (L.solver local)) c
                   in
                   (Unsat_constraint {constr; state; info})
                 )
          | I rt ->
             return rt
        in
        check_logical_constraints ftyp_c
      in
      return rt

    let calltype_ft loc args (ftyp : AT.ft) : RT.t m =
      spine RT.subst RT.pp loc FunctionCall args ftyp

    let calltype_lft loc (ftyp : AT.lft) : LRT.t m =
      spine LRT.subst LRT.pp loc FunctionCall [] ftyp

    let calltype_lt loc args ((ltyp : AT.lt), label_kind) : unit m =
      let@ False.False = 
        spine False.subst False.pp 
          loc (LabelCall label_kind) args ltyp
      in
      return ()

    let calltype_packing loc (name : Id.t) (ft : AT.packing_ft) : OutputDef.t m =
      spine OutputDef.subst OutputDef.pp 
        loc (Pack name) [] ft


    (* The "subtyping" judgment needs the same resource/lvar/constraint
       inference as the spine judgment. So implement the subtyping
       judgment 'arg <: RT' by type checking 'f(arg)' for 'f: RT -> False'. *)
    let subtype (loc : loc) arg (rtyp : RT.t) : unit m =
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


  let infer_tuple (loc : loc) (vts : vt list) : vt m = 
    let bts, its = List.split vts in
    return (Tuple bts, IT.tuple_ its)

  let infer_array (loc : loc) (vts : vt list) = 
    let item_bt = match vts with
      | [] -> Debug_ocaml.error "todo: empty arrays"
      | (i_bt, _) :: _ -> i_bt
    in
    let@ (_, it) = 
      ListM.fold_leftM (fun (index,it) (arg_bt, arg_it) -> 
          let@ () = ensure_base_type loc ~expect:item_bt arg_bt in
          return (index + 1, mod_ (it, int_ index, arg_it))
           ) (0, const_ Integer (default_ item_bt)) vts
    in
    return (BT.Array (Integer, item_bt), it)


  let infer_constructor (loc : loc) (constructor : mu_ctor) 
                        (args : arg list) : vt m = 
    match constructor, args with
    | M_Ctuple, _ -> 
       infer_tuple loc (List.map vt_of_arg args)
    | M_Carray, args -> 
       infer_array loc (List.map vt_of_arg args)
    | M_Cspecified, [arg] ->
       return (vt_of_arg arg)
    | M_Cspecified, _ ->
       fail loc (Number_arguments {has = List.length args; expect = 1})
    | M_Cnil item_bt, [] -> 
       let bt = List item_bt in
       return (bt, nil_ ~item_bt)
    | M_Cnil item_bt, _ -> 
       fail loc (Number_arguments {has = List.length args; expect=0})
    | M_Ccons, [arg1; arg2] -> 
       let bt = List arg1.bt in
       let@ () = ensure_base_type arg2.loc ~expect:bt arg2.bt in
       let list_it = cons_ (it_of_arg arg1, it_of_arg arg2) in
       return (arg2.bt, list_it)
    | M_Ccons, _ ->
       fail loc (Number_arguments {has = List.length args; expect = 2})



  let infer_ptrval (loc : loc) (ptrval : pointer_value) : vt m =
    CF.Impl_mem.case_ptrval ptrval
      ( fun ct -> 
        return (Loc, IT.null_) )
      ( fun sym -> 
        return (Loc, sym_ (sym, BT.Loc)) )
      ( fun _prov loc -> 
        return (Loc, pointer_ loc) )
      ( fun () -> 
        Debug_ocaml.error "unspecified pointer value" )

  let rec infer_mem_value (loc : loc) (mem : mem_value) : vt m =
    let open BT in
    CF.Impl_mem.case_mem_value mem
      ( fun ct -> 
        fail loc (Unspecified ct) )
      ( fun _ _ -> 
        unsupported loc !^"infer_mem_value: concurrent read case" )
      ( fun it iv -> 
        return (Integer, z_ (Memory.integer_value_to_num iv)) )
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
                   (member_values : (member * mem_value) list) : vt m =
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
         fail loc (Generic (!^"field" ^/^ Id.pp member ^^^ !^"missing"))
      | ((member,_) :: _), [] ->
         fail loc (Generic (!^"supplying unexpected field" ^^^ Id.pp member))
    in
    let@ it = check member_values (Memory.member_types layout) in
    return (BT.Struct tag, IT.struct_ (tag, it))

  and infer_union (loc : loc) (tag : tag) (id : Id.t) 
                  (mv : mem_value) : vt m =
    Debug_ocaml.error "todo: union types"

  let rec infer_object_value (loc : loc)
                         (ov : 'bty mu_object_value) : vt m =
    match ov with
    | M_OVinteger iv ->
       let i = Memory.integer_value_to_num iv in
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

  let rec infer_value (loc : loc) (v : 'bty mu_value) : vt m = 
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

  (* infer_pexpr: the raw type inference logic for pure expressions;
     returns a return type and a local environment *)
  (* infer_pexpr_pop: place a marker in the local environment, run
     the raw type inference, and return, in addition to what the raw
     inference returns, all logical (logical variables, resources,
     constraints) in the local environment *)

  let infer_array_shift loc asym1 ct asym2 =
    let@ arg1 = arg_of_asym asym1 in
    let@ arg2 = arg_of_asym asym2 in
    let@ () = ensure_base_type arg1.loc ~expect:Loc arg1.bt in
    let@ () = ensure_base_type arg2.loc ~expect:Integer arg2.bt in
    let@ provable = provable in
    let@ olength =
      map_and_fold_resources (fun re found ->
          match found, re with
          | Some _, _ -> 
             (re, found)
          | None, Point {ct = Sctype (_, Array (_, Some length)); pointer; _} 
               when provable (t_ (eq__ pointer (it_of_arg arg1))) ->
             (re, Some length)
          | _ -> 
             (re, found)
        ) None
    in
    let@ lrt = match olength with
      | None -> 
         return LRT.I
      | Some length ->
         (* don't fail if array cannot be unfolded *)
         RI.unfold_array loc ArrayShift
           ct (it_of_arg arg1) 
           length (q_ (1, 1))
    in
    let element_size = Memory.size_of_ctype ct in
    let v = 
      addPointer_ (it_of_arg arg1, 
                   mul_ (int_ element_size, it_of_arg arg2))
    in
    let rt = RT.concat (rt_of_vt loc (BT.Loc, v)) lrt in
    return rt

  let wrapI ity arg =
    (* try to follow wrapI from runtime/libcore/std.core *)
    let dlt = add_ (sub_ (maxInteger_ ity, minInteger_ ity), int_ 1) in
    let r = rem_f___ (arg, dlt) in
    ite_  (le_ (r, maxInteger_ ity), r,sub_ (r, dlt))



  let infer_pexpr (pe : 'bty mu_pexpr) : RT.t m = 
    let (M_Pexpr (loc, _annots, _bty, pe_)) = pe in
    let@ () = print_with_local (fun l ->
        debug 3 (lazy (action "inferring pure expression"));
        debug 3 (lazy (item "expr" (pp_pexpr pe)));
        debug 3 (lazy (item "ctxt" (L.pp l)))
      )
    in
    let@ rt = match pe_ with
      | M_PEsym sym ->
         let@ arg = arg_of_sym loc sym in
         return (rt_of_vt loc (vt_of_arg arg))
      | M_PEimpl i ->
         let rt = Global.get_impl_constant G.global i in
         return rt
      | M_PEval v ->
         let@ vt = infer_value loc v in
         return (rt_of_vt loc vt)
      | M_PEconstrained _ ->
         Debug_ocaml.error "todo: PEconstrained"
      | M_PEerror (err, asym) ->
         let@ arg = arg_of_asym asym in
         failS loc (fun local ->
             let expl = E.undefined_behaviour local in
             (StaticError (err, expl))
           )
      | M_PEctor (ctor, asyms) ->
         let@ args = args_of_asyms asyms in
         let@ vt = infer_constructor loc ctor args in
         return (rt_of_vt loc vt)
      | M_CivCOMPL _
        | M_CivAND _
        | M_CivOR _
        | M_CivXOR _ 
        -> 
         Debug_ocaml.error "todo: Civ..."
      | M_Cfvfromint _ -> 
         unsupported loc !^"floats"
      | M_Civfromfloat _ -> 
         unsupported loc !^"floats"
      | M_PEarray_shift (asym1, ct, asym2) ->
         infer_array_shift loc asym1 ct asym2
      | M_PEmember_shift (asym, tag, member) ->
         let@ arg = arg_of_asym asym in
         let@ () = ensure_base_type arg.loc ~expect:Loc arg.bt in
         let@ lrt = 
           RI.unfold_struct 
             loc MemberShift tag (it_of_arg arg) (q_ (1, 1)) 
         in
         let@ layout = get_struct_decl loc tag in
         let@ _member_bt = get_member_type loc tag member layout in
         let@ offset = match Memory.member_offset layout member with
           | Some offset -> return offset
           | None -> fail loc (Missing_member (tag, member))
         in
         let vt = (Loc, IT.addPointer_ (it_of_arg arg, int_ offset)) in
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
         let@ decl_typ = match called with
           | CF.Core.Impl impl -> 
              return (Global.get_impl_fun_decl G.global impl )
           | CF.Core.Sym sym -> 
              let@ (_, t) = match Global.get_fun_decl G.global sym with
                | Some t -> return t
                | None -> fail loc (Missing_function sym)
              in
              return t
         in
         let@ args = args_of_asyms asyms in
         Spine.calltype_ft loc args decl_typ
      | M_PEassert_undef (asym, _uloc, undef) ->
         let@ arg = arg_of_asym asym in
         let@ () = ensure_base_type arg.loc ~expect:Bool arg.bt in
         let@ provable = provable in
         if provable (t_ (it_of_arg arg)) then
           return (rt_of_vt loc (Unit, unit_))
         else
           failS loc (fun local ->
               let expl = E.undefined_behaviour local in
               (Undefined_behaviour (undef, expl))
             )
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
           | Sctype (_, Integer ity) -> ity
           | _ -> Debug_ocaml.error "conv_int applied to non-integer type"
         in
         begin match ity with
         | Bool ->
            let vt = (Integer, ite_ (eq_ (arg_it, int_ 0), int_ 0, int_ 1)) in
            return (rt_of_vt loc vt)
         | _
              when Sctypes.is_unsigned_integer_type ity ->
            let result = 
              ite_ (representable_ (act.ct, arg_it),
                    arg_it,
                    wrapI ity arg_it)
            in
            return (rt_of_vt loc (Integer, result))
         | _ ->
            let@ provable = provable in
            if provable (t_ (representable_ (act.ct, arg_it))) then
              return (rt_of_vt loc (Integer, arg_it))
            else
              failS loc (fun local ->
                  let (it_pp, state_pp) = E.implementation_defined_behaviour local arg_it in
                  (Implementation_defined_behaviour 
                     (it_pp ^^^ !^"outside representable range for" ^^^ 
                        Sctypes.pp act.ct, state_pp))
                )
         end
      | M_PEwrapI (act, asym) ->
         let@ arg = arg_of_asym asym in
         let@ () = ensure_base_type arg.loc ~expect:Integer arg.bt in
         let ity = match act.ct with
           | Sctype (_, Integer ity) -> ity
           | _ -> Debug_ocaml.error "wrapI applied to non-integer type"
         in
         let result = wrapI ity (it_of_arg arg) in
         return (rt_of_vt loc (Integer, result))
    in  
    debug 3 (lazy (item "type" (RT.pp rt)));
    return rt


  (* check_tpexpr: type check the pure expression `e` against return type
     `typ`; returns a "reduced" local environment *)

  let rec check_tpexpr (e : 'bty mu_tpexpr) (typ : RT.t) : unit m = 
    let (M_TPexpr (loc, _annots, _, e_)) = e in
    let@ () = print_with_local (fun l ->
        debug 3 (lazy (action "checking pure expression"));
        debug 3 (lazy (item "expr" (group (pp_tpexpr e))));
        debug 3 (lazy (item "type" (RT.pp typ)));
        debug 3 (lazy (item "ctxt" (L.pp l)));
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
               if provable (t_ (bool_ false)) 
               then return ()
               else check_tpexpr e typ
             end
         ) [(it_of_arg carg, e1); (not_ (it_of_arg carg), e2)]
    | M_PEcase (asym, pats_es) ->
       let@ arg = arg_of_asym asym in
       ListM.iterM (fun (pat, pe) ->
           pure begin 
               let@ () = pattern_match (it_of_arg arg) pat in
               let@ provable = provable in
               if provable (t_ (bool_ false))
               then return ()
               else check_tpexpr e typ
             end
         ) pats_es
    | M_PElet (p, e1, e2) ->
       let@ rt = infer_pexpr e1 in
       pure begin
           let@ () = match p with
             | M_Symbol sym -> bind_return_type (Some (Loc (loc_of_pexpr e1))) sym rt
             | M_Pat pat -> pattern_match_rt (Loc (loc_of_pexpr e1)) pat rt
           in
           check_tpexpr e2 typ
         end
    | M_PEdone asym ->
       let@ arg = arg_of_asym asym in
       let@ local = Spine.subtype loc arg typ in
       return ()
    | M_PEundef (_loc, undef) ->
       failS loc (fun local ->
           let expl = E.undefined_behaviour local in
           (Undefined_behaviour (undef, expl))
         )

  (*** impure expression inference **********************************************)


  (* type inference of impure expressions; returns either a return type
     and new local environment or False *)
  (* infer_expr: the raw type inference for impure expressions. *)
  (* infer_expr_pop: analogously to infer_pexpr: place a marker, run
     the raw type inference, and additionally return whatever is left in
     the local environment since that marker (except for computational
     variables) *)

  (* `t` is used for the type of Run/Goto: Goto has no return type
     (because the control flow does not return there), but instead
     returns `False`. Type inference of impure expressions returns
     either a return type and a local environment or `False` *)
  type 'a t = 
    | Normal of 'a
    | False

  type 'a orFalse = 'a t

  let pp_or_false (ppf : 'a -> Pp.document) (m : 'a t) : Pp.document = 
    match m with
    | Normal a -> ppf a
    | False -> parens !^"no return"


  (*** auxiliary ****************************************************************)
  (* let json_local loc local : Yojson.Safe.t = 
   *   `Assoc [("loc", json_loc loc);
   *           ("context", `Variant ("context", Some (Explain.json_state local)))]
   * 
   * let json_false loc : Yojson.Safe.t = 
   *   `Assoc [("loc", json_loc loc);
   *           ("context", `Variant ("unreachable", None))]
   * 
   * let json_local_or_false loc = function
   *   | Normal local -> json_local loc local
   *   | False -> json_false loc *)



  let all_empty loc = 
    let failure resource = 
      failS loc (fun local ->
          let (resource, state) = 
            E.resource local (S.get_model (L.solver local)) resource in
          (Unused_resource {resource; state})
        )
    in

    let@ provable = provable in
    let@ all_resources = all_resources () in
    let _ = 
      ListM.mapM (fun resource ->
          match resource with
          | Point p ->
             let holds = provable (t_ (le_ (p.permission, q_ (0, 1)))) in
             if holds then return () else failure resource
          | QPoint p ->
             let holds = 
               provable
                 (forall_ (p.qpointer, BT.Loc) None
                    (le_ (p.permission, q_ (0, 1))))
             in
             if holds then return () else failure resource
          | Predicate p ->
             let holds = provable (t_ (le_ (p.permission, q_ (0, 1)))) in
             if holds then return () else failure resource
          | QPredicate p ->
             let holds = 
               provable
                 (forall_ (p.qpointer, BT.Loc) None
                    (le_ (p.permission, q_ (0, 1))))
             in
             if holds then return () else failure resource
        ) all_resources
    in
    return ()


  type labels = (AT.lt * label_kind) SymMap.t


  let infer_expr labels (e : 'bty mu_expr) : RT.t m = 
    let (M_Expr (loc, _annots, e_)) = e in
    let@ () = print_with_local (fun l ->
         debug 3 (lazy (action "inferring expression"));
         debug 3 (lazy (item "expr" (group (pp_expr e))));
         debug 3 (lazy (item "ctxt" (L.pp l)));
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
            Debug_ocaml.error "todo: M_Ptrdiff"
         | M_IntFromPtr (act_from, act2_to, asym) ->
            let@ arg = arg_of_asym asym in
            let@ () = ensure_base_type arg.loc ~expect:Loc arg.bt in
            let vt = (Integer, pointerToIntegerCast_ (it_of_arg arg)) in
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
            let@ _ = 
              pure (RI.point_request loc (Access Deref) ({
                ct = act.ct; 
                pointer = it_of_arg arg;
                permission = q_ (1, 1);
                value = BT.of_sct act.ct;
                init = BT.Bool;
              }, None))
            in
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
                  permission = q_ (1, 1);
                  value = value_t; 
                  init = bool_ false;
                }
            in
            let rt = 
              RT.Computational ((ret, Loc), (loc, None),
              LRT.Constraint (t_ (representable_ (Sctypes.pointer_sct act.ct, sym_ (ret, Loc))), (loc, None),
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
            Debug_ocaml.error "todo: free"
         | M_Kill (M_Static ct, asym) -> 
            let@ arg = arg_of_asym asym in
            let@ () = ensure_base_type arg.loc ~expect:Loc arg.bt in
            let@ _ = 
              RI.point_request loc (Access Kill) ({
                ct = ct;
                pointer = it_of_arg arg;
                permission = q_ (1, 1);
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
              if holds then return () else 
                failS loc (fun local ->
                    let (constr,state) = 
                      E.unsatisfied_constraint local 
                        (S.get_model (L.solver local)) (t_ in_range_lc)
                    in
                    (Write_value_unrepresentable {state})
                  )
            in
            let@ _ = 
              RI.point_request loc (Access (Store None)) ({
                  ct = act.ct; 
                  pointer = it_of_arg parg;
                  permission = q_ (1, 1);
                  value = BT.of_sct act.ct; 
                  init = BT.Bool;
                }, None)
            in
            let resource = 
              RE.Point {
                  ct = act.ct;
                  pointer = it_of_arg parg;
                  permission = q_ (1, 1);
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
              pure (RI.point_request loc (Access (Load None)) ({ 
                      ct = act.ct;
                      pointer = it_of_arg parg;
                      permission = q_ (1, 1); (* fix *)
                      value = BT.of_sct act.ct; 
                      init = BT.Bool;
                    }, None))
            in
            let@ () = 
              let@ provable = provable in
              if provable (t_ point.init) then return () else
                failS loc (fun local ->
                    let (_, state) = 
                      E.unsatisfied_constraint local 
                        (S.get_model (L.solver local)) (t_ point.init) in
                    (Uninitialised_read {is_member = None; state})
                  )
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
         let@ (_loc, ft) = match Global.get_fun_decl G.global afsym.sym with
           | Some (loc, ft) -> return (loc, ft)
           | None -> fail loc (Missing_function afsym.sym)
         in
         Spine.calltype_ft loc args ft
      | M_Eproc (fname, asyms) ->
         let@ decl_typ = match fname with
           | CF.Core.Impl impl -> 
              return (Global.get_impl_fun_decl G.global impl)
           | CF.Core.Sym sym ->
              match Global.get_fun_decl G.global sym with
              | Some (loc, ft) -> return ft
              | None -> fail loc (Missing_function sym)
         in
         let@ args = args_of_asyms asyms in
         Spine.calltype_ft loc args decl_typ
      | M_Epredicate (pack_unpack, pname, asyms) ->
         let@ def = match Global.get_predicate_def G.global (Id.s pname) with
           | Some def -> return def
           | None -> fail loc (Missing_predicate (Id.s pname))
         in
         let@ pointer_asym, iarg_asyms = match asyms with
           | pointer_asym :: iarg_asyms -> return (pointer_asym, iarg_asyms)
           | _ -> fail loc (Generic !^"pointer argument to predicate missing")
         in
         let@ pointer_arg = arg_of_asym pointer_asym in
         (* todo: allow other permission amounts *)
         let permission = q_ (1, 1) in
         let@ iargs = args_of_asyms iarg_asyms in
         let@ () = 
           (* "+1" because of pointer argument *)
           let has, expect = List.length iargs + 1, List.length def.iargs + 1 in
           if has = expect then return ()
           else fail loc (Number_arguments {has; expect})
         in
         let@ () = ensure_base_type pointer_arg.loc ~expect:Loc pointer_arg.bt in
         let@ () = ensure_base_type loc ~expect:Real (IT.bt permission) in
         let@ () = 
           ListM.iterM (fun (arg, expected_sort) ->
               ensure_base_type arg.loc ~expect:expected_sort arg.bt
             ) (List.combine iargs (List.map snd def.iargs))
         in
         let instantiated_clauses = 
           let subst = 
             (def.pointer, it_of_arg pointer_arg) ::
             (def.permission, permission ) ::
             List.combine (List.map fst def.iargs) (List.map it_of_arg iargs)
           in
           List.map (Predicates.subst_clause subst) def.clauses
         in
         let@ provable = provable in
         let@ right_clause = 
           let rec try_clauses negated_guards clauses = 
             match clauses with
             | clause :: clauses -> 
                if provable (t_ (and_ (clause.guard :: negated_guards)))
                then return clause.packing_ft
                else try_clauses (not_ clause.guard :: negated_guards) clauses
             | [] -> 
                let err = 
                  !^"do not have enough information for" ^^^
                  (match pack_unpack with Pack -> !^"packing" | Unpack -> !^"unpacking") ^^^
                  Id.pp pname
                in
                fail loc (Generic err)
           in
           try_clauses [] instantiated_clauses
         in
         match pack_unpack with
         | Unpack ->
            let@ pred =
              RI.predicate_request loc (Unpack pname) ({
                  name = Id.s pname;
                  pointer = it_of_arg pointer_arg;
                  permission = permission;
                  iargs = List.map it_of_arg iargs;
                  oargs = List.map snd def.oargs;
                }, None)
            in
            let condition, outputs = AT.logical_arguments_and_return right_clause in
            let lc = and_ (List.map2 (fun it (_, it') -> eq__ it it') pred.oargs outputs) in
            let lrt = LRT.concat condition (Constraint (t_ lc, (loc, None), I)) in
            return (RT.Computational ((Sym.fresh (), BT.Unit), (loc, None), lrt))
         | Pack ->
            let@ output_assignment = Spine.calltype_packing loc pname right_clause in
            let resource = 
              Predicate {
                name = Id.s pname;
                pointer = it_of_arg pointer_arg;
                permission = q_ (1, 1);
                iargs = List.map it_of_arg iargs;
                oargs = List.map snd output_assignment;
              }
            in
            let rt =
              (RT.Computational ((Sym.fresh (), BT.Unit), (loc, None),
               Resource (resource, (loc, None),
               LRT.I)))
            in
            return rt
    in
    debug 3 (lazy (RT.pp result));
    return result

  (* check_expr: type checking for impure epressions; type checks `e`
     against `typ`, which is either a return type or `False`; returns
     either an updated environment, or `False` in case of Goto *)
  let rec check_texpr labels (e : 'bty mu_texpr) (typ : RT.t orFalse) 
          : unit m = 

    let (M_TExpr (loc, _annots, e_)) = e in
    let@ () = print_with_local (fun l ->
        debug 3 (lazy (action "checking expression"));
        debug 3 (lazy (item "expr" (group (pp_texpr e))));
        debug 3 (lazy (item "type" (pp_or_false RT.pp typ)));
        debug 3 (lazy (item "ctxt" (L.pp l)));
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
                 if provable (t_ (bool_ false))
                 then return ()
                 else check_texpr labels e typ 
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
                 if provable (t_ (bool_ false))
                 then return ()
                 else check_texpr labels e typ
               end
           ) pats_es
      | M_Elet (p, e1, e2) ->
         let@ rt = infer_pexpr e1 in
         pure begin
             let@ () = match p with 
               | M_Symbol sym -> bind_return_type (Some (Loc (loc_of_pexpr e1))) sym rt
               | M_Pat pat -> pattern_match_rt (Loc (loc_of_pexpr e1)) pat rt
             in
             check_texpr labels e2 typ
           end
      | M_Ewseq (pat, e1, e2) ->
         let@ rt = infer_expr labels e1 in
         pure begin
             let@ () = pattern_match_rt (Loc (loc_of_expr e1)) pat rt in
             check_texpr labels e2 typ
           end
      | M_Esseq (pat, e1, e2) ->
         let@ rt = infer_expr labels e1 in
         pure begin
             let@ () = match pat with
               | M_Symbol sym -> bind_return_type (Some (Loc (loc_of_expr e1))) sym rt
               | M_Pat pat -> pattern_match_rt (Loc (loc_of_expr e1)) pat rt
             in
             check_texpr labels e2 typ
           end
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
            fail loc (Generic !^err)
         end
      | M_Eundef (_loc, undef) ->
         failS loc (fun local ->
             let expl = E.undefined_behaviour local in
             (Undefined_behaviour (undef, expl))
           )
      | M_Erun (label_sym, asyms) ->
         let@ (lt,lkind) = match SymMap.find_opt label_sym labels with
           | None -> fail loc (Generic (!^"undefined code label" ^/^ Sym.pp label_sym))
           | Some (lt,lkind) -> return (lt,lkind)
         in
         let@ args = args_of_asyms asyms in
         let@ () = Spine.calltype_lt loc args (lt,lkind) in
         let@ () = all_empty loc in
         return ()

    in
    return result




  (* check_and_bind_arguments: typecheck the function/procedure/label
     arguments against its specification; returns
     1. the return type, or False, to type check the body against,
     2. a local environment binding the arguments,
     3. a local environment binding only the computational and logical
        arguments (for use when type checking a procedure, to include those 
        arguments in the environment for type checking the labels),
     4. the substitution of concrete arguments for the specification's
        type variables (this is used for instantiating those type variables
        in label specifications in the function body when type checking a
        procedure. *)
  (* the code is parameterised so it can be used uniformly for
     functions and procedures (with return type) and labels with
     no-return (False) type. *)
  let check_and_bind_arguments rt_subst loc arguments (function_typ : 'rt AT.t) = 
    let rec check resources args (ftyp : 'rt AT.t) =
      match args, ftyp with
      | ((aname,abt) :: args), (AT.Computational ((lname, sbt), _info, ftyp))
           when BT.equal abt sbt ->
         let new_lname = Sym.fresh () in
         let subst = [(lname, sym_ (new_lname, sbt))] in
         let ftyp' = AT.subst rt_subst subst ftyp in
         let@ () = add_l new_lname abt in
         let@ () = add_a aname (abt,new_lname) in
         check resources args ftyp'
      | ((aname, abt) :: args), (AT.Computational ((sname, sbt), _info, ftyp)) ->
         fail loc (Mismatch {has = abt; expect = sbt})
      | [], (AT.Computational (_, _, _))
      | (_ :: _), (AT.I _) ->
         let expect = AT.count_computational function_typ in
         let has = List.length arguments in
         fail loc (Number_arguments {expect; has})
      | args, (AT.Logical ((sname, sls), _, ftyp)) ->
         let@ () = add_l sname sls in
         check resources args ftyp
      | args, (AT.Resource (re, _, ftyp)) ->
         check (re :: resources) args ftyp
      | args, (AT.Constraint (lc, _, ftyp)) ->
         let@ local = add_c lc in
         check resources args ftyp
      | [], (AT.I rt) ->
         return (rt, resources)
    in
    check [] arguments function_typ


  (* check_function: type check a (pure) function *)
  let check_function 
        (loc : loc) 
        (info : string) 
        (arguments : (Sym.t * BT.t) list) (rbt : BT.t) 
        (body : 'bty mu_tpexpr) (function_typ : AT.ft) : unit m =
    debug 2 (lazy (headline ("checking function " ^ info)));
    pure begin 
        let@ (rt, resources) = 
          check_and_bind_arguments RT.subst loc arguments function_typ 
        in
        let@ () = ListM.iterM (add_r (Some (Label "start"))) resources in
        (* rbt consistency *)
        let@ () = 
          let Computational ((sname, sbt), _info, t) = rt in
          ensure_base_type loc ~expect:sbt rbt
        in
        let@ local_or_false = check_tpexpr body rt in
        return ()
      end

  (* check_procedure: type check an (impure) procedure *)
  let check_procedure 
        (loc : loc) (fsym : Sym.t)
        (arguments : (Sym.t * BT.t) list) (rbt : BT.t) 
        (body : 'bty mu_texpr) (function_typ : AT.ft) 
        (label_defs : 'bty mu_label_defs) : unit m =
    print stdout (!^("checking function " ^ Sym.pp_string fsym));
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
          ensure_base_type loc ~expect:sbt rbt
        in

        (* check well-typedness of labels and record their types *)
        let@ labels = 
          PmapM.foldM (fun sym def acc ->
              pure begin 
                  match def with
                  | M_Return (loc, lt) ->
                     let@ () = WT.WLT.good "return label" loc lt in
                     return (SymMap.add sym (lt, Return) acc)
                  | M_Label (loc, lt, _, _, annots) -> 
                     let label_kind = match CF.Annot.get_label_annot annots with
                       | Some (LAloop_body loop_id) -> Loop
                       | Some (LAloop_continue loop_id) -> Loop
                       | _ -> Other
                     in
                     let@ () = WT.WLT.welltyped "label" loc lt in
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
               let@ () = ListM.iterM (add_r (Some (Label label_name))) resources in
               let@ local_or_false = check_texpr labels body False in
               return ()
            end
        in
        let@ () = PmapM.foldM check_label label_defs () in

        (* check the function body *)
        debug 2 (lazy (headline ("checking function body " ^ Sym.pp_string fsym)));
        let@ () = ListM.iterM (add_r (Some (Label "start"))) resources in
        let@ local_or_false = check_texpr labels body (Normal rt) in
        return ()
      end

end
 




let check mu_file = 
  let open Resultat in

  let () = Debug_ocaml.begin_csv_timing "total" in
  let global = Global.empty in
  
  let () = Debug_ocaml.begin_csv_timing "tagDefs" in
  let@ global = 
    (* check and record tagDefs *)
    let open Memory in
    PmapM.foldM (fun tag def (global: Global.t) ->
        match def with
        | M_UnionDef _ -> 
           unsupported Loc.unknown !^"todo: union types"
        | M_StructDef layout -> 
           let@ () =
             ListM.iterM (fun piece ->
                 match piece.member_or_padding with
                 | Some (_, Sctypes.Sctype (_, Sctypes.Struct sym2)) ->
                    if SymMap.mem sym2 global.struct_decls then return ()
                    else fail Loc.unknown (Missing_struct sym2)
                 | _ -> return ()
               ) layout
           in
           let struct_decls = SymMap.add tag layout global.struct_decls in
           return { global with struct_decls }
      ) mu_file.mu_tagDefs global
  in
  let () = Debug_ocaml.end_csv_timing "tagDefs" in

  let module S = Solver.Make(struct let struct_decls = global.struct_decls end) in
  let module L = Local.Make(S) in
  let module Typing = Typing.Make(L) in

  let () = Debug_ocaml.begin_csv_timing "impls" in
  let@ global = 
    (* check and record impls *)
    let open Global in
    PmapM.foldM (fun impl impl_decl global ->
        let module G = struct let global = global end in
        let module C = Make(G)(S)(L) in
        let module WT = WellTyped.Make(G)(S)(L) in
        let descr = CF.Implementation.string_of_implementation_constant impl in
        match impl_decl with
        | M_Def (rt, rbt, pexpr) -> 
           let@ ((), _) = Typing.run (WT.WRT.welltyped Loc.unknown rt) (L.empty ()) in
           let@ ((), _) = 
             Typing.run (C.check_function Loc.unknown
               descr [] rbt pexpr (AT.I rt)) (L.empty ()) in
           let global = 
             { global with impl_constants = 
                             ImplMap.add impl rt global.impl_constants}
           in
           return global
        | M_IFun (ft, rbt, args, pexpr) ->
           let@ ((), _) = 
             Typing.run 
               (WT.WFT.welltyped "implementation-defined function" Loc.unknown ft) 
               (L.empty ())
           in
           let@ ((), _) = 
             Typing.run (C.check_function Loc.unknown
                (CF.Implementation.string_of_implementation_constant impl)
                args rbt pexpr ft) (L.empty ())
           in
           let impl_fun_decls = ImplMap.add impl ft global.impl_fun_decls in
           return { global with impl_fun_decls }
      ) mu_file.mu_impl global
  in
  let () = Debug_ocaml.end_csv_timing "impls" in
  

  let () = Debug_ocaml.begin_csv_timing "predicate defs" in
  let@ global = 
    (* check and record predicate defs *)
    ListM.fold_leftM (fun global (name,def) -> 
        let module WT = WellTyped.Make(struct let global = global end)(S)(L) in
        let@ ((), _) = Typing.run (WT.WPD.welltyped def) (L.empty ()) in
        let resource_predicates =
          StringMap.add name def global.resource_predicates in
        return {global with resource_predicates}
      ) global mu_file.mu_predicates
  in
  let () = Debug_ocaml.end_csv_timing "predicate defs" in


  let () = Debug_ocaml.begin_csv_timing "globals" in
  let@ local = 
    (* record globals *)
    (* TODO: check the expressions *)
    let open Global in
    ListM.fold_leftM (fun local (sym, def) ->
        match def with
        | M_GlobalDef (lsym, (_, ct), _)
        | M_GlobalDecl (lsym, (_, ct)) ->
           let bt = Loc in
           let local = L.add_l lsym bt local in
           let local = L.add_a sym (bt, lsym) local in
           let local = L.add_c (t_ (IT.good_pointer (sym_ (lsym, bt)) ct)) local in
           return local
      ) (L.empty ()) mu_file.mu_globs 
  in
  let () = Debug_ocaml.end_csv_timing "globals" in

  let@ (global, local) =
    let open Global in
    PmapM.foldM
      (fun fsym (M_funinfo (loc, _attrs, ftyp, _has_proto)) 
           (global, local) ->
        let global = 
          { global with fun_decls = SymMap.add fsym (loc, ftyp) global.fun_decls }
        in
        let local = 
          let voidstar = Sctypes.pointer_sct (Sctype ([], Void)) in
          let lc1 = t_ (ne_ (null_, sym_ (fsym, Loc))) in
          let lc2 = t_ (representable_ (voidstar, sym_ (fsym, Loc))) in
          L.add_l fsym Loc (L.add_cs [lc1; lc2] local)
        in
        return (global, local)
      ) mu_file.mu_funinfo (global, local)
  in
  let () = Debug_ocaml.begin_csv_timing "welltypedness" in
  let@ () =
    PmapM.iterM
      (fun fsym (M_funinfo (loc, _attrs, ftyp, _has_proto))  ->
        let () = debug 2 (lazy (headline ("checking welltypedness of procedure " ^ Sym.pp_string fsym))) in
        let () = debug 2 (lazy (item "type" (AT.pp RT.pp ftyp))) in
        let module WT = WellTyped.Make(struct let global = global end)(S)(L) in
        let@ ((), _) = Typing.run (WT.WFT.welltyped "global" loc ftyp) local in
        return ()
      ) mu_file.mu_funinfo
  in
  let () = Debug_ocaml.end_csv_timing "welltypedness" in

  let check_functions fns =
    let module C = Make(struct let global = global end)(S)(L) in
    PmapM.iterM (fun fsym fn -> 
        let@ ((), _) = match fn with
          | M_Fun (rbt, args, body) ->
             let@ (loc, ftyp) = match Global.get_fun_decl global fsym with
               | Some t -> return t
               | None -> fail Loc.unknown (Missing_function fsym)
             in
             Typing.run (C.check_function loc
                (Sym.pp_string fsym) args rbt body ftyp) local
          | M_Proc (loc, rbt, args, body, labels) ->
             let@ (loc', ftyp) = match Global.get_fun_decl global fsym with
               | Some t -> return t
               | None -> fail loc (Missing_function fsym)
             in
             Typing.run (C.check_procedure loc'
               fsym args rbt body ftyp labels) local
          | M_ProcDecl _ -> 
             return ((), local)
          | M_BuiltinDecl _ -> 
             return ((), local)
        in
        return ()
      ) fns
  in

  let () = Debug_ocaml.begin_csv_timing "check stdlib" in
  let@ () = check_functions mu_file.mu_stdlib in
  let () = Debug_ocaml.end_csv_timing "check stdlib" in
  let () = Debug_ocaml.begin_csv_timing "check functions" in
  let@ () = check_functions mu_file.mu_funs in
  let () = Debug_ocaml.end_csv_timing "check functions" in


  let () = Debug_ocaml.end_csv_timing "total" in

  return ()





(* TODO: 
   - sequencing strength
   - rem_t vs rem_f
   - check globals with expressions
 *)
