module IT = IndexTerms
open IT
open Pp
open ResourceTypes
open Resources
open Typing
open Effectful.Make(Typing)
open TypeErrors
open LogicalConstraints
module LAT = LogicalArgumentTypes
module RET = ResourceTypes
open ResourcePredicates
open Memory
open Pack





let unpack_def global name args =
    Option.bind (Global.get_logical_function_def global name)
    (fun def ->
    match def.definition with
    | Def body ->
       Some ((LogicalFunctions.open_fun def.args body args))
    | _ -> None
    )

let debug_constraint_failure_diagnostics lvl (model_with_q : Solver.model_with_q)
        global simp_ctxt c =
  let model = fst model_with_q in
  if ! Pp.print_level == 0 then () else
  let pp_f = pp_with_eval (Solver.eval global model) in
  let diag msg c = match (c, model_with_q) with
      | (LC.T tm, _) ->
        Pp.debug lvl (lazy (Pp.item msg (IT.pp tm)));
        Pp.debug lvl (lazy (pp_f tm))
      | (LC.Forall ((sym, bt), tm), (_, [(sym', bt')])) ->
        let tm' = IT.subst (IT.make_rename ~from:sym ~to_:sym') tm in
        Pp.debug lvl (lazy (Pp.item ("quantified " ^ msg) (IT.pp tm)));
        Pp.debug lvl (lazy (pp_f tm'))
      | _ ->
        Pp.warn Loc.unknown (Pp.bold "unexpected quantifier count with model")
  in
  diag "counterexample, expanding" c;
  let c2 = Simplify.LogicalConstraints.simp simp_ctxt c in
  if LC.equal c c2 then ()
  else diag "simplified variant" c2




module General = struct

  type one = {one_index : IT.t; value : IT.t}
  type many = {many_guard: IT.t; value : IT.t}

  type uiinfo = (TypeErrors.situation * TypeErrors.request_chain)

  type case =
    | One of one
    | Many of many

  let pp_case = function
    | One {one_index;value} ->
       !^"one" ^^ parens (IT.pp one_index ^^ colon ^^^ IT.pp value)
    | Many {many_guard;value} ->
       !^"many" ^^ parens (IT.pp many_guard ^^ colon ^^^ IT.pp value)

  type cases = C of case list
  let add_case case (C cases) = C (cases @ [case])




  let cases_to_map loc (uiinfo: uiinfo) a_bt item_bt (C cases) =
    (* TODO revisit this location *)
    let here = Locations.other __FUNCTION__ in
    let update_with_ones base_array ones =
      List.fold_left (fun m {one_index; value} ->
          map_set_ m (one_index, value) here
        ) base_array ones
    in
    let ones, manys =
      List.partition_map (function One c -> Left c | Many c -> Right c) cases in
    let@ base_value =
      match manys, item_bt with
      | [{many_guard = _; value}], _ ->
          return value
      | [], _
      | _, BT.Unit ->
          return (default_ (BT.Map (a_bt, item_bt)) here)
      | many, _ -> fail (fun ctxt -> {loc; msg = Generic (!^ "Merging multiple arrays with non-void values:" ^^^ Pp.list IT.pp
             (List.map (fun m -> m.value) many))})
(*
         let@ model = model () in
         fail (fun ctxt ->
             let msg = Merging_multiple_arrays {orequest; situation; oinfo; model =None; ctxt} in
             {loc; msg})
*)
    in
    return (update_with_ones base_value ones)




  (* this version is parametric in resource_request (defined below) to ensure
     the return-type (also parametric) is as general as possible *)
  let parametric_ftyp_args_request_step resource_request rt_subst loc
        (uiinfo : uiinfo) original_resources ftyp changed_or_deleted =
    (* take one step of the "spine" judgement, reducing a function-type
       by claiming an argument resource or otherwise reducing towards
       an instantiated return-type *)

    let@ simp_ctxt = simp_ctxt () in

    begin match ftyp with
    | LAT.Resource ((s, (resource, bt)), info, ftyp) ->
       let resource = Simplify.ResourceTypes.simp simp_ctxt resource in
       let (situation, request_chain) = uiinfo in
       let step = TypeErrors.{resource; loc = Some (fst info);
           reason = Some ("arg " ^ Sym.pp_string s)} in
       let request_chain = step :: request_chain in
       let uiinfo = (situation, request_chain) in
       let@ o_re_oarg = resource_request loc uiinfo resource in
       begin match o_re_oarg with
         | None ->
            let here = Locations.other __FUNCTION__ in
            let@ model = model_with loc (bool_ true here) in
            let model = Option.get model in
            fail (fun ctxt ->
                let ctxt = { ctxt with resources = original_resources } in
                let msg = Missing_resource
                           {requests = request_chain; situation; model; ctxt} in
                {loc; msg}
           )
         | Some ((re, O oargs), changed_or_deleted') ->
            assert (ResourceTypes.equal re resource);
            let oargs = Simplify.IndexTerms.simp simp_ctxt oargs in
            let changed_or_deleted = changed_or_deleted @ changed_or_deleted' in
            return ((LAT.subst rt_subst (IT.make_subst [(s, oargs)]) ftyp), changed_or_deleted)
       end
    | Define ((s, it), info, ftyp) ->
       let it = Simplify.IndexTerms.simp simp_ctxt it in
       return (LAT.subst rt_subst (IT.make_subst [(s, it)]) ftyp, changed_or_deleted)
    | Constraint (c, info, ftyp) ->
       let@ () = return (debug 9 (lazy (item "checking constraint" (LC.pp c)))) in
       let@ provable = provable loc in
       let res = provable c in
       begin match res with
       | `True ->
           return (ftyp, changed_or_deleted)
       | `False ->
           let@ model = model () in
           let@ global = get_global () in
           let@ all_cs = all_constraints () in
           let@ () = if Context.LCSet.mem c all_cs
             then begin
               let@ () = debug_solver_query c in
               fail (fun _ -> {loc; msg = Generic
                 (Pp.item "insane situation: failed constraint in context" (LC.pp c))})
             end
             else return () in
           debug_constraint_failure_diagnostics 6 model global simp_ctxt c;
           let@ () = Diagnostics.investigate model c in
           fail (fun ctxt ->
                  let ctxt = { ctxt with resources = original_resources } in
                  {loc; msg = Unproven_constraint {constr = c; info;
                      requests = snd uiinfo; ctxt; model; }}
                )
       end
    | I rt ->
       return (ftyp, changed_or_deleted)
    end







  (* TODO: check that oargs are in the same order? *)
  let rec predicate_request loc (uiinfo : uiinfo) (requested : RET.predicate_type)
    : (((predicate_type * oargs) * int list) option) m  =
       debug 7 (lazy (item "predicate request" (RET.pp (P requested))));
       let start_timing = time_log_start "predicate-request" "" in
       let@ oarg_bt = WellTyped.oarg_bt_of_pred loc requested.name in
       let@ provable = provable loc in
       let@ global = get_global () in
       let@ simp_ctxt = simp_ctxt () in
       let needed = true in
       let resource_scan re ((needed : bool), oargs) =
             let continue = (Unchanged, (needed, oargs)) in
             if not needed then continue else
             match re with
             | (P p', p'_oarg) when RET.subsumed requested.name p'.name ->
                let here = Locations.other __FUNCTION__ in
                let pmatch =
                  eq_ ((pointerToIntegerCast_ requested.pointer) here, (pointerToIntegerCast_ p'.pointer here)) here
                  :: List.map2 (fun x y -> eq__ x y here) requested.iargs p'.iargs
                in
                let took = and_ pmatch here in
                let prov =
                  eq_ (pointerToAllocIdCast_ requested.pointer here, pointerToAllocIdCast_ p'.pointer here) here in
                let debug_failure model msg term =
                  Pp.debug 9 (lazy (Pp.item msg (RET.pp (fst re))));
                  debug_constraint_failure_diagnostics 9 model global simp_ctxt (LC.T term) in
                begin match provable (LC.T took) with
                | `True ->
                  begin match provable (LC.T prov) with
                  | `True ->
                    Pp.debug 9 (lazy (Pp.item "used resource" (RET.pp (fst re))));
                    Deleted,
                    (false, p'_oarg)
                  | `False ->
                    debug_failure
                      (Solver.model ())
                      "couldn't use resource (matched address but not provenance)"
                      prov;
                    continue
                  end
                | `False ->
                  let model = Solver.model () in
                  begin match provable (LC.T prov) with
                  | `True ->
                    debug_failure
                      model
                      "couldn't use resource (matched provenance but not address)"
                      took;
                    continue
                  | `False ->
                    debug_failure
                      (Solver.model ())
                      "couldn't use resource"
                      (and_ (eq_ (requested.pointer, p'.pointer) here :: List.tl pmatch) here);
                    continue
                  end
                end
             | re ->
                continue
       in
       let here = Locations.other __FUNCTION__ in
       let@ ((needed, oarg), changed_or_deleted) =
         let here = Locations.other __FUNCTION__ in
         map_and_fold_resources loc resource_scan
             (needed, O (default_ oarg_bt here))
       in
       Pp.debug 9 (lazy (Pp.item "was resource found in context" (IT.pp (bool_ (not needed) here))));
       let@ res = begin match needed with
       | false ->
          let r = (({
              name = requested.name;
              pointer = requested.pointer;
              iargs = requested.iargs;
            } : predicate_type), oarg)
          in
          (* let r = RE.simp_predicate ~only_outputs:true global.struct_decls all_lcs r in *)
          return (Some (r, changed_or_deleted))
       | true ->
          (* TODO revisit this location *)
          let here = Locations.other __FUNCTION__ in
          begin match packing_ft here global provable (P requested) with
          | Some packing_ft ->
             Pp.debug 9 (lazy (Pp.item "attempting to pack compound resource"
                 (LAT.pp (fun _ -> Pp.string "resource") packing_ft)));
             let@ o, changed_or_deleted = ftyp_args_request_for_pack loc uiinfo packing_ft in
             return (Some ((requested, O o), changed_or_deleted))
          | None ->
             Pp.debug 9 (lazy (Pp.item "no pack rule for resource, out of options"
                 (RET.pp (P requested))));
             return None
          end
       end in
       time_log_end start_timing;
       return res






  and qpredicate_request_aux loc uiinfo (requested : RET.qpredicate_type) =
       debug 7 (lazy (item "qpredicate request" (RET.pp (Q requested))));
       let@ provable = provable loc in
       let@ simp_ctxt = simp_ctxt () in
       let@ global = get_global () in
       let needed = requested.permission in
       let step = Simplify.IndexTerms.simp simp_ctxt requested.step in
       let@ () =
           if Option.is_some (IT.is_const step) then return ()
           else fail (fun _ -> {loc; msg = Generic (!^ "cannot simplify iter-step to constant:"
               ^^^ IT.pp requested.step ^^ colon ^^^ IT.pp step)})
       in
       let@ ((needed, oarg), rw_time) =
         map_and_fold_resources loc (fun re (needed, oarg) ->
             let continue = (Unchanged, (needed, oarg)) in
             assert (RET.steps_constant (fst re));
             if is_false needed then continue else
             match re with
             | (Q p', O p'_oarg) when subsumed requested.name p'.name
                         && IT.equal step p'.step
                         && BT.equal (snd requested.q) (snd p'.q) ->
                let p' = alpha_rename_qpredicate_type_ (fst requested.q) p' in
                let here = Locations.other __FUNCTION__ in
                let pmatch = eq_ (requested.pointer, p'.pointer) here in
                let iarg_match = and_ (List.map2 (fun x y -> eq__ x y here) requested.iargs p'.iargs) here in
                let took = and_ [iarg_match; requested.permission; p'.permission] here in
                begin match provable (LC.Forall (requested.q, not_ took here)) with
                | `True -> continue
                | `False ->
                begin match provable (LC.T pmatch) with
                | `True ->
                   Pp.debug 9 (lazy (Pp.item "used resource" (RET.pp (fst re))));
                   let needed' = and_ [needed; not_ (and_ [iarg_match; p'.permission] here) here] here in
                   let permission' = and_ [p'.permission; not_ (and_ [iarg_match; needed] here) here] here in
                   let oarg = add_case (Many {many_guard = took; value = p'_oarg}) oarg in
                   Changed (Q {p' with permission = permission'}, O p'_oarg),
                   (Simplify.IndexTerms.simp simp_ctxt needed', oarg)
                | `False ->
                   let model = Solver.model () in
                   Pp.debug 9 (lazy (Pp.item "couldn't use q-resource" (RET.pp (fst re))));
                   debug_constraint_failure_diagnostics 9 model global simp_ctxt (LC.T pmatch);
                   continue
                end end
             | re ->
                continue
           ) (needed, C [])
       in
       let here = Locations.other __FUNCTION__ in
       let@ needed, oarg =
         let@ movable_indices = get_movable_indices () in
         ListM.fold_rightM (fun (predicate_name, index) (needed, oarg) ->
             let continue = return (needed, oarg) in
             if not (is_false needed) && subsumed requested.name predicate_name &&
                     BT.equal (snd requested.q) (IT.bt index) then
               let su = IT.make_subst [(fst requested.q, index)] in
               let needed_at_index = (IT.subst su needed) in
               match provable (LC.t_ needed_at_index) with
               | `False -> continue
               | `True ->
                   let@ o_re_index =
                     predicate_request loc uiinfo
                       { name = requested.name;
                         pointer = pointer_offset_ (requested.pointer,
                             (mul_ (cast_ Memory.intptr_bt requested.step here,
                                 cast_ Memory.intptr_bt index here) here)) here;
                         iargs = List.map (IT.subst su) requested.iargs;
                       }
                   in
                   match o_re_index with
                   | None -> continue
                   | Some ((p', O p'_oarg), _) ->
                      let oarg = add_case (One {one_index = index; value = p'_oarg}) oarg in
                      let (sym, bt) = requested.q in
                      let needed' = and_ [needed; ne__ (sym_ (sym, bt, here)) index here] here in
                      return (needed', oarg)
             else continue

           ) movable_indices (needed, oarg)
       in
       let nothing_more_needed = forall_ requested.q (not_ needed here) in
       Pp.debug 9 (lazy (Pp.item "checking resource remainder" (LC.pp nothing_more_needed)));
       let holds = provable nothing_more_needed in
       begin match holds with
       | `True -> return (Some (oarg, rw_time))
       | `False ->
         let@ model = model () in
         debug_constraint_failure_diagnostics 9 model global simp_ctxt nothing_more_needed;
         return None
       end

  and qpredicate_request loc uiinfo (requested : RET.qpredicate_type) =
    let@ o_oarg = qpredicate_request_aux loc uiinfo requested in
    let@ oarg_item_bt = WellTyped.oarg_bt_of_pred loc requested.name in
    match o_oarg with
    | None -> return None
    | Some (oarg, rw_time) ->
       let@ oarg = cases_to_map loc uiinfo (snd requested.q) oarg_item_bt oarg in
       let r = {
           name = requested.name;
           pointer = requested.pointer;
           q = requested.q;
           q_loc = requested.q_loc;
           step = requested.step;
           permission = requested.permission;
           iargs = requested.iargs;
         }
       in
       return (Some ((r, O oarg), rw_time))


  and ftyp_args_request_for_pack loc uiinfo ftyp =
    (* record the resources now, so errors are raised with all
       the resources present, rather than those that remain after some
       arguments are claimed *)
    let@ original_resources = all_resources_tagged loc in
    let rec loop ftyp rw_time =
      match ftyp with
      | LAT.I rt -> return (rt, rw_time)
      | _ ->
        let@ ftyp, rw_time =
          parametric_ftyp_args_request_step
            resource_request IT.subst loc
            uiinfo original_resources ftyp rw_time
        in
        loop ftyp rw_time
    in
    loop ftyp []

  and resource_request loc uiinfo (request : RET.t) : ((RE.t * int list) option) m =
    match request with
    | P request ->
       let@ result = predicate_request loc uiinfo request in
       return (Option.map (fun ((p, o), changed_or_deleted) -> ((P p, o), changed_or_deleted)) result)
    | Q request ->
       let@ result = qpredicate_request loc uiinfo request in
       return (Option.map (fun ((q, o), changed_or_deleted) -> ((Q q, o), changed_or_deleted)) result)



  (* I don't know if we need the rw_time in check.ml? *)
  let ftyp_args_request_step rt_subst loc situation original_resources ftyp =
    let@ rt, _rw_time =
      parametric_ftyp_args_request_step resource_request rt_subst loc
        situation original_resources ftyp []
    in
    return rt

end

module Special = struct

  let fail_missing_resource loc (situation, requests) =
    let here = Locations.other __FUNCTION__ in
    let@ model = model_with loc (bool_ true here) in
    let model = Option.get model in
    fail (fun ctxt ->
        let msg = Missing_resource {requests; situation; model; ctxt} in
        {loc; msg})


  let predicate_request loc situation (request, oinfo) =
    let requests = [TypeErrors.{resource = P request;
        loc = Option.map fst oinfo; reason = Option.map snd oinfo}] in
    let uiinfo = (situation, requests) in
    let@ result = General.predicate_request loc uiinfo request in
    match result with
    | Some r -> return r
    | None -> fail_missing_resource loc uiinfo


  let qpredicate_request loc situation (request, oinfo) =
    let requests = [TypeErrors.{resource = Q request;
        loc = Option.map fst oinfo; reason = Option.map snd oinfo}] in
    let uiinfo = (situation, requests) in
    let@ result = General.qpredicate_request loc uiinfo request in
    match result with
    | Some r -> return r
    | None -> fail_missing_resource loc uiinfo

end


