module IT = IndexTerms
open IT
open Pp
open ResourceTypes
open Resources
open Typing

open Effectful.Make (Typing)

open TypeErrors
open LogicalConstraints
module LAT = LogicalArgumentTypes
module RET = ResourceTypes
open ResourcePredicates
open Memory
open Pack

let unpack_def global name args =
  Option.bind (Global.get_logical_function_def global name) (fun def ->
    match def.definition with
    | Def body -> Some (LogicalFunctions.open_fun def.args body args)
    | _ -> None)


let debug_constraint_failure_diagnostics
  lvl
  (model_with_q : Solver.model_with_q)
  global
  simp_ctxt
  c
  =
  let model = fst model_with_q in
  if !Pp.print_level == 0 then
    ()
  else (
    let pp_f = pp_with_eval (Solver.eval global model) in
    let diag msg c =
      match (c, model_with_q) with
      | LC.T tm, _ ->
        Pp.debug lvl (lazy (Pp.item msg (IT.pp tm)));
        Pp.debug lvl (lazy (pp_f tm))
      | LC.Forall ((sym, _bt), tm), (_, [ (sym', _bt') ]) ->
        let tm' = IT.subst (IT.make_rename ~from:sym ~to_:sym') tm in
        Pp.debug lvl (lazy (Pp.item ("quantified " ^ msg) (IT.pp tm)));
        Pp.debug lvl (lazy (pp_f tm'))
      | _ ->
        Pp.warn
          (Locations.other __FUNCTION__)
          (Pp.bold "unexpected quantifier count with model")
    in
    diag "counterexample, expanding" c;
    let c2 = Simplify.LogicalConstraints.simp simp_ctxt c in
    if LC.equal c c2 then
      ()
    else
      diag "simplified variant" c2)


module General = struct
  type one =
    { one_index : IT.t;
      value : IT.t
    }

  type many =
    { many_guard : IT.t;
      value : IT.t
    }

  type uiinfo = TypeErrors.situation * TypeErrors.request_chain

  type case =
    | One of one
    | Many of many

  let pp_case = function
    | One { one_index; value } ->
      !^"one" ^^ parens (IT.pp one_index ^^ colon ^^^ IT.pp value)
    | Many { many_guard; value } ->
      !^"many" ^^ parens (IT.pp many_guard ^^ colon ^^^ IT.pp value)


  type cases = C of case list

  let add_case case (C cases) = C (cases @ [ case ])

  let cases_to_map loc (situation, requests) a_bt item_bt (C cases) =
    let here = Locations.other __FUNCTION__ in
    let update_with_ones base_array ones =
      List.fold_left
        (fun m { one_index; value } -> map_set_ m (one_index, value) here)
        base_array
        ones
    in
    let ones, manys =
      List.partition_map (function One c -> Left c | Many c -> Right c) cases
    in
    let@ base_value =
      match (manys, item_bt) with
      | [ { many_guard = _; value } ], _ -> return value
      | [], _ | _, BT.Unit -> return (default_ (BT.Map (a_bt, item_bt)) here)
      | _many, _ ->
        let term = IndexTerms.bool_ true here in
        let@ model = model_with here term in
        let model = Option.get model in
        fail (fun ctxt ->
          { loc; msg = Merging_multiple_arrays { requests; situation; ctxt; model } })
    in
    return (update_with_ones base_value ones)


  (* this version is parametric in resource_request (defined below) to ensure the
     return-type (also parametric) is as general as possible *)
  let parametric_ftyp_args_request_step
    resource_request
    rt_subst
    loc
    (uiinfo : uiinfo)
    _original_resources
    ftyp
    changed_or_deleted
    =
    (* take one step of the "spine" judgement, reducing a function-type by claiming an
       argument resource or otherwise reducing towards an instantiated return-type *)
    let@ simp_ctxt = simp_ctxt () in
    match ftyp with
    | LAT.Resource ((s, (resource, _bt)), info, ftyp) ->
      let resource = Simplify.ResourceTypes.simp simp_ctxt resource in
      let situation, request_chain = uiinfo in
      let step =
        TypeErrors.
          { resource; loc = Some (fst info); reason = Some ("arg " ^ Sym.pp_string s) }
      in
      let request_chain = step :: request_chain in
      let uiinfo = (situation, request_chain) in
      let@ o_re_oarg = resource_request loc uiinfo resource in
      (match o_re_oarg with
       | None ->
         let here = Locations.other __FUNCTION__ in
         let@ model = model_with loc (bool_ true here) in
         let model = Option.get model in
         fail (fun ctxt ->
           (* let ctxt = { ctxt with resources = original_resources } in *)
           let msg =
             Missing_resource { requests = request_chain; situation; model; ctxt }
           in
           { loc; msg })
       | Some ((re, O oargs), changed_or_deleted') ->
         assert (ResourceTypes.equal re resource);
         let oargs = Simplify.IndexTerms.simp simp_ctxt oargs in
         let changed_or_deleted = changed_or_deleted @ changed_or_deleted' in
         return
           (LAT.subst rt_subst (IT.make_subst [ (s, oargs) ]) ftyp, changed_or_deleted))
    | Define ((s, it), _info, ftyp) ->
      let it = Simplify.IndexTerms.simp simp_ctxt it in
      return (LAT.subst rt_subst (IT.make_subst [ (s, it) ]) ftyp, changed_or_deleted)
    | Constraint (c, info, ftyp) ->
      let@ () = return (debug 9 (lazy (item "checking constraint" (LC.pp c)))) in
      let@ provable = provable loc in
      let res = provable c in
      (match res with
       | `True -> return (ftyp, changed_or_deleted)
       | `False ->
         let@ model = model () in
         let@ global = get_global () in
         let@ all_cs = get_cs () in
         let () = assert (not (Context.LCSet.mem c all_cs)) in
         debug_constraint_failure_diagnostics 6 model global simp_ctxt c;
         let@ () = Diagnostics.investigate model c in
         fail (fun ctxt ->
           (* let ctxt = { ctxt with resources = original_resources } in *)
           { loc;
             msg =
               Unproven_constraint
                 { constr = c; info; requests = snd uiinfo; ctxt; model }
           }))
    | I _rt -> return (ftyp, changed_or_deleted)


  (* TODO: check that oargs are in the same order? *)
  let rec predicate_request
    loc
    (uiinfo : uiinfo)
    (requested : RET.predicate_type)
    ~alloc_or_owned
    : ((predicate_type * oargs) * int list) option m
    =
    debug 7 (lazy (item "predicate request" (RET.pp (P requested))));
    let start_timing = time_log_start "predicate-request" "" in
    let@ oarg_bt = WellTyped.oarg_bt_of_pred loc requested.name in
    let@ provable = provable loc in
    let@ global = get_global () in
    let@ simp_ctxt = simp_ctxt () in
    let resource_scan re ((needed : bool), oargs) =
      let continue = (Unchanged, (needed, oargs)) in
      if not needed then
        continue
      else (
        let alloc_owned = alloc_or_owned in
        match re with
        | P p', p'_oarg when RET.subsumed ~alloc_owned requested.name p'.name ->
          let here = Locations.other __FUNCTION__ in
          let p'_oarg, addr_iargs_eqs =
            if RET.equal_predicate_name RET.alloc requested.name then (
              match p'.name with
              | PName name ->
                assert (Sym.equal name Alloc.Predicate.sym);
                (p'_oarg, [])
              | Owned (ct, _) ->
                assert alloc_owned;
                let p'_addr = addr_ p'.pointer here in
                let req_addr = addr_ requested.pointer here in
                ( O (Alloc.History.lookup_ptr requested.pointer here),
                  [ le_ (p'_addr, req_addr) here;
                    le_ (req_addr, RE.upper_bound p'_addr ct here) here
                  ] ))
            else
              ( p'_oarg,
                eq_ ((addr_ requested.pointer) here, addr_ p'.pointer here) here
                :: List.map2 (fun x y -> eq__ x y here) requested.iargs p'.iargs )
          in
          let addr_iargs_match = and_ addr_iargs_eqs here in
          let alloc_id_eq =
            eq_ (allocId_ requested.pointer here, allocId_ p'.pointer here) here
          in
          let debug_failure model msg term =
            Pp.debug 9 (lazy (Pp.item msg (RET.pp (fst re))));
            debug_constraint_failure_diagnostics 9 model global simp_ctxt (LC.T term)
          in
          (match provable (LC.T addr_iargs_match) with
           | `True ->
             (match provable (LC.T alloc_id_eq) with
              | `True ->
                Pp.debug 9 (lazy (Pp.item "used resource" (RET.pp (fst re))));
                (Deleted, (false, p'_oarg))
              | `False ->
                debug_failure
                  (Solver.model ())
                  "couldn't use resource (matched address but not provenance)"
                  alloc_id_eq;
                continue)
           | `False ->
             let model = Solver.model () in
             (match provable (LC.T alloc_id_eq) with
              | `True ->
                debug_failure
                  model
                  "couldn't use resource (matched provenance but not address)"
                  addr_iargs_match;
                continue
              | `False ->
                debug_failure
                  (Solver.model ())
                  "couldn't use resource"
                  (and_
                     (eq_ (requested.pointer, p'.pointer) here :: List.tl addr_iargs_eqs)
                     here);
                continue))
        | _re -> continue)
    in
    let needed = true in
    let here = Locations.other __FUNCTION__ in
    let@ (needed, oarg), changed_or_deleted =
      map_and_fold_resources loc resource_scan (needed, O (default_ oarg_bt here))
    in
    let not_str = lazy (if needed then !^" not " else !^" ") in
    Pp.debug 9 (Lazy.map (fun x -> !^"resource was" ^^ x ^^ !^"found in context") not_str);
    let@ res =
      match needed with
      | false -> return (Some ((requested, oarg), changed_or_deleted))
      | true ->
        (match packing_ft here global provable (P requested) with
         | Some packing_ft ->
           let ft_pp = lazy (LAT.pp (fun _ -> Pp.string "resource") packing_ft) in
           Pp.debug 9 (Lazy.map (Pp.item "attempting to pack compound resource") ft_pp);
           let@ o, changed_or_deleted =
             ftyp_args_request_for_pack loc uiinfo packing_ft
           in
           return (Some ((requested, O o), changed_or_deleted))
         | None ->
           let req_pp = lazy (RET.pp (P requested)) in
           Pp.debug 9 (Lazy.map (Pp.item "no pack rule for resource, failing") req_pp);
           return None)
    in
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
      if Option.is_some (IT.is_const step) then
        return ()
      else
        fail (fun _ ->
          { loc;
            msg =
              Generic
                (!^"cannot simplify iter-step to constant:"
                 ^^^ IT.pp requested.step
                 ^^ colon
                 ^^^ IT.pp step)
          })
    in
    let@ (needed, oarg), rw_time =
      map_and_fold_resources
        loc
        (fun re (needed, oarg) ->
          let continue = (Unchanged, (needed, oarg)) in
          assert (RET.steps_constant (fst re));
          if is_false needed then
            continue
          else (
            match re with
            | Q p', O p'_oarg
              when subsumed ~alloc_owned:false requested.name p'.name
                   && IT.equal step p'.step
                   && BT.equal (snd requested.q) (snd p'.q) ->
              let p' = alpha_rename_qpredicate_type_ (fst requested.q) p' in
              let here = Locations.other __FUNCTION__ in
              let pmatch =
                (* Work-around for https://github.com/Z3Prover/z3/issues/7352 *)
                Simplify.IndexTerms.simp simp_ctxt
                @@ eq_ (requested.pointer, p'.pointer) here
              in
              let iarg_match =
                and_ (List.map2 (fun x y -> eq__ x y here) requested.iargs p'.iargs) here
              in
              let took = and_ [ iarg_match; requested.permission; p'.permission ] here in
              (match provable (LC.Forall (requested.q, not_ took here)) with
               | `True -> continue
               | `False ->
                 (match provable (LC.T pmatch) with
                  | `True ->
                    Pp.debug 9 (lazy (Pp.item "used resource" (RET.pp (fst re))));
                    let needed' =
                      and_
                        [ needed; not_ (and_ [ iarg_match; p'.permission ] here) here ]
                        here
                    in
                    let permission' =
                      and_
                        [ p'.permission; not_ (and_ [ iarg_match; needed ] here) here ]
                        here
                    in
                    let oarg =
                      add_case (Many { many_guard = took; value = p'_oarg }) oarg
                    in
                    ( Changed (Q { p' with permission = permission' }, O p'_oarg),
                      (Simplify.IndexTerms.simp simp_ctxt needed', oarg) )
                  | `False ->
                    let model = Solver.model () in
                    Pp.debug
                      9
                      (lazy (Pp.item "couldn't use q-resource" (RET.pp (fst re))));
                    debug_constraint_failure_diagnostics
                      9
                      model
                      global
                      simp_ctxt
                      (LC.T pmatch);
                    continue))
            | _re -> continue))
        (needed, C [])
    in
    let here = Locations.other __FUNCTION__ in
    let@ needed, oarg =
      let@ movable_indices = get_movable_indices () in
      ListM.fold_rightM
        (fun (predicate_name, index) (needed, oarg) ->
          let continue = return (needed, oarg) in
          if
            (not (is_false needed))
            && subsumed ~alloc_owned:false requested.name predicate_name
            && BT.equal (snd requested.q) (IT.bt index)
          then (
            let su = IT.make_subst [ (fst requested.q, index) ] in
            let needed_at_index = IT.subst su needed in
            match provable (LC.t_ needed_at_index) with
            | `False -> continue
            | `True ->
              let@ o_re_index =
                predicate_request
                  loc
                  uiinfo
                  { name = requested.name;
                    pointer =
                      pointer_offset_
                        ( requested.pointer,
                          mul_
                            ( cast_ Memory.uintptr_bt requested.step here,
                              cast_ Memory.uintptr_bt index here )
                            here )
                        here;
                    iargs = List.map (IT.subst su) requested.iargs
                  }
                  ~alloc_or_owned:false
              in
              (match o_re_index with
               | None -> continue
               | Some ((_p', O p'_oarg), _) ->
                 let oarg = add_case (One { one_index = index; value = p'_oarg }) oarg in
                 let sym, bt = requested.q in
                 let needed' =
                   and_ [ needed; ne__ (sym_ (sym, bt, here)) index here ] here
                 in
                 return (needed', oarg)))
          else
            continue)
        movable_indices
        (needed, oarg)
    in
    let nothing_more_needed = forall_ requested.q (not_ needed here) in
    Pp.debug 9 (lazy (Pp.item "checking resource remainder" (LC.pp nothing_more_needed)));
    let holds = provable nothing_more_needed in
    match holds with
    | `True -> return (Some (oarg, rw_time))
    | `False ->
      let@ model = model () in
      debug_constraint_failure_diagnostics 9 model global simp_ctxt nothing_more_needed;
      return None


  and qpredicate_request loc uiinfo (requested : RET.qpredicate_type) =
    let@ o_oarg = qpredicate_request_aux loc uiinfo requested in
    let@ oarg_item_bt = WellTyped.oarg_bt_of_pred loc requested.name in
    match o_oarg with
    | None -> return None
    | Some (oarg, rw_time) ->
      let@ oarg = cases_to_map loc uiinfo (snd requested.q) oarg_item_bt oarg in
      let r =
        { name = requested.name;
          pointer = requested.pointer;
          q = requested.q;
          q_loc = requested.q_loc;
          step = requested.step;
          permission = requested.permission;
          iargs = requested.iargs
        }
      in
      return (Some ((r, O oarg), rw_time))


  and ftyp_args_request_for_pack loc uiinfo ftyp =
    (* record the resources now, so errors are raised with all the resources present,
       rather than those that remain after some arguments are claimed *)
    let@ original_resources = all_resources_tagged loc in
    let rec loop ftyp rw_time =
      match ftyp with
      | LAT.I rt -> return (rt, rw_time)
      | _ ->
        let@ ftyp, rw_time =
          parametric_ftyp_args_request_step
            (resource_request ~alloc_or_owned:false)
            IT.subst
            loc
            uiinfo
            original_resources
            ftyp
            rw_time
        in
        loop ftyp rw_time
    in
    loop ftyp []


  and resource_request loc uiinfo (request : RET.t) ~alloc_or_owned
    : (RE.t * int list) option m
    =
    match request with
    | P request ->
      let@ result = predicate_request loc uiinfo request ~alloc_or_owned in
      return
        (Option.map
           (fun ((p, o), changed_or_deleted) -> ((P p, o), changed_or_deleted))
           result)
    | Q request ->
      let@ result = qpredicate_request loc uiinfo request in
      return
        (Option.map
           (fun ((q, o), changed_or_deleted) -> ((Q q, o), changed_or_deleted))
           result)


  (* I don't know if we need the rw_time in check.ml? *)
  let ftyp_args_request_step rt_subst loc situation original_resources ftyp =
    let@ rt, _rw_time =
      parametric_ftyp_args_request_step
        (resource_request ~alloc_or_owned:false)
        rt_subst
        loc
        situation
        original_resources
        ftyp
        []
    in
    return rt
end

module Special = struct
  let fail_missing_resource loc (situation, requests) =
    let here = Locations.other __FUNCTION__ in
    let@ model = model_with loc (bool_ true here) in
    let model = Option.get model in
    fail (fun ctxt ->
      let msg = Missing_resource { requests; situation; model; ctxt } in
      { loc; msg })


  let predicate_request loc situation (request, oinfo) ~alloc_or_owned =
    let requests =
      [ TypeErrors.
          { resource = P request;
            loc = Option.map fst oinfo;
            reason = Option.map snd oinfo
          }
      ]
    in
    let uiinfo = (situation, requests) in
    let@ result = General.predicate_request loc uiinfo request ~alloc_or_owned in
    match result with Some r -> return r | None -> fail_missing_resource loc uiinfo


  let is_pointer_live loc situation pointer =
    let request = RET.make_alloc pointer in
    pure @@ predicate_request loc situation (request, None) ~alloc_or_owned:true


  let predicate_request loc situation (request, oinfo) =
    predicate_request loc situation (request, oinfo) ~alloc_or_owned:false


  let qpredicate_request loc situation (request, oinfo) =
    let requests =
      [ TypeErrors.
          { resource = Q request;
            loc = Option.map fst oinfo;
            reason = Option.map snd oinfo
          }
      ]
    in
    let uiinfo = (situation, requests) in
    let@ result = General.qpredicate_request loc uiinfo request in
    match result with Some r -> return r | None -> fail_missing_resource loc uiinfo
end
