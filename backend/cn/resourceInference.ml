module IT = IndexTerms
open IT
open Pp
open ResourceTypes
open Resources
open Typing
open Effectful.Make(Typing)
open TypeErrors
open BaseTypes
open LogicalConstraints


let reorder_points = ref true
let additional_sat_check = ref true
let span_actions = ref true

let oargs_list (O oargs) = 
  let members = match IT.bt oargs with
    | Record members -> members
    | _ -> assert false
  in
  List.map (fun (s, member_bt) ->
      (s, recordMember_ ~member_bt (oargs, s))
    ) members


module General = struct

  type one = {one_index : IT.t; value : IT.t}
  type many = {many_guard: IT.t; value : IT.t}

  type case =
    | One of one
    | Many of many

  let pp_case = function
    | One {one_index;value} -> 
       !^"one" ^^ parens (IT.pp one_index ^^ colon ^^^ IT.pp value)
    | Many {many_guard;value} -> 
       !^"many" ^^ parens (IT.pp many_guard ^^ colon ^^^ IT.pp value)

  type cases = C of case list


  let unfold_struct_request tag pointer_t permission_t = 
    {
      name = Owned (Struct tag);
      pointer = pointer_t;
      iargs = [];
      permission = permission_t;
    }

  let exact_ptr_match () =
    let@ global = get_global () in
    let@ values, equalities, lcs = simp_constraints () in
    let simp t = Simplify.simp global.struct_decls values equalities lcs t in
    return (fun (p, p') -> is_true (simp (eq_ (p, p'))))

  let exact_match () =
    let@ pmatch = exact_ptr_match () in
    let match_f (request, resource) =
      match (request, resource) with
      | (P req_p, 
         P res_p) ->
         pmatch (req_p.pointer, res_p.pointer)
      | (Q ({name = Owned _; _} as req_qp), 
         Q ({name = Owned _; _} as res_qp)) ->
         pmatch (req_qp.pointer, res_qp.pointer)
      | _ -> false
    in
    return match_f

  let exact_match_point_ptrs ptrs =
    let@ pmatch = exact_ptr_match () in
    let match_f resource = 
      match resource with
      | P ({name = Owned _; _} as res_p) -> 
         List.exists (fun p -> pmatch (p, res_p.pointer)) ptrs
      | _ -> false
    in
    return match_f

  let scan_key_indices v_nm t =
    let is_i t = match t with
      | IT (Lit (Sym nm2), _) -> Sym.equal nm2 v_nm
      | _ -> false
    in
    let rec f pol t = match t with
      | IT (Bool_op (And xs), _) -> List.concat (List.map (f pol) xs)
      | IT (Bool_op (Or xs), _) -> List.concat (List.map (f pol) xs)
      | IT (Bool_op (Impl (x, y)), _) -> f (not pol) x @ f pol y
      | IT (Bool_op (EQ (x, y)), _) ->
        if pol && is_i x then [y] else if pol && is_i y then [x] else []
      | IT (Bool_op (Not x), _) -> f (not pol) x
      | _ -> []
    in
    let xs = f true t in
    List.sort_uniq IT.compare xs


  let cases_to_map loc (situation, (orequest, oinfo)) a_bt item_bt (C cases) = 
    let update_with_ones base_array ones =
      List.fold_left (fun m {one_index; value} ->
          map_set_ m (one_index, value)
        ) base_array ones
    in
    let ones, manys = 
      List.partition_map (function One c -> Left c | Many c -> Right c) cases in
    let@ base_value = match manys with
      | [] -> return (default_ (BT.Map (a_bt, item_bt)))
      | [{many_guard = _; value}] -> return value
      | _ -> 
         let@ model = model () in
         fail (fun ctxt ->
             let msg = Merging_multiple_arrays {orequest; situation; oinfo; model; ctxt} in
             {loc; msg})
    in
    return (update_with_ones base_value ones)






  (* TODO: check that oargs are in the same order? *)
  let rec predicate_request ~recursive loc uiinfo (requested : RET.predicate_type) =
    match requested.name with
    | Owned requested_ct ->
       assert (match requested.iargs with [] -> true | _ -> false);
       debug 7 (lazy (item "point request" (RET.pp (P requested))));
       let@ _ = span_fold_unfolds loc uiinfo (RET.P requested) false in
       let start_timing = time_log_start "point-request" "" in
       let@ provable = provable loc in
       let@ is_ex = exact_match () in
       let is_exact_re (re : RET.t) = !reorder_points && (is_ex (RET.P requested, re)) in
       let@ global = get_global () in
       let@ simp_lcs = simp_constraints () in
       let needed = requested.permission in 
       let sub_resource_if = fun cond re (needed, oargs) ->
             let continue = (Unchanged, (needed, oargs)) in
             if is_false needed || not (cond (fst re)) then continue else
             match re with
             | (P p', p'_oargs) when equal_predicate_name (Owned requested_ct) p'.name ->
                debug 15 (lazy (item "point/point sub at ptr" (IT.pp p'.pointer)));
                let pmatch = eq_ (requested.pointer, p'.pointer) in
                let took = and_ [pmatch; p'.permission; needed] in
                begin match provable (LC.T took) with
                | `True ->
                   Deleted, 
                   (bool_ false, p'_oargs)
                | `False -> 
                   continue
                end
             | (Q p', p'_oargs) when equal_predicate_name (Owned requested_ct) p'.name ->
                let base = p'.pointer in
                debug 15 (lazy (item "point/qpoint sub at base ptr" (IT.pp base)));
                let item_size = int_ (Memory.size_of_ctype requested_ct) in
                let offset = array_offset_of_pointer ~base ~pointer:requested.pointer in
                let index = array_pointer_to_index ~base ~item_size ~pointer:requested.pointer in
                let pre_match =
                  (* adapting from RE.subarray_condition *)
                  and_ [lePointer_ (base, requested.pointer);
                        divisible_ (offset, item_size)]
                in
                let subst = IT.make_subst [(p'.q, index)] in
                let took = and_ [pre_match; IT.subst subst p'.permission; needed] in
                begin match provable (LC.T took) with
                | `True ->
                   let permission' = and_ [p'.permission; ne_ (sym_ (p'.q, Integer), index)] in
                   let oargs = 
                     List.map_snd (fun oa' -> map_get_ oa' index) 
                       (oargs_list p'_oargs)
                   in
                   Changed (Q {p' with permission = permission'}, p'_oargs), 
                   (bool_ false, O (record_ oargs))
                | `False -> continue
                end
             | _ ->
                continue
       in
       let@ (needed, oargs) =
         map_and_fold_resources loc (sub_resource_if is_exact_re)
           (needed, O (default_ (owned_oargs requested_ct)))
       in
       let@ (needed, oargs) =
         map_and_fold_resources loc (sub_resource_if (fun re -> not (is_exact_re re)))
           (needed, oargs) in
       let@ res = begin match provable (t_ (not_ needed)) with
       | `True ->
          let r = ({ 
              name = Owned requested_ct;
              pointer = requested.pointer;
              iargs = [];
              permission = requested.permission 
            }, oargs)
          in
          return (Some r)
       | `False ->
          return None
       end in
       time_log_end start_timing;
       return res
    | pname -> 
       debug 7 (lazy (item "predicate request" (RET.pp (P requested))));
       let start_timing = time_log_start "predicate-request" "" in
       let@ def_oargs = match pname with
         | Block _ -> return Resources.block_oargs
         | Owned _ -> assert false
         | PName pname -> 
            let@ def = Typing.get_resource_predicate_def loc pname in
            return (Record def.oargs)
       in
       let@ provable = provable loc in
       let@ global = get_global () in
       let@ simp_lcs = simp_constraints () in
       let needed = requested.permission in 
       let sub_predicate_if = fun cond re (needed, oargs) ->
             let continue = (Unchanged, (needed, oargs)) in
             if is_false needed then continue else
             match re with
             | (P p', p'_oargs) when equal_predicate_name requested.name p'.name ->
                let pmatch = 
                  eq_ (requested.pointer, p'.pointer)
                  :: List.map2 eq__ requested.iargs p'.iargs
                in
                let took = and_ (needed :: p'.permission :: pmatch) in
                begin match provable (LC.T took) with
                | `True ->
                   Deleted, 
                   (bool_ false, p'_oargs)
                | `False -> continue
                end
             | (Q p', p'_oargs) when equal_predicate_name requested.name p'.name ->
                let base = p'.pointer in
                let item_size = int_ p'.step in
                let offset = array_offset_of_pointer ~base ~pointer:requested.pointer in
                let index = array_pointer_to_index ~base ~item_size ~pointer:requested.pointer in
                let subst = IT.make_subst [(p'.q, index)] in
                let pre_match = 
                  (* adapting from RE.subarray_condition *)
                  and_ (lePointer_ (base, requested.pointer)
                        :: divisible_ (offset, item_size)
                        :: List.map2 (fun ia ia' -> eq_ (ia, IT.subst subst ia')) requested.iargs p'.iargs)
                in
                let took = and_ [pre_match; needed; IT.subst subst p'.permission] in
                begin match provable (LC.T took) with
                | `True ->
                   let oargs = List.map_snd (fun oa' -> map_get_ oa' index) (oargs_list p'_oargs) in
                   let i_match = eq_ (sym_ (p'.q, Integer), index) in
                   let permission' = and_ [p'.permission; not_ i_match] in
                   Changed (Q {p' with permission = permission'}, p'_oargs), 
                   (bool_ false, O (record_ oargs))
                | `False -> continue
                end
             | re ->
                continue
       in
       let@ is_ex = exact_match () in
       let is_exact_re re = !reorder_points && (is_ex (P requested, re)) in
       let@ (needed, oargs) =
         map_and_fold_resources loc (sub_predicate_if is_exact_re)
             (needed, O (default_ def_oargs))
       in
       let@ (needed, oargs) =
         map_and_fold_resources loc (sub_predicate_if (fun re -> not (is_exact_re re)))
             (needed, oargs)
       in
       let@ res = begin match provable (t_ (not_ needed)) with
       | `True ->
          let r = ({ 
              name = requested.name;
              pointer = requested.pointer;
              permission = requested.permission;
              iargs = requested.iargs; 
            }, oargs)
          in
          (* let r = RE.simp_predicate ~only_outputs:true global.struct_decls all_lcs r in *)
          return (Some r)
       | `False ->
          begin match pname with
          | Block ct -> 
             let@ oresult = 
               predicate_request ~recursive loc uiinfo 
                 ({name = Owned ct; 
                   pointer = requested.pointer;
                   iargs = [];
                   permission = requested.permission;
                  } : predicate_type)
             in
             begin match oresult with
             | None -> return None
             | Some _ -> 
                let r = ({
                    name = requested.name;
                    pointer = requested.pointer;
                    permission = requested.permission;
                    iargs = requested.iargs;
                  }, O (record_ []))
                in
                return (Some r)
             end
          | _ -> 
             return None
          end
       end in
       time_log_end start_timing;
       return res


  and qpredicate_request_aux loc uiinfo (requested : RET.qpredicate_type) =
    match requested.name with
    | Owned requested_ct ->
       assert (match requested.iargs with [] -> true | _ -> false);
       debug 7 (lazy (item "qpoint request" (RET.pp (Q requested))));
       let@ _ = span_fold_unfolds loc uiinfo (RET.Q requested) false in
       let start_timing = time_log_start "qpoint-request" "" in
       let@ provable = provable loc in
       let@ is_ex = exact_match () in
       let is_exact_re re = !reorder_points && (is_ex (Q requested, re)) in
       let@ global = get_global () in
       let@ values, equalities, lcs = simp_constraints () in
       let simp t = Simplify.simp global.struct_decls values equalities lcs t in
       let needed = requested.permission in
       let sub_resource_if = fun cond re (needed, oargs) ->
             let continue = (Unchanged, (needed, oargs)) in
             if is_false needed || not (cond (fst re)) then continue else
             match re with
             | (P p', p'_oargs) when equal_predicate_name (Owned requested_ct) p'.name ->
                let base = requested.pointer in
                let item_size = int_ (Memory.size_of_ctype requested_ct) in
                let offset = array_offset_of_pointer ~base ~pointer:p'.pointer in
                let index = array_pointer_to_index ~base ~item_size ~pointer:p'.pointer in
                let pre_match = 
                  and_ [lePointer_ (base, p'.pointer);
                        divisible_ (offset, item_size)]
                in
                let subst = IT.make_subst [(requested.q, index)] in
                let took = and_ [pre_match; IT.subst subst needed; p'.permission] in
                begin match provable (LC.T took) with
                | `True -> 
                   let i_match = eq_ (sym_ (requested.q, Integer), index) in
                   let oargs = 
                     List.map2 (fun (oarg_name, C oargs) (oarg_name', oa') ->
                         assert (Sym.equal oarg_name oarg_name');
                         (oarg_name, C (oargs @ [One {one_index = index; value = oa'}]))
                       ) oargs (oargs_list p'_oargs)
                   in
                   let needed' = and_ [needed; not_ (i_match)] in
                   Deleted, 
                   (simp needed', oargs)
                | `False -> continue
                end
             | (Q p', p'_oargs) when equal_predicate_name (Owned requested_ct) p'.name ->
                let p' = alpha_rename_qpredicate_type requested.q p' in
                let pmatch = eq_ (requested.pointer, p'.pointer) in
                (* todo: check for p' non-emptiness? *)
                begin match provable (LC.T pmatch) with
                | `True ->
                   let took = and_ [requested.permission; p'.permission] in
                   let oargs = 
                     List.map2 (fun (oarg_name, C oargs) (oarg_name', oa') ->
                         (oarg_name, C (oargs @ [Many {many_guard = took; value = oa'}]))
                       ) oargs (oargs_list p'_oargs)
                   in
                   let needed' = and_ [needed; not_ p'.permission] in
                   let permission' = and_ [p'.permission; not_ needed] in
                   Changed (Q {p' with permission = permission'}, p'_oargs), 
                   (simp needed', oargs)
                | `False -> continue
                end
             | re ->
                continue
       in
       let@ (needed, oargs) =
         map_and_fold_resources loc (sub_resource_if is_exact_re)
           (needed, List.map_snd (fun _ -> C []) (q_owned_oargs_list requested_ct))
       in
       debug 10 (lazy (item "needed after exact matches:" (IT.pp needed)));
       let k_is = scan_key_indices requested.q needed in
       let k_ptrs = List.map (fun i -> (i, arrayShift_ (requested.pointer, requested_ct, i))) k_is in
       let k_ptrs = List.map (fun (i, p) -> (simp i, simp p)) k_ptrs in
       if List.length k_ptrs == 0 then ()
       else debug 10 (lazy (item "key ptrs for additional matches:"
           (Pp.list IT.pp (List.map snd k_ptrs))));
       let@ k_ptr_match = exact_match_point_ptrs (List.map snd k_ptrs) in
       let is_exact_k (re : RET.t) = !reorder_points && k_ptr_match re in
       let necessary_k_ptrs = List.filter (fun (i, p) ->
           let i_match = eq_ (sym_ (requested.q, Integer), i) in
           match provable (forall_ (requested.q, BT.Integer) (impl_ (i_match, needed)))
           with `True -> true | _ -> false) k_ptrs in
       let@ () = 
         ListM.iterM (fun (_, p) ->
             let@ r = 
               predicate_request ~recursive:true loc uiinfo {
                   name = Owned requested_ct;
                   pointer = p;
                   iargs = [];
                   permission = bool_ true;
                 }
             in
             match r with
             | Some (res, res_oargs) -> add_r None (P res, res_oargs)
             | None -> return ()
           ) necessary_k_ptrs 
       in
       let@ (needed, oargs) =
         map_and_fold_resources loc (sub_resource_if is_exact_k)
           (needed, oargs) 
       in
       if List.length k_ptrs == 0 then ()
       else debug 10 (lazy (item "needed after additional matches:" (IT.pp needed)));
       let needed = if !additional_sat_check
         then begin
         match provable (forall_ (requested.q, BT.Integer) (not_ needed)) with
           | `True -> (debug 10 (lazy (format [] "proved needed == false.")); bool_ false)
           | _ -> (debug 10 (lazy (format [] "checked, needed is satisfiable.")); needed)
         end
         else needed in
       let@ (needed, oargs) =
         map_and_fold_resources loc (sub_resource_if
           (fun re -> not (is_exact_re re) && not (is_exact_k re)))
           (needed, oargs) 
       in
       let holds = provable (forall_ (requested.q, BT.Integer) (not_ needed)) in
       time_log_end start_timing;
       begin match holds with
       | `True -> return (Some oargs)
       | `False -> return None
       end
    | pname ->
       debug 7 (lazy (item "qpredicate request" (RET.pp (Q requested))));
       let@ def_oargs = match pname with
         | Block _ -> return block_oargs_list 
         | Owned _ -> assert false
         | PName pname ->
            let@ def = Typing.get_resource_predicate_def loc pname in
            return def.oargs
       in
       let@ provable = provable loc in
       let@ global = get_global () in
       let@ values, equalities, lcs = simp_constraints () in
       let simp it = Simplify.simp global.struct_decls values equalities lcs it in
       let needed = requested.permission in
       let@ (needed, oargs) =
         map_and_fold_resources loc (fun re (needed, oargs) ->
             let continue = (Unchanged, (needed, oargs)) in
             if is_false needed then continue else
             match re with
             | (P p', p'_oargs) when equal_predicate_name requested.name p'.name ->
                let base = requested.pointer in
                let item_size = int_ requested.step in
                let offset = array_offset_of_pointer ~base ~pointer:p'.pointer in
                let index = array_pointer_to_index ~base ~item_size ~pointer:p'.pointer in
                let subst = IT.make_subst [(requested.q, index)] in
                let pre_match = 
                  and_ (lePointer_ (base, p'.pointer)
                        :: divisible_ (offset, item_size)
                        :: List.map2 (fun ia ia' -> eq_ (IT.subst subst ia, ia')) requested.iargs p'.iargs
                    )
                in
                let took = and_ [pre_match; IT.subst subst needed; p'.permission] in
                begin match provable (LC.T took) with
                | `True ->
                   let i_match = eq_ (sym_ (requested.q, Integer), index) in
                   let oargs = 
                     List.map2 (fun (name, C oa) (name', oa') -> 
                         assert (Sym.equal name name');
                         (name, C (oa @ [One {one_index = index; value = oa'}]))
                       ) oargs (oargs_list p'_oargs)
                   in
                   let needed' = and_ [needed; not_ i_match] in
                   Deleted, 
                   (simp needed', oargs)
                | `False -> continue
                end
             | (Q p', p'_oargs) when equal_predicate_name requested.name p'.name 
                         && requested.step = p'.step ->
                let p' = alpha_rename_qpredicate_type requested.q p' in
                let pmatch = eq_ (requested.pointer, p'.pointer) in
                begin match provable (LC.T pmatch) with
                | `True ->
                   let iarg_match = and_ (List.map2 eq__ requested.iargs p'.iargs) in
                   let took = and_ [iarg_match; requested.permission; p'.permission] in
                   let needed' = and_ [needed; not_ (and_ [iarg_match; p'.permission])] in
                   let permission' = and_ [p'.permission; not_ (and_ [iarg_match; needed])] in
                   let oargs = 
                     List.map2 (fun (name, C oa) (name', oa') -> 
                         assert (Sym.equal name name');
                         (name, C (oa @ [Many {many_guard = took; value = oa'}]))
                       ) oargs (oargs_list p'_oargs)
                   in
                   Changed (Q {p' with permission = permission'}, p'_oargs), 
                   (simp needed', oargs)
                | `False -> continue
                end
             | re ->
                continue
           ) (needed, List.map_snd (fun _ -> C []) def_oargs)
       in
       let holds = provable (forall_ (requested.q, BT.Integer) (not_ needed)) in
       begin match holds with
       | `True -> return (Some oargs)
       | `False -> return None
       end

  and qpredicate_request loc uiinfo (requested : RET.qpredicate_type) = 
    let@ o_oargs = qpredicate_request_aux loc uiinfo requested in
    let@ oarg_item_bts = match requested.name with
      | Block _ -> return block_oargs_list
      | Owned ct -> return (owned_oargs_list ct)
      | PName pn ->
         let@ def = Typing.get_resource_predicate_def loc pn in
         return def.oargs
    in
    match o_oargs with
    | None -> return None
    | Some oargs ->
       let@ oas = 
         ListM.map2M (fun (name, C oa) (name', oa_bt) ->
             assert (Sym.equal name name');
             let@ map = cases_to_map loc uiinfo Integer oa_bt (C oa) in
             return (name, map)
           ) oargs oarg_item_bts
       in
       let r = { 
           name = requested.name;
           pointer = requested.pointer;
           q = requested.q;
           step = requested.step;
           permission = requested.permission;
           iargs = requested.iargs; 
         } 
       in
       return (Some (r, O (record_ oas)))


  and fold_array loc uiinfo item_ct base length permission =
    debug 7 (lazy (item "fold array" Pp.empty));
    debug 7 (lazy (item "item_ct" (Sctypes.pp item_ct)));
    debug 7 (lazy (item "base" (IT.pp base)));
    debug 7 (lazy (item "length" (IT.pp (int_ length))));
    debug 7 (lazy (item "permission" (IT.pp permission)));
    let q_s, q = IT.fresh Integer in
    let@ o_values = 
      qpredicate_request_aux loc uiinfo {
          name = Owned item_ct;
          pointer = base;
          q = q_s;
          step = Memory.size_of_ctype item_ct;
          iargs = [];
          permission = and_ [permission; (int_ 0) %<= q; q %<= (int_ (length - 1))];
        }
    in
    match o_values with 
    | None -> return None
    | Some oargs ->
       let oarg_bts = owned_oargs_list item_ct in
       let@ oargs = 
         ListM.map2M (fun (name, oa) (name', oa_bt) ->
             assert (Sym.equal name name');
             cases_to_map loc uiinfo Integer oa_bt oa
           ) oargs oarg_bts
       in
       let folded_value = List.hd oargs in
       let value_s, value = IT.fresh (IT.bt folded_value) in
       let@ () = add_ls [(value_s, IT.bt value)] in
       let@ () = add_c (t_ (def_ value_s folded_value)) in
       let@ provable = provable loc in
       let folded_oargs = 
         record_ [(Resources.value_sym, value)]
       in
       let folded_resource = ({
           name = Owned (Array (item_ct, Some length));
           pointer = base;
           iargs = [];
           permission = permission;
         }, 
         O folded_oargs)
       in
       return (Some folded_resource)


  and fold_struct ~recursive loc uiinfo tag pointer_t permission_t =
    debug 7 (lazy (item "fold struct" Pp.empty));
    debug 7 (lazy (item "tag" (Sym.pp tag)));
    debug 7 (lazy (item "pointer" (IT.pp pointer_t)));
    debug 7 (lazy (item "permission" (IT.pp permission_t)));
    let open Memory in
    let@ global = get_global () in
    let@ layout = get_struct_decl loc tag in
    let@ values_err =
      ListM.fold_leftM (fun o_values {offset; size; member_or_padding} ->
          match o_values with
          | Result.Error e -> return (Result.Error e)
          | Result.Ok values ->
             match member_or_padding with
             | Some (member, sct) ->
                let request : RET.predicate_type = {
                    name = Owned sct;
                    pointer = memberShift_ (pointer_t, tag, member);
                    iargs = [];
                    permission = permission_t;
                  }
                in
                let@ point = predicate_request ~recursive loc uiinfo request in
                begin match point with
                | None -> 
                   return (Result.Error (RET.P request))
                | Some (point, point_oargs) -> 
                   let value = snd (List.hd (oargs_list point_oargs)) in
                   return (Result.Ok (values @ [(member, value)]))
                end
             | None ->
                let request : RET.predicate_type = {
                    name = Block (Array (Integer Char, Some size));
                    pointer = integerToPointerCast_ (add_ (pointerToIntegerCast_ pointer_t, int_ offset));
                    permission = permission_t;
                    iargs = [];
                  } 
                in
                let@ result = predicate_request ~recursive loc uiinfo request in
                begin match result with
                | None -> return (Result.Error (RET.P request))
                | Some _ -> return (Result.Ok values)
                end
     ) (Result.Ok []) layout
    in
    match values_err with
    | Result.Error e -> return (Result.Error e)
    | Result.Ok values ->
       let value_s, value = IT.fresh (Struct tag) in
       let@ () = add_ls [(value_s, IT.bt value)] in
       let@ () = add_c (t_ (def_ value_s (IT.struct_ (tag, values)))) in
       let folded_oargs = record_ [(Resources.value_sym, value)] in
       let folded_resource = ({
           name = Owned (Struct tag);
           pointer = pointer_t;
           iargs = [];
           permission = permission_t;
         }, 
         O folded_oargs)
       in
       return (Result.Ok folded_resource)


  and unfolded_array item_ct base length permission value =
    (let q_s, q = IT.fresh_named Integer "i" in
     let unfolded_oargs = record_ [(Resources.value_sym, value)] in
     {
       name = Owned item_ct;
       pointer = base;
       step = Memory.size_of_ctype item_ct;
       q = q_s;
       iargs = [];
       permission = and_ [permission; (int_ 0) %<= q; q %<= (int_ (length - 1))]
    },
     O unfolded_oargs)

  and unfold_array ~recursive loc uiinfo item_ct length base permission =
    debug 7 (lazy (item "unfold array" Pp.empty));
    debug 7 (lazy (item "item_ct" (Sctypes.pp item_ct)));
    debug 7 (lazy (item "base" (IT.pp base)));
    debug 7 (lazy (item "permission" (IT.pp permission)));
    let@ result = 
      predicate_request ~recursive loc uiinfo ({
            name = Owned (Array (item_ct, Some length));
            pointer = base;
            iargs = [];
            permission = permission;
        }
      ) 
    in
    match result with
    | None -> return None
    | Some (point, point_oargs) ->
       let length = match point.name with
         | Owned (Array (_, Some length)) -> length
         | _ -> assert false
       in
       let qpoint =
         unfolded_array item_ct base length permission 
           (snd (List.hd (oargs_list point_oargs))) 
       in
       return (Some qpoint)


  and unfolded_struct layout tag pointer_t permission_t value =
    let open Memory in
    List.map (fun {offset; size; member_or_padding} ->
        match member_or_padding with
        | Some (member, sct) ->
           let oargs = 
             record_
               [(Resources.value_sym, member_ ~member_bt:(BT.of_sct sct) (tag, value, member))]
           in
           let resource = 
             (P {
                 name = Owned sct;
                 pointer = memberShift_ (pointer_t, tag, member);
                 permission = permission_t;
                 iargs = [];
                },
              O oargs)
           in
           resource
        | None ->
           (P {
               name = Block (Array (Integer Char, Some size));
               pointer = integerToPointerCast_ (add_ (pointerToIntegerCast_ pointer_t, int_ offset));
               permission = permission_t;
               iargs = [];
             },
           O (record_ []))
      ) layout


  and unfold_struct ~recursive loc uiinfo tag pointer_t permission_t =
    debug 7 (lazy (item "unfold struct" Pp.empty));
    debug 7 (lazy (item "tag" (Sym.pp tag)));
    debug 7 (lazy (item "pointer" (IT.pp pointer_t)));
    debug 7 (lazy (item "permission" (IT.pp permission_t)));
    let@ global = get_global () in
    let@ result = 
      predicate_request ~recursive loc uiinfo
        (unfold_struct_request tag pointer_t permission_t)
    in
    match result with
    | None -> return None
    | Some (point, point_oargs) -> 
       let layout = SymMap.find tag global.struct_decls in
       let resources = 
         unfolded_struct layout tag pointer_t permission_t
           (snd (List.hd (oargs_list point_oargs))) 
       in
       return (Some resources)


  and span_fold_unfolds loc uiinfo req is_tail_rec =
    if not (! span_actions)
    then return ()
    else
    let start_timing = if is_tail_rec then 0.0
        else time_log_start "span_check" "" in
    let@ ress = all_resources () in
    let@ global = get_global () in
    let@ provable = provable loc in
    let@ m = model_with loc (bool_ true) in
    let@ _ = match m with
      | None -> return ()
      | Some (model, _) ->
        let opts = Spans.guess_span_intersection_action ress req model global in
        let confirmed = List.find_opt (fun (act, confirm) ->
            match provable (t_ confirm) with
                | `False -> false
                | `True -> true
        ) opts in
        begin match confirmed with
        | None -> return ()
        | Some (Spans.Pack (pt, ct), _) ->
            let@ success = do_pack loc uiinfo pt ct in
            if success then span_fold_unfolds loc uiinfo req true else return ()
        | Some (Spans.Unpack (pt, ct), _) ->
            let@ success = do_unpack loc uiinfo pt ct in
            if success then span_fold_unfolds loc uiinfo req true else return ()
        end
    in
    if is_tail_rec then () else time_log_end start_timing;
    return ()

  and do_pack loc uiinfo pt ct =
    let@ opt = match ct with
      | Sctypes.Array (act, Some length) ->
        fold_array loc uiinfo act pt length (bool_ true)
      | Sctypes.Struct tag ->
        let@ result = fold_struct ~recursive:true loc uiinfo tag pt (bool_ true) in
        begin match result with
          | Result.Ok res -> return (Some res)
          | _ -> return None
        end
      | _ -> return None
    in
    match opt with
    | None -> return false
    | Some (resource, oargs) ->
       let@ _ = add_r None (P resource, oargs) in
       return true

  and do_unpack loc uiinfo pt ct =
    match ct with
      | Sctypes.Array (act, Some length) ->
        let@ oqp = unfold_array ~recursive:true loc uiinfo act
                     length pt (bool_ true) in
        begin match oqp with
          | None -> return false
          | Some (qp, oargs) ->
              let@ _ = add_r None (Q qp, oargs) in
              return true
        end
      | Sctypes.Struct tag ->
        let@ ors = unfold_struct ~recursive:true loc uiinfo tag pt (bool_ true) in
        begin match ors with
          | None -> return false
          | Some rs ->
             let@ _ = add_rs None rs in
             return true
        end
      | _ -> return false




  let resource_request ~recursive loc uiinfo (request : RET.t) : (RE.t option, type_error) m = 
    match request with
    | P request ->
       let@ result = predicate_request ~recursive loc uiinfo request in
       return (Option.map_fst (fun p -> P p) result)
    | Q request ->
       let@ result = qpredicate_request loc uiinfo request in
       return (Option.map_fst (fun q -> Q q) result)

end

module Special = struct

  let fail_missing_resource loc situation (orequest, oinfo) = 
    let@ model = model () in
    fail_with_trace (fun trace -> fun ctxt ->
        let msg = Missing_resource_request {orequest; situation; oinfo; model; trace; ctxt} in
        {loc; msg})


  let predicate_request ~recursive loc situation (request, oinfo) = 
    let uiinfo = (situation, (Some (P request), oinfo)) in
    let@ result = General.predicate_request ~recursive loc uiinfo request in
    match result with
    | Some r -> return r
    | None -> fail_missing_resource loc situation (Some (P request), oinfo)

  let qpredicate_request loc situation (request, oinfo) = 
    let uiinfo = (situation, (Some (Q request), oinfo)) in
    let@ result = General.qpredicate_request loc uiinfo request in
    match result with
    | Some r -> return r
    | None -> fail_missing_resource loc situation (Some (Q request), oinfo)

  let unfold_struct ~recursive loc situation tag pointer_t permission_t = 
    let request = General.unfold_struct_request tag pointer_t permission_t in
    let uiinfo = (situation, (Some (P request), None)) in
    let@ result = General.unfold_struct ~recursive loc uiinfo tag pointer_t permission_t in
    match result with
    | Some resources -> return resources
    | None -> 
       fail_missing_resource loc situation (Some (P request), None)


  let fold_struct ~recursive loc situation tag pointer_t permission_t = 
    let uiinfo = (situation, (None, None)) in
    let@ result = General.fold_struct ~recursive loc uiinfo tag pointer_t permission_t in
    match result with
    | Result.Ok r -> return r
    | Result.Error request -> fail_missing_resource loc situation (Some request, None)

end


