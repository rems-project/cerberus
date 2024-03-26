open IndexTerms
open ResourceTypes
open Resources
open ResourcePredicates
open Memory
module IT = IndexTerms
module LAT = LogicalArgumentTypes

open Cerb_pp_prelude

let resource_empty provable resource =
  let constr = match resource with
    | (P p, _) -> LC.t_ (bool_ false)
    | (Q p, _) -> LC.forall_ p.q (not_ p.permission)
  in
  match provable constr with
  | `True -> `Empty
  | `False -> `NonEmpty (constr, Solver.model ())


let unfolded_array init (ict, olength) pointer =
  let length = Option.get olength in
  let q_s, q = IT.fresh_named Memory.intptr_bt "i" in
  Q {
    name = Owned (ict, init);
    pointer = pointer;
    q = (q_s, Memory.intptr_bt);
    step = intptr_int_ (Memory.size_of_ctype ict);
    iargs = [];
    permission = and_ [((intptr_int_ 0) %<= q); (q %< (intptr_int_ length))]
  }


let packing_ft global provable ret =
  let loc = Locations.unknown in
  match ret with
  | P ret ->
     begin match ret.name with
      | Owned ((Void | Integer _ | Pointer _ | Function _), _init) ->
         None
      | Owned ((Array (ict, olength)) as ct, init) ->
         let qpred = unfolded_array init (ict, olength) ret.pointer in
         let o_s, o = IT.fresh_named (Memory.bt_of_sct ct) "value" in
         let at =
           LAT.Resource ((o_s, (qpred, IT.bt o)), (loc, None),
           LAT.I o)
         in
         Some at
      | Owned (Struct tag, init) ->
          let layout = SymMap.find tag global.Global.struct_decls in
          let lrt, value =
            List.fold_right (fun {offset; size; member_or_padding} (lrt, value) ->
              match member_or_padding with
              | Some (member, mct) ->
                let request =
                  P {
                    name = Owned (mct, init);
                    pointer = memberShift_ (ret.pointer, tag, member);
                    iargs = [];
                  }
                in
                let m_value_s, m_value = IT.fresh_named (Memory.bt_of_sct mct) (Id.s member) in
                (LRT.Resource ((m_value_s, (request, IT.bt m_value)), (loc, None), lrt),
                (member, m_value) :: value)
              | None ->
                let padding_ct = Sctypes.Array (Sctypes.char_ct, Some size) in
                let request =
                  P {
                    name = Owned (padding_ct, Uninit);
                    pointer = pointer_offset_ (ret.pointer, intptr_int_ offset);
                    iargs = [];
                  }
                in
                let padding_s, padding = IT.fresh_named (Memory.bt_of_sct padding_ct) "padding" in
                (LRT.Resource ((padding_s, (request, IT.bt padding)), (loc, None), lrt),
                value)
              ) layout (LRT.I, [])
          in
          let at = LAT.of_lrt lrt (LAT.I (struct_ (tag, value))) in
          Some at
      | PName pn ->
          let def = SymMap.find pn global.resource_predicates in
          begin match identify_right_clause provable def ret.pointer ret.iargs with
          | None -> None
          | Some right_clause -> Some right_clause.packing_ft
          end
      end
  | Q _ ->
     None

let unpack_owned global (ct, init) pointer (O o) =
  let open Sctypes in
  match ct with
  | (Void | Integer _ | Pointer _ | Function _) ->
     None
  | Array (ict, olength) ->
    Some [(unfolded_array init (ict, olength) pointer, O o)]
  | Struct tag ->
    let layout = SymMap.find tag global.Global.struct_decls in
    let res =
      List.fold_right (fun {offset; size; member_or_padding} res ->
        match member_or_padding with
        | Some (member, mct) ->
          let mresource =
            (P {
              name = Owned (mct, init);
              pointer = memberShift_ (pointer, tag, member);
              iargs = [];
            },
            O (member_ ~member_bt:(Memory.bt_of_sct mct) (tag, o, member)))
          in
          (mresource :: res)
        | None ->
          let padding_ct = Sctypes.Array (Sctypes.char_ct, Some size) in
          let mresource =
            (P {
              name = Owned (padding_ct, Uninit);
              pointer = pointer_offset_ (pointer, intptr_int_ offset);
              iargs = [];
            }, O (default_ (Memory.bt_of_sct padding_ct)))
          in
          (mresource :: res)
        ) layout []
    in
    Some res



let unpack loc global provable (ret, O o) =
  match ret with
  | P {name = Owned (ct, init); pointer; iargs = []} ->
    begin match unpack_owned global (ct, init) pointer (O o) with
    | None -> None
    | Some re -> Some (`RES re)
    end
  | _ ->
    begin match packing_ft global provable ret with
    | None -> None
    | Some packing_ft -> Some (`LRT (ResourcePredicates.clause_lrt o packing_ft))
    end





let extractable_one global prove_or_model (predicate_name, index, verb) (ret, O o) =
    let tmsg hd tail = if verb
      then Pp.print stdout (Pp.item hd (ResourceTypes.pp ret ^^ Pp.hardline ^^
            Pp.string "--" ^^ Pp.hardline ^^ Lazy.force tail))
      else ()
    in
    match ret with
    | Q ret when equal_predicate_name predicate_name ret.name &&
             BT.equal (IT.bt index) (snd ret.q) ->
       let su = IT.make_subst [(fst ret.q, index)] in
       let index_permission = IT.subst su ret.permission in
       begin match prove_or_model (LC.t_ index_permission) with
        | `True ->
          let at_index =
            (P { name = ret.name;
                pointer = pointer_offset_ (ret.pointer,
                    mul_ (cast_ Memory.intptr_bt ret.step, cast_ Memory.intptr_bt index));
                iargs = List.map (IT.subst su) ret.iargs; },
            O (map_get_ o index))
          in
          let ret_reduced =
            { ret with permission = and_ [ret.permission; ne__ (sym_ ret.q) index ] }
          in
          tmsg "successfully extracted" (lazy (IT.pp index));
          Some ((Q ret_reduced, O o), at_index)
       | `Counterex m ->
          let eval_f = Solver.eval global (fst m) in
          tmsg "could not extract, counterexample"
            (lazy (IndexTerms.pp_with_eval eval_f index_permission));
          None
       end
    | Q qret ->
      if not (equal_predicate_name predicate_name qret.name)
      then tmsg "not extracting, predicate name differs"
          (lazy (ResourceTypes.pp_predicate_name predicate_name))
      else if not (BT.equal (IT.bt index) (snd qret.q))
      then tmsg "not extracting, index type differs"
          (lazy (Pp.typ (BT.pp (IT.bt index)) (BT.pp (snd qret.q))))
      else assert false;
      None
    | _ ->
      None


let extractable_multiple global prove_or_model =
  let rec aux is (re, extracted) =
    match is with
    | [] ->
        (re, extracted)
    | i::is ->
        match extractable_one global prove_or_model i re with
        | Some (re_reduced, extracted') ->
            aux is (re_reduced, extracted' :: extracted)
        | None ->
            aux is (re, extracted)
  in
  fun movable_indices re -> aux movable_indices (re, [])



