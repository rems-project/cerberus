(* This file implements an analysis to find 'promotable' variables,
   stack variables which can be promoted out of memory operations and
   into pure Core expressions. *)
open Core

module Event = struct
  type t = Neg_store of Cerb_location.t | Pos_store_or_load
  let is_neg_store = function Neg_store _ -> true | _ -> false
  let is_pos_store_or_load = function Pos_store_or_load -> true | _ -> false
  let compare (x : t) (y : t) = Stdlib.compare x y
end

module Event_set = Set.Make(Event)

let rm_neg = Event_set.map (fun _ -> Pos_store_or_load)

let neg_locs es = Event_set.fold (fun ev locs ->
    match ev with
    | Neg_store loc -> loc :: locs
    | Pos_store_or_load -> locs) es []

let wseq_static_check e =
  let may_race = ref [] in
  let rec approx_wseq_events (Expr (annots, e_)) =
    let module Es = Event_set in
    match e_ with
    | Eaction (Paction (polarity, Action (loc, _, act_))) ->
        begin match act_ with
        | Store0 _ ->
            begin match polarity with
              | Pos ->
                  Es.singleton Event.Pos_store_or_load
              | Neg ->
                  Es.singleton (Event.Neg_store loc)
            end
        | Load0 _ | SeqRMW _ ->
            Es.singleton Event.Pos_store_or_load
        | _ ->
            Es.empty
        end

    | Esseq (_, e1, e2) ->
        Es.union (approx_wseq_events e1) (approx_wseq_events e2)

    | Ewseq (_, e1, e2) ->
        let events1 = approx_wseq_events e1 in
        let events2 = approx_wseq_events e2 in
        let union = Es.union events1 events2 in
        if Es.exists Event.is_neg_store events1 && not (Es.is_empty events2) then
          (may_race := neg_locs events1 @ neg_locs events2 @ !may_race;
           rm_neg union)
        else
            union

    | Epure _ | Ememop _ | Eccall _ | Eproc _ | Ewait _ | Eexcluded _
    | End _ (* always true/false *) ->
        Es.empty

    | Elet (_, _, e) | Eannot (_, e) ->
        approx_wseq_events e

    | Ebound e ->
        let _ = approx_wseq_events e in
        Es.empty

    | Eif (_, e1, e2) ->
        Es.union (approx_wseq_events e1) (approx_wseq_events e2)

    | Ecase (_, arms) ->
        List.fold_left Es.union Es.empty @@ List.map (fun (_, e) -> approx_wseq_events e) arms

    | Epar arms | Eunseq arms ->
      let events = List.map approx_wseq_events arms in
      begin match List.filter (fun s -> not (Es.is_empty s)) events with
      | [] -> Es.empty
      | [x] -> x
      | _ :: _ :: _ as eventful ->
        let union = List.fold_left Es.union Es.empty eventful in
        if not (List.for_all (Es.for_all Event.is_pos_store_or_load) eventful) then
            (may_race := List.concat_map neg_locs eventful @ !may_race;
            rm_neg union)
        else
            union
      end

    | Esave (_, params, body) ->
        approx_wseq_events body

    | Erun (_, label_sym, args) ->
        Es.empty in

  ignore (approx_wseq_events e);
  !may_race

let analyse_file file =
  let locs = ref [] in
  Pmap.iter (fun f_sym decl ->
    match decl with
    | Proc (loc, env_marker, ret_bt, args, body) ->
        locs := wseq_static_check body @ !locs
    | Fun _ | ProcDecl _ | BuiltinDecl _ ->
        ()) file.funs;
  !locs
