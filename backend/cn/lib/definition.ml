module IT = IndexTerms
module LAT = LogicalArgumentTypes

module Function = struct
  type body =
    | Def of IT.t
    | Rec_Def of IT.t
    | Uninterp

  let subst_body subst = function
    | Def it -> Def (IT.subst subst it)
    | Rec_Def it -> Rec_Def (IT.subst subst it)
    | Uninterp -> Uninterp


  type t =
    { loc : Locations.t;
      args : (Sym.t * BaseTypes.t) list;
      (* If the predicate is supposed to get used in a quantified form, one of the arguments
         has to be the index/quantified variable. For now at least. *)
      return_bt : BaseTypes.t;
      emit_coq : bool;
      body : body
    }

  let is_recursive def =
    match def.body with Rec_Def _ -> true | Def _ -> false | Uninterp -> false


  let given_to_solver def =
    match def.body with Rec_Def _ -> false | Def _ -> true | Uninterp -> false


  let pp_args xs =
    let doc =
      Pp.flow_map
        (Pp.break 1)
        (fun (sym, typ) -> Pp.parens (Pp.typ (Sym.pp sym) (BaseTypes.pp typ)))
        xs
    in
    if PPrint.requirement doc = 0 then
      Pp.parens Pp.empty
    else
      doc


  let pp_sig nm def =
    let open Pp in
    nm ^^ pp_args def.args ^^^ colon ^^^ BaseTypes.pp def.return_bt


  let pp nm def =
    let open Pp in
    pp_sig nm def
    ^^^ equals
    ^/^
    match def.body with
    | Uninterp -> !^"uninterpreted"
    | Def t -> IT.pp t
    | Rec_Def t -> !^"rec:" ^^^ IT.pp t


  let open_ def_args def_body args =
    let su = IT.make_subst (List.map2 (fun (s, _) arg -> (s, arg)) def_args args) in
    IT.subst su def_body


  let unroll_once def args =
    match def.body with
    | Def body | Rec_Def body -> Some (open_ def.args body args)
    | Uninterp -> None


  let try_open def args =
    match def.body with
    | Def body -> Some (open_ def.args body args)
    | Rec_Def _ -> None
    | Uninterp -> None


  (*Extensibility hook. For now, all functions are displayed as "interesting" in error reporting*)
  let is_interesting : t -> bool = fun _ -> true
end

module Clause = struct
  type t =
    { loc : Locations.t;
      guard : IT.t;
      packing_ft : LAT.packing_ft
    }

  let pp { loc = _; guard; packing_ft } =
    let open Pp in
    item "condition" (IT.pp guard)
    ^^ comma
    ^^^ item "return type" (LAT.pp IT.pp packing_ft)


  let subst subst { loc; guard; packing_ft } =
    { loc;
      guard = IT.subst subst guard;
      packing_ft = LAT.subst IT.subst subst packing_ft
    }


  let lrt (pred_oarg : IT.t) clause_packing_ft =
    let module LRT = LogicalReturnTypes in
    let rec aux = function
      | LAT.Define (bound, info, lat) -> LRT.Define (bound, info, aux lat)
      | LAT.Resource (bound, info, lat) -> LRT.Resource (bound, info, aux lat)
      | LAT.Constraint (lc, info, lat) -> LRT.Constraint (lc, info, aux lat)
      | I output ->
        let loc = Locations.other __LOC__ in
        let lc = LogicalConstraints.T (IT.eq_ (pred_oarg, output) loc) in
        LRT.Constraint (lc, (loc, None), LRT.I)
    in
    aux clause_packing_ft


  let rec explicit_negative_guards_aux (cs : t list) (prev_negated : IT.t) : t list =
    let cerb_loc = Cerb_location.unknown in
    match cs with
    | [] -> []
    | { loc; guard = cur_guard; packing_ft } :: cs' ->
      let cur =
        { loc; guard = IT.and_ [ prev_negated; cur_guard ] cerb_loc; packing_ft }
      in
      let so_far_ng = IT.and_ [ IT.not_ cur_guard cerb_loc; prev_negated ] cerb_loc in
      cur :: explicit_negative_guards_aux cs' so_far_ng


  let explicit_negative_guards (cs : t list) : t list =
    let cerb_loc = Cerb_location.unknown in
    match cs with
    | [] -> []
    | h :: tl -> h :: explicit_negative_guards_aux tl (IT.not_ h.guard cerb_loc)
end

module Predicate = struct
  type t =
    { loc : Locations.t;
      pointer : Sym.t;
      iargs : (Sym.t * BaseTypes.t) list;
      oarg_bt : BaseTypes.t;
      clauses : Clause.t list option
    }

  let pp def =
    let open Pp in
    item "pointer" (Sym.pp def.pointer)
    ^/^ item "iargs" (Pp.list (fun (s, _) -> Sym.pp s) def.iargs)
    ^/^ item "oarg_bt" (BaseTypes.pp def.oarg_bt)
    ^/^ item
          "clauses"
          (match def.clauses with
           | Some clauses -> Pp.list Clause.pp clauses
           | None -> !^"(uninterpreted)")


  let instantiate (def : t) ptr_arg iargs =
    match def.clauses with
    | Some clauses ->
      let subst =
        IT.make_subst
          ((def.pointer, ptr_arg)
           :: List.map2 (fun (def_ia, _) ia -> (def_ia, ia)) def.iargs iargs)
      in
      Some (List.map (Clause.subst subst) clauses)
    | None -> None


  let identify_right_clause provable (def : t) pointer iargs =
    match instantiate def pointer iargs with
    | None ->
      (* "uninterpreted" predicates cannot be un/packed *)
      None
    | Some clauses ->
      let rec try_clauses : Clause.t list -> _ = function
        | [] -> None
        | clause :: clauses ->
          (match provable (LogicalConstraints.T clause.guard) with
           | `True -> Some clause
           | `False ->
             let loc = Locations.other __LOC__ in
             (match provable (LogicalConstraints.T (IT.not_ clause.guard loc)) with
              | `True -> try_clauses clauses
              | `False ->
                Pp.debug
                  5
                  (lazy
                    (Pp.item "cannot prove or disprove clause guard" (IT.pp clause.guard)));
                None))
      in
      try_clauses clauses


  (* determines if a resource predicate will be given to the solver
   *    TODO: right now this is an overapproximation *)
  let given_to_solver (def : t) =
    match def.clauses with
    | None -> false
    | Some [] -> true
    | Some [ _ ] -> true
    | _ -> false
end

let alloc =
  Predicate.
    { loc = Locations.other __LOC__;
      pointer = Sym.fresh_named "ptr";
      iargs = [];
      oarg_bt = Alloc.History.value_bt;
      clauses = None
    }


(*Extensibility hook. For now, all predicates are displayed as "interesting" in error reporting*)
let is_interesting : Predicate.t -> bool = fun _ -> true
