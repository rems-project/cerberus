module IT = IndexTerms
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes

module Function = struct
  type def_or_uninterp =
    | Def of IT.t
    | Rec_Def of IT.t
    | Uninterp

  let subst_def_or_uninterp subst = function
    | Def it -> Def (IT.subst subst it)
    | Rec_Def it -> Rec_Def (IT.subst subst it)
    | Uninterp -> Uninterp


  type definition =
    { loc : Locations.t;
      args : (Sym.t * BaseTypes.t) list;
      (* If the predicate is supposed to get used in a quantified form, one of the arguments
         has to be the index/quantified variable. For now at least. *)
      return_bt : BaseTypes.t;
      emit_coq : bool;
      definition : def_or_uninterp
    }

  let is_recursive def =
    match def.definition with Rec_Def _ -> true | Def _ -> false | Uninterp -> false


  let given_to_solver def =
    match def.definition with Rec_Def _ -> false | Def _ -> true | Uninterp -> false


  let pp_args xs =
    Pp.flow_map
      (Pp.break 1)
      (fun (sym, typ) -> Pp.parens (Pp.typ (Sym.pp sym) (BaseTypes.pp typ)))
      xs


  let pp_def nm def =
    let open Pp in
    nm
    ^^ colon
    ^^^ pp_args def.args
    ^^ colon
    ^/^
    match def.definition with
    | Uninterp -> !^"uninterpreted"
    | Def t -> IT.pp t
    | Rec_Def t -> !^"rec:" ^^^ IT.pp t


  let open_fun def_args def_body args =
    let su = IT.make_subst (List.map2 (fun (s, _) arg -> (s, arg)) def_args args) in
    IT.subst su def_body


  let unroll_once def args =
    match def.definition with
    | Def body | Rec_Def body -> Some (open_fun def.args body args)
    | Uninterp -> None


  let try_open_fun def args =
    match def.definition with
    | Def body -> Some (open_fun def.args body args)
    | Rec_Def _ -> None
    | Uninterp -> None


  (* let try_open_fun_to_term def name args = Option.map (fun body -> Body.to_term
     def.return_bt body ) (try_open_fun def name args) *)

  (* let add_unfolds_to_terms preds terms = let rec f acc t = match IT.term t with |
     IT.Apply (name, ts) -> let def = Sym.Map.find name preds in begin match
     try_open_fun_to_term def name ts with | None -> acc | Some t2 -> f (t2 :: acc) t2 end |
     _ -> acc in IT.fold_list (fun _ acc t -> f acc t) [] terms terms *)

  (* (\* Check for cycles in the logical predicate graph, which would cause *)
  (*    the system to loop trying to unfold them. Predicates whose definition *)
  (*    are marked with Rec_Def aren't checked, as cycles there are expected. *\) *)
  (* let cycle_check (defs : definition Sym.Map.t) = *)
  (*   let def_preds nm =  *)
  (*     let def =  Sym.Map.find nm defs in *)
  (*     begin match def.definition with *)
  (*     | Def t -> Sym.Set.elements (IT.preds_of (Body.to_term def.return_bt t)) *)
  (*     | _ -> [] *)
  (*     end *)
  (*   in *)
  (*   let rec search known_ok = function *)
  (*     | [] -> None *)
  (*     | (nm, Some path) :: q -> if Sym.Set.mem nm known_ok *)
  (*       then search known_ok q *)
  (*       else if List.exists (Sym.equal nm) path *)
  (*       then Some (List.rev path @ [nm]) *)
  (*       else *)
  (*         let deps = List.map (fun p -> (p, Some (nm :: path))) (def_preds nm) in *)
  (*         search known_ok (deps @ [(nm, None)] @ q) *)
  (*     | (nm, None) :: q -> search (Sym.Set.add nm known_ok) q *)
  (* in search Sym.Set.empty (List.map (fun (p, _) -> (p, Some [])) (Sym.Map.bindings
     defs)) *)

  (*Extensibility hook. For now, all functions are displayed as "interesting" in error reporting*)
  let is_interesting : definition -> bool = fun _ -> true
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
        let loc = Locations.other __FUNCTION__ in
        let lc = LogicalConstraints.T (IT.eq_ (pred_oarg, output) loc) in
        LRT.Constraint (lc, (loc, None), LRT.I)
    in
    aux clause_packing_ft
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
end

let alloc =
  Predicate.
    { loc = Locations.other (__FILE__ ^ ":" ^ string_of_int __LINE__);
      pointer = Sym.fresh_named "ptr";
      iargs = [];
      oarg_bt = Alloc.History.value_bt;
      clauses = None
    }


let instantiate_clauses (def : Predicate.t) ptr_arg iargs =
  match def.clauses with
  | Some clauses ->
    let subst =
      IT.make_subst
        ((def.pointer, ptr_arg)
         :: List.map2 (fun (def_ia, _) ia -> (def_ia, ia)) def.iargs iargs)
    in
    Some (List.map (Clause.subst subst) clauses)
  | None -> None


let identify_right_clause provable (def : Predicate.t) pointer iargs =
  match instantiate_clauses def pointer iargs with
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
           let loc = Locations.other __FUNCTION__ in
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
   TODO: right now this is an overapproximation *)
let given_to_solver (def : Predicate.t) =
  match def.clauses with
  | None -> false
  | Some [] -> true
  | Some [ _ ] -> true
  | _ -> false


(*Extensibility hook. For now, all predicates are displayed as "interesting" in error reporting*)
let is_interesting : Predicate.t -> bool = fun _ -> true
