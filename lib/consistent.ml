module LC = LogicalConstraints
module IT = IndexTerms
module Loc = Locations

let debug, item = Pp.(debug, item)

open Pp.Infix

let pure, add_l, add_r, add_c, fail, provable, add_a, map_and_fold_resources =
  Typing.(pure, add_l, add_r, add_c, fail, provable, add_a, map_and_fold_resources)


open Effectful.Make (Typing)

let logicalReturnTypes loc lrt =
  let rec aux =
    let here = Locations.other __LOC__ in
    function
    | LogicalReturnTypes.Define ((s, it), ((loc, _) as info), lrt) ->
      (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
      let@ () = add_l s (IT.get_bt it) (loc, lazy (Pp.string "let-var")) in
      let@ () = add_c (fst info) (LC.T (IT.def_ s it here)) in
      aux lrt
    | Resource ((s, (re, re_oa_spec)), (loc, _), lrt) ->
      (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
      let@ () = add_l s re_oa_spec (loc, lazy (Pp.string "let-var")) in
      let@ () = add_r loc (re, O (IT.sym_ (s, re_oa_spec, here))) in
      aux lrt
    | Constraint (lc, info, lrt) ->
      (* TODO abort early if one of the constraints is the literal fase,
         so that users are allowed to write such specs *)
      let@ () = add_c (fst info) lc in
      aux lrt
    | I ->
      let@ provable = provable loc in
      let here = Locations.other __LOC__ in
      (match provable (LC.T (IT.bool_ false here)) with
       | `True ->
         fail (fun ctxt_log ->
           { loc; msg = Inconsistent_assumptions ("return type", ctxt_log) })
       | `False -> return ())
  in
  pure (aux lrt)


let returnTypes loc rt =
  pure
    (match rt with
     | ReturnTypes.Computational ((name, bt), info, lrt) ->
       (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
       let@ () = add_a name bt (fst info, lazy (Sym.pp name)) in
       logicalReturnTypes loc lrt)


let logicalArgumentTypes i_welltyped i_pp kind loc at : unit Typing.t =
  let module LAT = LogicalArgumentTypes in
  let _ = (at : _ LAT.t) in
  debug
    12
    (lazy (item ("checking wf of " ^ kind ^ " at " ^ Loc.to_string loc) (LAT.pp i_pp at)));
  let rec aux =
    let here = Locations.other __LOC__ in
    function
    | LAT.Define ((s, it), info, at) ->
      (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
      let@ () = add_l s (IT.get_bt it) (loc, lazy (Pp.string "let-var")) in
      let@ () = add_c (fst info) (LC.T (IT.def_ s it here)) in
      aux at
    | Resource ((s, (re, re_oa_spec)), (loc, _), at) ->
      (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
      let@ () = add_l s re_oa_spec (loc, lazy (Pp.string "let-var")) in
      let@ () = add_r loc (re, O (IT.sym_ (s, re_oa_spec, here))) in
      aux at
    | Constraint (lc, info, at) ->
      let@ () = add_c (fst info) lc in
      aux at
    | I i ->
      let@ provable = provable loc in
      let here = Locations.other __LOC__ in
      let@ () =
        match provable (LC.T (IT.bool_ false here)) with
        | `True ->
          fail (fun ctxt_log -> { loc; msg = Inconsistent_assumptions (kind, ctxt_log) })
        | `False -> return ()
      in
      i_welltyped loc i
  in
  pure (aux at)


let argumentTypes i_welltyped i_pp kind loc at : unit Typing.t =
  let module AT = ArgumentTypes in
  let _ = (at : _ AT.t) in
  debug
    12
    (lazy (item ("checking wf of " ^ kind ^ " at " ^ Loc.to_string loc) (AT.pp i_pp at)));
  let rec aux = function
    | AT.Computational ((name, bt), info, at) ->
      (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
      let@ () = add_a name bt (fst info, lazy (Sym.pp name)) in
      aux at
    | L at -> logicalArgumentTypes i_welltyped i_pp kind loc at
  in
  pure (aux at)


let pure_and_no_initial_resources loc m =
  pure
    (let@ (), _ = map_and_fold_resources loc (fun _re () -> (Deleted, ())) () in
     m)


let function_type =
  argumentTypes
    (fun loc rt -> pure_and_no_initial_resources loc (returnTypes loc rt))
    ReturnTypes.pp


let logicalArguments
  (i_welltyped : Loc.t -> 'i -> 'j Typing.t)
  kind
  loc
  (at : 'i Mucore.arguments_l)
  : unit Typing.t
  =
  let rec aux =
    let here = Locations.other __LOC__ in
    function
    | Mucore.Define ((s, it), ((loc, _) as info), at) ->
      (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
      let@ () = add_l s (IT.get_bt it) (loc, lazy (Pp.string "let-var")) in
      let@ () = add_c (fst info) (LC.T (IT.def_ s it here)) in
      aux at
    | Resource ((s, (re, re_oa_spec)), (loc, _), at) ->
      (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
      let@ () = add_l s re_oa_spec (loc, lazy (Pp.string "let-var")) in
      let@ () = add_r loc (re, O (IT.sym_ (s, re_oa_spec, here))) in
      aux at
    | Constraint (lc, info, at) ->
      let@ () = add_c (fst info) lc in
      aux at
    | I i ->
      let@ provable = provable loc in
      let here = Locations.other __LOC__ in
      let@ () =
        match provable (LC.T (IT.bool_ false here)) with
        | `True ->
          fail (fun ctxt_log -> { loc; msg = Inconsistent_assumptions (kind, ctxt_log) })
        | `False -> return ()
      in
      i_welltyped loc i
  in
  pure (aux at)


let arguments
  :  (Loc.t -> 'i -> 'j Typing.t) -> string -> Loc.t -> 'i Mucore.arguments ->
  unit Typing.t
  =
  fun (i_welltyped : Loc.t -> 'i -> 'j Typing.t) kind loc (at : 'i Mucore.arguments) ->
  debug 6 (lazy !^__LOC__);
  debug
    12
    (lazy
      (item
         ("checking consistency of " ^ kind ^ " at " ^ Loc.to_string loc)
         (Cerb_frontend.Pp_ast.pp_doc_tree
            (Mucore.dtree_of_arguments (fun _i -> Dleaf !^"...") at))));
  let rec aux = function
    | Mucore.Computational ((name, bt), info, at) ->
      (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
      let@ () = add_a name bt (fst info, lazy (Sym.pp name)) in
      aux at
    | L at -> logicalArguments i_welltyped kind loc at
  in
  pure (aux at)


let procedure : Loc.t -> _ Mucore.args_and_body -> unit Typing.t =
  fun (loc : Loc.t) (at : 'TY1 Mucore.args_and_body) ->
  arguments
    (fun loc (_body, labels, rt) ->
      let@ () = pure_and_no_initial_resources loc (returnTypes loc rt) in
      PmapM.iterM
        (fun _sym def ->
          match def with
          | Mucore.Return _ -> return ()
          | Label (loc, label_args_and_body, _annots, _parsed_spec, _loop_info) ->
            pure_and_no_initial_resources
              loc
              (arguments
                 (fun _loc _label_body -> return ())
                 "label"
                 loc
                 label_args_and_body))
        labels)
    "function"
    loc
    at


let predicate pred =
  let module Def = Definition in
  let Def.Predicate.{ loc; pointer; iargs; oarg_bt = _; clauses } = pred in
  (* no need to alpha-rename, because context.ml ensures there's no name clashes *)
  pure
    (let@ () = add_l pointer BaseTypes.(Loc ()) (loc, lazy (Pp.string "ptr-var")) in
     let@ () =
       ListM.iterM (fun (s, bt) -> add_l s bt (loc, lazy (Pp.string "input-var"))) iargs
     in
     match clauses with
     | None -> return ()
     | Some clauses ->
       let@ _ =
         ListM.fold_leftM
           (fun acc Def.Clause.{ loc; guard; packing_ft } ->
             let here = Locations.other __LOC__ in
             let negated_guards =
               List.map (fun clause -> IT.not_ clause.Def.Clause.guard here) acc
             in
             pure
               (let@ () = add_c loc (LC.T guard) in
                let@ () = add_c loc (LC.T (IT.and_ negated_guards here)) in
                let@ () =
                  logicalArgumentTypes
                    (fun _loc _it -> return ())
                    IT.pp
                    "clause"
                    loc
                    packing_ft
                in
                return (acc @ [ Def.Clause.{ loc; guard; packing_ft } ])))
           []
           clauses
       in
       return ())


let lemma loc _lemma_s lemma_typ =
  argumentTypes
    (fun loc lrt -> pure_and_no_initial_resources loc (logicalReturnTypes loc lrt))
    LogicalReturnTypes.pp
    "lemma"
    loc
    lemma_typ
