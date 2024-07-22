module AT = ArgumentTypes
module BT = BaseTypes
module RP = ResourcePredicates
module IT = IndexTerms
module LS = LogicalSorts
module RET = ResourceTypes
module LC = LogicalConstraints
module LAT = LogicalArgumentTypes
open Constraints
open Utils
module CF = Cerb_frontend
open CF

let bt_of_ctype (loc : Cerb_location.t) (ty : Ctype.ctype) : BT.t =
  BT.of_sct
    AilTypesAux.is_signed_ity
    Memory.size_of_integer_type
    (Sctypes.of_ctype_unsafe loc ty)


let add_to_vars_ms
  (sigma : GenTypes.genTypeCategory AilSyntax.sigma)
  (sym : Symbol.sym)
  (ty : Ctype.ctype)
  (vars : variables)
  (ms : members)
  : variables * members
  =
  match ty with
  | Ctype (_, Struct n) ->
    (match List.assoc sym_codified_equal n sigma.tag_definitions with
     | _, _, StructDef (membs, _) ->
       let f (Symbol.Identifier (_, id), (_, _, _, cty)) =
         let sym' = Symbol.fresh () in
         ( ( sym',
             ( cty,
               IT.sym_
                 ( sym',
                   bt_of_ctype (Cerb_location.other __FUNCTION__) cty,
                   Cerb_location.other __FUNCTION__ ) ) ),
           { name = id; carrier = sym'; cty } )
       in
       let vars', member_data = List.split (List.map f membs) in
       ( (( sym,
            ( ty,
              IT.sym_
                ( sym,
                  bt_of_ctype (Cerb_location.other __FUNCTION__) ty,
                  Cerb_location.other __FUNCTION__ ) ) )
          :: vars)
         @ vars',
         (sym, member_data) :: ms )
     | _ ->
       failwith ("No struct '" ^ codify_sym n ^ "' defined"))
  | _ ->
    ( ( sym,
        ( ty,
          IT.fresh_named
            (bt_of_ctype (Cerb_location.other __FUNCTION__) ty)
            (codify_sym sym)
            (Cerb_location.other __FUNCTION__)
          |> snd ) )
      :: vars,
      ms )


let ( let@ ) (x : 'a list) (f : 'a -> 'b list) : 'b list = List.flatten (List.map f x)

let return (x : 'a) : 'a list = [ x ]

let collect_lc (vars : variables) (ms : members) (lc : LC.t)
  : (variables * members * locations * constraints) list
  =
  match lc with
  | T it ->
    return (vars, ms, [], [ it ])
  | Forall _ ->
    failwith "`each` not supported"


let rec collect_clauses
  (max_unfolds : int)
  (sigma : _ AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  (vars : variables)
  (ms : members)
  (cs : RP.clause list)
  : (IT.t * variables * members * locations * constraints) list
  =
  match cs with
  | cl :: cls' ->
    let rest =
      List.map
        (fun (v, vars, ms, locs, cs) ->
          (v, vars, ms, locs, IT.not_ cl.guard (Cerb_location.other __FUNCTION__) :: cs))
        (collect_clauses max_unfolds sigma prog5 vars ms cls')
    in
    let@ v, vars, ms, locs, cs =
      collect_lat_it max_unfolds sigma prog5 vars ms cl.packing_ft
    in
    (v, vars, ms, locs, cl.guard :: cs) :: rest
  | [] ->
    []


and collect_ret
  (max_unfolds : int)
  (sigma : _ AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  (vars : variables)
  (ms : members)
  (ret : RET.t)
  : (IT.t * variables * members * locations * constraints) list
  =
  match ret with
  | P { name = Owned (ty, _); pointer; iargs = [] } ->
    let sym = Symbol.fresh () in
    let ty = Sctypes.to_ctype ty in
    let vars, ms = add_to_vars_ms sigma sym ty vars ms in
    let l = Cerb_location.other __FUNCTION__ in
    return (IT.sym_ (sym, bt_of_ctype l ty, l), vars, ms, [ (pointer, sym) ], [])
  | P { name = Owned (_, _); _ } ->
    failwith "Incorrect number of arguments for `Owned`"
  | P { name = PName psym; pointer; iargs } ->
    if max_unfolds <= 0 then
      []
    else (
      let pred = List.assoc sym_codified_equal psym prog5.mu_resource_predicates in
      let args = List.combine (List.map fst pred.iargs) iargs in
      let clauses =
        Option.get pred.clauses
        |> List.map (RP.subst_clause (IT.make_subst [ (pred.pointer, pointer) ]))
        |> List.map
             (List.fold_right
                (fun (x, v) acc -> RP.subst_clause (IT.make_subst [ (x, v) ]) acc)
                args)
      in
      collect_clauses (max_unfolds - 1) sigma prog5 vars ms clauses)
  | Q _ ->
    failwith "`each` not supported"


and collect_lat_it
  (max_unfolds : int)
  (sigma : _ AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  (vars : variables)
  (ms : members)
  (lat : IT.t LAT.t)
  : (IT.t * variables * members * locations * constraints) list
  =
  let lat_subst x v e = LAT.subst IT.subst (IT.make_subst [ (x, v) ]) e in
  match lat with
  | Define ((x, tm), _, lat') ->
    collect_lat_it max_unfolds sigma prog5 vars ms (lat_subst x tm lat')
  | Resource ((x, (ret, _)), _, lat') ->
    let@ v, vars, ms, locs, cs = collect_ret max_unfolds sigma prog5 vars ms ret in
    let@ v', vars, ms, locs', cs' =
      collect_lat_it max_unfolds sigma prog5 vars ms (lat_subst x v lat')
    in
    return (v', vars, ms, locs @ locs', cs @ cs')
  | Constraint (lc, _, lat') ->
    let@ vars, ms, locs, cs = collect_lc vars ms lc in
    let@ v, vars, ms, locs', cs' = collect_lat_it max_unfolds sigma prog5 vars ms lat' in
    return (v, vars, ms, locs @ locs', cs @ cs')
  | I it ->
    return (it, vars, ms, [], [])


let rec collect_lat
  (max_unfolds : int)
  (sigma : _ AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  (vars : variables)
  (ms : members)
  (lat : unit LAT.t)
  : (variables * members * locations * constraints) list
  =
  let lat_subst x v e = LAT.subst (fun _ x -> x) (IT.make_subst [ (x, v) ]) e in
  match lat with
  | Define ((x, tm), _, lat') ->
    collect_lat max_unfolds sigma prog5 vars ms (lat_subst x tm lat')
  | Resource ((x, (ret, _)), _, lat') ->
    let@ v, vars, ms, locs, cs = collect_ret max_unfolds sigma prog5 vars ms ret in
    let@ vars, ms, locs', cs' =
      collect_lat max_unfolds sigma prog5 vars ms (lat_subst x v lat')
    in
    return (vars, ms, locs @ locs', cs @ cs')
  | Constraint (lc, _, lat') ->
    let@ vars, ms, locs, cs = collect_lc vars ms lc in
    let@ vars, ms, locs', cs' = collect_lat max_unfolds sigma prog5 vars ms lat' in
    return (vars, ms, locs @ locs', cs @ cs')
  | I _ ->
    return (vars, ms, [], [])
