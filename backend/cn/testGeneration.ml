module AT = ArgumentTypes
module BT = BaseTypes
module RP = ResourcePredicates
module IT = IndexTerms
module LS = LogicalSorts
module RET = ResourceTypes
module LC = LogicalConstraints
module LAT = LogicalArgumentTypes
module CF = Cerb_frontend
open CF

let weak_sym_equal s1 s2 =
  String.equal (Pp_symbol.to_string_pretty s1) (Pp_symbol.to_string_pretty s2)
;;

let string_of_ctype (ty : Ctype.ctype) : string =
  Cerb_colour.do_colour := false;
  let tmp = String_ail.string_of_ctype ~is_human:true Ctype.no_qualifiers ty ^ " " in
  Cerb_colour.do_colour := true;
  tmp
;;

type variables = (Symbol.sym * (Ctype.ctype * IT.t)) list

let string_of_variables (vars : variables) : string =
  "{ "
  ^ String.concat
      "; "
      (List.map
         (fun (x, (ty, e)) ->
           Pp_symbol.to_string_pretty x
           ^ " -> ("
           ^ string_of_ctype ty
           ^ ", "
           ^ Pp_utils.to_plain_pretty_string (IT.pp e)
           ^ ")")
         vars)
  ^ " }"
;;

type locations = (IT.t * Symbol.sym) list

let string_of_locations (locs : locations) : string =
  "{ "
  ^ String.concat
      "; "
      (List.map
         (fun (e, x) ->
           "(*"
           ^ Pp_utils.to_plain_pretty_string (IT.pp e)
           ^ ") -> "
           ^ Pp_symbol.to_string_pretty x)
         locs)
  ^ " }"
;;

type members = (Symbol.sym * (string * (Ctype.ctype * Symbol.sym)) list) list

let string_of_members (ms : members) : string =
  "{ "
  ^ String.concat
      "; "
      (List.map
         (fun (x, ms) ->
           Pp_symbol.to_string_pretty x
           ^ " -> {"
           ^ String.concat
               ", "
               (List.map
                  (fun (y, (ty, z)) ->
                    "."
                    ^ y
                    ^ ": "
                    ^ string_of_ctype ty
                    ^ " = "
                    ^ Pp_symbol.to_string_pretty z)
                  ms))
         ms)
  ^ " }"
;;

type constraints = IT.t list

let string_of_constraints (cs : constraints) : string =
  "{ "
  ^ String.concat "; " (List.map (fun e -> Pp_utils.to_plain_pretty_string (IT.pp e)) cs)
  ^ " }"
;;

type goal = variables * members * locations * constraints

let _string_of_goal ((vars, ms, locs, cs) : goal) : string =
  "Vars: "
  ^ string_of_variables vars
  ^ "\n"
  ^ "Ms: "
  ^ string_of_members ms
  ^ "\n"
  ^ "Locs: "
  ^ string_of_locations locs
  ^ "\n"
  ^ "Cs: "
  ^ string_of_constraints cs
  ^ "\n"
;;

let bt_of_ctype (loc : Cerb_location.t) (ty : Ctype.ctype) : BT.t =
  BT.of_sct
    AilTypesAux.is_signed_ity
    Memory.size_of_integer_type
    (Sctypes.of_ctype_unsafe loc ty)
;;

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
    (match List.assoc weak_sym_equal n sigma.tag_definitions with
     | _, _, StructDef (membs, _) ->
       let f (Symbol.Identifier (_, id), (_, _, _, ty)) =
         let sym' = Symbol.fresh () in
         ( ( sym'
           , ( ty
             , IT.IT
                 ( Sym sym'
                 , bt_of_ctype (Cerb_location.other __FUNCTION__) ty
                 , Cerb_location.other __FUNCTION__ ) ) )
         , (id, (ty, sym')) )
       in
       let vars', member_data = List.split (List.map f membs) in
       ( (( sym
          , ( ty
            , IT.IT
                ( Sym sym
                , bt_of_ctype (Cerb_location.other __FUNCTION__) ty
                , Cerb_location.other __FUNCTION__ ) ) )
          :: vars)
         @ vars'
       , (sym, member_data) :: ms )
     | _ -> failwith ("No struct '" ^ Pp_symbol.to_string_pretty n ^ "' defined"))
  | _ ->
    ( ( sym
      , ( ty
        , IT.fresh_named
            (bt_of_ctype (Cerb_location.other __FUNCTION__) ty)
            (Pp_symbol.to_string_pretty sym)
            (Cerb_location.other __FUNCTION__)
          |> snd ) )
      :: vars
    , ms )
;;

let ( >>= ) (x : 'a list) (f : 'a -> 'b list) : 'b list = List.flatten (List.map f x)
let return (x : 'a) : 'a list = [ x ]

let collect_lc (vars : variables) (ms : members) (lc : LC.t)
  : (variables * members * locations * constraints) list
  =
  match lc with
  | T it -> return (vars, ms, [], [ it ])
  | Forall _ -> failwith "`each` not supported"
;;

let rec collect_clauses
  (max_depth : int)
  (sigma : _ AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  (vars : variables)
  (ms : members)
  (cs : RP.clause list)
  : (IT.t * variables * members * locations * constraints) list
  =
  match cs with
  | c :: cs' ->
    let rest =
      List.map
        (fun (v, vars, ms, locs, cs) ->
          ( v
          , vars
          , ms
          , locs
          , IT.IT (Unop (Not, c.guard), BT.Bool, Cerb_location.other __FUNCTION__) :: cs ))
        (collect_clauses max_depth sigma prog5 vars ms cs')
    in
    collect_lat_it max_depth sigma prog5 vars ms c.packing_ft
    >>= fun (v, vars, ms, locs, cs) -> (v, vars, ms, locs, c.guard :: cs) :: rest
  | [] -> []

and collect_ret
  (max_depth : int)
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
    return (IT.IT (Sym sym, bt_of_ctype l ty, l), vars, ms, [ pointer, sym ], [])
  | P { name = Owned (_, _); _ } -> failwith "Incorrect number of arguments for `Owned`"
  | P { name = PName psym; pointer; iargs } ->
    if max_depth <= 0
    then []
    else (
      let pred = List.assoc weak_sym_equal psym prog5.mu_resource_predicates in
      let args = List.combine (List.map fst pred.iargs) iargs in
      let clauses =
        Option.get pred.clauses
        |> List.map (RP.subst_clause (IT.make_subst [ pred.pointer, pointer ]))
        |> List.map
             (List.fold_right
                (fun (x, v) acc -> RP.subst_clause (IT.make_subst [ x, v ]) acc)
                args)
      in
      collect_clauses (max_depth - 1) sigma prog5 vars ms clauses)
  | Q _ -> failwith "`each` not supported"

and collect_lat_it
  (max_depth : int)
  (sigma : _ AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  (vars : variables)
  (ms : members)
  (lat : IT.t LAT.t)
  : (IT.t * variables * members * locations * constraints) list
  =
  let lat_subst x v e = LAT.subst IT.subst (IT.make_subst [ x, v ]) e in
  match lat with
  | Define ((x, tm), _, lat') ->
    collect_lat_it max_depth sigma prog5 vars ms (lat_subst x tm lat')
  | Resource ((x, (ret, _)), _, lat') ->
    collect_ret max_depth sigma prog5 vars ms ret
    >>= fun (v, vars, ms, locs, cs) ->
    collect_lat_it max_depth sigma prog5 vars ms (lat_subst x v lat')
    >>= fun (v', vars, ms, locs', cs') -> return (v', vars, ms, locs @ locs', cs @ cs')
  | Constraint (lc, _, lat') ->
    collect_lc vars ms lc
    >>= fun (vars, ms, locs, cs) ->
    collect_lat_it max_depth sigma prog5 vars ms lat'
    >>= fun (v, vars, ms, locs', cs') -> return (v, vars, ms, locs @ locs', cs @ cs')
  | I it -> return (it, vars, ms, [], [])
;;

let rec _collect_lat
  (max_depth : int)
  (sigma : _ AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  (vars : variables)
  (ms : members)
  (lat : unit LAT.t)
  : (variables * members * locations * constraints) list
  =
  let lat_subst x v e = LAT.subst (fun _ x -> x) (IT.make_subst [ x, v ]) e in
  match lat with
  | Define ((x, tm), _, lat') ->
    _collect_lat max_depth sigma prog5 vars ms (lat_subst x tm lat')
  | Resource ((x, (ret, _)), _, lat') ->
    collect_ret max_depth sigma prog5 vars ms ret
    >>= fun (v, vars, ms, locs, cs) ->
    _collect_lat max_depth sigma prog5 vars ms (lat_subst x v lat')
    >>= fun (vars, ms, locs', cs') -> return (vars, ms, locs @ locs', cs @ cs')
  | Constraint (lc, _, lat') ->
    collect_lc vars ms lc
    >>= fun (vars, ms, locs, cs) ->
    _collect_lat max_depth sigma prog5 vars ms lat'
    >>= fun (vars, ms, locs', cs') -> return (vars, ms, locs @ locs', cs @ cs')
  | I _ -> return (vars, ms, [], [])
;;

type test_framework = GTest

let main
  (_output_dir : string)
  (_filename : string)
  (_max_depth : int)
  (_sigma : _ AilSyntax.sigma)
  (_prog5 : unit Mucore.mu_file)
  (_tf : test_framework)
  : unit
  =
  ()
;;
