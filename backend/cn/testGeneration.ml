(** Test Generation
    Handles all parts of test generation from
    gathering constraints to building
    generators and finally exporting C++ code.
**)

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

let codify_sym (s : Sym.sym) : string =
  let (Symbol (_, n, sd)) = s in
  match sd with
  | SD_Id x | SD_CN_Id x | SD_ObjectAddress x | SD_FunArgValue x -> x
  | SD_None -> "fresh_" ^ string_of_int n
  | _ -> failwith ("Symbol `" ^ Sym.show_raw s ^ "` cannot be codified")
;;

(** Only cares what their names in generated code will be *)
let sym_codified_equal (s1 : Sym.sym) (s2 : Sym.sym) =
  String.equal (codify_sym s1) (codify_sym s2)
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
           codify_sym x
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
           "(*" ^ Pp_utils.to_plain_pretty_string (IT.pp e) ^ ") -> " ^ codify_sym x)
         locs)
  ^ " }"
;;

(** Tracks indirection for a struct's member [name],
    where [car] carries its value of type [cty].
    **)
type member =
  { name : string (** The name of the member *)
  ; car : Sym.sym (** The name of the carrier*)
  ; cty : Ctype.ctype (** The type of the member *)
  }

let string_of_member (m : member) : string =
  "." ^ m.name ^ ": " ^ string_of_ctype m.cty ^ " = " ^ codify_sym m.car
;;

type members = (Symbol.sym * member list) list

let string_of_members (ms : members) : string =
  "{ "
  ^ String.concat
      "; "
      (List.map
         (fun (x, ms) ->
           codify_sym x ^ " -> {" ^ String.concat ", " (List.map string_of_member ms))
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

let string_of_goal ((vars, ms, locs, cs) : goal) : string =
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
    (match List.assoc sym_codified_equal n sigma.tag_definitions with
     | _, _, StructDef (membs, _) ->
       let f (Symbol.Identifier (_, id), (_, _, _, cty)) =
         let sym' = Symbol.fresh () in
         ( ( sym'
           , ( cty
             , IT.sym_
                 ( sym'
                 , bt_of_ctype (Cerb_location.other __FUNCTION__) cty
                 , Cerb_location.other __FUNCTION__ ) ) )
         , { name = id; car = sym'; cty } )
       in
       let vars', member_data = List.split (List.map f membs) in
       ( (( sym
          , ( ty
            , IT.sym_
                ( sym
                , bt_of_ctype (Cerb_location.other __FUNCTION__) ty
                , Cerb_location.other __FUNCTION__ ) ) )
          :: vars)
         @ vars'
       , (sym, member_data) :: ms )
     | _ -> failwith ("No struct '" ^ codify_sym n ^ "' defined"))
  | _ ->
    ( ( sym
      , ( ty
        , IT.fresh_named
            (bt_of_ctype (Cerb_location.other __FUNCTION__) ty)
            (codify_sym sym)
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
          v, vars, ms, locs, IT.not_ cl.guard (Cerb_location.other __FUNCTION__) :: cs)
        (collect_clauses max_unfolds sigma prog5 vars ms cls')
    in
    collect_lat_it max_unfolds sigma prog5 vars ms cl.packing_ft
    >>= fun (v, vars, ms, locs, cs) -> (v, vars, ms, locs, cl.guard :: cs) :: rest
  | [] -> []

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
    return (IT.sym_ (sym, bt_of_ctype l ty, l), vars, ms, [ pointer, sym ], [])
  | P { name = Owned (_, _); _ } -> failwith "Incorrect number of arguments for `Owned`"
  | P { name = PName psym; pointer; iargs } ->
    if max_unfolds <= 0
    then []
    else (
      let pred = List.assoc sym_codified_equal psym prog5.mu_resource_predicates in
      let args = List.combine (List.map fst pred.iargs) iargs in
      let clauses =
        Option.get pred.clauses
        |> List.map (RP.subst_clause (IT.make_subst [ pred.pointer, pointer ]))
        |> List.map
             (List.fold_right
                (fun (x, v) acc -> RP.subst_clause (IT.make_subst [ x, v ]) acc)
                args)
      in
      collect_clauses (max_unfolds - 1) sigma prog5 vars ms clauses)
  | Q _ -> failwith "`each` not supported"

and collect_lat_it
  (max_unfolds : int)
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
    collect_lat_it max_unfolds sigma prog5 vars ms (lat_subst x tm lat')
  | Resource ((x, (ret, _)), _, lat') ->
    collect_ret max_unfolds sigma prog5 vars ms ret
    >>= fun (v, vars, ms, locs, cs) ->
    collect_lat_it max_unfolds sigma prog5 vars ms (lat_subst x v lat')
    >>= fun (v', vars, ms, locs', cs') -> return (v', vars, ms, locs @ locs', cs @ cs')
  | Constraint (lc, _, lat') ->
    collect_lc vars ms lc
    >>= fun (vars, ms, locs, cs) ->
    collect_lat_it max_unfolds sigma prog5 vars ms lat'
    >>= fun (v, vars, ms, locs', cs') -> return (v, vars, ms, locs @ locs', cs @ cs')
  | I it -> return (it, vars, ms, [], [])
;;

let rec collect_lat
  (max_unfolds : int)
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
    collect_lat max_unfolds sigma prog5 vars ms (lat_subst x tm lat')
  | Resource ((x, (ret, _)), _, lat') ->
    collect_ret max_unfolds sigma prog5 vars ms ret
    >>= fun (v, vars, ms, locs, cs) ->
    collect_lat max_unfolds sigma prog5 vars ms (lat_subst x v lat')
    >>= fun (vars, ms, locs', cs') -> return (vars, ms, locs @ locs', cs @ cs')
  | Constraint (lc, _, lat') ->
    collect_lc vars ms lc
    >>= fun (vars, ms, locs, cs) ->
    collect_lat max_unfolds sigma prog5 vars ms lat'
    >>= fun (vars, ms, locs', cs') -> return (vars, ms, locs @ locs', cs @ cs')
  | I _ -> return (vars, ms, [], [])
;;

let subst_goal (x : Symbol.sym) (v : IT.t) ((vars, ms, locs, cs) : goal) : goal =
  let vars =
    List.map (fun (x', (ty, e)) -> x', (ty, IT.subst (IT.make_subst [ x, v ]) e)) vars
  in
  let locs = List.map (fun (e, y) -> IT.subst (IT.make_subst [ x, v ]) e, y) locs in
  let cs = List.map (fun e -> IT.subst (IT.make_subst [ x, v ]) e) cs in
  vars, ms, locs, cs
;;

let rec inline_constants' (g : goal) (iter : constraints) : goal =
  match iter with
  | IT (Binop (EQ, IT (Const c, bt, loc), IT (Sym x, _, _)), _, _) :: iter'
  | IT (Binop (EQ, IT (Sym x, _, _), IT (Const c, bt, loc)), _, _) :: iter' ->
    let g = subst_goal x (IT (Const c, bt, loc)) g in
    inline_constants' g iter'
  | _ :: iter' -> inline_constants' g iter'
  | [] -> g
;;

let inline_constants (g : goal) : goal =
  let _, _, _, cs = g in
  inline_constants' g cs
;;

let eval_term (it : IT.t) : IT.const option =
  let g = Global.empty in
  let m = Solver.empty_model in
  match Solver.eval g m it with
  | Some (IT (Const c, _, _)) -> Some c
  | _ -> None
;;

let rec remove_tautologies ((vars, ms, locs, cs) : goal) : goal =
  match cs with
  | IT (Binop (EQ, IT (Sym x, _, _), IT (Sym y, _, _)), _, _) :: cs
    when sym_codified_equal x y -> remove_tautologies (vars, ms, locs, cs)
  | c :: cs ->
    (match eval_term c with
     | Some (Bool b) ->
       if b
       then remove_tautologies (vars, ms, locs, cs)
       else failwith "Inconsistent constraints"
     | Some _ -> failwith "unreachable"
     | None ->
       let vars, ms, locs, cs = remove_tautologies (vars, ms, locs, cs) in
       vars, ms, locs, c :: cs)
  | [] -> vars, ms, locs, cs
;;

let rec cnf_ (e : BT.t IT.term_) : BT.t IT.term_ =
  match e with
  (* Double negation elimination *)
  | Unop (Not, IT (Unop (Not, IT (e, _, _)), _, _)) -> e
  (* Flip inequalities *)
  | Unop (Not, IT (Binop (LT, e1, e2), _, _)) -> Binop (LE, e2, e1)
  | Unop (Not, IT (Binop (LE, e1, e2), _, _)) -> Binop (LT, e2, e1)
  (* De Morgan's Law *)
  | Unop (Not, IT (Binop (And, e1, e2), info, loc)) ->
    Binop (Or, IT (Unop (Not, cnf e1), info, loc), IT (Unop (Not, cnf e2), info, loc))
  | Unop (Not, IT (Binop (Or, e1, e2), info, loc)) ->
    Binop (And, IT (Unop (Not, cnf e1), info, loc), IT (Unop (Not, cnf e2), info, loc))
  (* Distribute disjunction *)
  | Binop (Or, e1, IT (Binop (And, e2, e3), info, loc))
  | Binop (Or, IT (Binop (And, e2, e3), info, loc), e1) ->
    Binop (And, IT (Binop (Or, e1, e2), info, loc), IT (Binop (Or, e1, e3), info, loc))
  | _ -> e

and cnf (e : IT.t) : IT.t =
  let (IT (e, info, loc)) = e in
  IT (cnf_ e, info, loc)
;;

let rec inline_aliasing' (g : goal) (iter : constraints) : goal =
  match iter with
  | IT (Binop (EQ, IT (Sym x, info_x, loc_x), IT (Sym y, _, _)), info_y, loc_y) :: iter'
    ->
    let vars, _, _, _ = g in
    let g =
      match List.assoc sym_codified_equal x vars with
      | _, IT (Sym x', _, _) when sym_codified_equal x x' ->
        subst_goal x (IT (Sym y, info_y, loc_y)) g
      | _ -> subst_goal y (IT (Sym x, info_x, loc_x)) g
    in
    inline_aliasing' g iter'
  | _ :: iter' -> inline_aliasing' g iter'
  | [] -> g
;;

let inline_aliasing (g : goal) : goal =
  let _, _, _, cs = g in
  inline_aliasing' g cs
;;

let rec remove_nonnull_for_locs ((vars, ms, locs, cs) : goal) : goal =
  match cs with
  | IT (Unop (Not, IT (Binop (EQ, e, IT (Const Null, _, _)), _, _)), _, _) :: cs
    when List.assoc_opt Stdlib.( = ) e locs |> Option.is_some ->
    remove_nonnull_for_locs (vars, ms, locs, cs)
  | IT (Unop (Not, IT (Binop (EQ, IT (Const Null, _, _), e), _, _)), _, _) :: cs
    when List.assoc_opt Stdlib.( = ) e locs |> Option.is_some ->
    remove_nonnull_for_locs (vars, ms, locs, cs)
  | c :: cs ->
    let vars, ms, locs, cs = remove_nonnull_for_locs (vars, ms, locs, cs) in
    vars, ms, locs, c :: cs
  | [] -> vars, ms, locs, []
;;

let rec indirect_members_expr_ (ms : members) (e : BT.t IT.term_) : BT.t IT.term_ =
  match e with
  | StructMember (IT (Sym x, _, _), Symbol.Identifier (_, y)) ->
    let new_sym =
      (List.assoc sym_codified_equal x ms |> List.find (fun m -> String.equal m.name y))
        .car
    in
    Sym new_sym
  | Unop (op, e') -> Unop (op, indirect_members_expr ms e')
  | Binop (op, e1, e2) ->
    Binop (op, indirect_members_expr ms e1, indirect_members_expr ms e2)
  | ITE (e_if, e_then, e_else) ->
    ITE
      ( indirect_members_expr ms e_if
      , indirect_members_expr ms e_then
      , indirect_members_expr ms e_else )
  | EachI ((min, (x', bt), max), e') ->
    EachI ((min, (x', bt), max), indirect_members_expr ms e')
  | Tuple es -> Tuple (List.map (indirect_members_expr ms) es)
  | NthTuple (i, e') -> NthTuple (i, indirect_members_expr ms e')
  | Struct (x', xes) ->
    Struct (x', List.map (fun (x', e') -> x', indirect_members_expr ms e') xes)
  | StructMember (e', x') -> StructMember (indirect_members_expr ms e', x')
  | StructUpdate ((e', x'), e'') ->
    StructUpdate ((indirect_members_expr ms e', x'), indirect_members_expr ms e'')
  | Record xes -> Record (List.map (fun (x', e') -> x', indirect_members_expr ms e') xes)
  | RecordMember (e', x') -> RecordMember (indirect_members_expr ms e', x')
  | RecordUpdate ((e', x'), e'') ->
    RecordUpdate ((indirect_members_expr ms e', x'), indirect_members_expr ms e'')
  | Constructor (x', xes) ->
    Constructor (x', List.map (fun (x', e') -> x', indirect_members_expr ms e') xes)
  | MemberShift (e', x', x'') -> MemberShift (indirect_members_expr ms e', x', x'')
  | ArrayShift { base; ct; index } ->
    ArrayShift
      { base = indirect_members_expr ms base; ct; index = indirect_members_expr ms index }
  | CopyAllocId { addr; loc } ->
    CopyAllocId
      { addr = indirect_members_expr ms addr; loc = indirect_members_expr ms loc }
  | Cons (e1, e2) -> Cons (indirect_members_expr ms e1, indirect_members_expr ms e2)
  | Head e' -> Head (indirect_members_expr ms e')
  | Tail e' -> Tail (indirect_members_expr ms e')
  | NthList (e1, e2, e3) ->
    NthList
      ( indirect_members_expr ms e1
      , indirect_members_expr ms e2
      , indirect_members_expr ms e3 )
  | ArrayToList (e1, e2, e3) ->
    ArrayToList
      ( indirect_members_expr ms e1
      , indirect_members_expr ms e2
      , indirect_members_expr ms e3 )
  | Representable (ty, e') -> Representable (ty, indirect_members_expr ms e')
  | Good (ty, e') -> Good (ty, indirect_members_expr ms e')
  | Aligned { t; align } ->
    Aligned { t = indirect_members_expr ms t; align = indirect_members_expr ms align }
  | WrapI (ty, e') -> WrapI (ty, indirect_members_expr ms e')
  | MapConst (bt, e') -> MapConst (bt, indirect_members_expr ms e')
  | MapSet (e1, e2, e3) ->
    MapSet
      ( indirect_members_expr ms e1
      , indirect_members_expr ms e2
      , indirect_members_expr ms e3 )
  | MapGet (e1, e2) -> MapGet (indirect_members_expr ms e1, indirect_members_expr ms e2)
  | MapDef (xbt, e') -> MapDef (xbt, indirect_members_expr ms e')
  | Apply (x', es) -> Apply (x', List.map (indirect_members_expr ms) es)
  | Let ((x', e1), e2) ->
    Let ((x', indirect_members_expr ms e1), indirect_members_expr ms e2)
  | Match (e', pes) ->
    Match
      ( indirect_members_expr ms e'
      , List.map (fun (p, e') -> p, indirect_members_expr ms e') pes )
  | Cast (bt, e') -> Cast (bt, indirect_members_expr ms e')
  | Sym _ | Const _ | SizeOf _ | OffsetOf _ | Nil _ -> e

and indirect_members_expr (ms : members) (e : IT.t) : IT.t =
  let (IT (e, info, loc)) = e in
  IT (indirect_members_expr_ ms e, info, loc)
;;

let indirect_members ((vars, ms, locs, cs) : goal) : goal =
  ( List.map (fun (x, (ty, e)) -> x, (ty, indirect_members_expr ms e)) vars
  , ms
  , List.map (fun (e, x) -> indirect_members_expr ms e, x) locs
  , List.map (fun e -> indirect_members_expr ms e) cs )
;;

let listify_constraints (cs : constraints) : constraints =
  let rec loop (c : IT.t) : constraints =
    match c with
    | IT (Binop (And, e1, e2), _, _) -> loop e1 @ loop e2
    | _ -> [ c ]
  in
  List.map loop cs |> List.flatten
;;

let remove_good (cs : constraints) : constraints =
  List.filter
    (fun (c : IT.t) ->
      match c with
      | IT (Good _, _, _) -> false
      | _ -> true)
    cs
;;

let simplify (g : goal) : goal =
  let g = indirect_members g in
  let vars, ms, locs, cs = g in
  let g = vars, ms, locs, List.map cnf cs in
  let g = remove_nonnull_for_locs g in
  let rec loop (g : goal) : goal =
    let og = g in
    let g = inline_constants g in
    let g = inline_aliasing g in
    let vars, ms, locs, cs = remove_tautologies g in
    let cs = listify_constraints cs in
    let cs = remove_good cs in
    let g = vars, ms, locs, cs in
    if Stdlib.( <> ) og g then loop g else g
  in
  loop g
;;

type gen =
  | Arbitrary of Ctype.ctype
  | Return of Ctype.ctype * IT.t
  | Filter of Sym.sym * Ctype.ctype * IT.t * gen
  | Map of Sym.sym * Ctype.ctype * IT.t * gen
  | Alloc of Ctype.ctype * Sym.sym
  | Struct of Ctype.ctype * (string * Sym.sym) list

let rec string_of_gen (g : gen) : string =
  match g with
  | Arbitrary ty -> "arbitrary<" ^ string_of_ctype ty ^ ">"
  | Return (ty, e) ->
    "return<"
    ^ string_of_ctype ty
    ^ ">("
    ^ Pp_utils.to_plain_pretty_string (IT.pp e)
    ^ ")"
  | Filter (x, ty, e, g') ->
    "filter("
    ^ "|"
    ^ codify_sym x
    ^ ": "
    ^ string_of_ctype ty
    ^ "| "
    ^ Pp_utils.to_plain_pretty_string (IT.pp e)
    ^ ", "
    ^ string_of_gen g'
    ^ ")"
  | Map (x, ty, e, g') ->
    "map("
    ^ "|"
    ^ codify_sym x
    ^ ": "
    ^ string_of_ctype ty
    ^ "| "
    ^ Pp_utils.to_plain_pretty_string (IT.pp e)
    ^ ", "
    ^ string_of_gen g'
    ^ ")"
  | Alloc (ty, x) -> "alloc<" ^ string_of_ctype ty ^ ">(" ^ codify_sym x ^ ")"
  | Struct (ty, ms) ->
    "struct<"
    ^ string_of_ctype ty
    ^ ">("
    ^ String.concat ", " (List.map (fun (x, g') -> "." ^ x ^ ": " ^ codify_sym g') ms)
    ^ ")"
;;

type gen_context = (Symbol.sym * gen) list

let string_of_gen_context (gtx : gen_context) : string =
  "{ "
  ^ String.concat
      "; "
      (List.map
         (fun (x, g) -> "\"" ^ codify_sym x ^ "\" <- \"" ^ string_of_gen g ^ "\"")
         gtx)
  ^ " }"
;;

let filter_gen (x : Symbol.sym) (ty : Ctype.ctype) (cs : constraints) : gen =
  match cs with
  | _ :: _ -> Filter (x, ty, IT.and_ cs (Cerb_location.other __FUNCTION__), Arbitrary ty)
  | [] -> Arbitrary ty
;;

let compile_gen (x : Symbol.sym) (ty : Ctype.ctype) (e : IT.t) (cs : constraints) : gen =
  match e with
  | IT (Sym x', _, _) when sym_codified_equal x x' -> filter_gen x ty cs
  | _ -> Return (ty, e)
;;

let rec compile_singles'
  (gtx : gen_context)
  (locs : locations)
  (cs : constraints)
  (iter : variables)
  : gen_context * variables
  =
  let get_loc x =
    List.find_map
      (fun (e, y) ->
        if sym_codified_equal x y
        then (
          match e with
          | IT.IT (Sym z, _, _) -> Some z
          | _ -> None)
        else None)
      locs
  in
  match iter with
  | (x, (ty, e)) :: iter' ->
    let var_in_gtx y =
      List.find_opt (fun (z, _) -> sym_codified_equal y z) gtx |> Option.is_some
    in
    let relevant_cs =
      List.filter
        (fun c ->
          List.exists
            (sym_codified_equal x)
            (c |> IT.free_vars |> IT.SymSet.to_seq |> List.of_seq))
        cs
    in
    let no_free_vars =
      List.for_all
        (fun c ->
          List.for_all
            (fun y -> sym_codified_equal x y || var_in_gtx y)
            (c |> IT.free_vars |> IT.SymSet.to_seq |> List.of_seq))
        relevant_cs
    in
    if no_free_vars
    then (
      let gen = compile_gen x ty e relevant_cs in
      let gen_loc = Alloc (Ctype.Ctype ([], Pointer (Ctype.no_qualifiers, ty)), x) in
      match get_loc x with
      | Some x_loc -> compile_singles' ((x_loc, gen_loc) :: (x, gen) :: gtx) locs cs iter'
      | None -> compile_singles' ((x, gen) :: gtx) locs cs iter')
    else (
      let gtx, iter' = compile_singles' gtx locs cs iter' in
      gtx, (x, (ty, e)) :: iter')
  | [] -> gtx, iter
;;

let rec compile_singles
  (gtx : gen_context)
  (vars : variables)
  (locs : locations)
  (cs : constraints)
  : gen_context
  =
  let gtx, vars = compile_singles' gtx locs cs vars in
  if List.non_empty vars then compile_singles gtx vars locs cs else gtx
;;

let rec compile_structs'
  (gtx : gen_context)
  (vars : variables)
  (ms : members)
  (locs : locations)
  : gen_context * members
  =
  let get_loc x =
    List.find_map
      (fun (e, y) ->
        if sym_codified_equal x y
        then (
          match e with
          | IT.IT (Sym z, _, _) -> Some z
          | _ -> None)
        else None)
      locs
  in
  match ms with
  | (x, syms) :: ms' ->
    let gtx, ms' = compile_structs' gtx vars ms' locs in
    let free_vars =
      not
        (List.for_all
           (fun m -> List.assoc_opt sym_codified_equal m.car gtx |> Option.is_some)
           syms)
    in
    if free_vars
    then gtx, (x, syms) :: ms'
    else (
      let _, (ty, _) = List.find (fun (y, _) -> sym_codified_equal x y) vars in
      let mems = List.map (fun m -> m.name, m.car) syms in
      match get_loc x with
      | Some loc ->
        let gen = Struct (ty, mems) in
        let gen_loc = Alloc (Ctype.Ctype ([], Pointer (Ctype.no_qualifiers, ty)), x) in
        (loc, gen_loc) :: (x, gen) :: gtx, ms'
      | None -> (x, Struct (ty, mems)) :: gtx, ms')
  | [] -> gtx, []
;;

let rec compile_structs
  (gtx : gen_context)
  (vars : variables)
  (ms : members)
  (locs : locations)
  : gen_context
  =
  let gtx, ms = compile_structs' gtx vars ms locs in
  if List.non_empty ms then compile_structs gtx vars ms locs else gtx
;;

let compile ((vars, ms, locs, cs) : goal) : gen_context =
  (* Not owned *)
  let vars' =
    List.filter
      (fun (x, _) ->
        List.for_all
          (fun (e, _) ->
            match e with
            | IT.IT (Sym y, _, _) -> not (sym_codified_equal x y)
            | _ -> true)
          locs)
      vars
  in
  (* Not a struct *)
  let vars' =
    List.filter
      (fun (x, _) -> List.for_all (fun (y, _) -> not (sym_codified_equal x y)) ms)
      vars'
  in
  let gtx = compile_singles [] vars' locs cs in
  compile_structs gtx vars ms locs |> List.rev
;;

type test_framework = GTest

let rec codify_it_ (e : BT.t IT.term_) : string =
  match e with
  | Const Null -> "nullptr"
  | Const (Bits ((Signed, bits), n)) when bits <= 16 -> Int64.to_string (Z.to_int64 n)
  | Const (Bits ((Unsigned, bits), n)) when bits <= 16 ->
    Int64.to_string (Z.to_int64 n) ^ "U"
  | Const (Bits ((Signed, bits), n)) when bits <= 32 ->
    Int64.to_string (Z.to_int64 n) ^ "L"
  | Const (Bits ((Unsigned, bits), n)) when bits <= 32 ->
    string_of_int (Z.to_int n) ^ "UL"
  | Const (Bits ((Signed, bits), n)) when bits <= 64 ->
    Int64.to_string (Z.to_int64 n) ^ "LL"
  | Const (Bits ((Unsigned, bits), n)) when bits <= 64 ->
    Int64.to_string (Z.to_int64 n) ^ "ULL"
  | Const (Bool b) -> string_of_bool b
  | Sym x -> Sym.pp_string x
  | Unop (Not, e') -> "(!" ^ codify_it e' ^ ")"
  | Unop (Negate, e') -> "(-" ^ codify_it e' ^ ")"
  | Binop (And, e1, e2) -> "(" ^ codify_it e1 ^ " && " ^ codify_it e2 ^ ")"
  | Binop (Or, e1, e2) -> codify_it e1 ^ " || " ^ codify_it e2 ^ ")"
  | Binop (Implies, e1, e2) -> "((!" ^ codify_it e1 ^ ") || " ^ codify_it e2 ^ ")"
  | Binop (Add, e1, e2) -> "(" ^ codify_it e1 ^ " + " ^ codify_it e2 ^ ")"
  | Binop (Sub, e1, e2) -> "(" ^ codify_it e1 ^ " - " ^ codify_it e2 ^ ")"
  | Binop (Mul, e1, e2) | Binop (MulNoSMT, e1, e2) ->
    "(" ^ codify_it e1 ^ " * " ^ codify_it e2 ^ ")"
  | Binop (Div, e1, e2) | Binop (DivNoSMT, e1, e2) ->
    "(" ^ codify_it e1 ^ " / " ^ codify_it e2 ^ ")"
  | Binop (XORNoSMT, e1, e2) -> "(" ^ codify_it e1 ^ " ^ " ^ codify_it e2 ^ ")"
  | Binop (BWAndNoSMT, e1, e2) -> "(" ^ codify_it e1 ^ " & " ^ codify_it e2 ^ ")"
  | Binop (BWOrNoSMT, e1, e2) -> "(" ^ codify_it e1 ^ " | " ^ codify_it e2 ^ ")"
  | Binop (ShiftLeft, e1, e2) -> "(" ^ codify_it e1 ^ " << " ^ codify_it e2 ^ ")"
  | Binop (ShiftRight, e1, e2) -> "(" ^ codify_it e1 ^ " >> " ^ codify_it e2 ^ ")"
  | Binop (LT, e1, e2) | Binop (LTPointer, e1, e2) ->
    "(" ^ codify_it e1 ^ " < " ^ codify_it e2 ^ ")"
  | Binop (LE, e1, e2) | Binop (LEPointer, e1, e2) ->
    "(" ^ codify_it e1 ^ " <= " ^ codify_it e2 ^ ")"
  | Binop (EQ, e1, e2) -> "(" ^ codify_it e1 ^ " == " ^ codify_it e2 ^ ")"
  | Binop (Mod, e1, e2) -> "(" ^ codify_it e1 ^ " % " ^ codify_it e2 ^ ")"
  | ITE (e1, e2, e3) ->
    "(" ^ codify_it e1 ^ " ? " ^ codify_it e2 ^ " : " ^ codify_it e3 ^ ")"
  (* *)
  | _ -> failwith "unsupported operation"

and codify_it (e : IT.t) : string =
  let (IT (e_, _, _)) = e in
  try codify_it_ e_ with
  | Failure _ ->
    failwith ("unsupported operation" ^ Pp_utils.to_plain_pretty_string (IT.pp e))
;;

let rec codify_gen' (g : gen) : string =
  match g with
  | Arbitrary ty -> "rc::gen::arbitrary<" ^ string_of_ctype ty ^ ">()"
  | Return (ty, e) -> "rc::gen::just<" ^ string_of_ctype ty ^ ">(" ^ codify_it e ^ ")"
  | Filter (x', ty, e, g') ->
    let gen = codify_gen' g' in
    "rc::gen::suchThat("
    ^ gen
    ^ ", [=]("
    ^ string_of_ctype ty
    ^ " "
    ^ codify_sym x'
    ^ "){ return "
    ^ codify_it e
    ^ "; })"
  | Map (x', ty, e, g') ->
    let gen = codify_gen' g' in
    "rc::gen::map("
    ^ gen
    ^ ", [=]("
    ^ string_of_ctype ty
    ^ " "
    ^ codify_sym x'
    ^ "){ return "
    ^ codify_it e
    ^ "; })"
  | Alloc (ty, x) -> "rc::gen::just<" ^ string_of_ctype ty ^ ">(&" ^ codify_sym x ^ ")"
  | Struct (ty, ms) ->
    "rc::gen::just<"
    ^ string_of_ctype ty
    ^ ">({ "
    ^ String.concat ", " (List.map (fun (x, y) -> "." ^ x ^ " = " ^ codify_sym y) ms)
    ^ "})"
;;

let codify_gen (x : Sym.sym) (g : gen) : string =
  "/* "
  ^ string_of_gen g
  ^ " */\n"
  ^ "auto "
  ^ codify_sym x
  ^ " = *"
  ^ codify_gen' g
  ^ ";\n"
;;

let rec codify_gen_context (gtx : gen_context) : string =
  match gtx with
  | (x, g) :: gtx' -> codify_gen x g ^ codify_gen_context gtx'
  | [] -> ""
;;

let codify_pbt_header
  (tf : test_framework)
  (suite : string)
  (test : string)
  (oc : out_channel)
  : unit
  =
  match tf with
  | GTest ->
    output_string
      oc
      ("\nRC_GTEST_PROP(Test" ^ String.capitalize_ascii suite ^ ", " ^ test ^ ", ()){\n")
;;

let codify_pbt
  (tf : test_framework)
  (instrumentation : Core_to_mucore.instrumentation)
  (args : (Symbol.sym * Ctype.ctype) list)
  (index : int)
  (oc : out_channel)
  (gtx : gen_context)
  : unit
  =
  codify_pbt_header tf (codify_sym instrumentation.fn) ("Test" ^ string_of_int index) oc;
  output_string oc (codify_gen_context gtx);
  output_string oc (codify_sym instrumentation.fn);
  output_string oc "(";
  output_string oc (args |> List.map fst |> List.map codify_sym |> String.concat ", ");
  output_string oc ");\n";
  match tf with
  | GTest -> output_string oc "}\n\n"
;;

let get_args (sigma : _ AilSyntax.sigma) (fun_name : Sym.sym)
  : (Sym.sym * Ctype.ctype) list
  =
  let lookup_fn (x, _) = sym_codified_equal x fun_name in
  let fn_decl = List.filter lookup_fn sigma.declarations in
  let fn_def = List.filter lookup_fn sigma.function_definitions in
  let arg_types, arg_syms =
    match fn_decl, fn_def with
    | ( (_, (_, _, Decl_function (_, _, arg_types, _, _, _))) :: _
      , (_, (_, _, _, arg_syms, _)) :: _ ) ->
      let arg_types = List.map (fun (_, ctype, _) -> ctype) arg_types in
      arg_types, arg_syms
    | _ -> [], []
  in
  List.combine arg_syms arg_types
;;

let rec get_lat_from_at (at : _ AT.t) : _ LAT.t =
  match at with
  | AT.Computational (_, _, at') -> get_lat_from_at at'
  | AT.L lat -> lat
;;

let generate_pbt
  (max_unfolds : int)
  (sigma : _ AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  (tf : test_framework)
  (oc : out_channel)
  (instrumentation : Core_to_mucore.instrumentation)
  : unit
  =
  let args = get_args sigma instrumentation.fn in
  let vars, ms =
    List.fold_left
      (fun (vars, ms) (x, ty) -> add_to_vars_ms sigma x ty vars ms)
      ([], [])
      args
  in
  output_string oc ("/* Begin:\n" ^ string_of_goal (vars, ms, [], []) ^ "*/\n\n");
  let lat =
    Option.get instrumentation.internal |> get_lat_from_at |> LAT.map (fun _ -> ())
  in
  List.iteri
    (fun i g ->
      output_string oc ("/* Collected:\n" ^ string_of_goal g ^ "*/\n\n");
      let g = simplify g in
      output_string oc ("/* Simplified:\n" ^ string_of_goal g ^ "*/\n\n");
      let gtx = compile g in
      output_string oc ("/* Compiled: " ^ string_of_gen_context gtx ^ "*/\n");
      codify_pbt tf instrumentation args i oc gtx)
    (collect_lat max_unfolds sigma prog5 vars ms lat)
;;

let main
  ~(output_dir : string)
  ~(filename : string)
  ~(max_unfolds : int)
  (sigma : _ AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  (tf : test_framework)
  : unit
  =
  let instrumentation_list, _symbol_table =
    Core_to_mucore.collect_instrumentation prog5
  in
  let instrumentation_list =
    instrumentation_list
    |> List.filter (fun (inst : Core_to_mucore.instrumentation) ->
      match Cerb_location.get_filename inst.fn_loc with
      | Some filename' -> String.equal filename filename'
      | None -> false)
  in
  let oc =
    Stdlib.open_out
      (output_dir
       ^ "test_"
       ^ (filename |> Filename.basename |> Filename.chop_extension)
       ^ ".cpp")
  in
  List.iter (generate_pbt max_unfolds sigma prog5 tf oc) instrumentation_list
;;
