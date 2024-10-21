open Locations
module BT = BaseTypes
module IT = IndexTerms
module LS = LogicalSorts
module RET = ResourceTypes
module LC = LogicalConstraints
module SymSet = Set.Make (Sym)
module SymMap = Map.Make (Sym)

type 'i t =
  | Define of (Sym.t * IT.t) * info * 'i t
  | Resource of (Sym.t * (RET.t * BT.t)) * info * 'i t
  | Constraint of LC.t * info * 'i t
  | I of 'i

let mDefine (name, it, info) t = Define ((name, it), info, t)

let mResource (bound, info) t = Resource (bound, info, t)

let mConstraint (bound, info) t = Constraint (bound, info, t)

let mDefines defs t = List.fold_right mDefine defs t

let mResources ress t = List.fold_right mResource ress t

let mConstraints cons t = List.fold_right mConstraint cons t

let rec subst i_subst =
  let rec aux (substitution : _ Subst.t) at =
    match at with
    | Define ((name, it), info, t) ->
      let it = IT.subst substitution it in
      let name, t = suitably_alpha_rename i_subst substitution.relevant name t in
      Define ((name, it), info, aux substitution t)
    | Resource ((name, (re, bt)), info, t) ->
      let re = RET.subst substitution re in
      let name, t = suitably_alpha_rename i_subst substitution.relevant name t in
      let t = aux substitution t in
      Resource ((name, (re, bt)), info, t)
    | Constraint (lc, info, t) ->
      let lc = LC.subst substitution lc in
      let t = aux substitution t in
      Constraint (lc, info, t)
    | I i ->
      let i = i_subst substitution i in
      I i
  in
  aux


and alpha_rename i_subst s t =
  let s' = Sym.fresh_same s in
  (s', subst i_subst (IT.make_rename ~from:s ~to_:s') t)


and suitably_alpha_rename i_subst syms s t =
  if SymSet.mem s syms then
    alpha_rename i_subst s t
  else
    (s, t)


let free_vars_bts i_free_vars_bts =
  let union =
    SymMap.union (fun _ bt1 bt2 ->
      assert (BT.equal bt1 bt2);
      Some bt1)
  in
  let rec aux = function
    | Define ((s, it), _info, t) ->
      let it_vars = IT.free_vars_bts it in
      let t_vars = SymMap.remove s (aux t) in
      union it_vars t_vars
    | Resource ((s, (re, _bt)), _info, t) ->
      let re_vars = RET.free_vars_bts re in
      let t_vars = SymMap.remove s (aux t) in
      union re_vars t_vars
    | Constraint (lc, _info, t) ->
      let lc_vars = LC.free_vars_bts lc in
      let t_vars = aux t in
      union lc_vars t_vars
    | I i -> i_free_vars_bts i
  in
  aux


let free_vars i_free_vars =
  let rec aux = function
    | Define ((s, it), _info, t) ->
      let it_vars = IT.free_vars it in
      let t_vars = SymSet.remove s (aux t) in
      SymSet.union it_vars t_vars
    | Resource ((s, (re, _bt)), _info, t) ->
      let re_vars = RET.free_vars re in
      let t_vars = SymSet.remove s (aux t) in
      SymSet.union re_vars t_vars
    | Constraint (lc, _info, t) ->
      let lc_vars = LC.free_vars lc in
      let t_vars = aux t in
      SymSet.union lc_vars t_vars
    | I i -> i_free_vars i
  in
  aux


let simp i_subst simp_i simp_it simp_lc simp_re =
  let rec aux = function
    | Define ((s, it), info, t) ->
      let it = simp_it it in
      let s, t = alpha_rename i_subst s t in
      Define ((s, it), info, aux t)
    | Resource ((s, (re, bt)), info, t) ->
      let re = simp_re re in
      let s, t = alpha_rename i_subst s t in
      Resource ((s, (re, bt)), info, aux t)
    | Constraint (lc, info, t) ->
      let lc = simp_lc lc in
      Constraint (lc, info, aux t)
    | I i ->
      let i = simp_i i in
      I i
  in
  aux


open Pp

let rec pp_aux i_pp = function
  | Define ((name, it), _info, t) ->
    group (!^"let" ^^^ Sym.pp name ^^^ equals ^^^ IT.pp it ^^ semi) :: pp_aux i_pp t
  | Resource ((name, (re, _bt)), _info, t) ->
    group (!^"take" ^^^ Sym.pp name ^^^ equals ^^^ RET.pp re ^^ semi) :: pp_aux i_pp t
  | Constraint (lc, _info, t) ->
    let op = equals ^^ rangle () in
    group (LC.pp lc ^^^ op) :: pp_aux i_pp t
  | I i -> [ i_pp i ]


let pp i_pp ft = flow (break 1) (pp_aux i_pp ft)

let rec get_return = function
  | Define (_, _, ft) -> get_return ft
  | Resource (_, _, ft) -> get_return ft
  | Constraint (_, _, ft) -> get_return ft
  | I rt -> rt


module LRT = LogicalReturnTypes
module RT = ReturnTypes

let alpha_unique ss =
  let rename_if ss = suitably_alpha_rename RT.subst ss in
  let rec f ss at =
    match at with
    | Define ((name, it), info, t) ->
      let name, t = rename_if ss name t in
      let t = f (SymSet.add name ss) t in
      Define ((name, it), info, t)
    | Resource ((name, (re, bt)), info, t) ->
      let name, t = rename_if ss name t in
      let t = f (SymSet.add name ss) t in
      Resource ((name, (re, bt)), info, f ss t)
    | Constraint (lc, info, t) -> Constraint (lc, info, f ss t)
    | I i -> I (RT.alpha_unique ss i)
  in
  f ss


let binders i_binders i_subst =
  let rec aux = function
    | Define ((s, it), _, t) ->
      let s, t = alpha_rename i_subst s t in
      (Id.id (Sym.pp_string s), IT.bt it) :: aux t
    | Resource ((s, (_, bt)), _, t) ->
      let s, t = alpha_rename i_subst s t in
      (Id.id (Sym.pp_string s), bt) :: aux t
    | Constraint (_, _, t) -> aux t
    | I i -> i_binders i
  in
  aux


let rec of_lrt (lrt : LRT.t) (rest : 'i t) : 'i t =
  match lrt with
  | LRT.I -> rest
  | LRT.Define ((name, it), info, args) -> Define ((name, it), info, of_lrt args rest)
  | LRT.Resource ((name, t), info, args) -> Resource ((name, t), info, of_lrt args rest)
  | LRT.Constraint (t, info, args) -> Constraint (t, info, of_lrt args rest)


let rec map (f : 'i -> 'j) (at : 'i t) : 'j t =
  match at with
  | Define (bound, info, at) -> Define (bound, info, map f at)
  | Resource (bound, info, at) -> Resource (bound, info, map f at)
  | Constraint (lc, info, at) -> Constraint (lc, info, map f at)
  | I i -> I (f i)


let rec r_resource_requests r =
  match r with
  | Define (_, _, t) -> r_resource_requests t
  | Resource (resource, _info, t) -> resource :: r_resource_requests t
  | Constraint (_, _, t) -> r_resource_requests t
  | I _ -> []


type packing_ft = IT.t t

type lft = LogicalReturnTypes.t t

let rec has_resource (f : 'a -> bool) (at : 'a t) =
  match at with
  | I x -> f x
  | Resource _ -> true
  | Define (_, _, at) -> has_resource f at
  | Constraint (_, _, at) -> has_resource f at


open Cerb_frontend.Pp_ast

let dtree dtree_i =
  let rec aux = function
    | Define ((s, it), _, t) ->
      Dnode (pp_ctor "Define", [ Dleaf (Sym.pp s); IT.dtree it; aux t ])
    | Resource ((s, (rt, bt)), _, t) ->
      Dnode
        (pp_ctor "Resource", [ Dleaf (Sym.pp s); RET.dtree rt; Dleaf (BT.pp bt); aux t ])
    | Constraint (lc, _, t) -> Dnode (pp_ctor "Constraint", [ LC.dtree lc; aux t ])
    | I i -> Dnode (pp_ctor "I", [ dtree_i i ])
  in
  aux

(*CHT*)

(* Type of nonterminal lines in a predicate clause.
  Corresponds to packing_ft *)
type line =
  | DefineL of (Sym.t * IT.t) * info
  | ResourceL of (Sym.t * (RET.t * BT.t)) * info
  | ConstraintL of LC.t * info

(* Variable-assignment dependency graph for predicate clauses *)
(*CHT: this is really a DAG, but shouldn't matter here *)
type dep_tree =
  | UndefinedLT
  | NodeLT of line * dep_tree IT.SymMap.t

(* Match an expression with free variables against a candidate returned by the solver to
  get an assignment for those free variables *)
(*CHT TODO: this assumes candidate and exp have *exactly* the same structure *)
let rec get_assignment (exp : IT.t) (candidate : IT.t) : IT.t SymMap.t option =
  let sort_by_id l = List.map snd ( List.sort (fun p1 p2 -> Id.compare (fst p1) (fst p2)) l) in
  let merge = (fun k v1 v2 -> let _ = k in if v1 == v2 then Some v1 else None) in
  let match_lists exps exps' = (
    let rec zip (l1 : 'a list) (l2 : 'b list) : ('a * 'b) list option = match l1, l2 with
    | [], [] -> Some []
    | h1 :: tl1, h2 :: tl2 -> (match zip tl1 tl2 with
      | Some zs -> Some ((h1, h2) :: zs)
      | None -> None)
    | _, _ -> None
    in
    let comb acc (exp1, exp1') = match acc, get_assignment exp1 exp1' with
    | None, _ -> None
    | _, None -> None
    | Some acc', Some m -> Some (SymMap.union merge acc' m)
    in
    (match (zip exps exps') with
    | Some zs -> List.fold_left comb (Some SymMap.empty) zs
    | None -> None)) in
  match IT.term exp, IT.term candidate with
  | Const c, Const c' -> if (c == c') then Some SymMap.empty else None
  | Sym v, _' -> Some (SymMap.add v candidate SymMap.empty)
  | Unop (op, exp1), Unop (op', exp1') ->
    if (op == op') then get_assignment exp1 exp1' else None
  | Binop (op, exp1, exp2), Binop (op', exp1', exp2') ->
    if (op == op')
      then match_lists [exp1; exp2] [exp1'; exp2']
    else None
  | ITE (exp1, exp2, exp3), ITE (exp1', exp2', exp3') ->
    match_lists [exp1; exp2; exp3] [exp1'; exp2'; exp3']
  | EachI ((z1, (v, ty), z2), exp1), EachI ((z1', (v', ty'), z2'), exp1') ->
    let _ = (((z1, (v, ty), z2), exp1), ((z1', (v', ty'), z2'), exp1')) in
    failwith "CHT - out of scope"
  (* add Z3's Distinct for separation facts *)
  | Tuple exps, Tuple exps' -> match_lists exps exps'
  | NthTuple (n, exp1), NthTuple (n', exp1') ->
    let _ = (n, exp1, n', exp1') in
    failwith "CHT - out of scope"
  | Struct (name, fields), Struct (name', fields') -> if (name == name')
    then match_lists (sort_by_id fields) (sort_by_id fields')
    else None
  | StructMember (exp1, id), StructMember (exp1', id') ->
    let _ = (id, exp1, id', exp1') in
    failwith "CHT - out of scope"
  | StructUpdate ((exp1, id), exp2), StructUpdate ((exp1', id'), exp2') ->
    let _ = (((exp1, id), exp2), ((exp1', id'), exp2')) in
    failwith "CHT - out of scope"
  | Record fields, Record fields' ->
    let _ = (fields, fields') in
    failwith "CHT - out of scope"
  | RecordMember (exp1, id), RecordMember (exp1', id') ->
    let _ = (id, exp1, id', exp1') in
    failwith "CHT - out of scope"
  | RecordUpdate ((exp1, id), exp2), RecordUpdate ((exp1', id'), exp2') ->
    let _ = (((exp1, id), exp2), ((exp1', id'), exp2')) in
    failwith "CHT - out of scope"
  | Constructor (name, args), Constructor (name', args') -> if (name == name')
    then
      match_lists (sort_by_id args) (sort_by_id args')
    else None
  | MemberShift (ba, v, id), MemberShift (ba', v', id') ->
    let _ = ((ba, v, id), (ba', v', id')) in
    failwith "CHT - out of scope"
  | ArrayShift {base; ct; index}, ArrayShift {base=base'; ct=ct'; index=index'} ->
      if (ct == ct')
        then match_lists [base; index] [base'; index']
        else None
  | CopyAllocId {addr; loc}, CopyAllocId {addr=addr'; loc=loc'} ->
    let _ = ((addr, loc), (addr', loc')) in
    failwith "CHT - out of scope"
  | HasAllocId ba, HasAllocId ba' ->
    let _ = (ba, ba') in
    failwith "CHT - out of scope"
  | SizeOf cty, SizeOf cty' ->
    let _ = (cty, cty') in
    failwith "CHT - out of scope"
  | OffsetOf (v, id), OffsetOf (v', id') ->
    let _ = ((v, id), (v', id')) in
    failwith "CHT - out of scope"
  | Nil ty, Nil ty' ->
    let _ = (ty, ty') in
    failwith "CHT - out of scope"
  | Cons (h, tl), Cons (h', tl') ->
    let _ = ((h, tl), (h', tl')) in
    failwith "CHT - out of scope"
  | Head l, Head l' ->
    let _ = (l, l') in
    failwith "CHT - out of scope"
  | Tail l, Tail l' ->
    let _ = (l, l') in
    failwith "CHT - out of scope"
  | NthList (exp1, exp2, exp3),  NthList (exp1', exp2', exp3') ->
    let _ = ((exp1, exp2, exp3), (exp1', exp2', exp3')) in
    failwith "CHT - out of scope"
  | ArrayToList (exp1, exp2, exp3), ArrayToList (exp1', exp2', exp3') ->
    let _ = ((exp1, exp2, exp3), (exp1', exp2', exp3')) in
    failwith "CHT - out of scope"
  | Representable (cty, exp1), Representable (cty', exp1') ->
    let _ = ((cty, exp1), (cty', exp1')) in
    failwith "CHT - out of scope"
  | Good (cty, exp1), Good (cty', exp1') ->
    let _ = ((cty, exp1), (cty', exp1')) in
    failwith "CHT - out of scope"
  | Aligned { t; align}, Aligned { t=t'; align=align'} ->
    let _ = ((t, align), (t', align')) in
    failwith "CHT - out of scope"
  | WrapI (cty, exp1), WrapI (cty', exp1') ->
    let _ = ((cty, exp1), (cty', exp1')) in
    failwith "CHT - out of scope"
  | MapConst (ty, exp1), MapConst (ty', exp1') ->
    let _ = ((ty, exp1), (ty', exp1')) in
    failwith "CHT - out of scope"
  | MapSet (exp1, exp2, exp3), MapSet (exp1', exp2', exp3') ->
    let _ = ((exp1, exp2, exp3), (exp1', exp2', exp3')) in
    failwith "CHT - out of scope"
  | MapGet (exp1, exp2), MapGet (exp1', exp2') ->
    let _ = ((exp1, exp2), (exp1', exp2')) in
    failwith "CHT - out of scope"
  | MapDef ((v, ty), exp1), MapDef ((v', ty'), exp1') ->
    let _ = ((v, ty, exp1), (v', ty', exp1')) in
    failwith "CHT - out of scope"
  | Apply (v, exps), Apply (v', exps') ->
    let _ = ((v, exps), (v', exps')) in
    failwith "CHT - out of scope"
  | Let ((v, exp1), exp2), Let ((v', exp1'), exp2') ->
    let _ = ((v, exp1, exp2), (v', exp1', exp2')) in
    failwith "CHT - out of scope"
  | Match (exp1, pats), Match (exp1', pats') ->
    let _ = ((exp1, pats), (exp1', pats')) in
    failwith "CHT - out of scope"
  | Cast (bt, exp1), Cast (bt', exp1') ->
    let _ = ((bt, exp1), (bt', exp1')) in
    failwith "CHT - out of scope"
  (* included so the compiler will catch any missing new constructors *)
  | Const _, _ -> None
  | Unop _, _ -> None
  | Binop _, _-> None
  | ITE _, _ -> None
  | EachI _, _ -> None
  | Tuple _, _ -> None
  | NthTuple _, _ -> None
  | Struct _, _ -> None
  | StructMember _, _ -> None
  | StructUpdate _, _ -> None
  | Record _, _ -> None
  | RecordMember _, _ -> None
  | RecordUpdate _, _ -> None
  | Constructor _, _ -> None
  | MemberShift _, _ -> None
  | ArrayShift _, _ -> None
  | CopyAllocId _, _ -> None
  | HasAllocId _, _ -> None
  | SizeOf _, _ -> None
  | OffsetOf _, _ -> None
  | Nil _, _ -> None
  | Cons _, _ -> None
  | Head _, _ -> None
  | Tail _, _ -> None
  | NthList _, _ -> None
  | ArrayToList _, _ -> None
  | Representable _, _ -> None
  | Good _, _ -> None
  | Aligned _, _ -> None
  | WrapI _, _ -> None
  | MapConst _, _ -> None
  | MapSet _, _ -> None
  | MapGet _, _ -> None
  | MapDef _, _ -> None
  | Apply _, _ -> None
  | Let _, _ -> None
  | Match _, _ -> None
  | Cast _, _ -> None

(* Get the free variables from an expression *)
let get_fvs (exp : IT.t) : Sym.t list = SymSet.to_list (IT.free_vars exp)

let rec to_tree_aux (lines : packing_ft) (defs : dep_tree SymMap.t) : IT.t * dep_tree IT.SymMap.t =
  let get_children v' = match (SymMap.find_opt v' defs) with
  | Some t -> t
  | None -> UndefinedLT
  in
  let convert_children vs =
    (List.fold_left (fun acc v -> SymMap.add v (get_children v) acc) SymMap.empty vs) in
  match lines with
  | Define ((v, it), i, next) ->
    let vs = get_fvs it in
    let ln = DefineL ((v, it), i) in
    let root = NodeLT (ln, convert_children vs) in
    let new_defs = SymMap.add v root defs in
    to_tree_aux next new_defs
  | Resource ((v, (rt, bt)), i, next) ->
    let vs = match rt with
    | P {name=_; pointer; iargs} -> List.concat_map get_fvs (pointer :: iargs)
    | Q _ -> failwith "CHT - out of scope" in
    let ln = ResourceL ((v, (rt, bt)), i) in
    let root = NodeLT (ln, convert_children vs) in
    let new_defs = SymMap.add v root defs in
    to_tree_aux next new_defs
  | Constraint (_, _, next) -> to_tree_aux next defs (*CHT TODO - trees with asserts are out of scope for now*)
  | I it -> (it, defs)

(* Convert the body of a predicate clause into a variable-assignment dependency tree *)
let to_tree (lines : packing_ft) : IT.t * dep_tree IT.SymMap.t = to_tree_aux lines SymMap.empty
