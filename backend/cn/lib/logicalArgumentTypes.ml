open Locations
module BT = BaseTypes
module IT = IndexTerms
module Req = Request
module LC = LogicalConstraints

type 'i t =
  | Define of (Sym.t * IT.t) * info * 'i t
  | Resource of (Sym.t * (Req.t * BT.t)) * info * 'i t
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
      let re = Req.subst substitution re in
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
  if Sym.Set.mem s syms then
    alpha_rename i_subst s t
  else
    (s, t)


let free_vars_bts i_free_vars_bts =
  let union =
    Sym.Map.union (fun _ bt1 bt2 ->
      assert (BT.equal bt1 bt2);
      Some bt1)
  in
  let rec aux = function
    | Define ((s, it), _info, t) ->
      let it_vars = IT.free_vars_bts it in
      let t_vars = Sym.Map.remove s (aux t) in
      union it_vars t_vars
    | Resource ((s, (re, _bt)), _info, t) ->
      let re_vars = Req.free_vars_bts re in
      let t_vars = Sym.Map.remove s (aux t) in
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
      let t_vars = Sym.Set.remove s (aux t) in
      Sym.Set.union it_vars t_vars
    | Resource ((s, (re, _bt)), _info, t) ->
      let re_vars = Req.free_vars re in
      let t_vars = Sym.Set.remove s (aux t) in
      Sym.Set.union re_vars t_vars
    | Constraint (lc, _info, t) ->
      let lc_vars = LC.free_vars lc in
      let t_vars = aux t in
      Sym.Set.union lc_vars t_vars
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
    group (!^"take" ^^^ Sym.pp name ^^^ equals ^^^ Req.pp re ^^ semi) :: pp_aux i_pp t
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
      let t = f (Sym.Set.add name ss) t in
      Define ((name, it), info, t)
    | Resource ((name, (re, bt)), info, t) ->
      let name, t = rename_if ss name t in
      let t = f (Sym.Set.add name ss) t in
      Resource ((name, (re, bt)), info, f ss t)
    | Constraint (lc, info, t) -> Constraint (lc, info, f ss t)
    | I i -> I (RT.alpha_unique ss i)
  in
  f ss


let binders i_binders i_subst =
  let here = Locations.other __LOC__ in
  let rec aux = function
    | Define ((s, it), _, t) ->
      let s, t = alpha_rename i_subst s t in
      (Id.make here (Sym.pp_string s), IT.get_bt it) :: aux t
    | Resource ((s, (_, bt)), _, t) ->
      let s, t = alpha_rename i_subst s t in
      (Id.make here (Sym.pp_string s), bt) :: aux t
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
        (pp_ctor "Resource", [ Dleaf (Sym.pp s); Req.dtree rt; Dleaf (BT.pp bt); aux t ])
    | Constraint (lc, _, t) -> Dnode (pp_ctor "Constraint", [ LC.dtree lc; aux t ])
    | I i -> Dnode (pp_ctor "I", [ dtree_i i ])
  in
  aux

(** Infrastructure for checking if a countermodel satisfies a predicate **)
open ResultWithData

type check_result = (LC.t list, Pp.document) result_with_data
let pp_check_result = pp_result_with_data (Pp.list LC.pp) (fun d -> d)

let filter_map_some (f : 'a -> 'b option) (l : 'a list) : 'b list =
  List.fold_left (fun acc elem -> match f elem with None -> acc | Some x -> x :: acc) [] l

(* Gives a single canonical result *)
let combine_results (results : check_result list)
  : check_result =
  match results with
  | [] -> Error !^"Empty result list"
  | h :: t ->
    let combine = fun acc res -> match acc, res with
      | Yes l, _ -> Yes l
      | _, Yes l -> Yes l
      | Error s, _ -> Error s
      | _, Error s -> Error s
      | Unknown s, _ -> Unknown s
      | _, Unknown s -> Unknown s
      | No s, _ -> No s
    in
    List.fold_left combine h t


(* Type of nonterminal lines in a predicate clause.
  Corresponds to packing_ft *)
type def_line =
  | DefineL of (Sym.t * IT.t) * info
  | ResourceL of (Sym.t * (Req.t * BT.t)) * info

let def_line_pp dl = match dl with
  | DefineL ((s, t), _) -> group (!^"let" ^^^ Sym.pp s ^^^ equals ^^^ IT.pp t ^^ semi)
  | ResourceL ((s, (re, _)), _) -> group (!^"take" ^^^ Sym.pp s ^^^ equals ^^^ Req.pp re ^^ semi)

(* Optionally zip two lists, returning None if the lists have different lengths *)
let rec zip (l1 : 'a list) (l2 : 'b list) : ('a * 'b) list option = match l1, l2 with
| [], [] -> Some []
| h1 :: tl1, h2 :: tl2 -> (match zip tl1 tl2 with
  | Some zs -> Some ((h1, h2) :: zs)
  | None -> None)
| _, _ -> None

(* Take the union of two symbol maps,
    removing any key that is in both maps but has a different value in each *)
let merge_eq (eq : 'a -> 'a -> bool) (m1 : 'a Sym.Map.t) (m2 : 'a Sym.Map.t) : 'a Sym.Map.t =
  let merge = (fun k v1 v2 -> let _ = k in if eq v1 v2 then Some v1 else None) in
  Sym.Map.union merge m1 m2

(* Build a map by using f to develop a map for each
    pair of elements in the two lists, failing
    if they produce different results for any symbol or if
    the lists have different lengths *)
let map_from_lists f eq exps exps' =
  let merge_r_maps r_acc (exp1, exp1') =
    let@ acc = r_acc in
    let@ combined = f exp1 exp1' in
    Yes (merge_eq eq acc combined)
  in
  match zip exps exps' with
  | Some zipped -> List.fold_left merge_r_maps (Yes Sym.Map.empty) zipped
  | None -> Error !^"Could not zip lists of expressions." (* should never happen *)

(* Match an expression with free variables against a candidate returned by the solver to
  get candidates for each of those free variables *)
(* TODO: this is very naive right now;
  it assumes candidate and exp have *exactly* the same structure, modulo free variables in exp *)
let rec get_var_cands (exp : IT.t) (candidate : IT.t) : (IT.t Sym.Map.t, Pp.document) result_with_data =
  let map_from_IT_lists = map_from_lists get_var_cands IT.equal in
  let sort_by_discard_fst compare l =
    List.map snd ( List.sort (fun p1 p2 -> compare (fst p1) (fst p2)) l) in
  let sort_by_id = sort_by_discard_fst Id.compare in
  let sort_by_pattern = sort_by_discard_fst (Terms.compare_pattern BT.compare) in
  let map_with_guard_unknown g l1 l1' = if g then map_from_IT_lists l1 l1' else (Unknown (Pp.bool g ^^^ !^" not satisfied")) in
  let map_with_guard_no g l1 l1' = if g then map_from_IT_lists l1 l1' else (No (Pp.bool g ^^^ !^" not satisfied") ) in
  let default = Unknown (!^"Different CN constructors for " ^^^ IT.pp exp ^^^ !^" and " ^^^ IT.pp candidate) in
  match IT.get_term exp, IT.get_term candidate with
  | Const c, Const c' -> map_with_guard_no (IT.equal_const c c') [] []
  | Sym v, _' -> Yes (Sym.Map.add v candidate Sym.Map.empty)
  | Unop (op, exp1), Unop (op', exp1') ->
    map_with_guard_unknown (IT.equal_unop op op') [exp1] [exp1']
  | Binop (op, exp1, exp2), Binop (op', exp1', exp2') ->
    map_with_guard_unknown (IT.equal_binop op op') [exp1; exp2] [exp1'; exp2']
  | ITE (exp1, exp2, exp3), ITE (exp1', exp2', exp3') ->
    map_from_IT_lists [exp1; exp2; exp3] [exp1'; exp2'; exp3']
  | EachI ((z1, (v, bty), z2), exp1), EachI ((z1', (v', bty'), z2'), exp1') ->
    map_with_guard_unknown (z1 = z1' && Sym.equal v v' && BT.equal bty bty' && z2 = z2') [exp1] [exp1']
  | Tuple exps, Tuple exps' -> map_from_IT_lists exps exps'
  | NthTuple (n, exp1), NthTuple (n', exp1') ->
    map_with_guard_unknown (n = n') [exp1] [exp1']
  | Struct (name, fields), Struct (name', fields') ->
    map_with_guard_no (Sym.equal name name') (sort_by_id fields) (sort_by_id fields')
  | StructMember (exp1, id), StructMember (exp1', id') ->
    map_with_guard_unknown (Id.equal id id') [exp1] [exp1']
  | StructUpdate ((exp1, id), exp2), StructUpdate ((exp1', id'), exp2') ->
    map_with_guard_unknown (Id.equal id id') [exp1; exp2] [exp1'; exp2']
  | Record fields, Record fields' ->
    map_from_IT_lists (sort_by_id fields) (sort_by_id fields')
  | RecordMember (exp1, id), RecordMember (exp1', id') ->
    map_with_guard_unknown (Id.equal id id') [exp1] [exp1']
  | RecordUpdate ((exp1, id), exp2), RecordUpdate ((exp1', id'), exp2') ->
    map_with_guard_unknown (Id.equal id id') [exp1; exp2] [exp1'; exp2']
  | Constructor (name, args), Constructor (name', args') ->
    map_with_guard_no (Sym.equal name name') (sort_by_id args) (sort_by_id args')
  | MemberShift (exp1, v, id), MemberShift (exp1', v', id') ->
    map_with_guard_unknown (Sym.equal v v' && Id.equal id id') [exp1] [exp1']
  | ArrayShift {base; ct; index}, ArrayShift {base=base'; ct=ct'; index=index'} ->
    map_with_guard_unknown (Sctypes.equal ct ct') [base; index] [base'; index']
  | CopyAllocId {addr=exp1; loc=exp2}, CopyAllocId {addr=exp1'; loc=exp2'} ->
    map_from_IT_lists [exp1; exp2] [exp1'; exp2']
  | HasAllocId exp1, HasAllocId exp1' ->
    get_var_cands exp1 exp1'
  | SizeOf cty, SizeOf cty' ->
    map_with_guard_unknown (Sctypes.equal cty cty') [] []
  | OffsetOf (v, id), OffsetOf (v', id') ->
    map_with_guard_unknown (Sym.equal v v' && Id.equal id id') [] []
  | Nil bty, Nil bty' ->
    map_with_guard_no (BT.equal bty bty') [] []
  | Cons (h, tl), Cons (h', tl') ->
    map_from_IT_lists [h; tl] [h'; tl']
  | Head l, Head l' ->
    get_var_cands l l'
  | Tail l, Tail l' ->
    get_var_cands l l'
  | NthList (exp1, exp2, exp3),  NthList (exp1', exp2', exp3') ->
    map_from_IT_lists [exp1; exp2; exp3] [exp1'; exp2'; exp3']
  | ArrayToList (exp1, exp2, exp3), ArrayToList (exp1', exp2', exp3') ->
    map_from_IT_lists [exp1; exp2; exp3] [exp1'; exp2'; exp3']
  | Representable (cty, exp1), Representable (cty', exp1') ->
    map_with_guard_unknown (Sctypes.equal cty cty') [exp1] [exp1']
  | Good (cty, exp1), Good (cty', exp1') ->
    map_with_guard_unknown (Sctypes.equal cty cty') [exp1] [exp1']
  | Aligned { t=exp1; align=exp2}, Aligned { t=exp1'; align=exp2'} ->
    map_from_IT_lists [exp1; exp2] [exp1'; exp2']
  | WrapI (ity, exp1), WrapI (ity', exp1') ->
    map_with_guard_unknown (Cerb_frontend.IntegerType.integerTypeEqual ity ity') [exp1] [exp1']
  | MapConst (bty, exp1), MapConst (bty', exp1') ->
    map_with_guard_unknown (BT.equal bty bty') [exp1] [exp1']
  | MapSet (exp1, exp2, exp3), MapSet (exp1', exp2', exp3') ->
    map_from_IT_lists [exp1; exp2; exp3] [exp1'; exp2'; exp3']
  | MapGet (exp1, exp2), MapGet (exp1', exp2') ->
    map_from_IT_lists [exp1; exp2] [exp1'; exp2']
  | MapDef ((v, bty), exp1), MapDef ((v', bty'), exp1') ->
    map_with_guard_unknown (Sym.equal v v' && BT.equal bty bty') [exp1] [exp1']
  | Apply (v, exps), Apply (v', exps') ->
    map_with_guard_unknown (Sym.equal v v') exps exps'
  | Let ((v, exp1), exp2), Let ((v', exp1'), exp2') ->
    map_with_guard_unknown (Sym.equal v v') [exp1; exp2] [exp1'; exp2']
  | Match (exp1, pats), Match (exp1', pats') ->
    map_from_IT_lists (exp1 :: sort_by_pattern pats) (exp1' :: sort_by_pattern pats')
  | Cast (bt, exp1), Cast (bt', exp1') ->
    map_with_guard_unknown (BT.equal bt bt') [exp1] [exp1']
  (* included so the compiler will catch any missing new constructors *)
  | Const _, _ -> default
  | Unop _, _ -> default
  | Binop _, _-> default
  | ITE _, _ -> default
  | EachI _, _ -> default
  | Tuple _, _ -> default
  | NthTuple _, _ -> default
  | Struct _, _ -> default
  | StructMember _, _ -> default
  | StructUpdate _, _ -> default
  | Record _, _ -> default
  | RecordMember _, _ -> default
  | RecordUpdate _, _ -> default
  | Constructor _, _ -> default
  | MemberShift _, _ -> default
  | ArrayShift _, _ -> default
  | CopyAllocId _, _ -> default
  | HasAllocId _, _ -> default
  | SizeOf _, _ -> default
  | OffsetOf _, _ -> default
  | Nil _, _ -> default
  | Cons _, _ -> default
  | Head _, _ -> default
  | Tail _, _ -> default
  | NthList _, _ -> default
  | ArrayToList _, _ -> default
  | Representable _, _ -> default
  | Good _, _ -> default
  | Aligned _, _ -> default
  | WrapI _, _ -> default
  | MapConst _, _ -> default
  | MapSet _, _ -> default
  | MapGet _, _ -> default
  | MapDef _, _ -> default
  | Apply _, _ -> default
  | Let _, _ -> default
  | Match _, _ -> default
  | Cast _, _ -> default

(* Get the free variables from an expression *)
let get_fvs (exp : IT.t) : Sym.t list = Sym.Set.elements (IT.free_vars exp)

(*TODO: what if lcs mention vars not examined in the algorithm*)
let rec organize_lines_aux (lines : packing_ft) (defs : def_line Sym.Map.t) (lcs : LC.t list): IT.t * def_line Sym.Map.t * (LC.t list) =
  match lines with
  | Define ((v, it), i, next) ->
    let ln = DefineL ((v, it), i) in
    let new_defs = Sym.Map.add v ln defs in
    organize_lines_aux next new_defs lcs
  | Resource ((v, (rt, bt)), i, next) ->
    let ln = ResourceL ((v, (rt, bt)), i) in
    let new_defs = Sym.Map.add v ln defs in
    organize_lines_aux next new_defs lcs
  | Constraint (lc, _, next) -> organize_lines_aux next defs (lc :: lcs)
  | I it -> (it, defs, lcs)

(* Sort lines into the returned expression, a map of variables to their defining lines, and a list of constraints *)
let organize_lines (lines : packing_ft) : IT.t * def_line Sym.Map.t * (LC.t list) = organize_lines_aux lines Sym.Map.empty []

(** End infrastructure for checking if a countermodel satisfies a predicate **)