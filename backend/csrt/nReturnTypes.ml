open Subst

module BT = BaseTypes
module IT = IndexTerms
module LS = LogicalSorts
module RE = Resources
module LC = LogicalConstraints
module SymSet = Set.Make(Sym)


type c = Constraint of LC.t * c | I
type r = Resource of RE.t * r | C of c
type l = Logical of (Sym.t * LS.t) * l | R of r
type a = Computational of (Sym.t * BT.t) * l

type t = a



let mcomputational (name,bound) t = Computational ((name,bound),t)
let mlogical (name,bound) t = Logical ((name,bound),t)
let mconstraint bound t = Constraint (bound,t)
let mresource bound t = Resource (bound,t)



let rec subst_var_c substitution = function
  | Constraint (lc, t) -> 
     Constraint (LC.subst_var substitution lc, subst_var_c substitution t)
  | I -> I

let rec subst_var_r substitution = function
  | Resource (re, t) ->
     Resource (RE.subst_var substitution re, subst_var_r substitution t)
  | C c -> C (subst_var_c substitution c)

let rec subst_var_l substitution = function
  | Logical ((name,ls),t) -> 
     if name = substitution.s then 
       Logical ((name,ls),t) 
     else if SymSet.mem name (IT.vars_in substitution.swith) then
       let newname = Sym.fresh () in
       let t' = subst_var_l {s=name; swith=IT.S newname} t in
       let t'' = subst_var_l substitution t' in
       Logical ((newname,ls),t'')
     else
       let t' = subst_var_l substitution t in
       Logical ((name,ls),t')
  | R r -> R (subst_var_r substitution r)

let subst_var_a substitution = function
  | Computational ((name,bt),t) -> 
     if name = substitution.s then 
       Computational ((name,bt),t) 
     else if SymSet.mem name (IT.vars_in substitution.swith) then
       let newname = Sym.fresh () in
       let t' = subst_var_l {s=name; swith=IT.S newname} t in
       let t'' = subst_var_l substitution t' in
       Computational ((newname,bt),t'')
     else
       Computational ((name,bt),subst_var_l substitution t)


let subst_vars_l = Subst.make_substs subst_var_l
let subst_vars_r = Subst.make_substs subst_var_r
let subst_vars_c = Subst.make_substs subst_var_c
let subst_vars_a = Subst.make_substs subst_var_a

let subst_var = subst_var_a
let subst_vars = subst_vars_a


let rec instantiate_struct_member_c subst = function
  | Constraint (lc,t) ->
     Constraint (LC.instantiate_struct_member subst lc, 
                 instantiate_struct_member_c subst t)
  | I -> I

let rec instantiate_struct_member_r subst = function
  | Resource (bound,t) -> 
     Resource (RE.instantiate_struct_member subst bound, 
               instantiate_struct_member_r subst t)
  | C c -> C (instantiate_struct_member_c subst c)

let rec instantiate_struct_member_l subst = function
  | Logical ((name,bound),t) -> 
     Logical ((name,bound),instantiate_struct_member_l subst t)
  | R r -> R (instantiate_struct_member_r subst r)

let instantiate_struct_member_a subst = function
  | Computational ((name,bound),t) -> 
     Computational ((name,bound),instantiate_struct_member_l subst t)

let instantiate_struct_member = instantiate_struct_member_a


let (pp_a,pp_l,pp_r,pp_c) =   
  let open Pp in
  let rec aux_c = function
    | Constraint (lc,t) ->
       let op = if !unicode then utf8string "\u{2227}" else slash ^^ backslash in
       (LC.pp false lc ^^^ op) :: aux_c t
    | I -> [!^"I"]
  in
  let rec aux_r = function
    | Resource (re,t) ->
       let op = if !unicode then utf8string "\u{2217}" else star in
       (RE.pp false re ^^^ op) :: aux_r t
    | C c -> aux_c c
  in
  let rec aux_l = function
    | Logical ((name,ls),t) ->
       let op = if !unicode then utf8string "\u{2203}" else !^"E" in
       (op ^^^ typ (Sym.pp name) (LS.pp false ls) ^^ dot) :: aux_l t
    | R r -> aux_r r
  in
  let aux_a = function
    | Computational ((name,bt),t) ->
       let op = if !unicode then utf8string "\u{03A3}" else !^"EC" in
       (op ^^^ typ (Sym.pp name) (BT.pp false bt) ^^ dot) :: aux_l t
  in
  let pp_a rt = flow (break 1) (aux_a rt) in
  let pp_l rt = flow (break 1) (aux_l rt) in
  let pp_r rt = flow (break 1) (aux_r rt) in
  let pp_c rt = flow (break 1) (aux_l rt) in
  (pp_a,pp_l,pp_r,pp_c)

let pp = pp_a




     
let rec concat_c (t1: c) (t2: c) : c =
  match t1 with
  | Constraint (bound,t) -> Constraint (bound, concat_c t t2)
  | I -> t2

let rec concat_r (t1: r) (t2: r) : r = 
  match t1, t2 with
  | Resource (bound1,t1), t2 -> Resource (bound1, concat_r t1 t2)
  | C _, Resource (bound2,t2) -> Resource (bound2, concat_r t1 t2)
  | C t1, C t2 -> C (concat_c t1 t2)

(* check variable freshness? *)
let rec concat_l (t1: l) (t2: l) : l = 
  match t1, t2 with
  | Logical (bound1,t1), t2 -> Logical (bound1, concat_l t1 t2)
  | R _, Logical (bound2,t2) -> Logical (bound2, concat_l t1 t2)
  | R t1, R t2 -> R (concat_r t1 t2)

let (@@) = concat_l




