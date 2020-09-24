open Subst

module BT = BaseTypes
module IT = IndexTerms
module LS = LogicalSorts
module RE = Resources
module LC = LogicalConstraints
module SymSet = Set.Make(Sym)


module type RT_Sig = sig
  type t
  val subst_var: (Sym.t,IT.t) Subst.t -> t -> t
  val free_vars: t -> SymSet.t
  val instantiate_struct_member: (IT.t,IT.t) Subst.t -> t -> t
  val pp: t -> Pp.document
end

module Make (RT: RT_Sig) = struct


type t = 
  | Computational of (Sym.t * BT.t) * t
  | Logical of (Sym.t * LS.t) * t
  | Resource of RE.t * t
  | Constraint of LC.t * t
  | I of RT.t



let mComputational (name, bound) t = Computational ((name,bound),t)
let mLogical (name, bound) t = Logical ((name,bound),t)
let mConstraint bound t = Constraint (bound,t)
let mResource bound t = Resource (bound,t)



  let rec subst_var substitution = function
    | Computational ((name,bt),t) -> 
       if Sym.equal name substitution.before then 
         Computational ((name,bt),t) 
       else if SymSet.mem name (IT.vars_in substitution.after) then
         let newname = Sym.fresh () in
         let t' = subst_var {before=name; after=S newname} t in
         let t'' = subst_var substitution t' in
         Computational ((newname,bt),t'')
       else
         Computational ((name,bt),subst_var substitution t)
    | Logical ((name,ls),t) -> 
       if Sym.equal name substitution.before then 
         Logical ((name,ls),t) 
       else if SymSet.mem name (IT.vars_in substitution.after) then
         let newname = Sym.fresh () in
         let t' = subst_var {before=name; after=S newname} t in
         let t'' = subst_var substitution t' in
         Logical ((newname,ls),t'')
       else
         let t' = subst_var substitution t in
         Logical ((name,ls),t')
    | Resource (re,t) -> 
       let re = RE.subst_var substitution re in
       let t = subst_var substitution t in
       Resource (re,t)
    | Constraint (lc,t) -> 
       let lc = LC.subst_var substitution lc in
       let t = subst_var substitution t in
       Constraint (lc,t)
    | I i -> I (RT.subst_var substitution i)

  let subst_vars = make_substs subst_var

  let rec instantiate_struct_member subst = function
    | Computational ((name,bound),t) -> 
       Computational ((name,bound),
                      instantiate_struct_member subst t)
    | Logical ((name,bound),t) -> 
       Logical ((name,bound),
                instantiate_struct_member subst t)
    | Resource (bound,t) -> 
       Resource (bound, instantiate_struct_member subst t)
    | Constraint (bound,t) -> 
       Constraint (LC.instantiate_struct_member subst bound, 
                   instantiate_struct_member subst t)
    | I i -> 
       I (RT.instantiate_struct_member subst i)

  let rec free_vars = function
    | Computational ((sym,_),t) -> SymSet.remove sym (free_vars t)
    | Logical ((sym,_),t) -> SymSet.remove sym (free_vars t)
    | Resource (r,t) -> SymSet.union (RE.vars_in r) (free_vars t)
    | Constraint (c,t) -> SymSet.union (LC.vars_in c) (free_vars t)
    | I i -> RT.free_vars i


  let pp ft = 
    let open Pp in
    let rec aux = function
      | Computational ((name,bt),t) ->
         let op = if !unicode then utf8string "\u{03A0}" else !^"AC" in
         (op ^^^ typ (Sym.pp name) (BT.pp false bt) ^^ dot) :: aux t
      | Logical ((name,ls),t) ->
         let op = if !unicode then utf8string "\u{2200}" else !^"AL" in
         (op ^^^ typ (Sym.pp name) (LS.pp false ls) ^^ dot) :: aux t
      | Resource (re,t) ->
         let op = if !unicode then equals ^^ utf8string "\u{2217}" else minus ^^ star in
         (RE.pp re ^^^ op) :: aux t
      | Constraint (lc,t) ->
         let op = equals ^^ rangle in
         (LC.pp false lc ^^^ op) :: aux t
      | I i -> 
         [RT.pp i]
    in
    flow (break 1) (aux ft)


let rec get_return = function
  | Computational (_,ft) -> get_return ft
  | Logical (_,ft) -> get_return ft
  | Resource (_,ft) -> get_return ft
  | Constraint (_,ft) -> get_return ft
  | I rt -> rt


let rec count_computational = function
  | Computational (_,ft) -> 
     1 + count_computational ft
  | Logical (_,ft) 
    | Resource (_,ft)
    | Constraint (_,ft) -> 
     count_computational ft
  | I _ -> 0


end
