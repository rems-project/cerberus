open Subst

module BT = BaseTypes
module IT = IndexTerms
module LS = LogicalSorts
module RE = Resources
module LC = LogicalConstraints
module AT = ArgumentTypes
module SymSet = Set.Make(Sym)



module Make (RT: AT.RT_Sig) = struct

  module UT = AT.Make(RT)

  type 'rt c = I of 'rt
             | Constraint of LC.t * 'rt c
  type 'rt r = C of 'rt c 
             | Resource of RE.t * 'rt r 
  type 'rt l = R of 'rt r
             | Logical of (Sym.t * LS.t) * 'rt l
  type 'rt a = L of 'rt l 
             | Computational of (Sym.t * BT.t) * 'rt a

  type 'rt t = 'rt a


  let mcomputational (name,bound) t = Computational ((name,bound),t)
  let mlogical (name,bound) t = Logical ((name,bound),t)
  let mconstraint bound t = Constraint (bound,t)
  let mresource bound t = Resource (bound,t)


  let rec subst_var_c substitution = function
    | Constraint (lc, t) -> 
       Constraint (LC.subst_var substitution lc, 
                   subst_var_c substitution t)
    | I rt -> I (RT.subst_var substitution rt)

  let rec subst_var_r substitution = function
    | Resource (re, t) ->
       Resource (RE.subst_var substitution re, 
                 subst_var_r substitution t)
    | C c -> C (subst_var_c substitution c)

  let rec subst_var_l substitution = function
    | Logical ((name,ls),t) -> 
       if Sym.equal name substitution.before then 
         Logical ((name,ls),t) 
       else if SymSet.mem name (IT.vars_in substitution.after) then
         let newname = Sym.fresh () in
         let t' = subst_var_l {before=name; after=S newname} t in
         let t'' = subst_var_l substitution t' in
         Logical ((newname,ls),t'')
       else
         let t' = subst_var_l substitution t in
         Logical ((name,ls),t')
    | R r -> R (subst_var_r substitution r)

  let rec subst_var_a substitution = function
    | Computational ((name,bt),t) -> 
       if Sym.equal name substitution.before then 
         Computational ((name,bt),t) 
       else if SymSet.mem name (IT.vars_in substitution.after) then
         let newname = Sym.fresh () in
         let t' = subst_var_a {before=name; after=S newname} t in
         let t'' = subst_var_a substitution t' in
         Computational ((newname,bt),t'')
       else
         Computational ((name,bt),subst_var_a substitution t)
    | L l -> L (subst_var_l substitution l)

  let subst_vars_l = Subst.make_substs subst_var_l
  let subst_vars_r = Subst.make_substs subst_var_r
  let subst_vars_c = Subst.make_substs subst_var_c
  let subst_vars_a = Subst.make_substs subst_var_a

  let subst_var = subst_var_a
  let subst_vars_a = subst_vars_a


  let rec instantiate_struct_member_c subst = function
    | Constraint (lc,t) ->
       Constraint (LC.instantiate_struct_member subst lc, 
                   instantiate_struct_member_c 
                     subst t)
    | I rt -> I (RT.instantiate_struct_member subst rt)

  let rec instantiate_struct_member_r subst = function
    | Resource (bound,t) -> 
       Resource (bound, 
                 instantiate_struct_member_r 
                   subst t)
    | C c -> C (instantiate_struct_member_c subst c)

  let rec instantiate_struct_member_l subst = function
    | Logical ((name,bound),t) -> 
       Logical ((name,bound),
                instantiate_struct_member_l 
                  subst t)
    | R r -> R (instantiate_struct_member_r subst r)

  let rec instantiate_struct_member_a subst = function
    | Computational ((name,bound),t) -> 
       Computational ((name,bound),
                      instantiate_struct_member_a 
                        subst t)
    | L l -> L (instantiate_struct_member_l subst l)




  let (pp_a,pp_l,pp_r,pp_c) =
    let open Pp in
    let rec aux_c = function
      | Constraint (lc,t) ->
         let op = equals ^^ rangle in
         (LC.pp false lc ^^^ op) :: aux_c t
      | I rt -> [RT.pp rt]
    in
    let rec aux_r = function
      | Resource (re,t) ->
         let op = if !unicode then equals ^^ utf8string "\u{2217}" else minus ^^ star in
         (RE.pp false re ^^^ op) :: aux_r t
      | C c -> aux_c c
    in
    let rec aux_l = function
      | Logical ((name,ls),t) ->
         let op = if !unicode then utf8string "\u{2200}" else !^"AL" in
         (op ^^^ typ (Sym.pp name) (LS.pp false ls) ^^ dot) :: aux_l t
      | R r -> aux_r r
    in
    let rec aux_a = function
      | Computational ((name,bt),t) ->
         let op = if !unicode then utf8string "\u{03A0}" else !^"AC" in
         (op ^^^ typ (Sym.pp name) (BT.pp false bt) ^^ dot) :: aux_a t
      | L l -> aux_l l
    in
    let pp_a t = flow (break 1) (aux_a t) in
    let pp_l t = flow (break 1) (aux_l t) in
    let pp_r t = flow (break 1) (aux_r t) in
    let pp_c t = flow (break 1) (aux_c t) in
    (pp_a,pp_l,pp_r,pp_c)

  let pp = pp_a


  let rec count_computational = function
    | Computational (_,t) -> 1 + count_computational t
    | L _ -> 0



  let normalise ft : ('rt t) = 
    let rec aux l r c = function
      | UT.Computational ((name,bt),ft) -> Computational ((name,bt), aux l r c ft)
      | UT.Logical ((name,ls),ft) -> aux (l@[(name,ls)]) r c ft
      | UT.Resource (re,ft) -> aux l (r@[re]) c ft
      | UT.Constraint (lc,ft) -> aux l r (c@[lc]) ft
      | UT.I i ->
         L ((List.fold_right mlogical l)
              (R ((List.fold_right mresource r)
                    (C (List.fold_right mconstraint c
                          (I i))))))
    in
    aux [] [] [] ft





  let rec unnormalise_c = function
    | Constraint (lc,t) -> UT.Constraint (lc,unnormalise_c t)
    | I rt -> UT.I rt

  let rec unnormalise_r = function
    | Resource (re,t) -> UT.Resource (re,unnormalise_r t)
    | C t -> unnormalise_c t

  let rec unnormalise_l = function
    | Logical ((name,ls),t) -> UT.Logical ((name,ls),unnormalise_l t)
    | R t -> unnormalise_r t

  let rec unnormalise_a = function
    | Computational ((name,bt),t) -> UT.Computational ((name,bt),unnormalise_a t)
    | L t -> unnormalise_l t

  let unnormalise = unnormalise_a

end
