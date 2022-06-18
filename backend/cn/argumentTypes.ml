open Locations
module BT = BaseTypes
module IT = IndexTerms
module LS = LogicalSorts
module RET = ResourceTypes
module LC = LogicalConstraints
module SymSet = Set.Make(Sym)

module LAT = LogicalArgumentTypes

type 'i t = 
  | Computational of (Sym.t * BT.t) * info * 'i t
  | L of 'i LAT.t


let mComputational (name, bound, info) t = 
  Computational ((name, bound), info, t)

let mComputationals t = 
  List.fold_right mComputational t


let rec subst i_subst =
  let rec aux (substitution: IT.t Subst.t) at =
    match at with
    | Computational ((name, bt), info, t) -> 
       let name, t = suitably_alpha_rename i_subst substitution.relevant (name, bt) t in
       Computational ((name, bt), info, aux substitution t)
    | L t -> 
       L (LAT.subst i_subst substitution t)
  in
  aux

and alpha_rename i_subst (s, ls) t = 
  let s' = Sym.fresh_same s in
  (s', subst i_subst (IT.make_subst [(s, IT.sym_ (s', ls))]) t)

and suitably_alpha_rename i_subst syms (s, ls) t = 
  if SymSet.mem s syms 
  then alpha_rename i_subst (s, ls) t
  else (s, t)



let pp i_pp ft = 
  let open Pp in
  let rec aux = function
    | Computational ((name, bt), _info, t) ->
       let op = if !unicode then utf8string "\u{03A0}" else !^"AC" in
       group (op ^^^ typ (Sym.pp name) (BT.pp bt) ^^ dot) :: aux t
    | L t -> 
       LAT.pp_aux i_pp t
  in
  flow (break 1) (aux ft)


let rec get_return = function
  | Computational (_, _, ft) -> get_return ft
  | L t -> LAT.get_return t


let rec count_computational = function
  | Computational (_, _, ft) -> 1 + count_computational ft
  | L _ -> 0


module LRT = LogicalReturnTypes
module RT = ReturnTypes


let alpha_unique ss =
  let rename_if ss = suitably_alpha_rename RT.subst ss in
  let rec f ss at =
    match at with
    | Computational ((name, bt), info, t) ->
       let name, t = rename_if ss (name, bt) t in
       let t = f (SymSet.add name ss) t in
       Computational ((name, bt), info, t)
    | L t ->
       L (LAT.alpha_unique ss t)
  in
  f ss





let of_rt (rt : RT.t) (rest : 'i LAT.t) : 'i t = 
  let (RT.Computational ((name, t), info, lrt)) = rt in
  Computational ((name, t), info, L (LAT.of_lrt lrt rest))



let rec map (f : 'i -> 'j) (at : 'i t) : 'j t =
  match at with
  | Computational (bound, info, at) -> 
     Computational (bound, info, map f at)
  | L t ->
     L (LAT.map f t)







type ift = IndexTerms.t t
type ft = ReturnTypes.t t
type lt = False.t t

