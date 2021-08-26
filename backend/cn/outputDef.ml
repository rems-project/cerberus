module IT = IndexTerms
module SymSet = Set.Make(Sym)

type entry = string * IndexTerms.t

let subst_entry substitution (name,it) = 
  (name, IT.subst substitution it)
  
let pp_entry (name, it) = 
  let open Pp in
  Pp.string name ^^^ !^"==" ^^^ IT.pp it


type t = entry list

let subst substitution assignment = 
  List.map (subst_entry substitution) assignment

let substs substs assignment = 
  Subst.make_substs subst substs assignment


let pp assignment =
  Pp.list pp_entry assignment
