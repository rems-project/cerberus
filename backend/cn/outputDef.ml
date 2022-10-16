module IT = IndexTerms
module SymSet = Set.Make(Sym)

type entry = {
    loc : Locations.t;
    name : Sym.t;
    value : IndexTerms.t;
  }

let subst_entry substitution {loc; name; value} = 
  {loc; name; value = IT.subst substitution value}
  
let pp_entry {loc; name; value} = 
  let open Pp in
  Sym.pp name ^^^ !^"==" ^^^ IT.pp value


type t = entry list

let subst substitution assignment = 
  List.map (subst_entry substitution) assignment


let to_record (entries : t) =
  IT.record_ (List.map (fun o -> (o.name, o.value)) entries)



let pp assignment =
  Pp.list pp_entry assignment
