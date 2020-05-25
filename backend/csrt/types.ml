open Pp
open List


type t = ((Sym.t, VarTypes.t) Binders.t) list

let pp ts = flow_map (comma ^^ break 1) (Binders.pp Sym.pp VarTypes.pp) ts

let subst_var subst bs = 
  Binders.subst_list Sym.subst VarTypes.subst_var subst bs

let subst_vars = Tools.make_substs subst_var


let concretise_field subst t = 
 match t with
 | VarTypes.C t -> VarTypes.C (LogicalConstraints.concretise_field subst t)
 | _ -> t

let names t = List.map (fun {Binders.name; _} -> name) t

let rename newname t = 
  match t with
  | [] -> unsafe_warn !^"renaming empty return type"; []
  | {Binders.name; _} :: _ -> subst_var {substitute=name; swith=newname} t





let makeA name bt = Binders.{name; bound = VarTypes.A bt}
let makeL name ls = Binders.{name; bound = VarTypes.L ls}
let makeR name re = Binders.{name; bound = VarTypes.R re}
let makeC name lc = Binders.{name; bound = VarTypes.C lc}

let makeU t = Binders.{name = Sym.fresh (); bound = t}
let makeUA bt = makeA (Sym.fresh ()) bt
let makeUL bt = makeL (Sym.fresh ()) bt
let makeUR bt = makeR (Sym.fresh ()) bt
let makeUC bt = makeC (Sym.fresh ()) bt
