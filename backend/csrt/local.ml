open Pp
open List
open Result
open TypeErrors

module BT = BaseTypes
module LS = LogicalSorts
module RE = Resources
module LC = LogicalConstraints
module SymSet = Set.Make(Sym)
module CF = Cerb_frontend
module Loc = Locations
module VB = VariableBinding


type binding

type context_item = 
  | Binding of Sym.t * VB.t
  | Marker of Sym.t


type t = Local of context_item list

let empty = Local []

let marked sym = Local [Marker sym]

let concat (Local local') (Local local) = Local (local' @ local)








let wanted_but_found loc wanted found = 
  let err = match wanted with
  | `Computational -> !^"wanted computational variable but found" ^^^ VB.pp true found
  | `Logical -> !^"wanted logical variable but found" ^^^ VB.pp true found
  | `Resource -> !^"wanted resource variable but found" ^^^ VB.pp true found
  | `Constraint -> !^"wanted resource variable but found" ^^^ VB.pp true found
  in
  fail loc (unreachable err)



let get (loc : Loc.t) (sym: Sym.t) (Local local) : VB.t m =
  let rec aux = function
  | Binding (sym',b) :: _ when Sym.equal sym' sym -> return b
  | _ :: local -> aux local
  | [] -> fail loc (Unbound_name sym)
  in
  aux local


let add (name, b) (Local e) = Local (Binding (name, b) :: e)

let remove (loc : Loc.t) (sym: Sym.t) (Local local) : t m = 
  let rec aux = function
  | Binding (sym',_) :: rest when Sym.equal sym sym' -> return rest
  | i::rest -> let* rest' = aux rest in return (i::rest')
  | [] -> fail loc (Unbound_name sym)
  in
  let* local = aux local in
  return (Local local)

let use_resource loc sym where (Local local) = 
  let rec aux = function
  | Binding (sym',b) :: rest when Sym.equal sym sym' -> 
     begin match b with
     | Resource re -> return (Binding (sym',UsedResource (re,where)) :: rest)
     | UsedResource (re,where) -> fail loc (Resource_already_used (re,where))
     | b -> wanted_but_found loc `Resource (sym,b)
     end
  | i::rest -> let* rest' = aux rest in return (i::rest')
  | [] -> fail loc (Unbound_name sym)
  in
  let* local = aux local in
  return (Local local)



let since msym (Local local) = 
  let rec aux local =
    match msym, local with
    | _, [] -> ([],[])
    | _, Binding (sym,b) :: rest -> 
       let (newl,oldl) = aux rest in
       ((sym,b) :: newl,oldl)
    | Some sym, Marker sym' :: rest when Sym.equal sym sym' ->
       ([],rest)
    | _, Marker _ :: rest ->
       aux rest
  in
  let (newl,oldl) = (aux local) in
  (newl, Local oldl)



let is_bound sym (Local local) =
  List.exists 
    (function 
     | Binding (sym',_) -> Sym.equal sym' sym 
     | _ -> false
    ) local



let merge loc (Local l1) (Local l2) =
  let incompatible = unreachable !^"trying to merge incompatible environments" in
  let rec aux l1 l2 = 
    match l1, l2 with
    | [], [] -> return []
    | i1::l1, i2::l2 ->
       let* i = match i1, i2 with
         | Marker sym, Marker sym' when Sym.equal sym sym' -> 
            return (Marker sym)
         | Binding (s1,vb1), Binding(s2,vb2) when Sym.equal s1 s2 ->
            let* vb = match vb1, vb2 with
              | VB.Computational (sl1,bt1), VB.Computational (sl2,bt2) 
                   when Sym.equal sl1 sl2 && BT.equal bt1 bt2 ->
                 return (VB.Computational (sl1,bt1))
              | VB.Logical ls1, VB.Logical ls2  
                   when LS.equal ls1 ls2 ->
                 return (VB.Logical ls1)
              | VB.Resource re1, VB.Resource re2 
                   when RE.equal re1 re2 -> 
                 return (VB.Resource re1)
              | VB.UsedResource (re1,where1), VB.UsedResource (re2,where2) 
                   when RE.equal re1 re2 ->
                 return (VB.UsedResource (re1,where1@where2))
              | VB.Constraint lc1, VB.Constraint lc2 
                   when LC.equal lc1 lc2 ->
                 return (VB.Constraint lc1)
              | VB.Resource re, VB.UsedResource (used_re,where) 
              | VB.UsedResource (used_re,where), VB.Resource re
                   when RE.equal used_re re ->
                 fail loc (Unused_resource {resource=re;is_merge=true})
              | _ -> 
                 fail loc incompatible
            in
            return (Binding (s1,vb))
         | _ -> 
            fail loc incompatible
       in
       let* l = aux l1 l2 in
       return (i :: l)
    | _, _ -> 
       fail loc incompatible
  in
  let* l = aux l1 l2 in
  return (Local l)



let mA sym (bt,lname) = (sym, VB.Computational (lname,bt))
let mL sym ls = (sym, VB.Logical ls)
let mR sym re = (sym, VB.Resource re)
let mC sym lc = (sym, VB.Constraint lc)
let mUR re = mR (Sym.fresh ()) re
let mUC lc = mC (Sym.fresh ()) lc


let pp_context_item print_used = function
  | Binding (sym,binding) -> VB.pp print_used (sym,binding)
  | Marker sym -> 
     fancystring (Colour.ansi_format [Blue] "\u{25CF}") 2 ^^ parens (Sym.pp sym)

let pp (Local local) = 
  match local with
  | [] -> !^"(empty)"
  | _ -> flow_map (comma ^^ break 1) (pp_context_item false) (rev local)





let get_a (loc : Loc.t) (name: Sym.t) local = 
  let* b = get loc name local in
  match b with 
  | Computational (lname,bt) -> return (bt,lname)
  | _ -> wanted_but_found loc `Computational (name,b)

let get_l (loc : Loc.t) (local:t) (name: Sym.t) = 
  let* b = get loc name local in
  match b with 
  | Logical ls -> return ls
  | _ -> wanted_but_found loc `Logical (name,b)

let get_r (loc : Loc.t) local (name: Sym.t) = 
  let* b = get loc name local in
  match b with 
  | Resource re -> return re
  | _ -> wanted_but_found loc `Resource (name,b)

let get_c (loc : Loc.t) local (name: Sym.t) = 
  let* b = get loc name local in
  match b with 
  | Constraint lc -> return lc
  | _ -> wanted_but_found loc `Resource (name,b)

let removeS loc syms (local: t) = 
  ListM.fold_leftM (fun local sym -> remove loc sym local) local syms

let addA aname (bt,lname) = add (aname, Computational (lname,bt))
let addL lname ls         = add (lname, Logical ls)
let addR rname re         = add (rname, Resource re)
let addC cname lc         = add (cname, Constraint lc)
let addUR re = addR (Sym.fresh ()) re
let addUC lc = addC (Sym.fresh ()) lc


let filter p (Local e) = 
  filter_map (function Binding (sym,b) -> p sym b | _ -> None) e

let all_constraints local = 
  filter (fun _ b ->
      match b with
      | Constraint lc -> Some lc
      | _ -> None
    ) local

let filterM p (Local e) = 
  ListM.filter_mapM (function Binding (sym,b) -> p sym b | _ -> return None) e


let filter_a p (local : t) = 
  filter (fun sym b -> 
      match b with
      | Computational (lname,bt) -> p sym lname bt
      | _ -> None
    )
    local

let filter_r p (local : t) = 
  filter (fun sym b -> 
      match b with
      | Resource t -> p sym t
      | _ -> None
    )
    local

let filter_rM p (local : t) = 
  filterM (fun sym b -> 
      match b with
      | Resource t -> p sym t
      | _ -> return None
    )
    local


let all_a = filter_a (fun s _ _ -> Some s) 
let all_r = filter_r (fun s _ -> Some s) 

let (++) = concat






