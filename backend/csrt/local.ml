open Pp
open List
open Except
open TypeErrors

module SymSet = Set.Make(Sym)
module CF = Cerb_frontend
module Loc = Locations
module VB = VariableBinding


type binding

type context_item = 
  | Binding of Sym.t * VB.t
  | Marker


type t = Local of context_item list

let empty = Local []

let mark = Local [Marker]

let concat (Local local') (Local local) = Local (local' @ local)








let wanted_but_found loc wanted found = 
  let err = match wanted with
  | `Computational -> !^"wanted computational variable but found" ^^^ VB.pp true found
  | `Logical -> !^"wanted logical variable but found" ^^^ VB.pp true found
  | `Resource -> !^"wanted resource variable but found" ^^^ VB.pp true found
  | `Constraint -> !^"wanted resource variable but found" ^^^ VB.pp true found
  in
  fail loc (Unreachable err)



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
     | UsedResource (re,_) -> fail loc (Unreachable (!^"resource already used" ^^^ VB.pp true (sym,b)))
     | b -> wanted_but_found loc `Resource (sym,b)
     end
  | i::rest -> let* rest' = aux rest in return (i::rest')
  | [] -> fail loc (Unbound_name sym)
  in
  let* local = aux local in
  return (Local local)



let new_old (Local local) = 
  let rec aux = function
    | [] -> ([],[])
    | Binding (sym,b) :: rest -> 
       let (newl,oldl) = aux rest in
       ((sym,b) :: newl,oldl)
    | Marker :: rest ->
       ([],rest)
  in
  let (newl,oldl) = (aux local) in
  (newl, Local oldl)

let ensure_resource_used loc local sym = 
  let* b = get loc sym local in
  match b with
  | Resource re -> fail loc (Generic_error (!^"leftover unused resource" ^^^ VB.pp true (sym,b)))
  | UsedResource (re,where) -> return ()
  | _ -> wanted_but_found loc `Resource (sym,b)

let ensure_resources_used loc local syms = 
  fold_leftM (fun () sym -> ensure_resource_used loc local sym) () syms


let is_bound sym (Local local) =
  List.exists 
    (function 
     | Binding (sym',_) -> Sym.equal sym' sym 
     | _ -> false
    ) local





(* derived *)

let mA sym (bt,lname) = (sym, VB.Computational (lname,bt))
let mL sym ls = (sym, VB.Logical ls)
let mR sym re = (sym, VB.Resource re)
let mC sym lc = (sym, VB.Constraint lc)
let mUR re = mR (Sym.fresh ()) re
let mUC lc = mC (Sym.fresh ()) lc


let pp_context_item print_used = function
  | Binding (sym,binding) -> VB.pp print_used (sym,binding)
  | Marker -> fancystring (Colour.ansi_format [Magenta] "\u{2B1B}") 2

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
  fold_leftM (fun local sym -> remove loc sym local) local syms

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
  filter_mapM (function Binding (sym,b) -> p sym b | _ -> return None) e


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






