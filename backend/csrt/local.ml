open Pp
open List
open Resultat
open TypeErrors

module BT = BaseTypes
module LS = LogicalSorts
module RE = Resources
module LC = LogicalConstraints
module SymSet = Set.Make(Sym)
module CF = Cerb_frontend
module Loc = Locations
module VB = VariableBinding


type binding = Sym.t * VB.t

type context_item = 
  | Binding of binding
  | Marker


(* left-most is most recent *)
type t = Local of context_item list

let empty = Local []

let marked = Local [Marker]

let concat (Local local') (Local local) = Local (local' @ local)




let pp_context_item ?(print_all_names = false) ?(print_used = false) = function
  | Binding (sym,binding) -> VB.pp ~print_all_names ~print_used (sym,binding)
  | Marker -> uformat [FG (Blue,Dark)] "\u{25CF}" 1 

(* reverses the list order for matching standard mathematical
   presentation *)
let pp ?(print_all_names = false) ?(print_used = false) (Local local) = 
  match local with
  | [] -> !^"(empty)"
  | _ -> flow_map (comma ^^ break 1) 
           (pp_context_item ~print_all_names ~print_used) 
           (rev local)






let wanted_but_found loc wanted found = 
  let err = match wanted with
  | `Computational -> !^"wanted computational variable but found" ^^^ VB.pp found
  | `Logical -> !^"wanted logical variable but found" ^^^ VB.pp found
  | `Resource -> !^"wanted resource variable but found" ^^^ VB.pp found
  | `Constraint -> !^"wanted resource variable but found" ^^^ VB.pp found
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



let all (Local local) =
  List.filter_map (function 
      | Binding b -> Some b 
      | Marker -> None
    ) local

let since (Local local) = 
  let rec aux = function
    | [] -> ([],[])
    | Marker :: rest -> ([],rest)
    | Binding (sym,b) :: rest -> 
       let (newl,oldl) = aux rest in
       ((sym,b) :: newl,oldl)
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
  let incompatible hint msymbols = 
    let symbols_hint = match msymbols with
      | Some (s1,s2) -> space ^^ parens (Sym.pp s1 ^^ slash ^^ Sym.pp s2)
      | None -> Pp.empty
    in
    unreachable (!^"trying to merge incompatible environments" ^^^ 
                   hint ^^ symbols_hint ^/^
                   (pp ~print_used:true ~print_all_names:true (Local l1)) ^^ 
                   hardline ^^ !^"and" ^^ hardline ^^ 
                   (pp ~print_used:true ~print_all_names:true (Local l2)))
  in
  let rec aux l1 l2 = 
    match l1, l2 with
    | [], [] -> return []
    | i1::l1, i2::l2 ->
       let* i = match i1, i2 with
         | Marker, Marker -> 
            return Marker
         | Binding (s1,vb1), Binding(s2,vb2) ->
            let* () = if Sym.equal s1 s2 then return () 
                      else fail loc (incompatible !^"binding name mismatch" (Some (s1,s2)))
            in
            let* vb = match vb1, vb2 with
              | VB.Computational (sl1,bt1), VB.Computational (sl2,bt2) ->
                 if Sym.equal sl1 sl2 && BT.equal bt1 bt2 
                 then return (VB.Computational (sl1,bt1))
                 else fail loc (incompatible !^"computational variable mismatch" (Some (s1,s2)))
              | VB.Logical ls1, VB.Logical ls2 ->
                 if LS.equal ls1 ls2 
                 then return (VB.Logical ls1)
                 else fail loc (incompatible !^"logical variable mismatch" (Some (s1,s2)))
              | VB.Resource re1, VB.Resource re2 ->
                 if RE.equal re1 re2 
                 then return (VB.Resource re1)
                 else fail loc (incompatible !^"resource mismatch" (Some (s1,s2)))
              | VB.UsedResource (re1,where1), VB.UsedResource (re2,where2) ->
                 if RE.equal re1 re2
                 then return (VB.UsedResource (re1,where1@where2))
                 else fail loc (incompatible !^"used resource mismatch" (Some (s1,s2)))
              | VB.Constraint lc1, VB.Constraint lc2 ->
                 if LC.equal lc1 lc2 
                 then return (VB.Constraint lc1)
                 else fail loc (incompatible !^"constraint mismatch" (Some (s1,s2)))
              | VB.Resource re, VB.UsedResource (used_re,where) 
              | VB.UsedResource (used_re,where), VB.Resource re
                   when RE.equal used_re re ->
                 fail loc (Unused_resource {resource=re;is_merge=true})
              | _ ->
                 fail loc (incompatible !^"variable binding kind mismatch" (Some (s1,s2)))
            in
            return (Binding (s1,vb))
         | Marker, Binding (_,_)
         | Binding (_,_), Marker ->
            fail loc (incompatible !^"marker/binding mismatch" None)
       in
       let* l = aux l1 l2 in
       return (i :: l)
    | _, _ -> 
       fail loc (incompatible !^"length mismatch" None)
  in
  let* l = aux l1 l2 in
  return (Local l)

let big_merge (loc: Loc.t) (local: t) (locals: t list) : t m = 
  ListM.fold_leftM (merge loc) local locals


let mA sym (bt,lname) = (sym, VB.Computational (lname,bt))
let mL sym ls = (sym, VB.Logical ls)
let mR sym re = (sym, VB.Resource re)
let mC sym lc = (sym, VB.Constraint lc)
let mUR re = mR (Sym.fresh ()) re
let mUC lc = mC (Sym.fresh ()) lc





let get_a (loc : Loc.t) (name: Sym.t) (local:t)  = 
  let* b = get loc name local in
  match b with 
  | Computational (lname,bt) -> return (bt,lname)
  | _ -> wanted_but_found loc `Computational (name,b)

let get_l (loc : Loc.t) (name: Sym.t) (local:t) = 
  let* b = get loc name local in
  match b with 
  | Logical ls -> return ls
  | _ -> wanted_but_found loc `Logical (name,b)

let get_r (loc : Loc.t) (name: Sym.t) (local:t) = 
  let* b = get loc name local in
  match b with 
  | Resource re -> return re
  | _ -> wanted_but_found loc `Resource (name,b)

let get_c (loc : Loc.t) (name: Sym.t) (local:t) = 
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


let (++) = concat







