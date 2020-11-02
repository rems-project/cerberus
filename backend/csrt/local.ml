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






let get (loc : Loc.t) (sym: Sym.t) (Local local) : VB.t m =
  let rec aux = function
  | Binding (sym',b) :: _ when Sym.equal sym' sym -> return b
  | _ :: local -> aux local
  | [] -> fail loc (Unbound_name (Sym sym))
  in
  aux local


let add (name, b) (Local e) = Local (Binding (name, b) :: e)

let remove (loc : Loc.t) (sym: Sym.t) (Local local) : t m = 
  let rec aux = function
  | Binding (sym',_) :: rest when Sym.equal sym sym' -> return rest
  | i::rest -> let* rest' = aux rest in return (i::rest')
  | [] -> fail loc (Unbound_name (Sym sym))
  in
  let* local = aux local in
  return (Local local)

let use_resource loc sym where (Local local) = 
  let rec aux = function
  | Binding (sym',b) :: rest when Sym.equal sym sym' -> 
     begin match b with
     | Resource re -> 
        return (Binding (sym', UsedResource (re,where)) :: rest)
     | _ ->
        fail loc (Kind_mismatch {expect = KResource; has = VB.kind b})
     end
  | i::rest -> let* rest' = aux rest in return (i::rest')
  | [] -> fail loc (Unbound_name (Sym sym))
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



let incompatible_environments loc l1 l2=
  let msg = 
    !^"Merging incompatible contexts." ^^^ 
      item "ctxt1" (pp ~print_used:true ~print_all_names:true l1) ^/^
      item "ctxt2" (pp ~print_used:true ~print_all_names:true l2)
  in
  fail loc (Internal msg)

let merge loc (Local l1) (Local l2) =
  let incompatible () = incompatible_environments loc (Local l1) (Local l2) in
  let merge_ci = function
    | (Marker, Marker) -> return Marker
    | (Binding (s1,vb1), Binding(s2,vb2)) ->
       begin match Sym.equal s1 s2, VB.agree vb1 vb2 with
       | true, Some vb -> return (Binding (s1,vb))
       | _ -> incompatible ()
       end
    | (Marker, Binding (_,_)) -> incompatible ()
    | (Binding (_,_), Marker) -> incompatible ()
  in
  if List.length l1 <> List.length l2 then incompatible () else 
    let* l = ListM.mapM merge_ci (List.combine l1 l2) in
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
  | _ -> fail loc (Kind_mismatch {expect = KComputational; has = VB.kind b})

let get_l (loc : Loc.t) (name: Sym.t) (local:t) = 
  let* b = get loc name local in
  match b with 
  | Logical ls -> return ls
  | _ -> fail loc (Kind_mismatch {expect = KLogical; has = VB.kind b})

let get_r (loc : Loc.t) (name: Sym.t) (local:t) = 
  let* b = get loc name local in
  match b with 
  | Resource re -> return re
  | _ -> fail loc (Kind_mismatch {expect = KResource; has = VB.kind b})

let get_c (loc : Loc.t) (name: Sym.t) (local:t) = 
  let* b = get loc name local in
  match b with 
  | Constraint lc -> return lc
  | _ -> fail loc (Kind_mismatch {expect = KConstraint; has = VB.kind b})

let removeS loc syms (local: t) = 
  ListM.fold_leftM (fun local sym -> remove loc sym local) local syms

let add_a aname (bt,lname) = add (aname, Computational (lname,bt))
let add_l lname ls         = add (lname, Logical ls)
let add_r rname re         = add (rname, Resource re)
let add_c cname lc         = add (cname, Constraint lc)
let add_ur re = add_r (Sym.fresh ()) re
let add_uc lc = add_c (Sym.fresh ()) lc


let filter p (Local e) = 
  filter_map (function Binding (sym,b) -> p sym b | _ -> None) e

let filterM p (Local e) = 
  ListM.filter_mapM (function Binding (sym,b) -> p sym b | _ -> return None) e

let all_constraints local = 
  filter (fun _ b ->
      match b with
      | Constraint lc -> Some lc
      | _ -> None
    ) local



let (++) = concat

let all_names = filter (fun sym _ -> Some sym)
