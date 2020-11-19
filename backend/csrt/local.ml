open Pp
open List

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




let unbound_internal_error sym = 
  Debug_ocaml.error ("unbound symbol " ^ Sym.pp_string sym)


let kind_mismatch_internal_error ~expect ~has =
  let err = 
    "Expected" ^ (plain (VariableBinding.kind_pp expect)) ^
      "but found" ^ (plain (VariableBinding.kind_pp has))
  in
  Debug_ocaml.error err





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




(* internal *)
let get (sym: Sym.t) (Local local) : VB.t =
  let rec aux = function
  | Binding (sym',b) :: _ when Sym.equal sym' sym -> b
  | _ :: local -> aux local
  | [] -> unbound_internal_error sym
  in
  aux local


(* internal *)
let add (name, b) (Local e) = Local (Binding (name, b) :: e)

(* let remove (sym: Sym.t) (Local local) : t = 
 *   let rec aux = function
 *   | Binding (sym',_) :: rest when Sym.equal sym sym' -> rest
 *   | i :: rest -> i :: aux rest
 *   | [] -> unbound_internal_error sym
 *   in
 *   Local (aux local) *)

let filter p (Local e) = 
  filter_map (function Binding (sym,b) -> p sym b | _ -> None) e

(* let filterM p (Local e) = 
 *   ListM.filter_mapM (function Binding (sym,b) -> p sym b | _ -> None) e *)

let all_computational local = 
  filter (fun name b ->
      match b with
      | Computational (lname, b) -> Some (name, (lname, b))
      | _ -> None
    ) local

let all_logical local = 
  filter (fun name b ->
      match b with
      | Logical ls -> Some (name, ls)
      | _ -> None
    ) local

let all_resources local = 
  filter (fun name b ->
      match b with
      | Resource re -> Some (name, re)
      | _ -> None
    ) local

let all_used_resources local = 
  filter (fun name b ->
      match b with
      | UsedResource (re,where) -> Some (name, re, where)
      | _ -> None
    ) local

let all_constraints local = 
  filter (fun _ b ->
      match b with
      | Constraint lc -> Some lc
      | _ -> None
    ) local







let use_resource sym where (Local local) = 
  let rec aux = function
  | Binding (sym',b) :: rest when Sym.equal sym sym' -> 
     begin match b with
     | Resource re -> Binding (sym', UsedResource (re,where)) :: rest
     | _ -> kind_mismatch_internal_error ~expect:KResource ~has:(VB.kind b)
     end
  | i :: rest -> i :: aux rest
  | [] -> unbound_internal_error sym
  in
  Local (aux local)



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



let bound_to sym (Local local) = 
  let rec aux = function
    | [] -> None
    | Binding (sym',binding) :: rest ->
       if Sym.equal sym' sym then Some binding
       else aux rest
    | Marker :: rest -> aux rest
  in
  aux local



let incompatible_environments l1 l2 =
  let msg = 
    !^"Merging incompatible contexts." ^/^ 
      item "ctxt1" (pp ~print_used:true ~print_all_names:true l1) ^/^
      item "ctxt2" (pp ~print_used:true ~print_all_names:true l2)
  in
  Debug_ocaml.error (plain msg)

let merge (Local l1) (Local l2) =
  let incompatible () = incompatible_environments (Local l1) (Local l2) in
  let merge_ci = function
    | (Marker, Marker) -> Marker
    | (Binding (s1,vb1), Binding(s2,vb2)) ->
       begin match Sym.equal s1 s2, VB.agree vb1 vb2 with
       | true, Some vb -> Binding (s1,vb)
       | _ -> incompatible ()
       end
    | (Marker, Binding (_,_)) -> incompatible ()
    | (Binding (_,_), Marker) -> incompatible ()
  in
  if List.length l1 <> List.length l2 then incompatible () else 
    Local (List.map merge_ci (List.combine l1 l2))


let big_merge (local: t) (locals: t list) : t = 
  List.fold_left merge local locals


let mA sym (bt,lname) = (sym, VB.Computational (lname,bt))
let mL sym ls = (sym, VB.Logical ls)
let mR sym re = (sym, VB.Resource re)
let mC sym lc = (sym, VB.Constraint lc)
let mUR re = mR (Sym.fresh ()) re
let mUC lc = mC (Sym.fresh ()) lc





let get_a (name: Sym.t) (local:t)  = 
  match get name local with 
  | Computational (lname,bt) -> (bt,lname)
  | b -> kind_mismatch_internal_error ~expect:KComputational ~has:(VB.kind b)

let get_l (name: Sym.t) (local:t) = 
  match get name local with 
  | Logical ls -> ls
  | b -> kind_mismatch_internal_error ~expect:KLogical ~has:(VB.kind b)

let get_r (name: Sym.t) (local:t) = 
  match get name local with 
  | Resource re -> re
  | b -> kind_mismatch_internal_error ~expect:KResource ~has:(VB.kind b)

let get_c (name: Sym.t) (local:t) = 
  match get name local with 
  | Constraint lc -> lc
  | b -> kind_mismatch_internal_error ~expect:KConstraint ~has:(VB.kind b)


let add_a aname (bt,lname) = 
  add (aname, Computational (lname,bt))

let add_l lname ls local = 
  add (lname, Logical ls) local

let add_c cname lc local = 
  add (cname, Constraint lc) local

let add_uc lc local = 
  add_c (Sym.fresh ()) lc local


let add_r rname r local = 
  let lcs = match RE.fp r with
    | None -> []
    | Some fp ->
       List.filter_map (fun (_,r') -> 
           Option.bind (RE.fp r') (fun fp' -> Some (IndexTerms.Disjoint (fp, fp')))
         ) (all_resources local) 
  in
  add_uc (LC (And lcs)) (add (rname, Resource r) local)

let add_ur re local = 
  add_r (Sym.fresh ()) re local






let (++) = concat

let all_names = filter (fun sym _ -> Some sym)









  
