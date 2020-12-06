open Pp
open List

module BT = BaseTypes
module LS = LogicalSorts
module RE = Resources
module LC = LogicalConstraints
module SymSet = Set.Make(Sym)
module CF = Cerb_frontend
module Loc = Locations
module IT = IndexTerms





module VariableBinding = struct

  open Kind

  type t =
    | Computational of Sym.t * BT.t
    | Logical of LS.t
    | Resource of RE.t
    | UsedResource of RE.t * Loc.t list
    | Constraint of LC.t


  let kind = function
    | Computational _ -> KComputational
    | Logical _ -> KLogical
    | Resource _ -> KResource
    | Constraint _ -> KConstraint
    | UsedResource _ -> KUsedResource 




  let pp ?(print_all_names = false) ?(print_used = false) (sym,binding) =
    let btyp sym pped = 
      format [Pp.FG(Default,Bright)] (Sym.pp_string sym) ^^ colon ^^ pped in
    match binding with
    | Computational (lname,bt) -> 
       btyp sym (BT.pp true bt ^^ tilde ^^ Sym.pp lname)
    | Logical ls -> 
       btyp sym (LS.pp false ls)
    | Resource re -> 
       if print_all_names 
       then btyp sym (squotes (RE.pp re))
       else squotes (RE.pp re)
    | UsedResource (re,_locs) -> 
       if not print_used then underscore 
       else if print_all_names 
       then btyp sym (!^"used" ^^^ (squotes (RE.pp re)))
       else !^"used" ^^^ squotes (RE.pp re)
    | Constraint lc -> 
       if print_all_names 
       then btyp sym (LC.pp lc)
       else LC.pp lc

  (* let json_computational (sym, (lname, bt)) = 
   *   let args = `Assoc [("basetype", BT.json bt); ("logical", Sym.json lname)] in
   *   let bound = `Variant ("Computational", args) in
   *   (Sym.json sym, bound)
   * 
   * let json_logical (sym, ls) = 
   *   let args = LS.json ls in
   *   (Sym.json sym, `Variant ("Logical", args))
   * 
   * let json_resource (_sym, re) = 
   *   let args = RE.json re in
   *   (`Null, `Variant ("Resource", args))
   * 
   * let json_used_resource (_sym, (re, where)) = 
   *   let args = 
   *     `Assoc [("used", List.json Loc.json_loc where); 
   *             ("resource", RE.json re)] in
   *   (`Null, `Variant ("UsedResource", args))
   * 
   * let json_constraint (_sym, lc) = 
   *   let args = LC.json lc in
   *   (`Null, `Variant ("Constraint", args))
   * 
   * 
   * let json (sym, binding) = 
   *   let (name,bound) = 
   *     match binding with
   *     | Computational (lname,bt) -> json_computational (sym, (lname, bt))
   *     | Logical ls -> json_logical (sym, ls)
   *     | Resource re -> json_resource (sym, re)
   *     | UsedResource (re,locs) -> json_used_resource (sym, (re, locs))
   *     | Constraint lc -> json_constraint (sym, lc)
   *   in
   *   `Assoc [
   *       ("name", `String (Sym.pp_string sym));
   *       ("bound", bound);
   *       ] *)



  let agree vb1 vb2 = 
    match vb1, vb2 with
    | Computational (l1,bt1), Computational (l2,bt2)
         when Sym.equal l1 l2 && BT.equal bt1 bt2 -> 
       Some (Computational (l1,bt1))
    | Logical ls1, Logical ls2 
         when LS.equal ls1 ls2 -> 
       Some (Logical ls1)
    | Constraint lc1, Constraint lc2
           when LC.equal lc1 lc2 ->
       Some (Constraint lc1)
    | Resource re1, Resource re2 
         when RE.equal re1 re2 ->
       Some (Resource re1)
    | UsedResource (re1,locs1), UsedResource (re2,locs2)
           when RE.equal re1 re2 ->
       Some (UsedResource (re1, locs1 @ locs2))
    | _, _ ->
       None

end





type binding = Sym.t * VariableBinding.t

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
    "Expected" ^ (plain (Kind.pp expect)) ^
      "but found" ^ (plain (Kind.pp has))
  in
  Debug_ocaml.error err





let pp_context_item ?(print_all_names = false) ?(print_used = false) = function
  | Binding (sym,binding) -> VariableBinding.pp ~print_all_names ~print_used (sym,binding)
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
let get (sym: Sym.t) (Local local) : VariableBinding.t =
  let rec aux = function
  | Binding (sym',b) :: _ when Sym.equal sym' sym -> b
  | _ :: local -> aux local
  | [] -> unbound_internal_error sym
  in
  aux local


(* internal *)
let add (name, b) (Local e) = Local (Binding (name, b) :: e)

let filter p (Local e) = 
  filter_map (function Binding (sym,b) -> p sym b | _ -> None) e


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
      | Resource re -> Some re
      | _ -> None
    ) local

let all_named_resources local = 
  filter (fun name b ->
      match b with
      | Resource re -> Some (name, re)
      | _ -> None
    ) local


let all_used_resources local = 
  filter (fun name b ->
      match b with
      | UsedResource (re,where) -> Some (re, where)
      | _ -> None
    ) local

let all_named_used_resources local = 
  filter (fun name b ->
      match b with
      | UsedResource (re,where) -> Some (name, (re, where))
      | _ -> None
    ) local


let all_constraints local = 
  filter (fun name b ->
      match b with
      | Constraint lc -> Some (lc)
      | _ -> None
    ) local


let all_named_constraints local = 
  filter (fun name b ->
      match b with
      | Constraint lc -> Some (name, lc)
      | _ -> None
    ) local







let use_resource sym where (Local local) = 
  let rec aux = function
  | Binding (sym',b) :: rest when Sym.equal sym sym' -> 
     begin match b with
     | Resource re -> Binding (sym', UsedResource (re,where)) :: rest
     | _ -> kind_mismatch_internal_error 
              ~expect:KResource ~has:(VariableBinding.kind b)
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



let kind sym (Local local) = 
  let rec aux = function
    | [] -> None
    | Binding (sym',binding) :: rest ->
       if Sym.equal sym' sym 
       then Some (VariableBinding.kind binding)
       else aux rest
    | Marker :: rest -> aux rest
  in
  aux local

let bound sym local = 
  Option.is_some (kind sym local)



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
       begin match Sym.equal s1 s2, VariableBinding.agree vb1 vb2 with
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




let get_a (name: Sym.t) (local:t)  = 
  match get name local with 
  | Computational (lname,bt) -> (bt,lname)
  | b -> kind_mismatch_internal_error 
           ~expect:KComputational ~has:(VariableBinding.kind b)

let get_l (name: Sym.t) (local:t) = 
  match get name local with 
  | Logical ls -> ls
  | b -> kind_mismatch_internal_error 
           ~expect:KLogical ~has:(VariableBinding.kind b)

let get_r (name: Sym.t) (local:t) = 
  match get name local with 
  | Resource re -> re
  | b -> kind_mismatch_internal_error 
           ~expect:KResource ~has:(VariableBinding.kind b)

let get_c (name: Sym.t) (local:t) = 
  match get name local with 
  | Constraint lc -> lc
  | b -> kind_mismatch_internal_error 
           ~expect:KConstraint ~has:(VariableBinding.kind b)


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
    | Some ((addr,_) as fp) ->
       IT.Not (IT.Null addr) ::
       List.filter_map (fun r' -> 
           Option.bind (RE.fp r') (fun fp' -> 
               Some (IT.Disjoint (fp, fp'))
             )
         ) (all_resources local) 
  in
  add_uc (LC (And lcs)) (add (rname, Resource r) local)

let add_ur re local = 
  add_r (Sym.fresh ()) re local






let (++) = concat

let all_names = filter (fun sym _ -> Some sym)





let json local : Yojson.Safe.t = 

  let computational  = 
    List.map (fun (sym, (lname, bt)) ->
        `Assoc [("name", Sym.json sym);
                ("basetype", BT.json bt); 
                ("logical", Sym.json lname)]        
      ) (all_computational local )
  in
  let logical = 
    List.map (fun (sym, ls) ->
        `Assoc [("name", Sym.json sym);
                ("sort", LS.json ls)]
      ) (all_logical local)
  in
  let resources = 
    List.map (fun re ->
        RE.json re
      ) (all_resources local)
  in
  let used_resources = 
    List.map (fun (re, used) ->
        `Assoc [("location_used", List.json Loc.json_loc used);
                ("resource", RE.json re)]
      ) (all_used_resources local)
  in
  let constraints = 
    List.map (fun lc ->
        LC.json lc
      ) (all_constraints local)
  in

  let json_record = 
    `Assoc [("computational", `List computational);
            ("logical", `List logical);
            ("resources", `List resources);
            ("used resources", `List used_resources);
            ("constraints", `List constraints)
      ]
  in
  `Variant ("Context", Some json_record)

