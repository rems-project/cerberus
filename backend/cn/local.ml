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

  type solver_constraint = Z3.Expr.expr

  type t =
    | Computational of Sym.t * BT.t
    | Logical of LS.t
    | Resource of RE.t
    | UsedResource of RE.t * Loc.t list
    | Constraint of LC.t * solver_constraint


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
       btyp sym (BT.pp bt ^^ tilde ^^ Sym.pp lname)
    | Logical ls -> 
       btyp sym (LS.pp ls)
    | Resource re -> 
       if print_all_names 
       then btyp sym (squotes (RE.pp re))
       else squotes (RE.pp re)
    | UsedResource (re,_locs) -> 
       if not print_used then underscore 
       else if print_all_names 
       then btyp sym (!^"used" ^^^ (squotes (RE.pp re)))
       else !^"used" ^^^ squotes (RE.pp re)
    | Constraint (lc, _) -> 
       if print_all_names 
       then btyp sym (LC.pp lc)
       else LC.pp lc



  let agree vb1 vb2 = 
    match vb1, vb2 with
    | Computational (l1,bt1), Computational (l2,bt2)
         when Sym.equal l1 l2 && BT.equal bt1 bt2 -> 
       Some (Computational (l1,bt1))
    | Logical ls1, Logical ls2 
         when LS.equal ls1 ls2 -> 
       Some (Logical ls1)
    | Constraint (lc1,sc), Constraint (lc2, _)
           when LC.equal lc1 lc2 ->
       Some (Constraint (lc1, sc))
    | Resource re1, Resource re2 
         when RE.equal re1 re2 ->
       Some (Resource re1)
    | UsedResource (re1,locs1), UsedResource (re2,locs2)
           when RE.equal re1 re2 ->
       Some (UsedResource (re1, locs1 @ locs2))
    | _, _ ->
       None

end


module Make (G : sig val global : Global.t end) = struct

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
      "Expected" ^ (plain (Kind.pp expect)) ^
        "but found" ^ (plain (Kind.pp has))
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
  let get_safe (sym: Sym.t) (Local local) : VB.t option =
    let rec aux = function
    | Binding (sym',b) :: _ when Sym.equal sym' sym -> Some b
    | _ :: local -> aux local
    | [] -> 
       match List.assoc_opt Sym.equal sym G.global.logical with
       | Some ls -> Some (Logical ls)
       | None ->
          match List.assoc_opt Sym.equal sym G.global.computational with
          | Some (lsym, bt) -> Some (Computational (lsym, bt))
          | None -> None
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
    @
    G.global.computational

  let all_logical local = 
    filter (fun name b ->
        match b with
        | Logical ls -> Some (name, ls)
        | _ -> None
      ) local
    @
    G.global.logical

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
    let from_local = 
      filter (fun name b ->
          match b with
          | Constraint (lc, _) -> Some lc
          | _ -> None
        ) local
    in
    let from_global = List.map fst G.global.constraints in
    from_local @ from_global
  

  let all_solver_constraints local = 
    let from_local = 
      filter (fun name b ->
          match b with
          | Constraint (_, sc) -> Some sc
          | _ -> None
        ) local
    in
    let from_global = List.map snd G.global.constraints in
    from_local @ from_global









  let use_resource sym where (Local local) = 
    let rec aux = function
    | Binding (sym',b) :: rest when Sym.equal sym sym' -> 
       begin match b with
       | Resource re -> Binding (sym', UsedResource (re,where)) :: rest
       | _ -> kind_mismatch_internal_error 
                ~expect:KResource ~has:(VB.kind b)
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
    Option.bind 
      (get_safe sym (Local local))
      (fun b -> Some (VB.kind b))



  let bound sym local = 
    Option.is_some (kind sym local)



  let incompatible_environments l1 l2 (mismatch1,mismatch2) =
    let msg = 
      !^"Merging incompatible contexts." ^/^ 
        item "ctxt1" (pp ~print_used:true ~print_all_names:true l1) ^/^
        item "ctxt2" (pp ~print_used:true ~print_all_names:true l2) ^/^ 
        mismatch1 ^^^ !^"vs" ^^^ mismatch2
    in
    Debug_ocaml.error (plain msg)

  let merge (Local l1) (Local l2) =
    let incompatible = incompatible_environments (Local l1) (Local l2) in
    let merge_ci = function
      | (Marker, Marker) -> Marker
      | (Binding (s1,vb1), Binding(s2,vb2)) ->
         begin match Sym.equal s1 s2, VB.agree vb1 vb2 with
         | true, Some vb -> Binding (s1,vb)
         | _ -> incompatible (VB.pp (s1, vb1), VB.pp (s2, vb2))
         end
      | (Marker, Binding (s2,vb2)) -> 
         incompatible (!^"marker", VB.pp (s2,vb2))
      | (Binding (s1,vb1), Marker) -> 
         incompatible (!^"marker", VB.pp (s1,vb1))
    in
    if List.length l1 <> List.length l2 then 
      incompatible (!^"length ctxt1",!^"length ctxt2") 
    else 
      Local (List.map merge_ci (List.combine l1 l2))


  let big_merge (local: t) (locals: t list) : t = 
    List.fold_left merge local locals




  let get_a (name: Sym.t) (local:t)  = 
    match get_safe name local with 
    | None -> unbound_internal_error name
    | Some (Computational (lname,bt)) -> (bt,lname)
    | Some b -> kind_mismatch_internal_error 
                  ~expect:KComputational ~has:(VB.kind b)

  let get_l (name: Sym.t) (local:t) = 
    match get_safe name local with 
    | None -> unbound_internal_error name
    | Some (Logical ls) -> ls
    | Some b -> kind_mismatch_internal_error 
                  ~expect:KLogical ~has:(VB.kind b)

  let get_r (name: Sym.t) (local:t) = 
    match get_safe name local with 
    | None -> unbound_internal_error name
    | Some (Resource re) -> re
    | Some b -> kind_mismatch_internal_error 
                  ~expect:KResource ~has:(VB.kind b)


  let add_a aname (bt,lname) = 
    add (aname, Computational (lname,bt))

  let add_l lname ls local = 
    add (lname, Logical ls) local

  let _add_ls ls local = 
    List.fold_left (fun local (lname,ls) ->
        add_l lname ls local
      ) local ls

  let add_uc (LC.LC lc) local = 
    let sc = SolverConstraints.of_index_term G.global lc in
    add (Sym.fresh (), Constraint (LC lc, sc)) local

  let add_ucs lcs local = 
    List.fold_left (fun local lc ->
        add_uc lc local
      ) local lcs


  let add_r rname r local = 
    let lcs = match RE.footprint r with
      | None -> []
      | Some ((addr,_) as fp) ->
         let fps = List.filter_map RE.footprint (all_resources local) in
         LC.LC (IT.not_ (IT.null_ addr)) ::
         List.map LC.pack (IT.disjoint_from fp fps)
    in
    let local = add (rname, Resource r) local in
    let local = add_ucs lcs local in
    local

  let add_ur re local = 
    add_r (Sym.fresh ()) re local



  let (++) = concat

  let all_names local = 
    filter (fun sym _ -> Some sym) local @
    List.map fst G.global.computational @
    List.map fst G.global.logical





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


end
