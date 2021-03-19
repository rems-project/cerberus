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



module Make (G : sig val global : Global.t end) = struct

  module VB = VariableBindings

  open VB

  type context_item = 
    | Binding of binding
    | Marker


  (* left-most is most recent *)
  type t = 
    Local of context_item list
  

  let empty = Local []

  let marked = Local [Marker]




  let unbound_internal_error sym = 
    Debug_ocaml.error ("unbound symbol " ^ Sym.pp_string sym)


  let kind_mismatch_internal_error ~expect ~has =
    let err = 
      "Expected" ^ (plain (Kind.pp expect)) ^
        "but found" ^ (plain (Kind.pp has))
    in
    Debug_ocaml.error err





  let pp_context_item ?(print_all_names = false) = function
    | Binding (sym,binding) -> VB.pp ~print_all_names (sym,binding)
    | Marker -> uformat [Blue] "\u{25CF}" 1 

  (* reverses the list order for matching standard mathematical
     presentation *)
  let pp ?(print_all_names = false) (Local local) = 
    match local with
    | [] -> !^"(empty)"
    | _ -> flow_map (comma ^^ break 1) 
             (pp_context_item ~print_all_names) 
             (rev local)




  (* internal *)
  let get_safe (sym: Sym.t) (Local local) : VB.bound option =
    let rec aux = function
    | Binding (sym',b) :: _ when Sym.equal sym' sym -> Some b
    | _ :: local -> aux local
    | [] -> List.assoc_opt Sym.equal sym G.global.bindings
    in
    aux local


  (* internal *)
  let add (name, b) (Local e) = Local (Binding (name, b) :: e)

  let filter p (Local e) = 
    filter_map (function Binding (sym,b) -> p (sym, b) | _ -> None) e @
      List.filter_map p G.global.bindings

  let all_computational local = 
    filter (fun (name, b) ->
        match b with
        | Computational (lname, b) -> Some (name, (lname, b))
        | _ -> None
      ) local

  let all_logical local = 
    filter (fun (name, b) ->
        match b with
        | Logical ls -> Some (name, ls)
        | _ -> None
      ) local

  let all_resources local = 
    filter (fun (name, b) ->
        match b with
        | Resource re -> Some re
        | _ -> None
      ) local

  let all_named_resources local = 
    filter (fun (name, b) ->
        match b with
        | Resource re -> Some (name, re)
        | _ -> None
      ) local


  let all_constraints local = 
    filter (fun (name, b) ->
        match b with
        | Constraint (lc, _) -> Some lc
        | _ -> None
      ) local
  

  let all_solver_constraints local = 
    filter (fun (name, b) ->
        match b with
        | Constraint (_, sc) -> Some sc
        | _ -> None
      ) local




  let map_and_fold_resources (f : RE.t -> 'acc -> RE.t * 'acc) (Local initial_local) (acc : 'acc) = 
    let local, acc =
      List.fold_right (fun context_item (local, acc) ->
          let (context_item, acc) = 
            match context_item with
            | Binding (sym, Resource resource) ->
               let (resource, acc) = f resource acc in
               (Binding (sym, Resource resource), acc)
            | _ ->
               (context_item, acc)
          in
          (context_item :: local, acc)
        ) initial_local ([], acc)
    in
    (Local local, acc)



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
        item "ctxt1" (pp ~print_all_names:true l1) ^/^
        item "ctxt2" (pp ~print_all_names:true l2) ^/^ 
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

  let add_c cname (lc, sc) local = 
    add (cname, Constraint (lc, sc)) local

  let add_uc (LC.LC lc) local = 
    let sc = SolverConstraints.of_index_term G.global lc in
    add (Sym.fresh (), Constraint (LC lc, sc)) local

  let add_ucs lcs local = 
    List.fold_left (fun local lc ->
        add_uc lc local
      ) local lcs


  let add_r rname r local = 
    let lcs = 
      RE.derived_constraint r ::
      List.concat_map (RE.derived_constraints r) 
        (all_resources local)
    in
    let local = add (rname, Resource r) local in
    let local = add_ucs (List.map LC.pack lcs) local in
    local

  let add_ur re local = 
    add_r (Sym.fresh ()) re local





  (* let equalities local = 
   *   let pairs = 
   *     List.filter_map (fun (LC.LC it) ->
   *         match it with
   *         | IT (Bool_op (EQ (IT (Lit (Sym s1), _), IT (Lit (Sym s2), _))), _) ->
   *            if Sym.compare s1 s2 <= 0 then Some (s1, s2) else Some (s2, s1)
   *         |  _ -> 
   *             None
   *       ) (all_constraints local)
   *   in *)
    (* let pairs_sorted =
     *   List.sort (fun (a1, a2) (b1, b2) ->
     *       let cmp1 = Sym.compare a1 b1 in
     *       if cmp1 = 0 then Sym.compare a2 b2 else cmp1
     *     ) pairs
     * in
     * List.fold_left (fun classes (a1, b1) ->
     *     let rec aux = function
     *       | clss :: classes when SymSet.elem a1 clss ->
     *          SymSet.add b1 clss :: classes
     *       | clss :: classes ->
     *          clss :: aux classes
     *       | [] -> 
     *          [SymSet.of_list [a1; b1]]         1,5  2,3  3,4  4,5
     *     in
     *     aux classes
     *   ) [] pairs_sorted *)







  let concat (Local local') (Local local) = 
    List.fold_right (fun context_item (Local local) ->
        match context_item with
        | Marker -> (Local (Marker :: local))
        | Binding (sym,bound) ->
           match bound with
           | Computational (lsym, bt) ->
              add_a sym (bt, lsym) (Local local)
           | Logical ls ->
              add_l sym ls (Local local)
           | Resource re ->
              add_r sym re (Local local)
           | Constraint (lc, sc) ->
              add_c sym (lc, sc) (Local local)
      ) local' (Local local)


  let (++) = concat

  let all_names local = filter (fun (sym, _) -> Some sym) local


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
    (* let used_resources = 
     *   List.map (fun (re, used) ->
     *       `Assoc [("location_used", List.json Loc.json_loc used);
     *               ("resource", RE.json re)]
     *     ) (all_used_resources local)
     * in *)
    let constraints = 
      List.map (fun lc ->
          LC.json lc
        ) (all_constraints local)
    in

    let json_record = 
      `Assoc [("computational", `List computational);
              ("logical", `List logical);
              ("resources", `List resources);
              (* ("used resources", `List used_resources); *)
              ("constraints", `List constraints)
        ]
    in
    `Variant ("Context", Some json_record)


end
