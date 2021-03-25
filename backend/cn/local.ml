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
module SymMap = Map.Make(Sym)



module Make (G : sig val global : Global.t end) = struct

  module VB = VariableBindings

  open VB

  type t = bound SymMap.t
  

  let empty = SymMap.empty




  let unbound_internal_error sym = 
    Debug_ocaml.error ("unbound symbol " ^ Sym.pp_string sym)


  let kind_mismatch_internal_error ~expect ~has =
    let err = 
      "Expected" ^ (plain (Kind.pp expect)) ^
        "but found" ^ (plain (Kind.pp has))
    in
    Debug_ocaml.error err





  let pp_context_item ?(print_all_names = false) = function
    | (sym,binding) -> VB.pp ~print_all_names (sym,binding)

  
  (* reverses the list order for matching standard mathematical
     presentation *)
  let pp ?(print_all_names = false) (local : t) = 
    match SymMap.bindings local with
    | [] -> !^"(empty)"
    | local -> flow_map (comma ^^ break 1) 
                 (pp_context_item ~print_all_names) local




  (* internal *)
  let get_safe (sym: Sym.t) (local : t) : VB.bound option =
    match SymMap.find_opt sym local with
    | Some bound -> Some bound
    | None -> SymMap.find_opt sym G.global.bindings


  (* internal *)
  let add (name, b) (local : t) = 
    SymMap.add name b local

  let filter (p : Sym.t * bound -> 'a option) (local : t) = 
    let aux sym b (acc : 'a list) =
      match p (sym, b) with
      | Some a -> a :: acc
      | None -> acc
    in
    let from_global = SymMap.fold aux G.global.bindings [] in
    SymMap.fold aux local from_global

  let all_computational (local : t) = 
    filter (fun (name, b) ->
        match b with
        | Computational (lname, b) -> Some (name, (lname, b))
        | _ -> None
      ) local

  let all_logical (local : t) = 
    filter (fun (name, b) ->
        match b with
        | Logical ls -> Some (name, ls)
        | _ -> None
      ) local

  let all_resources (local : t) = 
    filter (fun (name, b) ->
        match b with
        | Resource re -> Some re
        | _ -> None
      ) local


  let all_constraints (local : t) = 
    filter (fun (name, b) ->
        match b with
        | Constraint (lc, _) -> Some lc
        | _ -> None
      ) local
  

  let all_solver_constraints (local : t) = 
    filter (fun (name, b) ->
        match b with
        | Constraint (_, sc) -> Some sc
        | _ -> None
      ) local




  let map_and_fold_resources (f : RE.t -> 'acc -> RE.t * 'acc) 
        (initial_local : t) (acc : 'acc) = 
    let local, acc =
      SymMap.fold (fun sym bound (local, acc) ->
          let (bound, acc) = 
            match bound with
            | Resource resource ->
               let (resource, acc) = f resource acc in
               (Resource resource, acc)
            | _ ->
               (bound, acc)
          in
          (SymMap.add sym bound local, acc)
        ) initial_local (SymMap.empty, acc)
    in
    (local, acc)



  let kind sym (local : t) = Option.map VB.kind (get_safe sym local)
  let bound sym (local : t) = Option.is_some (kind sym local)




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

  let add_l lname ls (local : t) = 
    add (lname, Logical ls) local

  let _add_ls ls (local : t) = 
    List.fold_left (fun local (lname,ls) ->
        add_l lname ls local
      ) local ls

  let add_c cname (lc, sc) (local : t)= 
    add (cname, Constraint (lc, sc)) local

  let add_uc (LC.LC lc) (local : t) = 
    let sc = SolverConstraints.of_index_term G.global lc in
    add (Sym.fresh (), Constraint (LC lc, sc)) local

  let add_ucs lcs (local : t) = 
    List.fold_left (fun local lc ->
        add_uc lc local
      ) local lcs


  let add_r rname r (local : t) = 
    let lcs = 
      RE.derived_constraint r ::
      List.map (fun r' -> RE.derived_constraints r r') 
        (all_resources local)
    in
    let local = add (rname, Resource r) local in
    let local = add_ucs (List.map LC.pack lcs) local in
    local

  let add_ur re (local : t)= 
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







  let concat (local' : t) (local : t) = 
    SymMap.fold (fun sym bound local ->
        match bound with
        | Computational (lsym, bt) ->
           add_a sym (bt, lsym) local
        | Logical ls ->
              add_l sym ls local
        | Resource re ->
           add_r sym re local
        | Constraint (lc, sc) ->
           add_c sym (lc, sc) local
      ) local' local


  let (++) = concat

  let all_names (local : t) = 
    filter (fun (sym, _) -> Some sym) local


  let json (local : t) : Yojson.Safe.t = 

    let computational  = 
      List.map (fun (sym, (lname, bt)) ->
          `Assoc [("name", Sym.json sym);
                  ("basetype", BT.json bt); 
                  ("logical", Sym.json lname)]        
        ) (all_computational local)
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
    let constraints = 
      List.map (fun lc ->
          LC.json lc
        ) (all_constraints local)
    in

    let json_record = 
      `Assoc [("computational", `List computational);
              ("logical", `List logical);
              ("resources", `List resources);
              ("constraints", `List constraints)
        ]
    in
    `Variant ("Context", Some json_record)


end
