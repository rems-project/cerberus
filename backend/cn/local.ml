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









  let use_resource sym where (Local local) = 
    let rec aux = function
    | Binding (sym',b) :: rest when Sym.equal sym sym' -> 
       begin match b with
       | Resource re -> 
          (* Binding (sym', UsedResource (re,where)) ::  *)
            rest
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

  let all_names local = filter (fun (sym, _) -> Some sym) local



  let normalise_resources (Local local) = 
    
    let normalise_resource = function
      | RE.Point p ->
         let pointer_s = Sym.fresh () in
         let pointer_t = IT.sym_ (BT.Loc, pointer_s) in
         let pointer_lc = IT.eq_ (pointer_t, p.pointer) in
         begin match p.content with
         | Block b -> 
            ([(pointer_s, BT.Loc)], 
             [pointer_lc], 
             RE.Point {p with pointer = pointer_t})
         | Value value ->
            let value_s = Sym.fresh () in
            let (IT.IT (_, value_bt)) = value in
            let value_t = IT.sym_ (value_bt, value_s) in
            let value_lc = IT.eq_ (value_t, value) in
            ([(pointer_s, BT.Loc); (value_s, value_bt)], 
             [pointer_lc; value_lc], 
             Point {p with pointer = pointer_t; content = Value value_t})
         end
      | Region r ->
         let pointer_s = Sym.fresh () in
         let pointer_t = IT.sym_ (BT.Loc, pointer_s) in
         let pointer_lc = IT.eq_ (pointer_t, r.pointer) in
         ([(pointer_s, BT.Loc)], 
          [pointer_lc], 
          Region {r with pointer = pointer_t})
      | Array a ->
         let pointer_s = Sym.fresh () in
         let pointer_t = IT.sym_ (BT.Loc, pointer_s) in
         let pointer_lc = IT.eq_ (pointer_t, a.pointer) in
         let content_s = Sym.fresh () in
         let (IT.IT (_, content_bt)) = a.content in
         let content_t = IT.sym_ (content_bt, content_s) in
         let content_lc = IT.eq_ (content_t, a.content) in
         ([(pointer_s, BT.Loc); (content_s, content_bt)], 
          [pointer_lc; content_lc], 
          Array {a with pointer = pointer_t; content = content_t})

      | Predicate p ->
         let logicals, lcs, oargs = 
           List.fold_right (fun arg (logicals, lcs, args) ->
               let arg_s = Sym.fresh () in 
               let (IT.IT (_, arg_bt)) = arg in
               let arg_t = IT.sym_ (arg_bt, arg_s) in
               ((arg_s, arg_bt) :: logicals,
                IT.eq_ (arg_t, arg) :: lcs,
                arg_t :: args)                 
             ) p.oargs ([], [], [])
         in
         let logicals, lcs, iargs = 
           List.fold_right (fun arg (logicals, lcs, args) ->
               let arg_s = Sym.fresh () in 
               let (IT.IT (_, arg_bt)) = arg in
               let arg_t = IT.sym_ (arg_bt, arg_s) in
               ((arg_s, arg_bt) :: logicals,
                IT.eq_ (arg_t, arg) :: lcs,
                arg_t :: args)                 
             ) p.iargs (logicals, lcs, []) 
         in
         (logicals, lcs, Predicate {p with iargs; oargs })

    in

    let local = 
      List.concat_map (function
          | Marker -> [Marker]
          | Binding (sym, bound) ->
             match bound with
             | Resource resource -> 
                let (logicals, constraints, resource) = normalise_resource resource in
                let new_logical_bindings = 
                  List.map (fun (s, bt) ->
                      Binding (s, Logical (Base bt))
                    ) logicals
                in
                let new_constraint_bindings = 
                  List.map (fun lc ->
                      let sc = SolverConstraints.of_index_term G.global lc in
                      Binding (Sym.fresh (), Constraint (LC lc, sc))
                    ) constraints
                in
                let new_resource_binding = 
                  Binding (sym, Resource resource)
                in
                new_resource_binding ::
                  List.rev new_constraint_bindings @ 
                  List.rev new_logical_bindings
             | _ ->
                [Binding (sym, bound)]
        ) local
    in
    Local local




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
