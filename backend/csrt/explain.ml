module BT = BaseTypes
module RE = Resources
module LC = LogicalConstraints
module LS = LogicalSorts
module SymSet = Set.Make(Sym)
module StringMap = Map.Make(String)
module SymPairMap = Map.Make(SymRel.SymPair)

module Make (G : sig val global : Global.t end) = struct 

  module L = Local.Make(G)
  module S = Solver.Make(G)


  module VEClass = struct

    type veclass = { 
        repr : Sym.t;
        sort: LS.t;
        l_elements : SymSet.t;
        c_elements : SymSet.t;
      }

    type t = veclass


    let new_veclass l ls = { 
        repr = l;
        sort = ls;
        l_elements = SymSet.singleton l;
        c_elements = SymSet.empty;
      }

    let add_l l veclass = 
      { veclass with l_elements = SymSet.add l veclass.l_elements }

    let add_c c veclass = 
      { veclass with c_elements = SymSet.add c veclass.c_elements }

    let o_add_c o_c veclass = 
      match o_c with
      | None -> veclass
      | Some c -> add_c c veclass

    let should_be_in_veclass local veclass (it, bt) = 
      if not (LS.equal veclass.sort (Base bt)) then false 
      else S.equal local (S (bt,veclass.repr)) it

    let classify local veclasses (o_c, l, (bt : BT.t)) : veclass list =
      let rec aux = function
        | veclass :: veclasses ->
           if should_be_in_veclass local veclass (S (bt, l), bt) then 
             let veclass' = o_add_c o_c (add_l l veclass) in
             (veclass' :: veclasses)
           else 
             let veclasses' = aux veclasses in
             (veclass :: veclasses')
        | [] -> 
           [o_add_c o_c (new_veclass l (Base bt))]
      in
      aux veclasses

    let is_in_veclass veclass sym = 
      SymSet.mem sym veclass.c_elements ||
        SymSet.mem sym veclass.l_elements


    let good_name veclass = 
      match SymSet.find_first_opt Sym.named veclass.c_elements with
      | Some s -> Sym.name s
      | None -> 
         match SymSet.find_first_opt Sym.named veclass.l_elements with
         | Some s -> Sym.name s
         | None -> None

    let make_name = 
      let faa counter = 
        let v = !counter in
        let () = counter := v + 1 in
        v
      in
      let sym_prefixed_int (prefix, i) = 
        "?" ^ prefix ^ string_of_int i
      in
      let unit_counter = ref 0 in
      let bool_counter = ref 0 in
      let integer_counter = ref 0 in
      let loc_counter = ref 0 in
      let array_counter = ref 0 in
      let list_counter = ref 0 in
      let tuple_counter = ref 0 in
      let struct_counter = ref 0 in
      let function_pointer_counter = ref 0 in
      let set_counter = ref 0 in
      fun veclass ->
      let (Base bt) = veclass.sort in
      sym_prefixed_int
        begin match bt with
        | Unit -> ("u", faa unit_counter)
        | Bool -> ("b", faa bool_counter)
        | Integer -> ("i", faa integer_counter)
        | Loc -> ("l", faa loc_counter)
        | Array -> ("a", faa array_counter)
        | List _ -> ("l", faa list_counter)
        | Tuple _ ->  ("t", faa tuple_counter)
        | Struct _ -> ("s", faa struct_counter)
        | FunctionPointer _ -> ("f", faa function_pointer_counter)
        | Set _ -> ("set", faa set_counter)
        end

    let compare veclass1 veclass2 = 
      Sym.compare veclass1.repr veclass2.repr

    let equal veclass1 veclass2 = 
      compare veclass1 veclass2 = 0

  end

  module VEClassSet = Set.Make(VEClass)

  module VEClassPair = struct 
    type t = VEClass.t * VEClass.t
    let compare a b = Lem_basic_classes.pairCompare VEClass.compare VEClass.compare a b
  end
  
  module VEClassRel = struct
    include Pset
    type t = VEClassPair.t Pset.set
    let empty = Pset.empty VEClassPair.compare
    let transitiveClosure = Pset.tc VEClassPair.compare
  end 


  module VEClassRelMap = Map.Make(VEClassPair)


  open VEClass

  module Path = Path.Make(struct 
      type t = String.t
      let equal = String.equal
      let pp = Pp.string
    end)

  open Path


  type variable_relation = 
    | Pointee

  let veclasses_partial_order local veclasses =
    List.fold_right (fun resource (graph, rels) ->
        match resource with
        | RE.Points p ->
           let found1 = 
             List.find_opt (fun veclass ->
                 should_be_in_veclass local veclass (p.pointer, BT.Loc)
               ) veclasses
           in
           let found2 = 
             List.find_opt (fun veclass ->
                 is_in_veclass veclass p.pointee
               ) veclasses
           in
           begin match found1, found2 with
           | Some veclass1, Some veclass2 
                when not (VEClassRel.mem (veclass2, veclass1) graph) ->
              (VEClassRel.add (veclass1, veclass2) graph,
               VEClassRelMap.add (veclass1, veclass2) Pointee rels)
           | _ -> 
              (graph, rels)
           end
        | _ -> 
           (graph, rels)
      ) (L.all_resources local) 
      (VEClassRel.empty, VEClassRelMap.empty)


  let veclasses_total_order local veclasses = 
    let (graph, rels) = veclasses_partial_order local veclasses in
    let graph = 
      List.fold_left (fun graph veclass1 ->
          List.fold_left (fun graph veclass2 ->
              if 
                VEClass.equal veclass1 veclass2 ||
                  VEClassRel.mem (veclass1, veclass2) graph ||
                    VEClassRel.mem (veclass2, veclass1) graph
              then
                graph
              else
                VEClassRel.transitiveClosure (VEClassRel.add (veclass1, veclass2) graph)
            ) graph veclasses
        ) graph veclasses
    in
    let graph_compare veclass1 veclass2 =
      if VEClassRel.mem (veclass1,veclass2) graph then -1 else 1
    in
    (List.sort graph_compare veclasses, rels)

  let preferred_name preferred_names veclass =
    List.find_opt (fun (sym,name) -> is_in_veclass veclass sym) 
      preferred_names

  let related_name (named_veclasses, rels) veclass =
    let rec aux = function
      | (named_veclass, name, good) :: named_veclasses ->
         begin match VEClassRelMap.find_opt (named_veclass, veclass) rels with
         | Some Pointee -> Some (pointee name, good)
         | None -> aux named_veclasses
         end
      | [] -> None         
    in
    aux named_veclasses

  let pick_name (named_veclasses, rels) preferred_names veclass =
    match preferred_name preferred_names veclass with
    | Some (_, name) -> (name, true)
    | None -> 
       match related_name (named_veclasses, rels) veclass with
       | Some name -> name
       | None -> 
          match good_name veclass with
          | Some name -> 
             (Addr name, true)
          | None -> 
             (Var (make_name veclass), false)
    
    
  type explanation = {
      substitutions : (Sym.t, Sym.t) Subst.t list;
      introduce : (Path.t * LS.t) list
    }


  let explanation preferred_names local =
    let c = L.all_computational local in
    let l = L.all_logical local in
    let veclasses = 
      let veclasses = 
        List.fold_left (fun veclasses (l, ls) ->
            let (LS.Base bt) = ls in
            classify local veclasses (None, l, bt)
          ) [] l
      in
      List.fold_left (fun veclasses (c, (l, bt)) ->
          classify local veclasses (Some c, l, bt)
        ) veclasses c
    in
    let (veclasses_sorted, rels) = 
      veclasses_total_order local veclasses in
    let named_veclasses, introduce = 
      List.fold_left (fun (named_veclasses, need_explaining) veclass ->
          let (name,good) = pick_name (named_veclasses, rels) preferred_names veclass in
          let named_veclasses = named_veclasses @ [(veclass, name, good)] in
          let need_explaining = 
            if good 
            then need_explaining 
            else need_explaining @ [(name, veclass.sort)]
          in
          (named_veclasses, need_explaining)
        ) ([],[]) veclasses_sorted
    in
    let substitutions = 
      List.fold_right (fun (veclass,name,good) substs ->
          let to_substitute = SymSet.union veclass.c_elements veclass.l_elements in
          SymSet.fold (fun sym substs ->
              let named_symbol = Sym.fresh_named (Pp.plain (Path.pp name)) in
              Subst.{ before = sym; after = named_symbol } :: substs
            ) to_substitute substs 
        ) named_veclasses []
    in
    {substitutions; introduce}


  let state preferred_names local =    
    let {substitutions; introduce} = explanation preferred_names local in
    let resources = List.map (RE.subst_vars substitutions) (L.all_resources local) in
    let constraints = List.map (LC.subst_vars substitutions) (L.all_constraints local) in
    let open Pp in
    Pp.item "resources" (Pp.list RE.pp resources) ^/^
    Pp.item "constaints" (Pp.list LC.pp constraints)

  let logical_constraint preferred_names local lc = 
    let {substitutions; introduce} = explanation preferred_names local in
    let lc = LC.subst_vars substitutions lc in
    if introduce = [] then
      (lc, None)
    else
      let resources = List.map (RE.subst_vars substitutions) 
                        (L.all_resources local) in
      let constraints = List.map (LC.subst_vars substitutions) 
                          (L.all_constraints local) in
      let open Pp in
      let state_pp = 
        Pp.item "resources" (Pp.list RE.pp resources) ^/^
          Pp.item "constaints" (Pp.list LC.pp constraints)
      in
    (lc, Some state_pp)
    



    (* let all_locations = 
     *   let from_context = 
     *     filter_map (fun (s, ls) -> 
     *         if LS.equal ls (LS.Base Loc) then Some (IT.S s) else None
     *       ) l
     *   in
     *   let from_resources = 
     *     map (fun (_, r) -> RE.pointer r) r in
     *   ListM.fold_rightM (fun location_it acc ->
     *       let* expr = of_index_term loc {local; global} context location_it in
     *       let* evaluated_expr = evaluate loc model expr in
     *       return (StringMap.add (Z3.Expr.to_string evaluated_expr) location_it acc)
     *     ) (from_context @ from_resources) StringMap.empty
     * in
     * let* pped_state = 
     *   ListM.fold_rightM (fun (location_string, location_it) acc_pp ->
     *       let* o_resource = resource_for_pointer loc {local; global} location_it in
     *       let* pp = match o_resource with
     *         | None -> 
     *            return (!^"location" ^^^ !^location_string ^^^ !^"unowned")
     *         | Some (_, RE.Uninit u) -> 
     *            return (!^"location" ^^^ !^location_string ^^^ parens (Z.pp u.size ^^^ !^"bytes size") ^^^ 
     *                      !^"uninitialised")
     *         | Some (_, RE.Points p) -> 
     *            let* (Base ls) = L.get_l loc p.pointee local in
     *            let* expr = of_index_term loc {local; global} context (S p.pointee) in
     *            let* evaluated_expr = evaluate loc model expr in
     *            let loc_pp = !^location_string ^^^ parens (Z.pp p.size ^^^ !^"bytes size") in
     *            let val_pp = !^(Z3.Expr.to_string evaluated_expr) in
     *            let location_it_pp = 
     *              let it = IT.subst_vars print_substs location_it in
     *              if all_it_names_good it then IT.pp it ^^^ !^"at" ^^ space else Pp.empty 
     *            in
     *            match ls with
     *            | Integer -> 
     *               return (location_it_pp ^^ !^"location" ^^^ loc_pp ^^^ !^"stores integer" ^^^ val_pp)
     *            | Loc -> 
     *               return (location_it_pp ^^ !^"location" ^^^ loc_pp ^^^ !^"stores pointer to location" ^^^ val_pp)
     *            | Array ->
     *               fail loc (Internal !^"todo: array print reporting")
     *            | Struct _ ->
     *               fail loc (Internal !^"todo: struct print reporting")
     *            | Unit 
     *              | Bool
     *              | List _
     *              | Tuple _
     *              | FunctionPointer _ -> fail loc (Internal !^"non-object stored in memory")
     *       in
     *       return (pp :: acc_pp)
     *     ) (StringMap.bindings all_locations) []
     * in *)





end
