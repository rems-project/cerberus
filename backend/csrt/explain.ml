module IT = IndexTerms
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

    let should_be_in_veclass local veclass (it, bt) = 
      if not (LS.equal veclass.sort (Base bt)) then false 
      else S.equal local (S (bt,veclass.repr)) it

    let classify local veclasses (l, (bt : BT.t)) : veclass list =
      let rec aux = function
        | veclass :: veclasses ->
           if should_be_in_veclass local veclass (S (bt, l), bt) 
           then (add_l l veclass :: veclasses)
           else (veclass :: aux veclasses)
        | [] -> 
           [new_veclass l (Base bt)]
      in
      aux veclasses

    let is_in_veclass veclass sym = 
      SymSet.mem sym veclass.c_elements ||
        SymSet.mem sym veclass.l_elements


    (* think about whether the 'Addr' part is always safe' *)
    let has_symbol_name veclass = 
      let all = SymSet.elements (SymSet.union veclass.c_elements veclass.l_elements) in
      Option.map (fun s -> Path.Addr s) (List.find_map Sym.name all)

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

  open Path


  type naming = (Sym.t * Path.t) list

  let naming_subst subst names = 
    List.map (fun (sym,p) ->
        (Sym.subst subst sym, p)
      ) names

  let naming_substs substs names = 
    Subst.make_substs naming_subst substs names

  let pp_naming = 
    let open Pp in
    Pp.list (fun (s, p) -> parens (Sym.pp s ^^ comma ^^ Path.pp p))

  let naming_of_mapping mapping = 
    List.map (fun i ->
        Parse_ast.Mapping.(i.sym, i.path)
      ) mapping


  type variable_relation = 
    | Pointee  

  type veclass_explanation = {
      path : Path.t;
      good_name : bool;
      veclass : veclass;
    }
  
  type explanation = {
      substitutions : (Sym.t, Sym.t) Subst.t list;
      veclasses : veclass_explanation list;
      relevant : SymSet.t;
    }


    
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

  let has_given_name names veclass =
    Option.map snd
      (List.find_opt (fun (sym,name) -> is_in_veclass veclass sym) names)

  let has_derived_name (named_veclasses, rels) veclass =
    let rec aux = function
      | {veclass = named_veclass; path;_} :: named_veclasses ->
         begin match VEClassRelMap.find_opt (named_veclass, veclass) rels with
         | Some Pointee -> Some (pointee None path)
         | None -> aux named_veclasses
         end
      | [] -> None         
    in
    aux named_veclasses





  let explanation names local relevant =
    let relevant =
      List.fold_left (fun acc r -> SymSet.union acc (RE.vars_in r))
        relevant (L.all_resources local)
    in
    let veclasses = 
      let with_logical_variables = 
        List.fold_left (fun veclasses (l, ls) ->
            if SymSet.mem l relevant then
              let (LS.Base bt) = ls in
              classify local veclasses (l, bt)
            else 
              veclasses
          ) [] (L.all_logical local)
      in
      let with_all_variables =
        List.fold_left (fun veclasses (c, (l, _)) ->
            List.map (fun veclass ->
                if is_in_veclass veclass l 
                then add_c c veclass else veclass
              ) veclasses
          ) with_logical_variables (L.all_computational local)
      in
      let (sorted, rels) = veclasses_total_order local with_all_variables in
      let named =
        List.fold_left (fun veclasses_explanation veclass ->
            let candidate_names = 
              List.filter_map (fun p -> p) [
                  has_given_name names veclass; 
                  has_symbol_name veclass; 
                  has_derived_name (veclasses_explanation, rels) veclass;
                ] 
            in
            let (path,good_name) = match candidate_names with
              | p :: _ -> 
                 let without_labels = Path.remove_labels p in
                 if List.mem without_labels candidate_names 
                 then (without_labels, true) 
                 else (p, true)
              | _ ->
                 let name = LabeledName.{label = None; v = make_name veclass} in
                 (Var name, false)
            in
            veclasses_explanation @ [{veclass; path; good_name}]
          ) [] sorted
      in
      named
    in
    let substitutions = 
      List.fold_right (fun {veclass;path;_} substs ->
          let to_substitute = SymSet.union veclass.c_elements veclass.l_elements in
          let named_symbol = Sym.fresh_named (Pp.plain (Path.pp path)) in
          SymSet.fold (fun sym substs ->
              Subst.{ before = sym; after = named_symbol } :: substs
            ) to_substitute substs 
        ) veclasses []
    in
    {substitutions; veclasses; relevant}





  let always_state = true

  let rec boring_it = 
    let open IT in
    function
    | EQ (it1, And [it2;it3]) -> IT.equal it1 it2 && IT.equal it2 it3
    | EQ (it1, it2) -> IT.equal it1 it2 || boring_it it2
    | Impl (it1, it2) -> IT.equal it1 it2 || boring_it it2
    | (And its | Or its) -> List.for_all boring_it its
    | _ -> false

  let boring_lc (LC.LC it) = boring_it it
  let interesting_lc lc = not (boring_lc lc)


  let evaluate model expr = 
    match Z3.Model.evaluate model (SolverConstraints.of_index_term G.global expr) true with
    | None -> Debug_ocaml.error "failure constructing counter model"
    | Some evaluated_expr -> Z3.Expr.to_string evaluated_expr


  let pp_state local {substitutions; veclasses; relevant} model =
    let resources = List.map (RE.subst_vars substitutions) (L.all_resources local) in
    let veclasses_with_values =
      List.map (fun veclass ->
          match model, veclass.veclass.sort with
          | Some model, Base Integer -> (veclass, Some (evaluate model (S (Integer, veclass.veclass.repr))))
          | _ -> (veclass, None)
        ) veclasses
    in
    let open Pp in
    let resource_pp = List.map RE.pp resources in
    let var_pp = 
      List.filter_map (fun (c,value) -> 
          let (Base bt) = c.veclass.sort in
          let relevant = not (SymSet.is_empty (SymSet.inter relevant c.veclass.l_elements)) in
          match relevant, not c.good_name, value with
          | true, _, Some v -> Some (Path.pp c.path ^^^ colon ^^^ BT.pp false bt ^^^ equals ^^ equals ^^^ !^v)
          | true, true, None -> Some (Path.pp c.path ^^^ colon ^^^ BT.pp false bt)
          | _ -> None
        ) veclasses_with_values
    in
    (resource_pp, var_pp)




  let state names local = 
    let explanation = explanation names local SymSet.empty in
    (pp_state local explanation None)

  let undefined_behaviour names local model = 
    let explanation = explanation names local SymSet.empty in
    (pp_state local explanation model)

  let missing_ownership names local it = 
    let explanation = explanation names local (IT.vars_in it) in
    let it_pp = IT.pp (IT.subst_vars explanation.substitutions it) in
    (it_pp, pp_state local explanation None)

  let unsatisfied_constraint names local lc model = 
    let explanation = explanation names local (LC.vars_in lc) in
    let lc_pp = LC.pp (LC.subst_vars explanation.substitutions lc) in
    (lc_pp, pp_state local explanation model)

  let resource names local re = 
    let explanation = explanation names local (RE.vars_in re) in
    let re_pp = RE.pp (RE.subst_vars explanation.substitutions re) in
    (re_pp, pp_state local explanation None)

  let resources names local (re1, re2) = 
    let relevant = (SymSet.union (RE.vars_in re1) (RE.vars_in re2)) in
    let explanation = explanation names local relevant in
    let re1 = RE.pp (RE.subst_vars explanation.substitutions re1) in
    let re2 = RE.pp (RE.subst_vars explanation.substitutions re2) in
    ((re1, re2), pp_state local explanation None)
    



end
