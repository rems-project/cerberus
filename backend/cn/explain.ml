module IT = IndexTerms
module BT = BaseTypes
module RE = Resources.RE
module RER = Resources.Requests
module LC = LogicalConstraints
module LS = LogicalSorts
module SymSet = Set.Make(Sym)
module StringMap = Map.Make(String)
module SymPairMap = Map.Make(SymRel.SymPair)
module L = Local

open Resources.RE
open IndexTerms
open LogicalConstraints
open Pp

module Make (G : sig val global : Global.t end) = struct 
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

    let should_be_in_veclass local veclass it = 
      let bt = IT.bt it in
      if not (LS.equal veclass.sort bt) then false 
      else S.holds ~ignore_unknown:true local (t_ (eq_ (IT.sym_ (veclass.repr, bt), it)))

    let is_in_veclass veclass sym = 
      SymSet.mem sym veclass.c_elements ||
        SymSet.mem sym veclass.l_elements

    let classify local veclasses (l, (bt : BT.t)) : veclass list =
      let rec aux = function
        | veclass :: veclasses ->
           if is_in_veclass veclass l ||
             should_be_in_veclass local veclass (IT.sym_ (l, bt)) 
           then (add_l l veclass :: veclasses)
           else (veclass :: aux veclasses)
        | [] -> 
           [new_veclass l bt]
      in
      aux veclasses


    (* think about whether the 'Addr' part is always safe' *)
    let has_symbol_name veclass = 
      let all = SymSet.elements (SymSet.union veclass.c_elements veclass.l_elements) in
      Option.map (fun s -> Ast.Addr s) (List.find_map Sym.name all)

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
      let real_counter = ref 0 in
      let loc_counter = ref 0 in
      let list_counter = ref 0 in
      let tuple_counter = ref 0 in
      let struct_counter = ref 0 in
      let set_counter = ref 0 in
      (* let array_counter = ref 0 in *)
      let option_counter = ref 0 in
      let param_counter = ref 0 in
      fun veclass ->
      let bt = veclass.sort in
      sym_prefixed_int
        begin match bt with
        | Unit -> ("u", faa unit_counter)
        | Bool -> ("b", faa bool_counter)
        | Integer -> ("i", faa integer_counter)
        | Real -> ("r", faa real_counter)
        | Loc -> ("l", faa loc_counter)
        | List _ -> ("l", faa list_counter)
        | Tuple _ ->  ("t", faa tuple_counter)
        | Struct _ -> ("s", faa struct_counter)
        | Set _ -> ("set", faa set_counter)
        (* | Array _ -> ("array", faa array_counter) *)
        | Option _ -> ("option", faa option_counter)
        | Param _ -> ("p", faa param_counter)
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

  type naming = (Sym.t * Ast.term) list

  let naming_subst subst names = 
    List.map (fun (sym,p) ->
        (Sym.subst subst sym, p)
      ) names

  let naming_substs substs names = 
    Subst.make_substs naming_subst substs names

  let pp_naming = 
    Pp.list (fun (s, p) -> parens (Sym.pp s ^^ comma ^^ Ast.Terms.pp true p))

  let naming_of_mapping mapping = 
    let open Mapping in
    List.filter_map (fun i ->
        match IT.is_sym i.it with
        | Some (sym, _) -> Some (sym, i.path)
        | None -> None
      ) mapping


  type variable_relation = 
    | Pointee  

  type name_kind = 
    | Given
    | Symbol
    | Derived
    | Default

  type veclass_explanation = {
      path : Ast.term;
      name_kind : name_kind;
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
        | RE.Point {pointer; size; value; init; permission} ->
           let found1 = 
             List.find_opt (fun veclass ->
                 should_be_in_veclass local veclass pointer
               ) veclasses
           in
           let found2 = 
             List.find_opt (fun veclass ->
                 should_be_in_veclass local veclass value
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
         | Some Pointee -> Some (Ast.pointee None path)
         | None -> aux named_veclasses
         end
      | [] -> None         
    in
    aux named_veclasses





  let explanation names local relevant =

    print stdout !^"producing error report";


    let () = Debug_ocaml.begin_csv_timing "explanation" in

    let relevant =
      let names_syms = SymSet.of_list (List.map fst names) in
      let named_syms = SymSet.of_list (List.filter Sym.named (L.all_names local)) in
      let from_resources = RE.free_vars_list (L.all_resources local) in
      SymSet.union (SymSet.union (SymSet.union names_syms named_syms) from_resources)
        relevant
    in
    let veclasses = 
      let with_some =
        List.fold_left (fun veclasses (c, (bt, l)) ->
            if SymSet.mem c relevant || SymSet.mem l relevant then
              let veclasses = classify local veclasses (l, bt) in
              List.map (fun veclass ->
                  if is_in_veclass veclass l
                  then add_c c veclass 
                  else veclass
                ) veclasses
            else veclasses
          ) [] (L.all_computational local)
      in
      let with_all = 
        List.fold_left (fun veclasses (l, bt) ->
            if SymSet.mem l relevant 
            then classify local veclasses (l, bt)
            else veclasses
          ) with_some (L.all_logical local)
      in
      let (sorted, rels) = veclasses_total_order local with_all in
      let named =
        List.fold_left (fun veclasses_explanation veclass ->
            match has_given_name names veclass, 
                  has_symbol_name veclass,
                  has_derived_name (veclasses_explanation, rels) veclass with
            | Some given_name, o_symbol_name, o_derived_name ->
               let without_labels = Ast.remove_labels_term given_name in
               let path = 
                 if Option.equal Ast.term_equal (Some without_labels) (o_symbol_name) ||
                      Option.equal Ast.term_equal (Some without_labels) (o_derived_name) 
                 then without_labels
                 else given_name
               in
               veclasses_explanation @ [{veclass; path; name_kind = Given}]
            | None, Some symbol_name, _ ->
               veclasses_explanation @ [{veclass; path = symbol_name; name_kind = Symbol}]
            | None, None, Some derived_name ->
               veclasses_explanation @ [{veclass; path = derived_name; name_kind = Symbol}]
            | None, None, None ->
               let name = Ast.LabeledName.{label = None; v = make_name veclass} in
               veclasses_explanation @ [{veclass; path = Var name; name_kind = Default}]
          ) [] sorted
      in
      named
    in
    let substitutions = 
      List.fold_right (fun {veclass;path;_} substs ->
          let to_substitute = SymSet.union veclass.c_elements veclass.l_elements in
          let named_symbol = Sym.fresh_named (Pp.plain (Ast.Terms.pp false path)) in
          SymSet.fold (fun sym substs ->
              Subst.{ before = sym; after = named_symbol } :: substs
            ) to_substitute substs 
        ) veclasses []
    in

    let () = Debug_ocaml.end_csv_timing "explanation" in

    ({substitutions; veclasses; relevant}, local)






  let rec o_evaluate o_model expr = 
    let open Option in
    let@ model = o_model in
    match Z3.Model.evaluate model (fst (S.of_index_term expr)) true with
    | None -> Debug_ocaml.error "failure constructing counter model"
    | Some evaluated_expr -> 
       match IT.bt expr with
       | BT.Integer -> 
          return (Pp.string (Z3.Expr.to_string evaluated_expr))
       | BT.Real -> 
          return (Pp.string (Z3.Expr.to_string evaluated_expr))
       | BT.Loc ->
          return (Z.pp_hex 16 (Z.of_string (Z3.Expr.to_string evaluated_expr)))
       | BT.Bool ->
          return (Pp.string (Z3.Expr.to_string evaluated_expr))
       | BT.Param _ ->
          return (Pp.string (Z3.Expr.to_string evaluated_expr))
       | BT.Unit ->
          return (BT.pp BT.Unit)
       | BT.Struct tag ->
         let layout = Global.SymMap.find tag G.global.struct_decls in
         let members = Memory.member_types layout in
         let@ members = 
           ListM.mapM (fun (member, sct) -> 
               let@ s = o_evaluate o_model (IT.member_ ~member_bt:(BT.of_sct sct) (tag, expr, member)) in
               return (dot ^^ Id.pp member ^^^ equals ^^^ s)
             ) members 
         in
         return (braces (separate comma members))
       | _ -> None


  let symbol_it = function
    | IT.IT (Lit (Sym s), _) -> SymSet.singleton s
    | _ -> SymSet.empty

  let something_symbol_it = function
    | IT.IT (Lit (Sym s), _) -> SymSet.singleton s
    | IT.IT (Option_op (Something (IT.IT (Lit (Sym s), _))), _) -> SymSet.singleton s
    | _ -> SymSet.empty


  let pp_state_aux local {substitutions; veclasses; relevant} o_model =
    (* let resources = List.map (RE.subst_vars substitutions) (L.all_resources local) in *)

    let (resource_lines, reported_pointees) = 
      List.fold_right (fun resource (acc_table, acc_reported) ->
          match resource with
          | Point {pointer; size; value; init; permission} ->
             let permission = 
               Option.bind (o_evaluate o_model permission)
                 (fun p -> Some (!^"permission:" ^^^ p))
             in
             let init = 
               Option.bind (o_evaluate o_model init)
                 (fun p -> Some (!^"init:" ^^^ p))
             in
             let state = 
               !^"owned" ^^^ 
                 separate comma 
                   (List.filter_map (fun p -> p) [permission; init]) 
             in
             let entry = 
               (Some (IT.pp (IT.subst_vars substitutions pointer)), 
                o_evaluate o_model pointer,
                Some (Z.pp size),
                Some state,
                Some (IT.pp (IT.subst_vars substitutions value)),
                o_evaluate o_model value
               )
             in
             (entry :: acc_table, SymSet.union (SymSet.union (symbol_it pointer) (something_symbol_it value)) acc_reported)
          | QPoint p ->
             let entry =
               (None,
                None, 
                None, 
                Some (RE.pp (RE.subst_vars substitutions resource)),
                None,
                None
               )
             in
             (entry :: acc_table, SymSet.add p.qpointer acc_reported)
          | Predicate p ->
             let entry =
               (Some (IT.pp (IT.subst_vars substitutions p.pointer)),
                None, 
                None, 
                Some (RE.pp (RE.subst_vars substitutions (Predicate p))),
                None,
                None
               )
             in
             (entry :: acc_table, SymSet.empty)
          | QPredicate p ->
             let entry =
               (Some (IT.pp (IT.subst_vars substitutions p.pointer)),
                None, 
                None, 
                Some (RE.pp (RE.subst_vars substitutions (QPredicate p))),
                None,
                None
               )
             in
             (entry :: acc_table, SymSet.empty)
        ) (L.all_resources local) ([], SymSet.empty)
    in
    let var_lines = 
      List.filter_map (fun c ->
          let bt = c.veclass.sort in
          let relevant = not (SymSet.is_empty (SymSet.inter c.veclass.l_elements relevant)) in
          let reported = not (SymSet.is_empty (SymSet.inter c.veclass.l_elements reported_pointees)) in
          if (not reported) && relevant then
            match bt with
            | BT.Loc -> 
               Some (Some (Ast.Terms.pp false c.path), 
                     o_evaluate o_model (IT.sym_ (c.veclass.repr, bt)),
                     None, 
                     None, 
                     None, 
                     None)
            | _ -> 
               Some (None,
                     None, 
                     None, 
                     None, 
                     Some (Ast.Terms.pp false c.path), 
                     o_evaluate o_model (IT.sym_ (c.veclass.repr, bt)))
          else
            None)
        veclasses
    in
    resource_lines @ var_lines



  let pp_state_with_model local explanation o_model =
    let lines = 
      List.map (fun (a,b,c,d,e,f) -> ((L,a), (R,b), (R,c), (L,d), (L,e), (R,f)))
        (pp_state_aux local explanation o_model)
    in
    table6 ("pointer", "location", "size", "state", "variable", "value") lines
      

  let pp_state local explanation =
    let lines = 
      List.map (fun (a,_,c,d,e,_) -> ((L,a), (R,c), (L,d), (L,e)))
        (pp_state_aux local explanation None)
    in
    table4 ("pointer", "size", "state", "variable") lines


  let json_state names local : Yojson.Safe.t = 
    let (explanation, local) = explanation names local SymSet.empty in
    let lines = 
      List.map (fun (a,_,c,d,e,_) : Yojson.Safe.t ->
          let jsonf doc = `String (Pp.plain doc) in
          `Assoc [("pointer", Option.json jsonf a);
                  ("size", Option.json jsonf c);
                  ("state", Option.json jsonf d);
                  ("variable", Option.json jsonf e)]
        ) (pp_state_aux local explanation None)
    in
    `List lines


  let counter_model local = 
    let (_, solver) = S.holds_and_solver local (t_ (bool_ false)) in
    S.get_model solver



  let state names local = 
    let (explanation, local) = explanation names local SymSet.empty in
    pp_state local explanation

  let undefined_behaviour names local = 
    let (explanation, local) = explanation names local SymSet.empty in
    pp_state_with_model local explanation (counter_model local)

  let implementation_defined_behaviour names local it = 
    let (explanation, local) = 
      explanation names local (IT.free_vars it)
    in
    let it_pp = IT.pp (IT.subst_vars explanation.substitutions it) in
    (it_pp, pp_state_with_model local explanation (counter_model local))

  let missing_ownership names local it = 
    let (explanation, local) = explanation names local (IT.free_vars it) in
    let it_pp = IT.pp (IT.subst_vars explanation.substitutions it) in
    (it_pp, pp_state_with_model local explanation (counter_model local))

  let index_term names local it = 
    let (explanation, local) = 
      explanation names local (IT.free_vars it)
    in
    let it_pp = IT.pp (IT.subst_vars explanation.substitutions it) in
    it_pp

  let index_terms names local (it,it') = 
    let (explanation, local) = 
      explanation names local 
        (SymSet.union (IT.free_vars it) (IT.free_vars it'))
    in
    let it_pp = IT.pp (IT.subst_vars explanation.substitutions it) in
    let it_pp' = IT.pp (IT.subst_vars explanation.substitutions it') in
    (it_pp, it_pp')

  let unsatisfied_constraint names local lc = 
    let model = let (_,solver) = S.holds_and_solver local lc in S.get_model solver in
    let (explanation, local) = explanation names local (LC.free_vars lc) in
    let lc_pp = LC.pp (LC.subst_vars explanation.substitutions lc) in
    (lc_pp, pp_state_with_model local explanation model)

  let resource names local re = 
    let (explanation, local) = explanation names local (RE.free_vars re) in
    let re_pp = RE.pp (RE.subst_vars explanation.substitutions re) in
    (re_pp, pp_state_with_model local explanation (counter_model local))

  let resource_request names local re = 
    let (explanation, local) = explanation names local (RER.free_vars re) in
    let re_pp = RER.pp (RER.subst_vars explanation.substitutions re) in
    (re_pp, pp_state_with_model local explanation (counter_model local))

  let resources names local (re1, re2) = 
    let relevant = (SymSet.union (RE.free_vars re1) (RE.free_vars re2)) in
    let (explanation, local) = explanation names local relevant in
    let re1 = RE.pp (RE.subst_vars explanation.substitutions re1) in
    let re2 = RE.pp (RE.subst_vars explanation.substitutions re2) in
    ((re1, re2), pp_state_with_model local explanation (counter_model local))

end
