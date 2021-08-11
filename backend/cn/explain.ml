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


module VClass = struct

  type t = {
      id : int;
      sort : LS.t;
      ovalue : Z3.Expr.expr option;
      computational : SymSet.t;
      logical : SymSet.t;
    }


  let compare vc1 vc2 = compare vc1.id vc2.id
  let equal vc1 vc2 = vc1.id = vc2.id

  type vclass = t

  let make sort ovalue computational logical = 
    let id = Fresh.int () in
    { id; sort; ovalue; computational; logical }

  let right_class sort ovalue vclass =
    LS.equal sort vclass.sort &&
    match vclass.ovalue, ovalue with
    | Some value, Some value' ->
       Z3.Expr.equal value value'
    | _ -> false    

end

open VClass





let make_name = 
  let unit_c = ref 0 in
  let bool_c = ref 0 in
  let integer_c = ref 0 in
  let real_c = ref 0 in
  let loc_c = ref 0 in
  let list_c = ref 0 in
  let tuple_c = ref 0 in
  let struct_c = ref 0 in
  let set_c = ref 0 in
  let option_c = ref 0 in
  let array_c = ref 0 in
  
  let bt_prefix (bt : BT.t) = 
    match bt with
    | Unit -> "u"
    | Bool -> "b"
    | Integer -> "i"
    | Real -> "r"
    | Loc -> "l"
    | List _ -> "list"
    | Tuple _ -> "tuple"
    | Struct _ -> "s"
    | Set _ -> "set"
    | Option _ -> "option"
    | Array _ -> "a"
  in
  
  let bt_counter (bt : BT.t) = 
    match bt with
    | Unit -> unit_c
    | Bool -> bool_c
    | Integer -> integer_c
    | Real -> real_c
    | Loc -> loc_c
    | List _ -> list_c
    | Tuple _ -> tuple_c
    | Struct _ -> struct_c
    | Set _ -> set_c
    | Option _ -> option_c
    | Array _ -> array_c
  in


  let counter_and_increment bt = 
    let c = !(bt_counter bt) in
    let () = (bt_counter bt) := (c + 1) in
    c
  in
  fun vclass ->
  "?" ^ bt_prefix vclass.sort ^ 
    string_of_int (counter_and_increment vclass.sort)




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

type vclass_explanation = {
    path : Ast.term;
    name_kind : name_kind;
  }

type explanation = {
    substitutions : (Sym.t, Sym.t) Subst.t list;
    vclasses : (vclass * vclass_explanation) list;
    relevant : SymSet.t
  }


module Make 
         (G : sig val global : Global.t end)
         (S : Solver.S) 
         (L : Local.S)
  = struct 




  let evaluate model expr = 
    Z3.Model.evaluate model (S.expr expr) true


  module VClassGraph = Graph.Make(VClass)
  open VClassGraph     


  let explanation local model relevant =


    print stdout !^"producing error report";

    let names = SymMap.bindings (L.descriptions local) in

    (* only report the state of the relevant variables *)
    let relevant =
      List.fold_left SymSet.union SymSet.empty
        [SymSet.of_list (List.map fst names); 
         SymSet.of_list (List.filter Sym.named (L.all_vars local)); 
         RE.free_vars_list (L.all_resources local); 
         relevant]
    in

    (* populate empty graph with variable equivalence classes *)
    let graph = 
      (* for a new class vclass, add it into the graph, either merging
         it into an equivalent existing one or as a new class *)
      let classify vclass graph : 'a VClassGraph.t = 
        match find_node_opt (right_class vclass.sort vclass.ovalue) graph with
        | Some vclass' ->
           let c = SymSet.union vclass.computational vclass'.computational in
           let l = SymSet.union vclass.logical vclass'.logical in
           add_node { vclass with computational = c; logical = l}
             (remove_node vclass' graph)
        | None ->
           add_node vclass graph
      in
      let classify_l (l, bt) = 
        classify (VClass.make bt (evaluate model (sym_ (l, bt)))
                    SymSet.empty (SymSet.singleton l))
      in
      let classify_c (c, (bt, l)) =
        classify (VClass.make bt (evaluate model (sym_ (l, bt)))
                    (SymSet.singleton c) (SymSet.singleton l))
      in
      List.fold_right classify_l (L.all_logical local) 
        (List.fold_right classify_c (L.all_computational local)
           VClassGraph.empty) 
    in

    (* add 'Pointee' edges between nodes whenever the resources indicate that *)
    let graph = 
      List.fold_right (fun resource graph ->
          match resource with
          | RE.Point {pointer; size; value; init; permission} ->
             (* the 'not found' cases should not be fatal: e.g. the
                resource might have 'x + 16' as a pointer *)
             let ovc1 = VClassGraph.find_node_opt (right_class (IT.bt pointer) (evaluate model pointer)) graph in
             let ovc2 = VClassGraph.find_node_opt (right_class (IT.bt value) (evaluate model value)) graph in
             begin match ovc1, ovc2 with
             | Some vc1, Some vc2 -> VClassGraph.add_edge (vc1, vc2) Pointee graph
             | _ -> graph
             end
          | _ -> 
             graph
        ) (L.all_resources local) 
        graph
    in

    (* add an explanation to each equivalence class: either because one o *)
    let vclass_explanations = 
      List.fold_left (fun vclasses_explanation vclass ->
          let has_given_name =
            Option.map snd
              (List.find_opt (fun (sym,name) -> 
                   SymSet.mem sym vclass.logical ||
                     SymSet.mem sym vclass.computational
                 ) names)
          in
          let has_symbol_name = 
            let all = SymSet.elements (SymSet.union vclass.computational vclass.logical) in
            Option.map (fun s -> Ast.Addr s) (List.find_map Sym.name all)
          in        
          let has_derived_name =
            List.find_map (fun (named_vclass, {path;_}) -> 
                Option.bind 
                  (VClassGraph.edge_label (named_vclass, vclass) graph)
                  (function Pointee -> Some (Ast.pointee None path))  
              ) vclasses_explanation
          in
          match has_given_name, has_symbol_name, has_derived_name with
          | Some given_name, o_symbol_name, o_derived_name ->
             let without_labels = Ast.remove_labels_term given_name in
             let path = 
               if Option.equal Ast.term_equal (Some without_labels) (o_symbol_name) ||
                    Option.equal Ast.term_equal (Some without_labels) (o_derived_name) 
               then without_labels
               else given_name
             in
             vclasses_explanation @ [(vclass, {path; name_kind = Given})]
          | None, Some symbol_name, _ ->
             vclasses_explanation @ [(vclass, {path = symbol_name; name_kind = Symbol})]
          | None, None, Some derived_name ->
             vclasses_explanation @ [(vclass, {path = derived_name; name_kind = Symbol})]
          | None, None, None ->
             let name = Ast.LabeledName.{label = None; v = make_name vclass} in
             vclasses_explanation @ [(vclass, {path = Var name; name_kind = Default})]
        ) [] (VClassGraph.linearise graph)
    in


    let substitutions = 
      List.fold_right (fun (vclass, {path;_}) substs ->
          let to_substitute = SymSet.union vclass.computational vclass.logical in
          let named_symbol = Sym.fresh_named (Pp.plain (Ast.Terms.pp false path)) in
          SymSet.fold (fun sym substs ->
              Subst.{ before = sym; after = named_symbol } :: substs
            ) to_substitute substs 
        ) vclass_explanations []
    in

    ({substitutions; vclasses = vclass_explanations; relevant}, local)




  let rec o_evaluate model expr = 
    let open Option in
    match evaluate model expr with
    | None -> Debug_ocaml.error "failure constructing counter model"
    | Some evaluated_expr -> 
       match IT.bt expr with
       | BT.Integer -> 
          return (Pp.string (Z3.Expr.to_string evaluated_expr))
       | BT.Real -> 
          return (Pp.string (Z3.Expr.to_string evaluated_expr))
       | BT.Loc ->
          (* adapting from core_parser_driver.ml *)
          let str = Z3.Expr.to_string evaluated_expr in
          let lexbuf = Lexing.from_string str in
          let z = try Assertion_parser.integer Assertion_lexer.main lexbuf with
                  | _ -> Debug_ocaml.error ("error parsing string: " ^ str)
          in
          return (Z.pp_hex 16 z)
       | BT.Bool ->
          return (Pp.string (Z3.Expr.to_string evaluated_expr))
       | BT.Array _ ->
          return (Pp.string (Z3.Expr.to_string evaluated_expr))
       | BT.Unit ->
          return (BT.pp BT.Unit)
       | BT.Struct tag ->
         let layout = Global.SymMap.find tag G.global.struct_decls in
         let members = Memory.member_types layout in
         let@ members = 
           ListM.mapM (fun (member, sct) -> 
               let@ s = o_evaluate model (IT.member_ ~member_bt:(BT.of_sct sct) (tag, expr, member)) in
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


  let pp_state_aux local {substitutions; vclasses; relevant} o_model =
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
                o_evaluate o_model p.pointer, 
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
      List.filter_map (fun (vclass,c) ->
          let bt = vclass.sort in
          let relevant = not (SymSet.is_empty (SymSet.inter vclass.logical relevant)) in
          let reported = not (SymSet.is_empty (SymSet.inter vclass.logical reported_pointees)) in
          if (not reported) && relevant then
            match bt with
            | BT.Loc -> 
               Some (Some (Ast.Terms.pp false c.path), 
                     o_evaluate o_model (IT.sym_ (SymSet.choose vclass.logical, bt)),
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
                     o_evaluate o_model (IT.sym_ (SymSet.choose vclass.logical, bt)))
          else
            None)
        vclasses
    in
    resource_lines @ var_lines



  let pp_state_with_model local explanation o_model =
    let lines = 
      List.map (fun (a,b,c,d,e,f) -> ((L,a), (R,b), (R,c), (L,d), (L,e), (R,f)))
        (pp_state_aux local explanation o_model)
    in
    table6 ("pointer", "location", "size", "state", "variable", "value") lines
      

  (* let pp_state local explanation =
   *   let lines = 
   *     List.map (fun (a,_,c,d,e,_) -> ((L,a), (R,c), (L,d), (L,e)))
   *       (pp_state_aux local explanation None)
   *   in
   *   table4 ("pointer", "size", "state", "variable") lines *)


  (* let json_state local : Yojson.Safe.t = 
   *   let (explanation, local) = explanation local SymSet.empty in
   *   let lines = 
   *     List.map (fun (a,_,c,d,e,_) : Yojson.Safe.t ->
   *         let jsonf doc = `String (Pp.plain doc) in
   *         `Assoc [("pointer", Option.json jsonf a);
   *                 ("size", Option.json jsonf c);
   *                 ("state", Option.json jsonf d);
   *                 ("variable", Option.json jsonf e)]
   *       ) (pp_state_aux local explanation None)
   *   in
   *   `List lines *)


  (* let state local = 
   *   let (explanation, local) = explanation local SymSet.empty in
   *   pp_state local explanation *)

  let undefined_behaviour local = 
    let (_, solver) = 
      S.provable_and_solver (L.all_solver_constraints local) (t_ (bool_ false)) in
    let model = S.get_model solver in
    let (explanation, local) = explanation local model SymSet.empty in
    pp_state_with_model local explanation model

  let implementation_defined_behaviour local it = 
    let (_, solver) = 
      S.provable_and_solver (L.all_solver_constraints local) (t_ (bool_ false)) in
    let model = S.get_model solver in
    let (explanation, local) = explanation local model (IT.free_vars it) in
    let it_pp = IT.pp (IT.subst_vars explanation.substitutions it) in
    (it_pp, pp_state_with_model local explanation model)

  let missing_ownership local model it = 
    let (explanation, local) = explanation local model (IT.free_vars it) in
    let it_pp = IT.pp (IT.subst_vars explanation.substitutions it) in
    (it_pp, pp_state_with_model local explanation model)

  let index_term local it = 
    let (_, solver) = 
      S.provable_and_solver (L.all_solver_constraints local) (t_ (bool_ false)) in
    let model = S.get_model solver in
    let (explanation, local) = explanation local model (IT.free_vars it) in
    let it_pp = IT.pp (IT.subst_vars explanation.substitutions it) in
    it_pp

  let unsatisfied_constraint local model lc = 
    let (explanation, local) = explanation local model (LC.free_vars lc) in
    let lc_pp = LC.pp (LC.subst_vars explanation.substitutions lc) in
    (lc_pp, pp_state_with_model local explanation model)

  let resource local model re = 
    let (explanation, local) = explanation local model (RE.free_vars re) in
    let re_pp = RE.pp (RE.subst_vars explanation.substitutions re) in
    (re_pp, pp_state_with_model local explanation model)

  let resource_request local model re = 
    let (explanation, local) = explanation local model (RER.free_vars re) in
    let re_pp = RER.pp (RER.subst_vars explanation.substitutions re) in
    (re_pp, pp_state_with_model local explanation model)

  let resources local model (re1, re2) = 
    let relevant = (SymSet.union (RE.free_vars re1) (RE.free_vars re2)) in
    let (explanation, local) = explanation local model relevant in
    let re1 = RE.pp (RE.subst_vars explanation.substitutions re1) in
    let re2 = RE.pp (RE.subst_vars explanation.substitutions re2) in
    ((re1, re2), pp_state_with_model local explanation model)



  let illtyped_index_term local context it =
    let (_, solver) = 
      S.provable_and_solver (L.all_solver_constraints local) (t_ (bool_ false)) in
    let model = S.get_model solver in
    let (explanation, local) = 
      explanation local model (IT.free_vars_list [it; context])
    in
    let it = IT.pp (IT.subst_vars explanation.substitutions it) in
    let context = IT.pp (IT.subst_vars explanation.substitutions context) in
    (context, it)

end
