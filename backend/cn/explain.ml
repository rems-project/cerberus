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
      computational : SymSet.t;
      logical : SymSet.t;
    }


  let compare vc1 vc2 = compare vc1.id vc2.id
  let equal vc1 vc2 = vc1.id = vc2.id

  type vclass = t

  let make ((l, sort) : Sym.t * LS.t) : t = {
      id = Fresh.int (); 
      sort; 
      computational = SymSet.empty; 
      logical = SymSet.singleton l
    }

  let merge (c1 : t) (c2 : t) : t = 
    let computational = SymSet.union c1.computational c2.computational in
    let logical = SymSet.union c1.logical c2.logical in
    { c1 with id = Fresh.int (); computational; logical }

  let in_class (lvar : Sym.t) (c : t) = 
    SymSet.mem lvar c.logical

end

open VClass

module VClassSet = Set.Make(VClass)




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






  module VClassGraph = Graph.Make(VClass)

  let veclasses local model = 
    let find_class p classes = 
      VClassSet.choose (VClassSet.filter p classes) in
    let with_logical = 
      List.fold_right (fun (l, sort) g ->
          VClassSet.add (make (l, sort)) g
        ) (L.all_logical local) VClassSet.empty
    in
    (* add computational variables into the classes *)
    let with_all = 
      List.fold_right (fun (s, (bt, l)) g ->
          let c = find_class (in_class l) g in
          let c' = { c with computational = SymSet.add s c.computational } in
          VClassSet.add c' (VClassSet.remove c g)
        ) (L.all_computational local) with_logical
    in
    (* merge classes based on variable equalities *)
    List.fold_right (fun lc g ->
        match is_sym_equality lc with
        | Some (s, s') ->
           let c = find_class (in_class s) g in
           let c' = find_class (in_class s') g in
           let merged = VClass.merge c c' in
           VClassSet.add merged 
             (VClassSet.remove c' 
                (VClassSet.remove c g))
        | None -> 
           g
      ) (L.all_constraints local) with_all


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

    (* add 'Pointee' edges between nodes whenever the resources indicate that *)
    let graph = 
      List.fold_right (fun resource graph ->
          match resource with
          (* | RE.Point {pointer; size; value; init; permission} ->
           *    (\* the 'not found' cases should not be fatal: e.g. the
           *       resource might have 'x + 16' as a pointer *\)
           *    let ovc1 = 
           *      Option.bind (IT.is_sym pointer) 
           *        (fun (s, _) -> VClassGraph.find_node_opt (in_class s) graph)
           *    in
           *    let ovc2 = 
           *      Option.bind (IT.is_sym value)
           *        (fun (s, _) -> VClassGraph.find_node_opt (in_class s) graph)
           *    in
           *    begin match ovc1, ovc2 with
           *    | Some vc1, Some vc2 -> VClassGraph.add_edge (vc1, vc2) Pointee graph
           *    | _ -> graph
           *    end *)
          | _ -> 
             graph
        ) (L.all_resources local) 
        (VClassSet.fold VClassGraph.add_node (veclasses local model) VClassGraph.empty)
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




  let rec evaluate model expr : string = 
    match Z3.Model.evaluate model (S.expr expr) true with
    | None -> "(not evaluated)"
    | Some evaluated_expr -> 
       match IT.bt expr with
       | BT.Integer -> 
          Z3.Expr.to_string evaluated_expr
       | BT.Real -> 
          Z3.Expr.to_string evaluated_expr
       | BT.Loc ->
          (* adapting from core_parser_driver.ml *)
          let str = Z3.Expr.to_string evaluated_expr in
          let lexbuf = Lexing.from_string str in
          let z = try Assertion_parser.integer Assertion_lexer.main lexbuf with
                  | _ -> Debug_ocaml.error ("error parsing string: " ^ str)
          in
          Pp.plain (Z.pp_hex 16 z)
       | BT.Bool ->
          Z3.Expr.to_string evaluated_expr
       | BT.Array _ ->
          Z3.Expr.to_string evaluated_expr
       | BT.Unit ->
          Pp.plain (BT.pp BT.Unit)
       | BT.Struct tag ->
         let layout = Global.SymMap.find tag G.global.struct_decls in
         let members = Memory.member_types layout in
         let members = 
           List.map (fun (member, sct) -> 
               let s = evaluate model (IT.member_ ~member_bt:(BT.of_sct sct) (tag, expr, member)) in
               "." ^ Id.pp_string member ^ " = " ^ s
             ) members 
         in
         "{" ^ (String.concat ", " members) ^ "}"
       | _ -> 
          "(not evaluated)"

  let evaluate_bool model expr = 
    match evaluate model expr with
    | "true" -> true
    | "false" -> false
    | str -> Debug_ocaml.error ("error parsing string: " ^ str)

  let symbol_it = function
    | IT.IT (Lit (Sym s), _) -> SymSet.singleton s
    | _ -> SymSet.empty

  let pp_state_aux local {substitutions; vclasses; relevant} o_model =
    (* let resources = List.map (RE.subst_vars substitutions) (L.all_resources local) in *)


    let (resource_lines, reported_pointees) = 
      List.fold_right (fun resource (acc_table, acc_reported) ->
          match resource with
          | Point p ->
             let loc_val = !^(evaluate o_model p.pointer) in
             let size = !^(Z.to_string p.size) in
             let loc_expr = IT.pp (IT.subst_vars substitutions p.pointer) in
             let permission_v = evaluate o_model p.permission in
             let init_v = evaluate_bool o_model p.init in
             let state = 
               !^"owned" ^^
                 begin match permission_v with
                 | "1.0" -> 
                    Pp.empty
                 | _ ->
                    Pp.space ^^ comma ^^^ !^"permission" ^^ colon ^^^ !^permission_v
                 end ^^ comma ^^^
                   !^(if init_v then "init" else "uninit")
             in
             let value = 
               (BT.pp (IT.bt p.value)) ^^^ 
               IT.pp (IT.subst_vars substitutions p.value) ^^^ 
               equals ^^^
               !^(evaluate o_model p.value) 
             in
             let entry = (Some loc_expr, Some loc_val, Some size, Some state, Some value) in
             let reported = 
               List.fold_left SymSet.union SymSet.empty
                 [symbol_it p.pointer; 
                  IT.free_vars p.value;
                  IT.free_vars p.init;
                  IT.free_vars p.permission;
                 ]
             in
             (entry :: acc_table, SymSet.union reported acc_reported)
          | QPoint p ->
             let p = RE.alpha_rename_qpoint p "?p" in
             let loc_expr = Sym.pp p.qpointer in
             let value = (BT.pp (IT.bt p.value)) ^^^ !^(evaluate o_model p.value) in
             let entry = (Some loc_expr, None, None, None, Some value) in
             (entry :: acc_table, SymSet.add p.qpointer acc_reported)
          | Predicate p when p.unused ->
             begin match p.name, p.oargs with
             | Ctype ct, [p_value; p_init] ->
                let loc_val = !^(evaluate o_model p.pointer) in
                let osize = Option.map (fun n -> !^(Z.to_string n)) (Memory.size_of_ctype_opt ct) in
                let loc_expr = IT.pp (IT.subst_vars substitutions p.pointer) in
                let init_v = !^(evaluate o_model p_init) in
                let state = !^"owned" ^^ comma ^^^ !^"init:" ^^^ init_v in
                let value = 
                  (BT.pp (IT.bt p_value)) ^^^ 
                    IT.pp (IT.subst_vars substitutions p_value) ^^^ 
                      equals ^^^
                        !^(evaluate o_model p_value) 
                in
                let entry = (Some loc_expr, Some loc_val, osize, Some state, Some value) in
                let reported = 
                  List.fold_left SymSet.union SymSet.empty
                    [symbol_it p.pointer; 
                     IT.free_vars p_value;
                     IT.free_vars p_init;
                    ]
                in
                (entry :: acc_table, SymSet.union reported acc_reported)
             | _ ->
                let loc_val = !^(evaluate o_model p.pointer) in
                let loc_expr = IT.pp (IT.subst_vars substitutions p.pointer) in
                let state = (RE.pp (RE.subst_vars substitutions (Predicate p))) in
                let entry = (Some loc_expr, Some loc_val, None, Some state, None) in
                (entry :: acc_table, symbol_it p.pointer)
             end
          | QPredicate p when p.unused ->
             let index_name = "$i" in
             let p = RE.alpha_rename_qpredicate p index_name in
             let pointer = qpredicate_index_to_pointer p (sym_ (p.i, BT.Integer)) in
             let pred = ({pointer; name = p.name; iargs = p.iargs; oargs = p.oargs; unused = true} :  predicate) in
             let loc_val = !^(evaluate o_model p.pointer) in
             let loc_expr = IT.pp (IT.subst_vars substitutions pred.pointer) in
             let state = 
               !^"for each" ^^^ 
                 IT.pp p.istart ^^ !^ "<="^^ !^index_name^^ !^"<" ^^ IT.pp p.iend ^^ colon ^^^ 
                   (RE.pp (RE.subst_vars substitutions (Predicate pred))) 
             in 
             let entry = (Some loc_expr, Some loc_val, None, Some state, None) in
             (entry :: acc_table, symbol_it p.pointer)
          | _ ->
             (acc_table, acc_reported)
        ) (L.all_resources local) ([], SymSet.empty)
    in
    let report vclass = 
      let relevant = not (SymSet.is_empty (SymSet.inter vclass.logical relevant)) in
      let reported = not (SymSet.is_empty (SymSet.inter vclass.logical reported_pointees)) in
      (not reported) && relevant
    in
    let memory_var_lines = 
      List.filter_map (fun (vclass,c) ->
          if report vclass && BT.equal vclass.sort Loc then
               let loc_val = !^(evaluate o_model (IT.sym_ (SymSet.choose vclass.logical, vclass.sort))) in
               let loc_expr = Ast.Terms.pp false c.path in
               let entry = (Some loc_expr, Some loc_val, None, None, None) in
               Some entry
          else None
        ) vclasses
    in
    let logical_var_lines = 
      List.filter_map (fun (vclass,c) ->
          if report vclass && not (BT.equal vclass.sort Loc) then
            let expr = Ast.Terms.pp false c.path in
            let state = !^(evaluate o_model (IT.sym_ (SymSet.choose vclass.logical, vclass.sort))) in
            let entry = (Some expr, Some state) in
            Some entry
          else
            None)
        vclasses
    in
    (resource_lines @ memory_var_lines, logical_var_lines)



  let pp_state_with_model local explanation o_model =
    let (memory, variables) = (pp_state_aux local explanation o_model) in
    table5 ("pointer", "location", "size", "state", "value") 
      (List.map (fun (a, b, c, d, e) -> ((L, a), (R, b), (R, c), (L, d), (L, e))) memory) ^/^
    table2 ("variable", "value") 
      (List.map (fun (a, b) -> ((L, a), (L, b))) variables)
      

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
