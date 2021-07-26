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

  type vclass = t


  let make sort ovalue = {
      id = Fresh.int ();
      sort = sort;
      ovalue = ovalue;
      computational = SymSet.empty;
      logical = SymSet.empty
    }

  let right_class vclass sort ovalue =
    LS.equal sort vclass.sort &&
    match vclass.ovalue, ovalue with
    | Some value, Some value' ->
       Z3.Expr.equal value value'
    | _ -> false

  let rec classify vclasses vclass' : vclass list = 
    match vclasses with
    | vclass :: vclasses when right_class vclass vclass'.sort vclass'.ovalue ->
       let computational = 
         SymSet.union vclass.computational vclass'.computational in
       let logical = 
         SymSet.union vclass.logical vclass'.logical in
       let vclass = { vclass with computational; logical} in
       vclass :: vclasses
    | vclass :: vclasses ->
       vclass :: classify vclasses vclass'
    | [] -> [vclass']
    

  let find vclasses sort value = 
    List.find_opt (fun vclass -> 
        right_class vclass sort value
      ) vclasses


  let compare vc1 vc2 = compare vc1.id vc2.id
  let equal vc1 vc2 = vc1.id = vc2.id

end

open VClass


module VClassPair = struct 
  type t = VClass.t * VClass.t
  let compare a b = 
    Lem_basic_classes.pairCompare VClass.compare VClass.compare a b
end
  
module VClassRel = struct
  include Pset
  type t = VClassPair.t Pset.set
  let empty = Pset.empty VClassPair.compare
  let transitiveClosure = Pset.tc VClassPair.compare
end 


module VClassRelMap = Map.Make(VClassPair)





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
    vclass : vclass;
  }

type explanation = {
    substitutions : (Sym.t, Sym.t) Subst.t list;
    vclasses : vclass_explanation list;
    relevant : SymSet.t
  }


module Make 
         (G : sig val global : Global.t end)
         (S : Solver.S) 
         (L : Local.S)
  = struct 




  let lvar_value model (l, bt) =
    Z3.Model.evaluate model (S.symbol_expression l bt) true




  let vclasses_graph local model vclasses =
    List.fold_right (fun resource graph ->
        match resource with
        | RE.Point {pointer; size; value; init; permission} ->
           let pointer_value, pointer_sort = 
             let (s,bt) = Option.value_err "resource not normalised" (IT.is_sym pointer) in
             (lvar_value model (s, bt), bt)
           in
           let value_value, value_sort = 
             let (s,bt) = Option.value_err "resource not normalised" (IT.is_sym value) in
             (lvar_value model (s, bt), bt)
           in
           let found1 = VClass.find vclasses pointer_sort pointer_value in
           let found2 = VClass.find vclasses value_sort value_value in
           begin match found1, found2 with
           | Some vclass1, Some vclass2 
                when not (VClassRelMap.mem (vclass2, vclass1) graph) ->
              (VClassRelMap.add (vclass1, vclass2) Pointee graph)
           | _ -> 
              graph
           end
        | _ -> 
           graph
      ) (L.all_resources local) 
      VClassRelMap.empty


  let vclasses_total_order local model vclasses = 
    let graph = vclasses_graph local model vclasses in

    let no_incoming_edges graph n = 
      not (VClassRelMap.exists (fun (_, n2) _ -> VClass.equal n n2) graph)
    in

    let order = [] in
    let inits, others = List.partition (no_incoming_edges graph) vclasses in

    let rec aux graph inits others order =
      match inits with
      | [] -> (List.rev order, others)
      | init :: inits ->
         let order = init :: order in
         let (graph, inits, others) = 
           VClassRelMap.fold (fun (n1, n2) _ (graph, inits, others) ->
               if VClass.equal init n1 then
                 let graph = VClassRelMap.remove (n1, n2) graph in
                 let new_inits, others = List.partition (no_incoming_edges graph) others in
                 (graph, inits @ new_inits, others)
               else 
                 (graph, inits, others)
             ) graph (graph, inits, others)
         in
         aux graph inits others order
    in

    let (order, not_yet_ordered) = aux graph inits others order in
    (order @ not_yet_ordered, graph)




  let has_given_name names veclass =
    Option.map snd
      (List.find_opt (fun (sym,name) -> 
           SymSet.mem sym veclass.logical ||
           SymSet.mem sym veclass.computational
         ) names)

  let has_derived_name (named_veclasses, rels) veclass =
    let rec aux = function
      | {vclass = named_veclass; path;_} :: named_veclasses ->
         begin match VClassRelMap.find_opt (named_veclass, veclass) rels with
         | Some Pointee -> Some (Ast.pointee None path)
         | None -> aux named_veclasses
         end
      | [] -> None         
    in
    aux named_veclasses

  let has_symbol_name veclass = 
    let all = SymSet.elements (SymSet.union veclass.computational veclass.logical) in
    Option.map (fun s -> Ast.Addr s) (List.find_map Sym.name all)


let explanation local model relevant =

  print stdout !^"producing error report";

  
  let names = SymMap.bindings (L.descriptions local) in


  let relevant =
    let names_syms = SymSet.of_list (List.map fst names) in
    let named_syms = SymSet.of_list (List.filter Sym.named (L.all_vars local)) in
    let from_resources = RE.free_vars_list (L.all_resources local) in
    SymSet.union (SymSet.union (SymSet.union names_syms named_syms) from_resources)
      relevant
  in

  let vclasses =

    let vclasses = 
      List.fold_left (fun vclasses (c, (bt, l)) ->
          classify vclasses 
            { (VClass.make bt (lvar_value model (l, bt))) with
              computational = SymSet.singleton c;
              logical = SymSet.singleton l; }
        ) [] (L.all_computational local)
    in

    let vclasses = 
      List.fold_left (fun vclasses (l, bt) ->
          classify vclasses 
            { (VClass.make bt (lvar_value model (l, bt))) with
              computational = SymSet.empty;
              logical = SymSet.singleton l; }
        ) vclasses (L.all_logical local)
    in

    let (sorted, rels) = vclasses_total_order local model vclasses in


    List.fold_left (fun vclasses_explanation vclass ->
        match has_given_name names vclass, 
              has_symbol_name vclass,
              has_derived_name (vclasses_explanation, rels) vclass with
        | Some given_name, o_symbol_name, o_derived_name ->
           let without_labels = Ast.remove_labels_term given_name in
           let path = 
             if Option.equal Ast.term_equal (Some without_labels) (o_symbol_name) ||
                  Option.equal Ast.term_equal (Some without_labels) (o_derived_name) 
             then without_labels
             else given_name
           in
           vclasses_explanation @ [{vclass; path; name_kind = Given}]
        | None, Some symbol_name, _ ->
           vclasses_explanation @ [{vclass; path = symbol_name; name_kind = Symbol}]
        | None, None, Some derived_name ->
           vclasses_explanation @ [{vclass; path = derived_name; name_kind = Symbol}]
        | None, None, None ->
           let name = Ast.LabeledName.{label = None; v = make_name vclass} in
           vclasses_explanation @ [{vclass; path = Var name; name_kind = Default}]
      ) [] sorted
  in

  let substitutions = 
    List.fold_right (fun {vclass;path;_} substs ->
        let to_substitute = SymSet.union vclass.computational vclass.logical in
        let named_symbol = Sym.fresh_named (Pp.plain (Ast.Terms.pp false path)) in
        SymSet.fold (fun sym substs ->
            Subst.{ before = sym; after = named_symbol } :: substs
          ) to_substitute substs 
      ) vclasses []
  in
  
  let () = Debug_ocaml.end_csv_timing "explanation" in
  
  ({substitutions; vclasses; relevant}, local)




  let rec o_evaluate model expr = 
    let open Option in
    match Z3.Model.evaluate model (fst (S.expr expr)) true with
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
          let bt = c.vclass.sort in
          let relevant = not (SymSet.is_empty (SymSet.inter c.vclass.logical relevant)) in
          let reported = not (SymSet.is_empty (SymSet.inter c.vclass.logical reported_pointees)) in
          if (not reported) && relevant then
            match bt with
            | BT.Loc -> 
               Some (Some (Ast.Terms.pp false c.path), 
                     o_evaluate o_model (IT.sym_ (SymSet.choose c.vclass.logical, bt)),
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
                     o_evaluate o_model (IT.sym_ (SymSet.choose c.vclass.logical, bt)))
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

  let index_terms local (it,it') = 
    let (_, solver) = 
      S.provable_and_solver (L.all_solver_constraints local) (t_ (bool_ false)) in
    let model = S.get_model solver in
    let (explanation, local) = 
      explanation local model (SymSet.union (IT.free_vars it) (IT.free_vars it'))
    in
    let it_pp = IT.pp (IT.subst_vars explanation.substitutions it) in
    let it_pp' = IT.pp (IT.subst_vars explanation.substitutions it') in
    (it_pp, it_pp')

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


end
