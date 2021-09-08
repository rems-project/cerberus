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
module Loc = Locations

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


let find_class p classes = 
  VClassSet.choose (VClassSet.filter p classes)




let good_description s = 
  match Sym.description s with
  | Sym.SD_Id _ -> None
  | Sym.SD_None -> None
  | Sym.SD_ObjectAddress name -> Some (Ast.Addr name)
  | Sym.SD_Return -> Some (Ast.Var "return")
  | Sym.SD_FunArg (loc, i) -> 
     Some (Ast.Addr ("ARG" ^ string_of_int i ^ "@" ^ Loc.simple_location loc))
  (* | Sym.SD_Pointee *)

let has_good_description s =
  Option.is_some (good_description s)




let counter_and_increment (ref : int ref) = 
  let c = !ref in
  let () = ref := (c + 1) in
  c


let make_predicate_name = 
  let c = ref 0 in
  fun () ->
  "?pred" ^ string_of_int (counter_and_increment c)

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
  fun sort ->
  "?" ^ bt_prefix sort ^ 
    string_of_int (counter_and_increment (bt_counter sort))






type variable_relation = 
  | Pointee  

type name_kind = 
  | Description
  | Derived
  | Default

type vclass_explanation = {
    path : Ast.term;
    name_kind : name_kind;
  }

type explanation = {
    substitution : IT.t Subst.t;
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

    (* only report the state of the relevant variables *)
    let relevant =
      List.fold_left SymSet.union SymSet.empty
        [SymSet.of_list (List.filter has_good_description (L.all_vars local)); 
         RE.free_vars_list (L.all_resources local); 
         relevant]
    in

    (* add 'Pointee' edges between nodes whenever the resources indicate that *)
    let graph = 
      VClassSet.fold VClassGraph.add_node (veclasses local model) 
        VClassGraph.empty 
    in
    let graph = 
      List.fold_right (fun resource graph ->
          match resource with
          | RE.Point p ->
             (* the 'not found' cases should not be fatal: e.g. the
                resource might have 'x + 16' as a pointer *)
             let ovc1 = 
               Option.bind (IT.is_sym p.pointer) 
                 (fun (s, _) -> VClassGraph.find_node_opt (in_class s) graph)
             in
             let ovc2 = 
               Option.bind (IT.is_sym p.value)
                 (fun (s, _) -> VClassGraph.find_node_opt (in_class s) graph)
             in
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
          let has_description = 
            let all = SymSet.elements (SymSet.union vclass.computational vclass.logical) in
            List.find_map good_description all
          in        
          let has_derived_name =
            List.find_map (fun (named_vclass, {path;_}) -> 
                Option.bind 
                  (VClassGraph.edge_label (named_vclass, vclass) graph)
                  (function Pointee -> Some (Ast.pointee path))  
              ) vclasses_explanation
          in
          match has_description, has_derived_name with
          | Some description, _ ->
             vclasses_explanation @ [(vclass, {path = description; name_kind = Description})]
          | None, Some derived_name ->
             vclasses_explanation @ [(vclass, {path = derived_name; name_kind = Derived})]
          | None, None ->
             let name = make_name vclass.sort in
             vclasses_explanation @ [(vclass, {path = Var name; name_kind = Default})]
        ) [] (VClassGraph.linearise graph)
    in


    let substitution = 
      List.fold_right (fun (vclass, {path;_}) subst ->
          let to_substitute = SymSet.union vclass.computational vclass.logical in
          let named_symbol = Sym.fresh_named (Pp.plain (Ast.Terms.pp false path)) in
          SymSet.fold (fun sym subst ->
              (sym, sym_ (named_symbol, vclass.sort)) :: subst
            ) to_substitute subst
        ) vclass_explanations []
    in

    {substitution; vclasses = vclass_explanations; relevant}




  let rec evaluate model expr : string = 
    match Z3.Model.evaluate model (S.term expr) true with
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

  let pp_state_aux local {substitution; vclasses; relevant} o_model =

    let (points, predicates, predicate_oargs, reported) = 
      List.fold_right (fun resource acc ->

          let (points, 
               predicates, 
               predicate_oargs, 
               acc_reported) = acc 
          in

          match resource with
          | Point p ->
             let loc_expr = IT.pp (IT.subst substitution p.pointer) in
             let loc_val = !^(evaluate o_model p.pointer) in
             let permission_v = evaluate o_model p.permission in
             let init_v = evaluate o_model p.init in
             let state = 
               Sctypes.pp p.ct ^^^
                 parens (
                   !^"permission" ^^ colon ^^^ !^permission_v ^^ comma ^^^
                   !^"init" ^^ colon ^^ !^init_v
                   )
             in
             let value = 
               IT.pp (IT.subst substitution p.value) ^^^ 
               equals ^^^
               !^(evaluate o_model p.value) 
             in
             let entry = (Some loc_expr, Some loc_val, Some state, Some value) in
             let reported = 
               List.fold_left SymSet.union SymSet.empty
                 [symbol_it p.pointer; 
                  IT.free_vars p.value;
                  IT.free_vars p.init;
                  IT.free_vars p.permission;
                 ]
             in
             (entry :: points, 
              predicates, 
              predicate_oargs,
              SymSet.union reported acc_reported)
          | QPoint p ->
             let p = alpha_rename_qpoint (Sym.fresh_same p.qpointer) p in
             let loc_expr = !^"each" ^^^ Sym.pp p.qpointer in
             let permission_v = evaluate o_model p.permission in
             let init_v = evaluate o_model p.init in
             let state = 
               Sctypes.pp p.ct ^^^
                 parens (
                   !^"permission" ^^ colon ^^^ !^permission_v ^^ comma ^^^
                   !^"init" ^^ colon ^^ !^init_v
                   )
             in
             let value = 
               IT.pp (IT.subst substitution p.value) ^^^ 
               equals ^^^
               !^(evaluate o_model p.value) 
             in
             let entry = (Some loc_expr, None, Some state, Some value) in
             let reported = 
               SymSet.remove p.qpointer
                 (List.fold_left SymSet.union SymSet.empty
                    [IT.free_vars p.value;
                     IT.free_vars p.init;
                     IT.free_vars p.permission;
                    ])
             in
             (entry :: points, 
              predicates,
              predicate_oargs,
              SymSet.union reported acc_reported)
          | Predicate p ->
             let id = make_predicate_name () in
             let loc_expr = IT.pp (IT.subst substitution p.pointer) in
             let loc_val = !^(evaluate o_model p.pointer) in
             let permission_v = evaluate o_model p.permission in
             let state = 
               !^id ^^^ equals ^^^
               Pp.string p.name ^^
                 parens (separate comma (List.map (fun i -> IT.pp (IT.subst substitution i)) 
                                           (p.pointer :: p.iargs))) ^^^
                   parens (!^"permission" ^^ colon ^^^ !^permission_v)
             in
             let entry = (Some loc_expr, Some loc_val, Some state) in
             let predicate_def = Option.get (Global.get_predicate_def G.global p.name) in
             let oargs = 
               List.map2 (fun oarg (name, _) ->
                   let var = !^id ^^ dot ^^ dot ^^ !^name in
                   let value = IT.pp oarg ^^^ equals ^^^ !^(evaluate o_model oarg) in
                   (Some var, Some value)
                 ) p.oargs predicate_def.oargs
             in
             (points, 
              entry :: predicates,
              oargs @ predicate_oargs,
              SymSet.union (symbol_it p.pointer) acc_reported)
          | QPredicate p ->
             let p = alpha_rename_qpredicate (Sym.fresh_same p.qpointer) p in
             let id = make_predicate_name () in
             let loc_expr = !^"each" ^^^ Sym.pp p.qpointer in
             let permission_v = evaluate o_model p.permission in
             let state = 
               !^id ^^^ equals ^^^
               Pp.string p.name ^^
                 parens (separate comma (List.map (fun i -> IT.pp (IT.subst substitution i)) 
                                           (sym_ (p.qpointer, BT.Loc) :: p.iargs))) ^^^
                   parens (!^"permission" ^^ colon ^^^ !^permission_v)
             in
             let entry = (Some loc_expr, None, Some state) in
             let predicate_def = Option.get (Global.get_predicate_def G.global p.name) in
             let oargs = 
               List.map2 (fun oarg (name, _) ->
                   let var = !^id ^^ dot ^^ dot ^^ !^name in
                   let value = IT.pp oarg ^^^ equals ^^^ !^(evaluate o_model oarg) in
                   (Some var, Some value)
                 ) p.oargs predicate_def.oargs
             in
             (points, 
              entry :: predicates,
              oargs @ predicate_oargs,
              acc_reported)

        ) (L.all_resources local) ([], [], [], SymSet.empty)
    in
    let report vclass = 
      let syms = SymSet.union vclass.logical vclass.computational in
      let relevant = not (SymSet.is_empty (SymSet.inter syms relevant)) in
      let unreported = SymSet.is_empty (SymSet.inter syms reported) in
      relevant && unreported
    in
    let memory_var_lines = 
      List.filter_map (fun (vclass,c) ->
          if report vclass && BT.equal vclass.sort Loc then
               let loc_val = !^(evaluate o_model (IT.sym_ (SymSet.choose vclass.logical, vclass.sort))) in
               let loc_expr = Ast.Terms.pp false c.path in
               let entry = (Some loc_expr, Some loc_val, None, None) in
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

    (* let () = print stdout (list Local.pp_old (L.old local)) in *)

    (points @ memory_var_lines, predicates, predicate_oargs @ logical_var_lines)



  let pp_state_with_model local explanation o_model =
    let (memory, predicates, variables) = (pp_state_aux local explanation o_model) in
    table4 ("pointer", "location", "state", "value") 
      (List.map (fun (a, b, c, d) -> ((L, a), (R, b), (R, c), (L, d))) memory) ^/^
    table3 ("pointer", "location", "predicate") 
      (List.map (fun (a, b, c) -> ((L, a), (R, b), (R, c))) predicates) ^/^
    table2 ("expression", "value") 
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
    let _ = S.provable (L.solver local) (t_ (bool_ false)) in
    let model = S.get_model (L.solver local) in
    let explanation = explanation local model SymSet.empty in
    pp_state_with_model local explanation model

  let implementation_defined_behaviour local it = 
    let _ = S.provable (L.solver local) (t_ (bool_ false)) in
    let model = S.get_model (L.solver local) in
    let explanation = explanation local model (IT.free_vars it) in
    let it_pp = IT.pp (IT.subst explanation.substitution it) in
    (it_pp, pp_state_with_model local explanation model)

  let missing_ownership local model it = 
    let explanation = explanation local model (IT.free_vars it) in
    let it_pp = IT.pp (IT.subst explanation.substitution it) in
    (it_pp, pp_state_with_model local explanation model)

  let index_term local it = 
    let _ = S.provable (L.solver local) (t_ (bool_ false)) in
    let model = S.get_model (L.solver local) in
    let explanation = explanation local model (IT.free_vars it) in
    let it_pp = IT.pp (IT.subst explanation.substitution it) in
    it_pp

  let unsatisfied_constraint local model lc = 
    let explanation = explanation local model (LC.free_vars lc) in
    let lc_pp = LC.pp (LC.subst explanation.substitution lc) in
    (lc_pp, pp_state_with_model local explanation model)

  let resource local model re = 
    let explanation = explanation local model (RE.free_vars re) in
    let re_pp = RE.pp (RE.subst explanation.substitution re) in
    (re_pp, pp_state_with_model local explanation model)

  let resource_request local model re = 
    let explanation = explanation local model (RER.free_vars re) in
    let re_pp = RER.pp (RER.subst explanation.substitution re) in
    (re_pp, pp_state_with_model local explanation model)

  let resources local model (re1, re2) = 
    let relevant = (SymSet.union (RE.free_vars re1) (RE.free_vars re2)) in
    let explanation = explanation local model relevant in
    let re1 = RE.pp (RE.subst explanation.substitution re1) in
    let re2 = RE.pp (RE.subst explanation.substitution re2) in
    ((re1, re2), pp_state_with_model local explanation model)


  let illtyped_index_term local context it =
    let _ = S.provable (L.solver local) (t_ (bool_ false)) in
    let model = S.get_model (L.solver local) in
    let explanation = explanation local model (IT.free_vars_list [it; context]) in
    let it = IT.pp (IT.subst explanation.substitution it) in
    let context = IT.pp (IT.subst explanation.substitution context) in
    (context, it)

end
