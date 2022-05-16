module IT = IndexTerms
module BT = BaseTypes
module RE = Resources.RE
module RER = Resources.Requests
module LC = LogicalConstraints
module LS = LogicalSorts
module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module StringMap = Map.Make(String)
module SymPairMap = Map.Make(SymRel.SymPair)
module C = Context
module Loc = Locations
module S = Solver

open Resources.RE
open IndexTerms
open LogicalConstraints
open Pp
open C




module VClass = struct

  type t = {
      id : int;
      sort : LS.t;
      computational_vars : SymSet.t;
      logical_vars : SymSet.t;
    }

  let compare vc1 vc2 = Stdlib.compare vc1.id vc2.id
  let equal vc1 vc2 = vc1.id = vc2.id

  type vclass = t

  let make ((l, sort) : Sym.t * LS.t) : t = {
      id = Fresh.int (); 
      sort; 
      computational_vars = SymSet.empty; 
      logical_vars = SymSet.singleton l
    }

  let merge (c1 : t) (c2 : t) : t = 
    assert (LS.equal c1.sort c2.sort);
    let computational_vars = 
      SymSet.union c1.computational_vars 
        c2.computational_vars 
    in
    let logical_vars = 
      SymSet.union c1.logical_vars c2.logical_vars 
    in
    { id = Fresh.int (); 
      sort = c1.sort;
      computational_vars; 
      logical_vars }

  let in_class (lvar : Sym.t) (c : t) = 
    SymSet.mem lvar c.logical_vars


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
  | Sym.SD_FunArgValue str ->
     Some (Ast.Var str)
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
  (* let option_c = ref 0 in *)
  let map_c = ref 0 in
  
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
    (* | Option _ -> "o" *)
    | Map _ -> "m"
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
    (* | Option _ -> option_c *)
    | Map _ -> map_c
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


module VClassGraph = Graph.Make(VClass)

let veclasses ctxt = 
  let with_logical = 
    List.fold_right (fun (l, sort) g ->
        VClassSet.add (make (l, sort)) g
      ) ctxt.logical VClassSet.empty
  in
  (* add computational variables into the classes *)
  let with_all = 
    List.fold_right (fun (s, (bt, l)) g ->
        let c = find_class (in_class l) g in
        let c' = { c with computational_vars = SymSet.add s c.computational_vars } in
        VClassSet.add c' (VClassSet.remove c g)
      ) ctxt.computational with_logical
  in
  (* merge classes based on variable equalities *)
  Context.LCSet.fold (fun lc g ->
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
    ) ctxt.constraints with_all


let explanation ctxt relevant =

  print stdout !^"producing error report";

  (* only report the state of the relevant variables *)
  let relevant = 
    List.fold_right (fun (s, _) acc -> 
        if has_good_description s then SymSet.add s acc else acc
      ) ctxt.computational relevant
  in
  let relevant = 
    List.fold_right (fun (s, _) acc -> 
        if has_good_description s then SymSet.add s acc else acc
      ) ctxt.logical relevant
  in
  let relevant = 
    List.fold_right (fun re acc ->
        SymSet.union (RE.free_vars re) acc
      ) ctxt.resources relevant
  in

  (* add 'Pointee' edges between nodes whenever the resources indicate that *)
  let graph = 
    VClassSet.fold VClassGraph.add_node (veclasses ctxt) VClassGraph.empty 
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
      ) ctxt.resources
      graph
  in

  (* add an explanation to each equivalence class: either because one o *)
  let vclass_explanations = 
    List.fold_left (fun vclasses_explanation vclass ->
        let has_description = 
          let all = 
            SymSet.elements 
              (SymSet.union vclass.computational_vars 
                 vclass.logical_vars) 
          in
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
        let to_substitute = 
          SymSet.union vclass.computational_vars 
            vclass.logical_vars 
        in
        let named_symbol = Sym.fresh_named (Pp.plain (Ast.Terms.pp false path)) in
        SymSet.fold (fun sym subst ->
            (sym, sym_ (named_symbol, vclass.sort)) :: subst
          ) to_substitute subst
      ) vclass_explanations []
  in

  { substitution = IT.make_subst substitution; 
    vclasses = vclass_explanations; 
    relevant = relevant }






let symbol_it = function
  | IT.IT (Lit (Sym s), _) -> SymSet.singleton s
  | _ -> SymSet.empty

let app_symbol_it q = function
  | IT.IT (Map_op (Get (IT (Lit (Sym v_s), _), IT (Lit (Sym i_s), _))), _)
       when Sym.equal i_s q ->
     SymSet.singleton v_s
  | _ -> SymSet.empty

let clause_has_resource req c =
  let open ArgumentTypes in
  let rec f = function
    | Resource (r, _, c) -> Resources.same_type_resource req r || f c
    | Constraint (_, _, c) -> f c
    | Computational (_, _, c) -> f c
    | Logical (_, _, c) -> f c
    | Define (_, _, c) -> f c
    | I _ -> false
  in
  let open ResourcePredicates in
  f c.packing_ft

let relevant_predicate_clauses global oname req =
  let open Global in
  let open ResourcePredicates in
  let clauses = StringMap.bindings global.resource_predicates
    |> List.map (fun (nm, def) -> List.map (fun c -> (nm, c)) def.clauses)
    |> List.concat in
  List.filter (fun (nm, c) -> Option.equal String.equal (Some nm) oname
    || clause_has_resource req c) clauses

let state ctxt {substitution; vclasses; relevant} (model_with_q : Solver.model_with_q)
    (orequest : RER.resource option) =

  let model, quantifier_counter_model = model_with_q in

  let open Report in

  let l_tr = let open Context in ctxt.location_trace in
  let location_trace = List.map (fun l -> Pp.string (Locations.to_string l))
    (List.rev l_tr) in

  let evaluate it = Solver.eval ctxt.global model it in

  let evaluate_lambda (q_s, q_bt) it = 
    let open Option in
    let lambda = map_def_ (q_s, q_bt) it in
    let@ it_val = evaluate lambda in
    match it_val with
    | IT (Map_op (Def ((s, _), body)), _) ->
       return (IT.subst (make_subst [(s, sym_ (q_s, q_bt))]) body)
    | _ ->
       return (map_get_ it_val (sym_ (q_s, q_bt)))
  in


  let maybe_evaluated = function
    | Some v -> IT.pp v
    | None -> parens !^"not evaluated"
  in

  let name_subst = IT.subst substitution in

  let entry = function
    | Point p ->
       let loc_e, permission_e, init_e, value_e = 
         IT.pp (name_subst p.pointer),
         IT.pp (name_subst p.permission),
         IT.pp (name_subst p.init), 
         IT.pp (name_subst p.value)
       in
       let loc_v, permission_v, init_v, value_v = 
         evaluate p.pointer,
         evaluate p.permission,
         evaluate p.init,
         evaluate p.value
       in
       let state = match Option.bind permission_v is_bool, Option.bind init_v is_bool with
         | Some true, Some true ->
            Sctypes.pp p.ct ^^ colon ^^^
            value_e ^^^ equals ^^^ maybe_evaluated value_v
         | _ -> 
            let permission = !^"permission" ^^ colon ^^^ maybe_evaluated permission_v in
            let init = !^"init" ^^ colon ^^^ maybe_evaluated init_v in
            Sctypes.pp p.ct ^^^ parens (permission ^^ comma ^^^ init) ^^ colon ^^^
            value_e ^^^ equals ^^^ maybe_evaluated value_v
       in
       let entry = {
           loc_e = Some loc_e; 
           loc_v = Some (maybe_evaluated loc_v); 
           state = Some state;
         } 
       in
       let reported = 
         List.fold_left SymSet.union SymSet.empty [
             symbol_it p.pointer; 
             symbol_it p.value;
           ]
       in
       (entry, [], reported)
    | QPoint p ->
       let p = alpha_rename_qpoint (Sym.fresh_pretty "i") p in
       let q = (p.q, BT.Integer) in
       let loc_e, permission_e, init_e, value_e = 
         IT.pp (name_subst p.pointer),
         IT.pp (name_subst p.permission),
         IT.pp (name_subst p.init), 
         IT.pp (name_subst p.value)
       in
       let loc_v, permission_v, init_v, value_v = 
         evaluate p.pointer,
         evaluate_lambda q p.permission,
         evaluate_lambda q p.init,
         evaluate_lambda q p.value
       in
       let state = 
         let permission = !^"permission" ^^ colon ^^^ maybe_evaluated permission_v in
         let init = !^"init" ^^ colon ^^^ init_e (* maybe_evaluated init_v *) in
         !^"each" ^^^ Sym.pp (fst q) ^^ colon ^^^
         Sctypes.pp p.ct ^^^ parens (permission ^^ comma ^^^ init) ^^ colon ^^^
           value_e (* ^^^ equals ^^^ maybe_evaluated value_v *)
       in
       let entry = {
           loc_e = Some loc_e;
           loc_v = Some (maybe_evaluated loc_v);
           state = Some state;
         } 
       in
       let reported = 
         (List.fold_left SymSet.union SymSet.empty [
              symbol_it p.pointer;
              (* app_symbol_it p.q p.value; *)
              (* app_symbol_it p.q p.init; *)
              app_symbol_it p.q p.permission;
         ])
       in
       (entry, [], reported)
    | Predicate p ->
       let id = make_predicate_name () in
       let loc_e, permission_e, iargs_e = 
         IT.pp (name_subst p.pointer),
         IT.pp (name_subst p.permission), 
         (List.map (fun i -> IT.pp (name_subst i)) p.iargs)
       in
       let loc_v, permission_v = 
         evaluate p.pointer,
         evaluate p.permission
       in
       let state = match Option.bind permission_v is_bool with
         | Some true ->
            !^id ^^^ equals ^^^
            Pp.string p.name ^^ parens (separate comma (loc_e :: iargs_e))
         | _ ->
            !^id ^^^ equals ^^^
            Pp.string p.name ^^ parens (separate comma (loc_e :: iargs_e)) ^^^
            parens (!^"permission" ^^ colon ^^^ maybe_evaluated permission_v)
       in
       let entry = {
           loc_e = Some loc_e;
           loc_v = Some (maybe_evaluated loc_v);
           state = Some state
           } 
       in
       let oargs = 
         let predicate_def = Option.get (Global.get_resource_predicate_def ctxt.global p.name) in
         List.map2 (fun oarg (name, _) ->
             let var = !^id ^^ dot ^^ dot ^^ Sym.pp name in
             let value = IT.pp oarg ^^^ equals ^^^ (maybe_evaluated (evaluate oarg)) in
             {var; value}
           ) p.oargs predicate_def.oargs
       in
       let reported = 
         (List.fold_left SymSet.union SymSet.empty (
              symbol_it p.pointer ::
              symbol_it p.permission ::
              List.map symbol_it p.iargs
         ))
       in
       (entry, oargs, reported)
    | QPredicate p ->
       let p = alpha_rename_qpredicate (Sym.fresh_pretty "i") p in
       let q = (p.q, BT.Integer) in
       let id = make_predicate_name () in
       let loc_e, permission_e, iargs_e = 
         IT.pp (name_subst p.pointer),
         IT.pp (name_subst p.permission), 
         (List.map (fun ia -> IT.pp (name_subst ia)) p.iargs)
       in
       let loc_v = evaluate p.pointer in
       let permission_v = evaluate_lambda q p.permission in
       let state = 
         !^id ^^^ equals ^^^
         !^"each" ^^^ Sym.pp (fst q) ^^ colon ^^^
         Pp.string p.name ^^ parens (separate comma (loc_e :: iargs_e)) ^^^
         parens (!^"permission" ^^ colon ^^^ maybe_evaluated permission_v)
       in
       let entry = {
           loc_e = Some loc_e;
           loc_v = Some (maybe_evaluated loc_v);
           state = Some state
         } 
       in
       let oargs = 
         let predicate_def = Option.get (Global.get_resource_predicate_def ctxt.global p.name) in
         List.map2 (fun oarg (name, _) ->
             let var = !^id ^^ dot ^^ dot ^^ Sym.pp name in
             let value = IT.pp oarg ^^^ equals ^^^ maybe_evaluated (evaluate_lambda q oarg) in
             {var; value}
           ) p.oargs predicate_def.oargs
       in
       let reported = 
         (List.fold_left SymSet.union SymSet.empty (
              symbol_it p.pointer ::
              app_symbol_it p.q p.permission ::
              List.map (app_symbol_it p.q) p.iargs
         ))
       in
       (entry, oargs, reported)
  in

  let (memory, predicate_oargs, reported) = 
    List.fold_right (fun resource acc ->
        let (memory, vars, reported) = acc in
        let (entry', vars', reported') = entry resource in
        let vars = vars' @ vars in
        let reported = SymSet.union reported' reported in
        (entry' :: memory, vars, reported)
      ) ctxt.resources ([], [], SymSet.empty)
  in
  let report vclass = 
    let syms = SymSet.union vclass.logical_vars vclass.computational_vars in
    let relevant = not (SymSet.is_empty (SymSet.inter syms relevant)) in
    let unreported = SymSet.is_empty (SymSet.inter syms reported) in
    relevant && unreported
  in
  let memory_var_lines = 
    List.filter_map (fun (vclass,c) ->
        if report vclass && BT.equal vclass.sort Loc then
             let loc_val = evaluate (IT.sym_ (SymSet.choose vclass.logical_vars, vclass.sort)) in
             let loc_expr = Ast.Terms.pp false c.path in
             let entry = 
               { loc_e = Some loc_expr;
                 loc_v = Some (maybe_evaluated loc_val);
                 state = None } 
             in
             Some entry
        else None
      ) vclasses
  in


  let logical_var_lines = 
    
    let qvars = List.mapi (fun i (qs, bt) ->
         let expr = 
           !^("?QVAR" ^ string_of_int i) ^^
             match List.assoc_opt Sym.equal qs substitution.replace with
             | None -> Pp.empty
             | Some it -> Pp.space ^^ equals ^^^ IT.pp it
         in
         let value = evaluate (IT.sym_ (qs, bt)) in
         {var = expr; value = maybe_evaluated value}
     ) quantifier_counter_model
    in


    qvars 
    @ 
    List.filter_map (fun (vclass,c) ->
        if report vclass && not (BT.equal vclass.sort Loc) then
          let expr = Ast.Terms.pp false c.path in
          let value = evaluate (IT.sym_ (SymSet.choose vclass.logical_vars, vclass.sort)) in
          let entry = {var = expr; value = maybe_evaluated value} in
          Some entry
        else
          None)
      vclasses
  in

  let constraints = 
    let trivial = function
      | T (IT (Lit (Bool true), _)) -> true
      | T (IT (Bool_op (EQ (t, t')), _)) -> IT.equal t t'
      | _ -> false
    in
    Context.LCSet.fold (fun lc acc ->
        let lc = LC.subst substitution lc in
        if trivial lc then acc else LC.pp lc :: acc
      ) ctxt.constraints []
  in

  let req_cmp = Option.bind orequest (Spans.spans_compare_for_pp model ctxt.global) in
  let req_entry req_cmp same req = {res = RER.pp (RER.subst substitution req);
    res_span = Spans.pp_model_spans model ctxt.global req_cmp req
        ^^ (if same then !^" - same-type" else !^"")} in
  let res_entry req_cmp same res = req_entry req_cmp same (RE.request res) in

  begin match orequest with
    | None -> ()
    | Some req -> Spans.diag_req ctxt.resources req model ctxt.global
  end;

  let requested = match orequest with
    | None -> []
    | Some req -> [req_entry None false req]
  in

  let (same_res, diff_res) = match orequest with
    | None -> ([], ctxt.resources)
    | Some req -> List.partition (Resources.same_type_resource req) ctxt.resources
  in
  let same = match (same_res, orequest) with
    | ([], Some _) -> [{res = !^""; res_span = !^"(no same-type resources)"}]
    | _ -> List.map (res_entry req_cmp true) same_res 
  in
  let resources = same @ List.map (res_entry req_cmp false) diff_res in

  let predicate_name = match orequest with
    | Some (Predicate p) -> Some p.name
    | Some (QPredicate qp) -> Some qp.name
    | _ -> None
  in
  let predicate_clauses = match orequest with
    | None -> []
    | Some req -> relevant_predicate_clauses ctxt.global predicate_name req
  in
  let doc_clause (nm, c) =
    let open ResourcePredicates in
    {
      cond = IT.pp c.guard;
      clause = ArgumentTypes.pp OutputDef.pp c.packing_ft
    }
  in
  let predicate_hints = List.map doc_clause predicate_clauses in

  { location_trace;
    memory = memory @ memory_var_lines;
    variables = predicate_oargs @ logical_var_lines;
    requested;
    resources;
    predicate_hints = predicate_hints;
    constraints }







