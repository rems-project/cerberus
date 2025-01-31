module CF = Cerb_frontend
module CB = Cerb_backend
open Executable_spec_utils
module BT = BaseTypes
module A = CF.AilSyntax
module IT = IndexTerms
module LRT = LogicalReturnTypes
module LAT = LogicalArgumentTypes
module AT = ArgumentTypes

let rec add_records_to_map_from_it it =
  match IT.get_term it with
  | IT.Sym _s -> ()
  | Const c -> (match c with Default bt -> Cn_to_ail.augment_record_map bt | _ -> ())
  | Unop (_uop, t1) -> add_records_to_map_from_it t1
  | Binop (_bop, t1, t2) -> List.iter add_records_to_map_from_it [ t1; t2 ]
  | ITE (t1, t2, t3) -> List.iter add_records_to_map_from_it [ t1; t2; t3 ]
  | EachI ((_, (_, _), _), t) -> add_records_to_map_from_it t
  | Tuple _ts -> failwith "TODO: Tuples not yet supported"
  | NthTuple (_, _t) -> failwith "TODO: Tuples not yet supported"
  | Struct (_tag, members) ->
    List.iter (fun (_, it') -> add_records_to_map_from_it it') members
  | StructMember (t, _member) -> add_records_to_map_from_it t
  | StructUpdate ((t1, _member), t2) -> List.iter add_records_to_map_from_it [ t1; t2 ]
  | Record members ->
    (* Anonymous record instantiation -> add to records map *)
    Cn_to_ail.augment_record_map (IT.get_bt it);
    List.iter (fun (_, it') -> add_records_to_map_from_it it') members
  | RecordMember (t, _member) -> add_records_to_map_from_it t
  | RecordUpdate ((t1, _member), t2) -> List.iter add_records_to_map_from_it [ t1; t2 ]
  | Cast (_cbt, t) -> add_records_to_map_from_it t
  | MemberShift (t, _tag, _id) -> add_records_to_map_from_it t
  | ArrayShift { base; ct = _; index = _ } -> add_records_to_map_from_it base
  | CopyAllocId { addr; loc } -> List.iter add_records_to_map_from_it [ addr; loc ]
  | HasAllocId loc -> add_records_to_map_from_it loc
  | SizeOf _ct -> ()
  | OffsetOf (_tag, _member) -> ()
  | Nil _bt -> ()
  | Cons (t1, t2) -> List.iter add_records_to_map_from_it [ t1; t2 ]
  | Head t -> add_records_to_map_from_it t
  | Tail t -> add_records_to_map_from_it t
  | NthList (i, xs, d) -> List.iter add_records_to_map_from_it [ i; xs; d ]
  | ArrayToList (arr, i, len) -> List.iter add_records_to_map_from_it [ arr; i; len ]
  | Representable (_sct, t) -> add_records_to_map_from_it t
  | Good (_sct, t) -> add_records_to_map_from_it t
  | WrapI (_ity, t) -> add_records_to_map_from_it t
  | Aligned { t; align } -> List.iter add_records_to_map_from_it [ t; align ]
  | MapConst (_bt, t) -> add_records_to_map_from_it t
  | MapSet (t1, t2, t3) -> List.iter add_records_to_map_from_it [ t1; t2; t3 ]
  | MapGet (t1, t2) -> List.iter add_records_to_map_from_it [ t1; t2 ]
  | MapDef ((_, _), t) -> add_records_to_map_from_it t
  | Apply (_pred, ts) -> List.iter add_records_to_map_from_it ts
  | Let ((_, t1), t2) -> List.iter add_records_to_map_from_it [ t1; t2 ]
  | Match (e, cases) -> List.iter add_records_to_map_from_it (e :: List.map snd cases)
  | Constructor (_sym, args) -> List.iter add_records_to_map_from_it (List.map snd args)


let add_records_to_map_from_resource = function
  | Request.P p -> List.iter add_records_to_map_from_it (p.pointer :: p.iargs)
  | Q q ->
    List.iter add_records_to_map_from_it (q.pointer :: q.step :: q.permission :: q.iargs)


let add_records_to_map_from_lc = function
  | LogicalConstraints.T it | Forall (_, it) -> add_records_to_map_from_it it


let add_records_to_map_from_cn_statement = function
  | Cnprog.Assert lc -> add_records_to_map_from_lc lc
  (* All other CN statements are (currently) no-ops at runtime *)
  | Pack_unpack _ | To_from_bytes _ | Have _ | Instantiate _ | Split_case _ | Extract _
  | Unfold _ | Apply _ | Inline _ | Print _ ->
    ()


let add_records_to_map_from_cnprogs (_, cn_progs) =
  let rec aux = function
    | Cnprog.Let (_, (_, { ct = _; pointer }), prog) ->
      add_records_to_map_from_it pointer;
      aux prog
    | Statement (_, stmt) -> add_records_to_map_from_cn_statement stmt
  in
  List.iter aux cn_progs


let add_records_to_map_from_instrumentation (i : Executable_spec_extract.instrumentation) =
  let rec aux_lrt = function
    | LRT.Define ((_, it), _, t) ->
      add_records_to_map_from_it it;
      aux_lrt t
    | Resource ((_, (re, _)), _, t) ->
      add_records_to_map_from_resource re;
      aux_lrt t
    | Constraint (lc, _, t) ->
      add_records_to_map_from_lc lc;
      aux_lrt t
    | I -> ()
  in
  let aux_rt = function ReturnTypes.Computational (_, _, t) -> aux_lrt t in
  let rec aux_lat = function
    | LAT.Define ((_, it), _, lat) ->
      add_records_to_map_from_it it;
      aux_lat lat
    | Resource ((_, (ret, _)), _, lat) ->
      add_records_to_map_from_resource ret;
      aux_lat lat
    | Constraint (lc, _, lat) ->
      add_records_to_map_from_lc lc;
      aux_lat lat
    (* Postcondition *)
    | I i -> i
  in
  let rec aux_at = function
    | AT.Computational ((_, _), _, at) -> aux_at at
    | L lat -> aux_lat lat
  in
  match i.internal with
  | None -> ()
  | Some instr ->
    let rt, (stmts, loops) = aux_at instr in
    aux_rt rt;
    List.iter add_records_to_map_from_cnprogs stmts;
    List.iter
      (fun (_loc, loop_at) ->
        let loop_stmts = aux_at loop_at in
        List.iter add_records_to_map_from_cnprogs loop_stmts)
      loops


let rec populate ?cn_sym bt =
  match bt with
  | BT.Record members ->
    (match cn_sym with
     (* Naming convention only needed for top-level records returned from CN functions and predicates *)
     | Some cn_sym' -> Cn_to_ail.augment_record_map ~cn_sym:cn_sym' bt
     | None -> Cn_to_ail.augment_record_map bt);
    List.iter (fun bt' -> populate bt') (List.map snd members)
  | _ -> ()


let add_records_to_map_from_fns_and_preds cn_funs cn_preds =
  let fun_syms_and_ret_types =
    List.map (fun (sym, (def : Definition.Function.t)) -> (sym, def.return_bt)) cn_funs
  in
  let pred_syms_and_ret_types =
    List.map (fun (sym, (def : Definition.Predicate.t)) -> (sym, def.oarg_bt)) cn_preds
  in
  List.iter
    (fun (cn_sym, bt) -> populate ~cn_sym bt)
    (fun_syms_and_ret_types @ pred_syms_and_ret_types)


let add_records_to_map_from_datatype (dt : Mucore.datatype) =
  let bts = List.map (fun (_, ms) -> List.map snd ms) dt.cases in
  let bts = List.concat bts in
  List.iter populate bts


let add_records_to_map_from_struct (tag_def : Mucore.tag_definition) =
  match tag_def with
  | Mucore.StructDef sl ->
    List.iter
      (fun (sp : Memory.struct_piece) ->
        match sp.member_or_padding with
        | Some (_, sct) ->
          populate
            (BT.of_sct Memory.is_signed_integer_type Memory.size_of_integer_type sct)
        | None -> ())
      sl
  | UnionDef -> ()


(* Populate record table *)
let populate_record_map
  (instrumentation : Executable_spec_extract.instrumentation list)
  (prog5 : unit Mucore.file)
  =
  add_records_to_map_from_fns_and_preds prog5.logical_predicates prog5.resource_predicates;
  List.iter add_records_to_map_from_datatype (List.map snd prog5.datatypes);
  List.iter
    add_records_to_map_from_struct
    (List.map snd (Pmap.bindings_list prog5.tagDefs));
  List.iter add_records_to_map_from_instrumentation instrumentation


let generate_all_record_strs () =
  let ail_records =
    Cn_to_ail.cn_to_ail_records (Cn_to_ail.RecordMap.bindings !Cn_to_ail.records)
  in
  let record_def_strs, record_decl_strs =
    Executable_spec_internal.generate_c_records ail_records
  in
  (record_def_strs, record_decl_strs)


let generate_c_record_funs (sigm : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma) =
  let cn_record_info = Cn_to_ail.RecordMap.bindings !Cn_to_ail.records in
  let cn_record_info = List.map (fun (ms, sym) -> (sym, ms)) cn_record_info in
  let record_equality_functions =
    List.concat
      (List.map
         (Cn_to_ail.generate_record_equality_function sigm.cn_datatypes)
         cn_record_info)
  in
  let record_default_functions =
    List.concat
      (List.map
         (Cn_to_ail.generate_record_default_function sigm.cn_datatypes)
         cn_record_info)
  in
  let record_map_get_functions =
    List.concat (List.map Cn_to_ail.generate_record_map_get cn_record_info)
  in
  let eq_decls, eq_defs = List.split record_equality_functions in
  let default_decls, default_defs = List.split record_default_functions in
  let mapget_decls, mapget_defs = List.split record_map_get_functions in
  let modified_prog1 : CF.GenTypes.genTypeCategory CF.AilSyntax.sigma =
    { sigm with
      declarations = eq_decls @ default_decls @ mapget_decls;
      function_definitions = eq_defs @ default_defs @ mapget_defs
    }
  in
  let fun_doc =
    CF.Pp_ail.pp_program ~executable_spec:true ~show_include:true (None, modified_prog1)
  in
  let fun_strs = CF.Pp_utils.to_plain_pretty_string fun_doc in
  let decl_docs =
    List.map
      (fun (sym, (_, _, decl)) ->
        CF.Pp_ail.pp_function_prototype ~executable_spec:true sym decl)
      (eq_decls @ default_decls @ mapget_decls)
  in
  let fun_prot_strs =
    List.map (fun doc -> [ CF.Pp_utils.to_plain_pretty_string doc ]) decl_docs
  in
  let fun_prot_strs = String.concat "\n" (List.concat fun_prot_strs) in
  (fun_strs, fun_prot_strs)
