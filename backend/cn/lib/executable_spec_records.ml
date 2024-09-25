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
  match IT.term it with
  | IT.Sym _s -> ()
  | Const _c -> ()
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
    Cn_internal_to_ail.augment_record_map (IT.bt it);
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
  | ResourceTypes.P p -> List.iter add_records_to_map_from_it (p.pointer :: p.iargs)
  | Q q ->
    List.iter add_records_to_map_from_it (q.pointer :: q.step :: q.permission :: q.iargs)


let add_records_to_map_from_lc = function
  | LogicalConstraints.T it | Forall (_, it) -> add_records_to_map_from_it it


let add_records_to_map_from_cn_statement = function
  | Cnprog.M_CN_assert lc -> add_records_to_map_from_lc lc
  (* All other CN statements are (currently) no-ops at runtime *)
  | M_CN_pack_unpack _ | M_CN_have _ | M_CN_instantiate _ | M_CN_split_case _
  | M_CN_extract _ | M_CN_unfold _ | M_CN_apply _ | M_CN_inline _ | M_CN_print _ ->
    ()


let add_records_to_map_from_cnprogs (_, cn_progs) =
  let rec aux = function
    | Cnprog.M_CN_let (_, (_, { ct = _; pointer }), prog) ->
      add_records_to_map_from_it pointer;
      aux prog
    | M_CN_statement (_, stmt) -> add_records_to_map_from_cn_statement stmt
  in
  List.iter aux cn_progs


let add_records_to_map_from_instrumentation (i : Core_to_mucore.instrumentation) =
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
    | I (ReturnTypes.Computational (_, _, t), stats) ->
      List.iter add_records_to_map_from_cnprogs stats;
      aux_lrt t
  in
  let rec aux_at = function
    | AT.Computational ((_, _), _, at) -> aux_at at
    | L lat -> aux_lat lat
  in
  match i.internal with Some instr -> aux_at instr | None -> ()


(* Populate record table *)
let populate_record_map
  (instrumentation : Core_to_mucore.instrumentation list)
  (prog5 : unit Mucore.mu_file)
  =
  let fun_syms_and_ret_types =
    List.map
      (fun (sym, (def : LogicalFunctions.definition)) -> (sym, def.return_bt))
      prog5.mu_logical_predicates
  in
  let pred_syms_and_ret_types =
    List.map
      (fun (sym, (def : ResourcePredicates.definition)) -> (sym, def.oarg_bt))
      prog5.mu_resource_predicates
  in
  List.iter
    (fun (cn_sym, bt) -> Cn_internal_to_ail.augment_record_map ~cn_sym bt)
    (fun_syms_and_ret_types @ pred_syms_and_ret_types);
  List.iter add_records_to_map_from_instrumentation instrumentation
