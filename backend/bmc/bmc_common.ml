open Bmc_globals
open Bmc_sorts
open Bmc_utils

open Cerb_frontend
open Ctype
open Core
open Printf
open Cerb_util
open Z3

(* =========== <> =========== *)

let assert_memory_mode_linux () =
  if !!bmc_conf.memory_mode <> MemoryMode_Linux then
    failwith "Error: Linux memory model only, please change model."

let assert_memory_mode_c () =
  if !!bmc_conf.memory_mode <> MemoryMode_C then
    failwith "Error: C memory model only, please change model."

let is_integer_type (ctype: ctype) =
  match ctype with
  | Ctype (_, Basic (Integer _)) -> true
  | _ -> false

let is_pointer_type (ctype: ctype) =
  match ctype with
  | Ctype (_, Pointer (_, Ctype (_, Basic (Integer _)))) -> true
  | _ -> false



(* =========== BmcZ3Sort: Z3 representation of Ctypes =========== *)
type bmcz3sort =
  | CaseSortBase of ctype * Sort.sort
  | CaseSortList of bmcz3sort list

let rec bmcz3sort_size (sort: bmcz3sort) =
  match sort with
  | CaseSortBase _        -> 1
  | CaseSortList sortlist ->
      List.fold_left (fun x y -> x + (bmcz3sort_size y)) 0 sortlist

let rec flatten_bmcz3sort (l: bmcz3sort): (ctype * Sort.sort) list =
  match l with
  | CaseSortBase (expr, sort) -> [(expr, sort)]
  | CaseSortList ss -> List.concat (List.map flatten_bmcz3sort ss)

let rec base_ctype (Ctype (_, ty) as cty) : ctype =
  match ty with
  | Void -> assert false
  | Byte -> cty
  | Basic _ -> cty
  | Array (ty2, _) ->
      base_ctype ty2
  | Function _
  | FunctionNoParams _ -> assert false
  | Pointer _ -> cty
  | Atomic ty2 ->
      base_ctype ty2
  | Struct _ ->
      cty
  | Union _ ->
      cty

let rec ctype_to_bmcz3sort (Ctype (_, ty) as cty)
                           (file: unit typed_file)
                           : bmcz3sort =
  match ty with
  | Void     -> assert false
  | Byte ->
      CaseSortBase (cty, LoadedInteger.mk_sort)
  | Basic(Integer i) ->
      CaseSortBase (cty, LoadedInteger.mk_sort)
  | Basic(Floating _) ->
      failwith "Error: floats are not supported."
  | Array(ty2, Some n) ->
      (* TODO *)
      let sort = ctype_to_bmcz3sort ty2 file in
      CaseSortList (repeat_n (Nat_big_num.to_int n) sort)
  | Array(_, None) ->
      assert false
  | Function _
  | FunctionNoParams _ -> assert false
  | Pointer _ ->
      CaseSortBase (cty, LoadedPointer.mk_sort)
  | Atomic (Ctype (_, Basic _) as _ty) (* fall through *)
  | Atomic (Ctype (_, Pointer _) as _ty) ->
      begin
      match ctype_to_bmcz3sort _ty file with
        | CaseSortBase(_, sort) -> CaseSortBase (Ctype ([], Atomic _ty), sort)
      | _ -> assert false
      end
  | Atomic _ ->
      assert false
  | Struct sym ->
      begin match Pmap.lookup sym file.tagDefs with
      | Some (_, StructDef (memlist, _)) ->
          CaseSortList (List.map (fun (_, (_, _, _, ty)) -> ctype_to_bmcz3sort ty file)
                                 memlist)
      | _ -> assert false
      end
  | Union _ ->
    failwith "Error: unions are not supported."


  (*
and
struct_to_sort (sym, memlist_def) file  =
  match memlist_def with
  | StructDef  memlist ->
    let sortlist =
        List.map (fun (_, mem_ty) -> ctype_to_z3_sort mem_ty file) memlist in
      (* TODO: Does Z3 allow tuples to contain tuples? *)
    let tuple_sort = sorts_to_tuple sortlist in
    (module LoadedSort(struct let obj_sort = tuple_sort end) : LoadedSortTy)
  | _ -> assert false
  *)




let size_of_ctype (ty: ctype)
                  (file: unit typed_file) =
  bmcz3sort_size (ctype_to_bmcz3sort ty file)



(* =========== CORE TYPES -> Z3 SORTS =========== *)

let integer_value_to_z3 (ival: Impl_mem.integer_value) : Expr.expr =
  (* TODO: check which is the correct ival->big num function *)
  match Mem.eval_integer_value ival with
  | None -> assert false
  | Some i -> big_num_to_z3 i

let object_value_to_z3 (oval: object_value) : Expr.expr =
  match oval with
  | OVinteger ival -> integer_value_to_z3 ival
  | OVfloating _ ->
        failwith "Floats are not supported."
  | OVpointer pv ->
      assert (is_null pv);
      PointerSort.mk_null
  | OVarray _
  | OVstruct _
  | OVunion _ ->
    failwith "Error: unions are not supported."

(* TODO: HACK; need some function like this *)
let is_fun_ptr (p: Impl_mem.pointer_value) : bool =
  let ptr_str = pp_to_string (Impl_mem.pp_pointer_value p) in
  let cfun_hdr = "Cfunction(" in
  if String.length ptr_str < String.length cfun_hdr then false
  else (String.sub ptr_str 0 (String.length cfun_hdr) = cfun_hdr)

let value_to_z3 (value: value) (file: unit typed_file) : Expr.expr =
  match value with
  | Vunit        -> UnitSort.mk_unit
  | Vtrue        -> mk_true
  | Vfalse       -> mk_false
  | Vlist _      -> assert false
  | Vtuple _     -> assert false
  | Vctype cty   -> CtypeSort.mk_expr cty
  | Vobject oval -> object_value_to_z3 oval
  | Vloaded (LVspecified oval) ->
      begin match oval with
       | OVinteger ival ->
           LoadedInteger.mk_specified (integer_value_to_z3 ival)
       | OVpointer p ->
           (* TODO: function is a hack *)
           if is_fun_ptr p then
             LoadedPointer.mk_specified (PointerSort.mk_fn_ptr)
           else
             assert false
       | _ -> assert false
      end
  | Vloaded (LVunspecified ctype) ->
      begin
      match ctype with
      | Ctype (_, Basic (Integer _)) ->
          LoadedInteger.mk_unspecified (CtypeSort.mk_expr ctype)
      | Ctype (_, Pointer (_, Ctype (_, Basic (Integer _)))) ->
          LoadedPointer.mk_unspecified (CtypeSort.mk_expr ctype)
      | _ ->
          assert false
      end

let cot_to_z3 (cot: core_object_type) : Sort.sort =
  match cot with
  | OTy_integer     -> integer_sort
  | OTy_pointer     -> PointerSort.mk_sort
  | OTy_floating ->
      failwith "Error: floats are not supported."
  | OTy_array _
  | OTy_struct _ ->
      assert false
  (*| OTy_cfunction _ -> CFunctionSort.mk_sort (* TODO *)*)
  | OTy_union _ ->
    failwith "Error: unions are not supported."

let cbt_to_z3 (cbt: core_base_type)
              (file: unit typed_file): Sort.sort =
  match cbt with
  | BTy_unit                -> UnitSort.mk_sort
  | BTy_boolean             -> boolean_sort
  | BTy_ctype               -> CtypeSort.mk_sort
  | BTy_list BTy_ctype      -> CtypeListSort.mk_sort
  | BTy_list _              -> assert false
  | BTy_tuple cbt_list      -> assert false
  | BTy_object obj_type     -> cot_to_z3 obj_type
  | BTy_loaded OTy_integer  ->
      (* Experimenting with modules
       * let module X = struct let obj_sort = integer_sort end in
       * let module T = (val (module LoadedSort (X) : LoadedSortTy)) in
       *)
      LoadedInteger.mk_sort
  | BTy_loaded OTy_pointer  -> LoadedPointer.mk_sort
  | BTy_loaded (OTy_array OTy_integer) ->
      LoadedIntArray.mk_sort
  | BTy_loaded (OTy_array cot) ->
      CtypeToZ3.mk_array_sort cot file

      (*failwith "TODO: support for general array types"*)
  | BTy_loaded (OTy_struct sym) ->
      failwith "TODO: structs as values"
      (*let struct_sort = struct_sym_to_z3_sort sym file in
        TODO_LoadedSort.mk_sort struct_sort*)
  | BTy_loaded oty  ->
      failwith (sprintf "TODO: support for loaded type: %s"
                        (pp_to_string (Pp_core.Basic.pp_core_object_type oty)))
  | BTy_storable            ->
      failwith "TODO: support for BTy_storable"


let ctype_from_pexpr (ctype_pe: typed_pexpr) =
  match ctype_pe with
  | Pexpr(_, BTy_ctype, PEval (Vctype ctype)) -> ctype
  | _ -> assert false


let ctor_to_z3 (ctor  : ctor)
               (exprs : Expr.expr list)
               (bTy   : core_base_type option)
               (uid   : int)
               (file  : unit typed_file) =
  match ctor,exprs with
  | Ctuple,exprs ->
      let sort = sorts_to_tuple (List.map Expr.get_sort exprs) in
      (*print_endline ((string_of_int (Tuple.get_num_fields sort)));*)
      (*let mk_decl = Tuple.get_mk_decl sort in
      FuncDecl.apply mk_decl exprs *)
      CustomTuple.mk_tuple sort exprs
  | Civmax,_ ->
      (* Handled as special case in bmc_pexpr *)
      assert false
  | Civmin,_ ->
      (* Handled as special case in bmc_pexpr *)
      assert false
  | Civsizeof,_ ->
      (* Handled as special case in bmc_pexpr *)
      assert false
  | Civalignof,_ ->
      (* Handled as special case in bmc_pexpr *)
      assert false
  | CivAND,[ctype;e1;e2] -> (* bitwise AND *)
      failwith "TODO: CivAND"
      (*if (not g_bv) then failwith "CivAND is supported only with bitvectors";
      assert (g_bv);
      bmc_debug_print 7 "TODO: ctype ignored in CivAND";
      BitVector.mk_and g_ctx e1 e2*)
  | CivOR,[ctype;e1;e2] -> (* bitwise OR *)
      failwith "TODO: CivOR"
      (*if (not g_bv) then failwith "CivOR is supported only with bitvectors";
      assert (g_bv);
      bmc_debug_print 7 "TODO: ctype ignored in CivOR";
      BitVector.mk_or g_ctx e1 e2*)
  | CivXOR,[ctype;e1;e2] -> (* bitwise XOR *)
      failwith "TODO: CivXOR"
      (*if (not g_bv) then failwith "CivXOR is supported only with bitvectors";
      assert (g_bv);
      bmc_debug_print 7 "TODO: ctype ignored in CivXOR";
      BitVector.mk_xor g_ctx e1 e2*)
  | Cspecified,[e] ->
      assert (is_some bTy);
      begin
      match Option.get bTy with
      | BTy_loaded OTy_integer (* fall through *)
      | BTy_loaded OTy_pointer (* fall through *)
      | BTy_loaded (OTy_array _) (* fall through *)
      | BTy_loaded (OTy_struct _) ->
          TODO_LoadedSort.mk_specified e
      | ty ->
          failwith (sprintf "TODO: support Cspecified %s"
                            (pp_to_string (Pp_core.Basic.pp_core_base_type ty)))
      end
      (*
      | BTy_loaded OTy_integer ->
          LoadedInteger.mk_specified e
      | BTy_loaded OTy_pointer ->
          LoadedPointer.mk_specified e
      | BTy_loaded (OTy_array cot) ->
          let sort =

      | BTy_loaded (OTy_array OTy_integer) ->
          LoadedIntArray.mk_specified e
      | BTy_loaded (OTy_array (OTy_array OTy_integer)) ->
          LoadedIntArrayArray.mk_specified e
      | ty ->
          failwith (sprintf "TODO: support Cspecified %s"
                            (pp_to_string (Pp_core.Basic.pp_core_base_type ty)))
        *)
  | Cunspecified, [e] ->
      assert (is_some bTy);
      if (Option.get bTy = BTy_loaded OTy_integer) then
        LoadedInteger.mk_unspecified e
      else if (Option.get bTy = BTy_loaded OTy_pointer) then
        LoadedPointer.mk_unspecified e
      else
        failwith (sprintf "TODO: support Cspecified %s"
                          (pp_to_string (Pp_core.Basic.pp_core_base_type (Option.get bTy))))
  | Ccons,[hd;tl] ->
      CtypeListSort.mk_cons hd tl
  | Cnil BTy_ctype, [] ->
      CtypeListSort.mk_nil
  | Carray,_ ->
      (* TODO: move this to CtypeToZ3 or some other function? *)
      begin match Option.get bTy with
      | BTy_object (OTy_array OTy_integer) ->
          Z3Array.mk_const_s g_ctx (sprintf "array_%d" uid)
                             integer_sort LoadedInteger.mk_sort
      | BTy_object (OTy_array OTy_pointer) ->
          Z3Array.mk_const_s g_ctx (sprintf "array_%d" uid)
                             integer_sort LoadedPointer.mk_sort
      | BTy_object (OTy_array (OTy_array cot)) ->
          let sort = CtypeToZ3.mk_array_sort cot file in
          Z3Array.mk_const_s g_ctx (sprintf "array_%d" uid)
                             integer_sort sort
      | BTy_object (OTy_array (OTy_struct tag)) ->
          failwith "TODO: Arrays of structs"
          (*
          let sort = CtypeToZ3.struct_sym_to_z3_sort tag file in
          Z3Array.mk_const_s g_ctx (sprintf "array_%d" uid)
                             integer_sort (TODO_LoadedSort.mk_sort sort)
          *)
      | _ -> failwith "TODO: support arbitrary Carrays"
      end
  | _ ->
      assert false

(* =========== PATTERN MATCHING =========== *)
let rec pattern_match (Pattern(_,pattern): typed_pattern)
                      (expr: Expr.expr)
                      : Expr.expr =
  match pattern with
  | CaseBase(_,_) ->
      mk_true
  | CaseCtor(Ctuple, patlist) ->
      assert (Expr.get_num_args expr = List.length patlist);
      let expr_list = Expr.get_args expr in
      let match_conditions =
        List.map2 (fun pat e -> pattern_match pat e) patlist expr_list in
      mk_and match_conditions
  | CaseCtor(Cspecified, [Pattern(_,CaseBase(_, BTy_object OTy_integer))]) ->
      LoadedInteger.is_specified expr
  | CaseCtor(Cspecified, [Pattern(_,CaseBase(_, BTy_object OTy_pointer))]) ->
      LoadedPointer.is_specified expr
  | CaseCtor(Cspecified, _) ->
      assert false
  | CaseCtor(Cunspecified, [Pattern(_,CaseBase(_, BTy_ctype))]) ->
      if (Sort.equal (Expr.get_sort expr) (LoadedInteger.mk_sort)) then
        LoadedInteger.is_unspecified expr
      else if (Sort.equal (Expr.get_sort expr) (LoadedPointer.mk_sort)) then
        LoadedPointer.is_unspecified expr
      else
        assert false
  | CaseCtor(Cnil BTy_ctype, []) ->
      CtypeListSort.is_nil expr
  | CaseCtor(Ccons, [hd;tl]) ->
      (* BTy_ctype supported only *)
      assert (Sort.equal (Expr.get_sort expr) (CtypeListSort.mk_sort));
      mk_and [CtypeListSort.is_cons expr
             ;pattern_match hd (CtypeListSort.get_head expr)
             ;pattern_match tl (CtypeListSort.get_tail expr)
             ]
  | _ -> assert false

let mk_guarded_ite (exprs : Expr.expr list)
                   (guards: Expr.expr list) =
  assert (List.length exprs = List.length guards);
  match List.length exprs with
  | 0 -> assert false
  | 1 -> List.hd exprs
  | _ -> let rev_exprs = List.rev exprs in
         let rev_guards = List.rev guards in
         let last_case_expr = List.hd rev_exprs in
         List.fold_left2 (fun acc guard expr -> mk_ite guard expr acc)
                         last_case_expr
                         (List.tl rev_guards)
                         (List.tl rev_exprs)

(* =========== CUSTOM Z3 FUNCTIONS =========== *)
(* Used for declaring Ivmin/Ivmax/is_unsigned/sizeof/etc *)
module ImplFunctions = struct
  (* ---- Implementation ---- *)
  let sizeof_ity = (Ocaml_implementation.get ()).sizeof_ity
  let sizeof_ptr = (Ocaml_implementation.get ()).sizeof_pointer

  (* TODO: precision of Bool is currently 8... *)
  let impl : IntegerImpl.implementation = {
    impl_binary_mode = Two'sComplement;
    impl_signed      = (function
                   | Char       -> (Ocaml_implementation.get ()).is_signed_ity Char
                   | Bool       -> false
                   | Signed _   -> true
                   | Unsigned _ -> false
                   | Size_t     -> false
                   | Ptrdiff_t  -> true
                   | _          -> assert false);
    impl_precision   = (fun i -> match sizeof_ity i with
                   | Some x -> x * 8
                   | None   -> assert false );
    impl_size_t     = Unsigned Long;
    impl_ptrdiff_t  = Signed Long;
    impl_ptraddr_t  = Unsigned Long;
  }

  (* ---- Helper functions ---- *)
  let integer_range (impl: IntegerImpl.implementation)
                    (ity : Ctype.integerType) =
    let prec = impl.impl_precision ity in
    if impl.impl_signed ity then
      let prec_minus_one = prec - 1 in
      (match impl.impl_binary_mode with
       | Two'sComplement ->
          (Nat_big_num.sub (Nat_big_num.of_int 0)
                           (Nat_big_num.pow_int (Nat_big_num.of_int 2)
                                                prec_minus_one)),
          (Nat_big_num.sub (Nat_big_num.pow_int (Nat_big_num.of_int 2)
                                                prec_minus_one)
                           (Nat_big_num.of_int 1))
       | _ -> assert false)
    else
     Nat_big_num.of_int 0,
     Nat_big_num.sub (Nat_big_num.pow_int (Nat_big_num.of_int 2) prec)
                     (Nat_big_num.of_int 1)
  let ibt_list = [Ichar; Short; Int_; Long; LongLong; Intptr_t]
  let signed_ibt_list = List.map (fun ty -> Signed ty) ibt_list
  let unsigned_ibt_list = List.map (fun ty -> Unsigned ty) ibt_list

  let ity_list = signed_ibt_list
               @ unsigned_ibt_list
               @ [Char; Bool; Size_t; Ptrdiff_t]

  let ity_to_ctype (ity: Ctype.integerType) : ctype =
    Ctype ([], Basic (Integer ity))

  (* ---- HELPER MAP MAKING FUNCTION ---- *)
  let mk_integerType_map (name : string)
                   (itys: integerType list)
                   (sort : Sort.sort)
                   : (integerType, Expr.expr) Pmap.map =
    List.fold_left (fun acc ity ->
      let ctype_expr = CtypeSort.mk_expr (ity_to_ctype ity) in
      let expr = mk_fresh_const
                    (sprintf "%s(%S)" name (Expr.to_string ctype_expr))
                    sort in
      Pmap.add ity expr acc) (Pmap.empty Stdlib.compare) itys
  (* ---- Constants ---- *)


  (* TODO: massive code duplication *)
  let ivmin_map : (integerType, Expr.expr) Pmap.map =
    mk_integerType_map "ivmin" ity_list integer_sort

  let ivmax_map : (integerType, Expr.expr) Pmap.map =
    mk_integerType_map "ivmax" ity_list integer_sort


  let sizeof_map : (integerType, Expr.expr) Pmap.map =
    mk_integerType_map "sizeof" ity_list integer_sort

  let is_unsigned_map : (integerType, Expr.expr) Pmap.map =
    mk_integerType_map "is_unsigned" ity_list boolean_sort
  (* ---- Assertions ---- *)
  let ivmin_asserts =
    let ivmin_assert (ity: integerType) : Expr.expr =
      let const = Pmap.find ity ivmin_map in
      let (min, _) = integer_range impl ity in
      mk_eq const (big_num_to_z3 min)
    in
    List.map ivmin_assert ity_list

  let ivmax_asserts =
    let ivmax_assert (ity: integerType) : Expr.expr =
      let const = Pmap.find ity ivmax_map in
      let (_, max) = integer_range impl ity in
      mk_eq const (big_num_to_z3 max)
    in
    List.map ivmax_assert ity_list

  let sizeof_asserts =
    let sizeof_assert (ity: integerType) : Expr.expr =
      let const = Pmap.find ity sizeof_map in
      mk_eq const (int_to_z3 (Option.get (sizeof_ity ity)))
    in
    List.map sizeof_assert ity_list

  (* TODO: char; other types *)
  let is_unsigned_asserts =
    let signed_tys =
      List.map (fun ity -> Pmap.find ity is_unsigned_map)
               signed_ibt_list in
    let unsigned_tys =
      List.map (fun ity -> Pmap.find ity is_unsigned_map)
               unsigned_ibt_list in
    List.map (fun signed_const ->
                mk_eq signed_const (mk_false)) signed_tys
    @ List.map (fun unsigned_const ->
                  mk_eq unsigned_const (mk_true)) unsigned_tys

  (* ---- All assertions ---- *)
  let all_asserts =   ivmin_asserts
                    @ ivmax_asserts
                    @ sizeof_asserts
                    @ is_unsigned_asserts
end



(* Assert const is in range of ctype *)
let assert_initial_range (ctype: ctype) (const: Expr.expr)
                         : Expr.expr list =
  match ctype with
  | Ctype (_, Void) ->
      []
  | Ctype (_, Basic (Integer ity)) ->
      let ge_ivmin =
          binop_to_z3 OpGe const (Pmap.find ity ImplFunctions.ivmin_map) in
      let le_ivmax =
          binop_to_z3 OpLe const (Pmap.find ity ImplFunctions.ivmax_map) in
      [ge_ivmin;le_ivmax]
  | _ ->
      bmc_debug_print 8 (sprintf "TODO: assert_initial_range of non-int type");
      []

(* TODO: big hack for function calls...
 * let weak (p': loaded pointer, (...)) =
 *     let strong p : loaded pointer = pure(Specified(Cfunction(f))) in
 *     (p, cfunction(p))
 * in...
 *)


let is_ptr_pat (pat: typed_pattern) : bool =
  match pat with
  | Pattern(_, (CaseBase(Some _, BTy_loaded OTy_pointer))) -> true
  | _ -> false

let get_sym_from_base_pattern (pat: typed_pattern) : sym_ty option =
  match pat with
  | Pattern(_, (CaseBase(sym, _))) -> sym
  | _ -> assert false

let is_loaded_ptr_expr (expr: unit typed_expr) =
  match expr with
  | Expr(_, (Epure(Pexpr(_,_,PEval(Vloaded (LVspecified (OVpointer p))))))) ->
      true
  | _ -> false

let get_ptr_from_loaded_ptr_expr (expr: unit typed_expr)
                                 : Impl_mem.pointer_value =
  match expr with
  | Expr(_, (Epure(Pexpr(_,_,PEval(Vloaded (LVspecified (OVpointer p))))))) ->
      p
  | _ -> assert false


type cfun_call_symbols = {
  fn_ptr  : sym_ty;
  fn_ptr_inner : sym_ty option;
  ptr     : Impl_mem.pointer_value;
}


(* Return ptr sym and rewritten expr *)
let extract_cfun_if_cfun_call (pat: typed_pattern)
                              (e1: unit typed_expr)
                              (e2: unit typed_expr)
                              : cfun_call_symbols option =
  match (pat, e1,e2) with
  | (Pattern(_, (CaseCtor(Ctuple,
              [ptr_pat1;Pattern(_, (CaseCtor(Ctuple, tuple)))]))),
     Expr(_, (Esseq(
       ptr_pat2,
       ((Expr(_, (Epure(loaded_ptr_pexpr)))) as loaded_ptr_expr),
       Expr(_,(Epure(Pexpr(_,_,PEctor(Ctuple,[_;Pexpr(_,_,PEcfunction _)])))))))),_) ->
   (*
   * let weak (p': loaded pointer, (...)) =
   *     let strong p : loaded pointer = pure(Specified(Cfunction(f))) in
   *     (p, cfunction(p))
   * in...
   *)
      if (is_ptr_pat ptr_pat1 && is_ptr_pat ptr_pat2 &&
          is_loaded_ptr_expr loaded_ptr_expr)
      then begin
        assert (List.length tuple = 4);
        Some { fn_ptr       = Option.get (get_sym_from_base_pattern ptr_pat1);
               fn_ptr_inner = (get_sym_from_base_pattern ptr_pat2);
               ptr   = get_ptr_from_loaded_ptr_expr loaded_ptr_expr;
             }
      end else
        None
  | (_,
    Expr(_, (Epure(loaded_ptr_pexpr))),
    Expr(_, (Esseq(Pattern(_, (CaseCtor(Ctuple, tuple))),
                   Expr(_,(Epure(Pexpr(_,_,PEcfunction (Pexpr(_,_,PEsym p)))))),
                   continuation
            )))) ->
     (*
      * for a void function call:
      *   let strong p : loaded pointer = pure(Specified(Cfunction(f...))) in
      *   let strong (... : tuple) = pure (c_function(p)) in ...
      *)
      if (is_ptr_pat pat && is_loaded_ptr_expr e1 &&
          sym_eq p (Option.get (get_sym_from_base_pattern pat)))
      then begin
        let tuple_syms  = List.map get_sym_from_base_pattern tuple in
        assert (List.length tuple_syms = 4);
        Some { fn_ptr       = Option.get(get_sym_from_base_pattern pat);
               fn_ptr_inner = None;
               ptr   = get_ptr_from_loaded_ptr_expr e1;
             }
      end else
        None
  | (Pattern(_, (CaseCtor(Ctuple, tuple1::_))),
     Expr(_, (Eunseq (sub_e1 :: (sub_e2 :: _)))),_) ->
      (* Unseq pattern:
       *  let weak ((p, (...)), _) =
       *  unseq(let strong inner = pure(Specified(Cfunction(f))) in
       *        pure((inner, cfunction(inner))),
       *)
      begin match tuple1,sub_e1 with
      | (Pattern(_, (CaseCtor(Ctuple,
              [ptr_pat1;Pattern(_, (CaseCtor(Ctuple, tuple)))])))),
         Expr(_, (Esseq(
           ptr_pat2,
           ((Expr(_, (Epure(loaded_ptr_pexpr)))) as loaded_ptr_expr),
           Expr(_,(Epure(Pexpr(_,_,PEctor(Ctuple,[_;Pexpr(_,_,PEcfunction _)]))))))))
         ->

           if (is_ptr_pat ptr_pat1 && is_ptr_pat ptr_pat2 &&
               is_loaded_ptr_expr loaded_ptr_expr) then
             begin
             assert (List.length tuple = 4);
             Some {fn_ptr = Option.get (get_sym_from_base_pattern ptr_pat1)
                  ;fn_ptr_inner = (get_sym_from_base_pattern ptr_pat2)
                  ;ptr = get_ptr_from_loaded_ptr_expr loaded_ptr_expr
                  }
             end
           else None
      | _ ->
          None
      end
  | _ -> None

