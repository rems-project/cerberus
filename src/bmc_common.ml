open Bmc_globals
open Bmc_sorts
open Bmc_utils

open AilTypes
open Core
open Ocaml_mem
open Printf
open Util
open Z3

let is_integer_type (ctype: Core_ctype.ctype0) =
  match ctype with
  | Basic0 (Integer _) -> true
  | _ -> false

let is_pointer_type (ctype: Core_ctype.ctype0) =
  match ctype with
  | Pointer0 (_,Basic0 (Integer _)) -> true
  | _ -> false

(* =========== CORE TYPES -> Z3 SORTS =========== *)

let integer_value_to_z3 (ival: Ocaml_mem.integer_value) : Expr.expr =
  (* TODO: check which is the correct ival->big num function *)
  match eval_integer_value ival with
  | None -> assert false
  | Some i -> big_num_to_z3 i

let object_value_to_z3 (oval: object_value) : Expr.expr =
  match oval with
  | OVinteger ival -> integer_value_to_z3 ival
  | OVfloating _ -> assert false
  | OVpointer pv ->
      assert (is_null pv);
      PointerSort.mk_null
  | OVarray _
  | OVstruct _
  | OVunion _
  | OVcomposite _ ->
      assert false

(* TODO: HACK; need some function like this *)
let is_fun_ptr (p: Ocaml_mem.pointer_value) : bool =
  let ptr_str = pp_to_string (Ocaml_mem.pp_pointer_value p) in
  let cfun_hdr = "Cfunction(" in
  if String.length ptr_str < String.length cfun_hdr then false
  else (String.sub ptr_str 0 (String.length cfun_hdr) = cfun_hdr)

let value_to_z3 (value: value) : Expr.expr =
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
      | Basic0 (Integer _) ->
          LoadedInteger.mk_unspecified (CtypeSort.mk_expr ctype)
      | Pointer0 (_, Basic0 (Integer _)) ->
          LoadedPointer.mk_unspecified (CtypeSort.mk_expr ctype)
      | _ ->
          assert false
      end

let cot_to_z3 (cot: core_object_type) : Sort.sort =
  match cot with
  | OTy_integer     -> integer_sort
  | OTy_pointer     -> PointerSort.mk_sort
  | OTy_floating
  | OTy_array _
  | OTy_struct _ ->
      assert false
  (*| OTy_cfunction _ -> CFunctionSort.mk_sort (* TODO *)*)
  | OTy_union _ ->
      assert false

let rec cbt_to_z3 (cbt: core_base_type) : Sort.sort =
  match cbt with
  | BTy_unit                -> UnitSort.mk_sort
  | BTy_boolean             -> boolean_sort
  | BTy_ctype               -> CtypeSort.mk_sort
  | BTy_list BTy_ctype      -> CtypeListSort.mk_sort
  | BTy_list _              -> assert false
  | BTy_tuple cbt_list      -> assert false
  | BTy_object obj_type     -> cot_to_z3 obj_type
  | BTy_loaded OTy_integer  -> LoadedInteger.mk_sort
  | BTy_loaded OTy_pointer  -> LoadedPointer.mk_sort
  | BTy_loaded (OTy_array OTy_integer) ->
      LoadedIntArray.mk_sort
  | BTy_loaded _            -> assert false
  | BTy_storable            -> assert false

let sorts_to_tuple (sorts: Sort.sort list) : Sort.sort =
  let tuple_name =
    "(" ^ (String.concat "," (List.map Sort.to_string sorts)) ^ ")" in
  let arg_list = List.mapi
    (fun i _ -> mk_sym ("#" ^ (string_of_int i))) sorts in
  Tuple.mk_sort g_ctx (mk_sym tuple_name) arg_list sorts

let ctype_from_pexpr (ctype_pe: typed_pexpr) =
  match ctype_pe with
  | Pexpr(_, BTy_ctype, PEval (Vctype ctype)) -> ctype
  | _ -> assert false


let ctor_to_z3 (ctor  : typed_ctor)
               (exprs : Expr.expr list)
               (bTy   : core_base_type option)
               (uid   : int) =
  match ctor,exprs with
  | Ctuple,exprs ->
      let sort = sorts_to_tuple (List.map Expr.get_sort exprs) in
      let mk_decl = Tuple.get_mk_decl sort in
      FuncDecl.apply mk_decl exprs
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
      assert false;
      if (not g_bv) then failwith "CivAND is supported only with bitvectors";
      assert (g_bv);
      bmc_debug_print 7 "TODO: ctype ignored in CivAND";
      BitVector.mk_and g_ctx e1 e2
  | CivOR,[ctype;e1;e2] -> (* bitwise OR *)
      assert false;
      if (not g_bv) then failwith "CivOR is supported only with bitvectors";
      assert (g_bv);
      bmc_debug_print 7 "TODO: ctype ignored in CivOR";
      BitVector.mk_or g_ctx e1 e2
  | CivXOR,[ctype;e1;e2] -> (* bitwise XOR *)
      assert false;
      if (not g_bv) then failwith "CivXOR is supported only with bitvectors";
      assert (g_bv);
      bmc_debug_print 7 "TODO: ctype ignored in CivXOR";
      BitVector.mk_xor g_ctx e1 e2
  | Cspecified,[e] ->
      assert (is_some bTy);
      if (Option.get bTy = BTy_loaded OTy_integer) then
        LoadedInteger.mk_specified e
      else if (Option.get bTy = BTy_loaded OTy_pointer) then
        LoadedPointer.mk_specified e
      else if (Option.get bTy = BTy_loaded (OTy_array OTy_integer)) then
        LoadedIntArray.mk_specified e
      else
        assert false
  | Cunspecified, [e] ->
      assert (is_some bTy);
      if (Option.get bTy = BTy_loaded OTy_integer) then
        LoadedInteger.mk_unspecified e
      else if (Option.get bTy = BTy_loaded OTy_pointer) then
        LoadedPointer.mk_unspecified e
      else
        assert false
  | Ccons,[hd;tl] ->
      CtypeListSort.mk_cons hd tl
  | Cnil BTy_ctype, [] ->
      CtypeListSort.mk_nil
  | Carray,_ ->
      begin match Option.get bTy with
      | BTy_object (OTy_array OTy_integer) ->
          (* Just create a new array; need to bind values to Z3 though *)
          IntArray.mk_const_s (sprintf "array_%d" uid)
      | _ -> assert false
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

(* =========== BmcZ3Sort: Z3 representation of Ctypes =========== *)
type bmcz3sort =
  | CaseSortBase of Core_ctype.ctype0 * Sort.sort
  | CaseSortList of bmcz3sort list

let rec bmcz3sort_size (sort: bmcz3sort) =
  match sort with
  | CaseSortBase _        -> 1
  | CaseSortList sortlist ->
      List.fold_left (fun x y -> x + (bmcz3sort_size y)) 0 sortlist

let rec flatten_bmcz3sort (l: bmcz3sort): (Core_ctype.ctype0 * Sort.sort) list =
  match l with
  | CaseSortBase (expr, sort) -> [(expr, sort)]
  | CaseSortList ss -> List.concat (List.map flatten_bmcz3sort ss)

let rec ailctype_to_ctype (Ctype (_, ty): AilTypes.ctype)
                          : Core_ctype.ctype0 =
  match ty with
  | Void -> Void0
  | Basic bty -> Basic0 bty
  | Array (cty, n) -> Array0 (ailctype_to_ctype cty, n)
  | Function (_, (q,ty1), args, variadic) ->
      Function0 ((q, ailctype_to_ctype ty1),
                 List.map (fun (q,ty1,_) -> (q, ailctype_to_ctype ty1)) args,
                 variadic)
  | Pointer (v1,v2) -> Pointer0 (v1,ailctype_to_ctype v2)
  | Atomic cty -> Atomic0 (ailctype_to_ctype cty)
  | Struct v -> Struct0 v
  | Union v ->  Union0 v
  | Builtin v -> Builtin0 v

let rec ctype_to_z3_sort (ty: Core_ctype.ctype0)
                         : Sort.sort =
   match ty with
  | Void0     -> assert false
  | Basic0(Integer i) -> LoadedInteger.mk_sort
  | Basic0 _ -> assert false
  | Array0(Basic0 (Integer i), Some n) ->
      LoadedIntArray.mk_sort
  | Array0(_, _) ->
      assert false
  | Function0 _ -> assert false
  | Pointer0 _ -> LoadedPointer.mk_sort
  | Atomic0 (Basic0 _ as _ty) (* fall through *)
  | Atomic0 (Pointer0 _ as _ty) ->
      ctype_to_z3_sort _ty
  | Atomic0 _ ->
      assert false
  | Struct0 _ ->
      assert false
  | Union0 _
  | Builtin0 _ -> assert false

let rec ctype_to_bmcz3sort (ty  : Core_ctype.ctype0)
                           (file: unit typed_file)
                           : bmcz3sort =
  match ty with
  | Void0     -> assert false
  | Basic0(Integer i) ->
      CaseSortBase (ty, LoadedInteger.mk_sort)
  | Basic0 _ -> assert false
  | Array0(ty2, Some n) ->
      let sort = ctype_to_bmcz3sort ty2 file in
      CaseSortList (repeat_n (Nat_big_num.to_int n) sort)
  | Array0(_, None) ->
      assert false
  | Function0 _ -> assert false
  | Pointer0 _ ->
      CaseSortBase (ty, LoadedPointer.mk_sort)
  | Atomic0 (Basic0 _ as _ty) (* fall through *)
  | Atomic0 (Pointer0 _ as _ty) ->
      begin
      match ctype_to_bmcz3sort _ty file with
      | CaseSortBase(_, sort) -> CaseSortBase (Atomic0 _ty, sort)
      | _ -> assert false
      end
  | Atomic0 _ ->
      assert false
  | Struct0 sym ->
      begin match Pmap.lookup sym file.tagDefs with
      | Some (StructDef memlist) ->
          CaseSortList (List.map (fun (_, ty) -> ctype_to_bmcz3sort ty file)
                                 memlist)
      | _ -> assert false
      end
  | Union0 _
  | Builtin0 _ -> assert false

let size_of_ctype (ty: Core_ctype.ctype0)
                  (file: unit typed_file) =
  bmcz3sort_size (ctype_to_bmcz3sort ty file)

(* =========== CUSTOM Z3 FUNCTIONS =========== *)
(* Used for declaring Ivmin/Ivmax/is_unsigned/sizeof/etc *)
module ImplFunctions = struct
  open Z3.FuncDecl
  (* ---- Implementation ---- *)
  let sizeof_ity = Ocaml_implementation.Impl.sizeof_ity
  let sizeof_ptr = Ocaml_implementation.Impl.sizeof_pointer

  (* TODO: precision of Bool is currently 8... *)
  let impl : Implementation.implementation = {
    impl_binary_mode = Two'sComplement;
    impl_signed      = (function
                   | Char       -> Ocaml_implementation.Impl.char_is_signed
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
    impl_ptrdiff_t  = Signed Long
  }

  (* ---- Helper functions ---- *)
  let integer_range (impl: Implementation.implementation)
                    (ity : AilTypes.integerType) =
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

  let ity_to_ctype (ity: AilTypes.integerType) : Core_ctype.ctype0 =
    Core_ctype.Basic0 (Integer ity)


  (* ---- HELPER MAP MAKING FUNCTION ---- *)
  let mk_ctype_map (name : string)
                   (types: Core_ctype.ctype0 list)
                   (sort : Sort.sort)
                   : (Core_ctype.ctype0, Expr.expr) Pmap.map =
    List.fold_left (fun acc ctype ->
      let ctype_expr = CtypeSort.mk_expr ctype in
      let expr = mk_fresh_const
                    (sprintf "%s(%S)" name (Expr.to_string ctype_expr))
                    sort in
      Pmap.add ctype expr acc) (Pmap.empty Pervasives.compare) types
  (* ---- Constants ---- *)


  (* TODO: massive code duplication *)
  let ivmin_map : (Core_ctype.ctype0, Expr.expr) Pmap.map =
    mk_ctype_map "ivmin" (List.map ity_to_ctype ity_list) integer_sort

  let ivmax_map : (Core_ctype.ctype0, Expr.expr) Pmap.map =
    mk_ctype_map "ivmax" (List.map ity_to_ctype ity_list) integer_sort


  let sizeof_map : (Core_ctype.ctype0, Expr.expr) Pmap.map =
    mk_ctype_map "sizeof" (List.map ity_to_ctype ity_list) integer_sort

  let is_unsigned_map : (Core_ctype.ctype0, Expr.expr) Pmap.map =
    mk_ctype_map "is_unsigned" (List.map ity_to_ctype ity_list)
                               boolean_sort
  (* ---- Assertions ---- *)
  let ivmin_asserts =
    let ivmin_assert (ctype: Core_ctype.ctype0) : Expr.expr =
      let const = Pmap.find ctype ivmin_map in
      match ctype with
      | Basic0 (Integer ity) ->
          let (min, _) = integer_range impl ity in
          mk_eq const (big_num_to_z3 min)
      | _ -> assert false
    in
    List.map (fun ity -> ivmin_assert (ity_to_ctype ity))
             ity_list

  let ivmax_asserts =
    let ivmax_assert (ctype: Core_ctype.ctype0) : Expr.expr =
      let const = Pmap.find ctype ivmax_map in
      match ctype with
      | Basic0 (Integer ity) ->
          let (_, max) = integer_range impl ity in
          mk_eq const (big_num_to_z3 max)
      | _ -> assert false
    in
    List.map (fun ity -> ivmax_assert (ity_to_ctype ity))
             ity_list

  let sizeof_asserts =
    let sizeof_assert (ctype: Core_ctype.ctype0) : Expr.expr =
      let const = Pmap.find ctype sizeof_map in
      match ctype with
      | Basic0 (Integer ity) ->
          mk_eq const (int_to_z3 (Option.get (sizeof_ity ity)))
      (*| Pointer0 _ ->
          (* TODO: Check this *)
          mk_eq const (int_to_z3 (Option.get (sizeof_pointer)) *)
      | _ -> assert false
    in
    List.map (fun ity -> sizeof_assert (ity_to_ctype ity))
             ity_list

  (* TODO: char; other types *)
  let is_unsigned_asserts =
    let signed_tys =
      List.map (fun ty -> Pmap.find (ity_to_ctype ty) is_unsigned_map)
               signed_ibt_list in
    let unsigned_tys =
      List.map (fun ty -> Pmap.find (ity_to_ctype ty) is_unsigned_map)
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
                                 : Ocaml_mem.pointer_value =
  match expr with
  | Expr(_, (Epure(Pexpr(_,_,PEval(Vloaded (LVspecified (OVpointer p))))))) ->
      p
  | _ -> assert false


type cfun_call_symbols = {
  fn_ptr  : sym_ty;
  (*fn_ptr_inner : sym_ty;*)
  ret_ty  : sym_ty option;
  arg_tys : sym_ty option;
  bool1   : sym_ty option; (* TODO: no idea what these are *)
  bool2   : sym_ty option;
  ptr     : Ocaml_mem.pointer_value;
  core_ptr_pexpr: typed_pexpr;
  continuation  : unit typed_expr;
}

(* TODO: big hack for function calls...
 *
 *)

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
        pp_to_stdout (Pp_core.Basic.pp_expr e1);
        pp_to_stdout (Pp_core.Basic.pp_expr e2);

        let tuple_syms  = List.map get_sym_from_base_pattern tuple in
        assert (List.length tuple_syms = 4);
        Some { fn_ptr       = Option.get (get_sym_from_base_pattern ptr_pat1);
               (*fn_ptr_inner = get_sym_from_base_pattern ptr_pat2;*)
               ret_ty       = List.nth tuple_syms 0;
               arg_tys      = List.nth tuple_syms 1;
               bool1 = List.nth tuple_syms 2; (* TODO: No idea what these are *)
               bool2 = List.nth tuple_syms 3;
               ptr   = get_ptr_from_loaded_ptr_expr loaded_ptr_expr;
               core_ptr_pexpr = loaded_ptr_pexpr;
               continuation   = e2;
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
               (*fn_ptr_inner = get_sym_from_base_pattern ptr_pat2;*)
               ret_ty       = List.nth tuple_syms 0;
               arg_tys      = List.nth tuple_syms 1;
               bool1 = List.nth tuple_syms 2; (* TODO: No idea what these are *)
               bool2 = List.nth tuple_syms 3;
               ptr   = get_ptr_from_loaded_ptr_expr e1;
               core_ptr_pexpr = loaded_ptr_pexpr;
               continuation   = continuation;
             }
      end else
        None
  | _ -> None

