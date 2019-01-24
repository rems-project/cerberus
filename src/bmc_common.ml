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
      | _ -> assert false
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

let ctor_to_z3 (ctor  : typed_ctor)
               (exprs : Expr.expr list)
               (bTy   : core_base_type option)
               (uid   : int) =
  match ctor with
  | Ctuple ->
      let sort = sorts_to_tuple (List.map Expr.get_sort exprs) in
      let mk_decl = Tuple.get_mk_decl sort in
      FuncDecl.apply mk_decl exprs
  | Civmax ->
      (* Handled as special case in bmc_pexpr *)
      assert false
  | Civmin ->
      (* Handled as special case in bmc_pexpr *)
      assert false
  | Civsizeof ->
      (* Handled as special case in bmc_pexpr *)
      assert false
  | Cspecified ->
      assert (List.length exprs = 1);
      assert (is_some bTy);
      if (Option.get bTy = BTy_loaded OTy_integer) then
        LoadedInteger.mk_specified (List.hd exprs)
      else if (Option.get bTy = BTy_loaded OTy_pointer) then
        LoadedPointer.mk_specified (List.hd exprs)
      else if (Option.get bTy = BTy_loaded (OTy_array OTy_integer)) then
        LoadedIntArray.mk_specified (List.hd exprs)
      else
        assert false
  | Cunspecified ->
      assert (List.length exprs = 1);
      assert (is_some bTy);
      if (Option.get bTy = BTy_loaded OTy_integer) then
        LoadedInteger.mk_unspecified (List.hd exprs)
      else if (Option.get bTy = BTy_loaded OTy_pointer) then
        LoadedPointer.mk_unspecified (List.hd exprs)
      else
        assert false
  | Ccons ->
      assert (List.length exprs = 2);
      begin match exprs with
      | [hd;tl] ->
          CtypeListSort.mk_cons hd tl
      | _ -> assert false
      end
  | Cnil BTy_ctype ->
      assert (List.length exprs = 0);
      CtypeListSort.mk_nil
  | Carray ->
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


(* =========== CUSTOM Z3 FUNCTIONS =========== *)
(* Used for declaring Ivmin/Ivmax/is_unsigned/sizeof/etc *)
module ImplFunctions = struct
  open Z3.FuncDecl
  (* ---- Implementation ---- *)
  let sizeof_ity = Ocaml_implementation.Impl.sizeof_ity

  (* TODO: precision of Bool is currently 8... *)
  let impl : Implementation.implementation = {
    impl_binary_mode = Two'sComplement;
    impl_signed      = (function
                   | Char       -> Ocaml_implementation.Impl.char_is_signed
                   | Bool       -> false
                   | Signed _   -> true
                   | Unsigned _ -> false
                   | Size_t     -> false
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
  let ibt_list = [Ichar; Short; Int_; Long; LongLong]
  let signed_ibt_list = List.map (fun ty -> Signed ty) ibt_list
  let unsigned_ibt_list = List.map (fun ty -> Unsigned ty) ibt_list

  let ity_list = signed_ibt_list
               @ unsigned_ibt_list
               @ [Char; Bool; Size_t]

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

let is_c_function_call (pat: typed_pattern) (expr: unit typed_expr)
                       : bool =
  match (pat, expr) with
  | (Pattern(_, (CaseCtor(Ctuple,
              [Pattern(_, (CaseBase(Some _, BTy_loaded OTy_pointer)))
              ;Pattern(_, (CaseCtor(Ctuple, _)))
              ]))),
     Expr(_, (Esseq(Pattern(_, (CaseBase(Some _, BTy_loaded OTy_pointer))),
                    Expr(_, (Epure(Pexpr(_,_,
                                         PEval(Vloaded (LVspecified (OVpointer p))))))),
                    Expr(_,
                    (Epure(Pexpr(_,_,PEctor(Ctuple,[_;Pexpr(_,_,PEcfunction
                    _)]))))))))) -> true
  | _ -> false

type cfun_call_symbols = {
  fn_ptr  : sym_ty;
  fn_ptr_inner : sym_ty;
  ret_ty  : sym_ty;
  arg_tys : sym_ty;
  bool1   : sym_ty; (* TODO: no idea what these are *)
  bool2   : sym_ty;
  ptr     : Ocaml_mem.pointer_value;
  core_ptr_pexpr: typed_pexpr;

}

let extract_cfun (pat: typed_pattern) (expr: unit typed_expr)
                 : cfun_call_symbols =
  match (pat, expr) with
  | (Pattern(_, (CaseCtor(Ctuple,
              [Pattern(_, (CaseBase(Some fn_ptr, BTy_loaded OTy_pointer)))
              ;Pattern(_, (CaseCtor(Ctuple, tuple)))
              ]))),
     Expr(_, (Esseq(Pattern(_, (CaseBase(Some sym2, BTy_loaded OTy_pointer))),
              (Expr(_, (Epure
                        ((Pexpr(_,_,PEval(Vloaded (LVspecified (OVpointer p)))) as core_ptr_pexpr))))),
              Expr(_,(Epure(Pexpr(_,_,PEctor(Ctuple,[_;Pexpr(_,_,PEcfunction
                    _)]))))))))) ->
       let tuple_syms  = List.map (fun pat ->
         match pat with
         | Pattern(_, (CaseBase(Some sym, _))) -> sym
         | _ -> assert false
       ) tuple in
       assert (List.length tuple_syms = 4);
       { fn_ptr  = fn_ptr;
         fn_ptr_inner = sym2;
         ret_ty  = List.nth tuple_syms 0;
         arg_tys = List.nth tuple_syms 1;
         bool1   = List.nth tuple_syms 2; (* TODO: no idea what these are *)
         bool2   = List.nth tuple_syms 3;
         ptr     = p;
         core_ptr_pexpr = core_ptr_pexpr
       }
  | _ -> assert false
