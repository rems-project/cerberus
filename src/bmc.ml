open Bmc_substitute
open Bmc_utils
open Z3
open Z3.Arithmetic

open AilTypes
open Core
open Core_aux
open Ocaml_mem
open Printf
open Util

(* TODO:
 *  - Maintain symbol table properly
 *  - Maintain memory table properly
 *      - Also creates within branches not preserved.
 *  - Kill ignored; Ebound ignored
 *  - More complex create types
 *  - Alias analysis
 *  - Alignment
 *  - PtrValidForDeref
 *  - Globals
 *  - See if guarding assumptions will reduce solver time
 *  - Pointer ctype not translated properly in Z3
 *  - C functions are currently just identifiers.
 *  - Structs, 2D arrays
 *  - Null pointers
 *
 *  - Concurrency
 *)

(* =========== GLOBALS =========== *)

(* Z3 context config *)
let g_z3_ctx_cfg = [ ("model", "true")  (* Generate model *)
                   ; ("proof", "false") (* Disable proof generation *)
                   ]
let g_ctx = mk_context g_z3_ctx_cfg

let g_z3_solver_logic_opt = None        (* Logic used by the solver *)
let g_solver      = Solver.mk_solver g_ctx g_z3_solver_logic_opt

(* true => use bit vector representation *)
let g_bv = true
let g_bv_precision = 32

let g_max_run_depth = 5
let g_sequentialise = true

(* =========== Z3 aliases =========== *)
let mk_implies = Boolean.mk_implies g_ctx
let mk_and     = Boolean.mk_and g_ctx
let mk_not     = Boolean.mk_not g_ctx
let mk_or      = Boolean.mk_or g_ctx
let mk_true    = Boolean.mk_true g_ctx
let mk_false   = Boolean.mk_false g_ctx
let mk_xor     = Boolean.mk_xor g_ctx
let mk_eq      = Boolean.mk_eq g_ctx
let mk_ite     = Boolean.mk_ite g_ctx

let mk_fresh_const = Expr.mk_fresh_const g_ctx

(* =========== TYPES =========== *)
(* Pure return *)

type addr_ty = int * int

(* TODO: use Set.Make *)
module AddrSet = struct
    type t = addr_ty Pset.set

    let cmp = Pervasives.compare
    let empty = Pset.empty cmp
    let of_list = Pset.from_list cmp
    let union s1 s2 = Pset.union s1 s2
    let fold = Pset.fold

    let pp s = Pset.fold (fun (x,y) acc ->
      sprintf "(%d,%d) %s" x y acc) s ""
end

type bmc_ret = {
  expr              : Expr.expr;
  assume            : Expr.expr list;
  vcs               : Expr.expr list;
  drop_cont         : Expr.expr; (* drop continuation; e.g. after Erun *)
  mod_addr          : AddrSet.t; (* addresses modified in memory *)
  ret_cond          : Expr.expr; (* constraints on the returned value *)
}

type bmc_pret = {
  expr              : Expr.expr;
  assume            : Expr.expr list;
  vcs               : Expr.expr list;
}

let pget_expr   (pret: bmc_pret) = pret.expr
let pget_assume (pret: bmc_pret) = pret.assume
let pget_vcs    (pret: bmc_pret) = pret.vcs

let eget_expr   (eret: bmc_ret) = eret.expr
let eget_assume (eret: bmc_ret) = eret.assume
let eget_vcs    (eret: bmc_ret) = eret.vcs
let eget_ret    (eret: bmc_ret) = eret.ret_cond

let bmc_pret_to_ret (pret: bmc_pret) : bmc_ret =
  { expr      = pret.expr
  ; assume    = pret.assume
  ; vcs       = pret.vcs
  ; drop_cont = mk_false
  ; mod_addr  = AddrSet.empty
  ; ret_cond  = mk_true
  }

(* Sort list *)
type bmcz3sort =
  | CaseSortBase of Expr.expr * Sort.sort
  | CaseSortList of bmcz3sort list

let rec bmcz3sort_size (sort: bmcz3sort) =
  match sort with
  | CaseSortBase _        -> 1
  | CaseSortList sortlist ->
      List.fold_left (fun x y -> x + (bmcz3sort_size y)) 0 sortlist

let rec flatten_bmcz3sort (l: bmcz3sort) : (Expr.expr * Sort.sort) list =
  match l with
  | CaseSortBase (expr, sort) -> [(expr, sort)]
  | CaseSortList ss -> List.concat (List.map flatten_bmcz3sort ss)


let integer_sort = if g_bv then BitVector.mk_sort g_ctx g_bv_precision
                   else Integer.mk_sort g_ctx
(* =========== Z3 HELPER FUNCTIONS =========== *)

let big_num_to_z3 (i: Nat_big_num.num) : Expr.expr =
  if g_bv then
    BitVector.mk_numeral g_ctx (Nat_big_num.to_string i) g_bv_precision
  else Integer.mk_numeral_s g_ctx (Nat_big_num.to_string i)

let int_to_z3 (i: int) : Expr.expr =
  big_num_to_z3 (Nat_big_num.of_int i)

let z3num_to_int (expr: Expr.expr) =
  assert (Sort.equal (Expr.get_sort expr) integer_sort);
  if g_bv then
    int_of_string (BitVector.numeral_to_string expr)
  else
    (assert (Arithmetic.is_int_numeral expr);
     Integer.get_int expr)


let binop_to_z3 (binop: binop) (arg1: Expr.expr) (arg2: Expr.expr)
                : Expr.expr =
  if g_bv then
    begin match binop with
    | OpAdd   -> BitVector.mk_add  g_ctx arg1 arg2
    | OpSub   -> BitVector.mk_sub  g_ctx arg1 arg2
    | OpMul   -> BitVector.mk_mul  g_ctx arg1 arg2
    | OpDiv   -> BitVector.mk_sdiv g_ctx arg1 arg2
    | OpRem_t -> assert false
    | OpRem_f -> BitVector.mk_srem g_ctx arg1 arg2
    | OpExp   ->
        if (Expr.is_numeral arg1 && (BitVector.get_int arg1 = 2)) then
          let one = BitVector.mk_numeral g_ctx "1" g_bv_precision in
          BitVector.mk_shl g_ctx one arg2
      else
        assert false
    | OpEq    -> mk_eq arg1 arg2
    | OpLt    -> BitVector.mk_slt g_ctx arg1 arg2
    | OpLe    -> BitVector.mk_sle g_ctx arg1 arg2
    | OpGt    -> BitVector.mk_sgt g_ctx arg1 arg2
    | OpGe    -> BitVector.mk_sge g_ctx arg1 arg2
    | OpAnd   -> mk_and [ arg1; arg2 ]
    | OpOr    -> mk_or  [ arg1; arg2 ]
    end
  else begin
    match binop with
    | OpAdd   -> Arithmetic.mk_add g_ctx [arg1; arg2]
    | OpSub   -> Arithmetic.mk_sub g_ctx [arg1; arg2]
    | OpMul   -> Arithmetic.mk_mul g_ctx [arg1; arg2]
    | OpDiv   -> Arithmetic.mk_div g_ctx arg1 arg2
    | OpRem_t -> assert false
    | OpRem_f -> Integer.mk_mod g_ctx arg1 arg2 (* TODO: Rem_t vs Rem_f? *)
    | OpExp   -> assert false
    | OpEq    -> mk_eq arg1 arg2
    | OpLt    -> Arithmetic.mk_lt g_ctx arg1 arg2
    | OpLe    -> Arithmetic.mk_le g_ctx arg1 arg2
    | OpGt    -> Arithmetic.mk_gt g_ctx arg1 arg2
    | OpGe    -> Arithmetic.mk_ge g_ctx arg1 arg2
    | OpAnd   -> mk_and [arg1; arg2]
    | OpOr    -> mk_or  [arg1; arg2]
  end

(* =========== CUSTOM SORTS =========== *)
let mk_ctor str =
  Datatype.mk_constructor_s g_ctx str (mk_sym g_ctx ("is_" ^ str)) [] [] []

module UnitSort = struct
  open Z3.Datatype

  let mk_sort =
    mk_sort_s g_ctx "Unit"
      [ mk_constructor_s g_ctx "unit"
                         (Symbol.mk_string g_ctx "isUnit")
                         [] [] []
      ]

  let mk_unit =
    let constructors = get_constructors mk_sort in
    Expr.mk_app g_ctx (List.hd constructors) []
end

module IntegerBaseTypeSort = struct
  open Z3.Datatype
  let mk_sort = mk_sort_s g_ctx "IntegerBaseType"
    [ mk_ctor "ichar_ibty"
    ; mk_ctor "short_ibty"
    ; mk_ctor "int_ibty"
    ; mk_ctor "long_ibty"
    ; mk_ctor "long_long_ibty"
    ]

  let mk_expr (ibty: AilTypes.integerBaseType) =
    let fdecls = get_constructors mk_sort in
    match ibty with
    | Ichar ->
        Expr.mk_app g_ctx (List.nth fdecls 0) []
    | Short ->
        Expr.mk_app g_ctx (List.nth fdecls 1) []
    | Int_ ->
        Expr.mk_app g_ctx (List.nth fdecls 2) []
    | Long ->
        Expr.mk_app g_ctx (List.nth fdecls 3) []
    | LongLong ->
        Expr.mk_app g_ctx (List.nth fdecls 4) []
    | _ -> assert false
end

module IntegerTypeSort = struct
  open Z3.Datatype
  let mk_sort = mk_sort_s g_ctx "IntegerType"
    [ mk_ctor "char_ity"
    ; mk_ctor "bool_ity"
    ; mk_constructor_s g_ctx "signed_ity" (mk_sym g_ctx "is_signed_ity")
        [mk_sym g_ctx "_signed_ity"] [Some IntegerBaseTypeSort.mk_sort] [0]
    ; mk_constructor_s g_ctx "unsigned_ity" (mk_sym g_ctx "is_unsigned_ity")
        [mk_sym g_ctx "_unsigned_ity"] [Some IntegerBaseTypeSort.mk_sort] [0]
    ]

  let mk_expr (ity: AilTypes.integerType) =
    let fdecls = get_constructors mk_sort in
    match ity with
    | Char ->
        Expr.mk_app g_ctx (List.nth fdecls 0) []
    | Bool ->
        Expr.mk_app g_ctx (List.nth fdecls 1) []
    | Signed ibty ->
        Expr.mk_app g_ctx (List.nth fdecls 2) [IntegerBaseTypeSort.mk_expr ibty]
    | Unsigned ibty ->
        Expr.mk_app g_ctx (List.nth fdecls 3) [IntegerBaseTypeSort.mk_expr ibty]
    | _ -> assert false
end

module BasicTypeSort = struct
  open Z3.Datatype
  let mk_sort = mk_sort_s g_ctx "BasicType"
      [ mk_constructor_s g_ctx "integer_bty" (mk_sym g_ctx "is_integer_bty")
        [mk_sym g_ctx "_integer_bty"] [Some IntegerTypeSort.mk_sort] [0]
      ]

  let mk_expr (btype: AilTypes.basicType) : Expr.expr =
    let fdecls = get_constructors mk_sort in
    match btype with
    | Integer ity ->
        Expr.mk_app g_ctx (List.nth fdecls 0) [IntegerTypeSort.mk_expr ity]
    | _ -> assert false
end

module CtypeSort = struct
  open Z3.Datatype
  let mk_sort : Sort.sort = mk_sort_s g_ctx "Ctype"
    [ mk_ctor "void_ty"
    ; mk_constructor_s g_ctx "basic_ty" (mk_sym g_ctx "is_basic_ty")
        [mk_sym g_ctx "_basic_ty"] [Some BasicTypeSort.mk_sort] [0]
    ; mk_constructor_s g_ctx "ptr_ty" (mk_sym g_ctx "is_ptr_ty")
        [] [] []
        (* TODO: recursive data types can not be nested in other types
         * such as tuple  *)
        (*[mk_sym g_ctx "_ptr_ty"] [None] [0] *)
    ]

  let rec mk_expr (ctype: Core_ctype.ctype0) : Expr.expr =
    let fdecls = get_constructors mk_sort in
    match ctype with
    | Void0  ->
        Expr.mk_app g_ctx (List.nth fdecls 0) []
    | Basic0 bty ->
        Expr.mk_app g_ctx (List.nth fdecls 1) [BasicTypeSort.mk_expr bty]
    | Pointer0 (_, ty) ->
        Expr.mk_app g_ctx (List.nth fdecls 2) []
    | _ -> assert false
end

module AddressSort = struct
  open Z3.Datatype
  open Z3.FuncDecl

  let mk_sort =
    mk_sort_s g_ctx ("Addr")
      [ mk_constructor_s g_ctx "addr"
            (mk_sym g_ctx ("_addr"))
            [mk_sym g_ctx ("get_alloc"); mk_sym g_ctx ("get_index")]
            [Some integer_sort; Some integer_sort] [0; 0]
      ]

  let mk_expr (alloc_id: Expr.expr) (index: Expr.expr) =
    let ctor = List.nth (get_constructors mk_sort) 0 in
    Expr.mk_app g_ctx ctor [alloc_id; index]

  let mk_expr_from_addr ((alloc_id, index) : int * int) : Expr.expr =
    mk_expr (int_to_z3 alloc_id) (int_to_z3 index)

  let get_alloc (expr: Expr.expr) : Expr.expr =
    assert (Sort.equal (Expr.get_sort expr) mk_sort);
    let accessors = get_accessors mk_sort in
    let get_value = List.hd (List.nth accessors 0) in
    Expr.mk_app g_ctx get_value [ expr ]

  let get_index (expr: Expr.expr) : Expr.expr =
    assert (Sort.equal (Expr.get_sort expr) mk_sort);
    let accessors = get_accessors mk_sort in
    let get_value = List.nth (List.nth accessors 0) 1 in
    Expr.mk_app g_ctx get_value [ expr ]

  (* ======== *)
  let alloc_size_decl =
    mk_fresh_func_decl g_ctx "alloc_size" [integer_sort] integer_sort

  let valid_index_range (addr: Expr.expr) : Expr.expr =
    let alloc = get_alloc addr in
    let index = get_index addr in
    let alloc_size = Expr.mk_app g_ctx alloc_size_decl [alloc] in
    mk_and [ binop_to_z3 OpGe index (int_to_z3 0)
           ; binop_to_z3 OpLt index alloc_size
           ]

  let shift_index_by_n (addr: Expr.expr) (n: Expr.expr) : Expr.expr =
    let alloc = get_alloc addr in
    let index = get_index addr in
    mk_expr alloc (binop_to_z3 OpAdd index n)

end

module PointerSort = struct
  open Z3.Datatype
  open Z3.FuncDecl

  let mk_sort =
    mk_sort_s g_ctx ("Ptr")
      [ mk_constructor_s g_ctx "ptr"
            (mk_sym g_ctx "_ptr")
            [mk_sym g_ctx ("get_addr")]
            [Some AddressSort.mk_sort] [0]
      ]

  let mk_ptr (addr: Expr.expr) =
    let ctor = List.nth (get_constructors mk_sort) 0 in
    Expr.mk_app g_ctx ctor [addr]

  let get_addr (expr: Expr.expr) =
    assert (Sort.equal (Expr.get_sort expr) mk_sort);
    let accessors = get_accessors mk_sort in
    let get_value = List.hd (List.nth accessors 0) in
    Expr.mk_app g_ctx get_value [ expr ]
end

(* TODO: should create once using fresh names and reuse.
 * Current scheme may be susceptible to name reuse => bugs. *)
module LoadedSort (M : sig val obj_sort : Sort.sort end) = struct
  open Z3.Datatype
  let mk_sort =
    let obj_name = Sort.to_string M.obj_sort in
    mk_sort_s g_ctx ("Loaded_" ^ obj_name)
             [ mk_constructor_s g_ctx
                                ("specified_" ^ obj_name)
                                (mk_sym g_ctx ("is_specified_" ^ obj_name))
                                [mk_sym g_ctx ("get_" ^ obj_name)]
                                [Some M.obj_sort] [0]
             ;  mk_constructor_s g_ctx
                                ("unspecified_" ^ obj_name)
                                (mk_sym g_ctx ("is_unspecified_" ^ obj_name))
                                [mk_sym g_ctx ("get_" ^ obj_name)]
                                [Some CtypeSort.mk_sort] [0]
             ]

  let mk_specified (expr: Expr.expr) =
    assert (Sort.equal (Expr.get_sort expr) M.obj_sort);
    let ctors = get_constructors mk_sort in
    let loaded_ctor = List.nth ctors 0 in
    Expr.mk_app g_ctx loaded_ctor [expr]

  let mk_unspecified (expr: Expr.expr) =
    assert (Sort.equal (Expr.get_sort expr) CtypeSort.mk_sort);
    let ctors = get_constructors mk_sort in
    let unspec_ctor = List.nth ctors 1 in
    Expr.mk_app g_ctx unspec_ctor [expr]


  let is_specified (expr: Expr.expr) =
    assert (Sort.equal (Expr.get_sort expr) mk_sort);
    let recognizers = get_recognizers mk_sort in
    let is_spec = List.nth recognizers 0 in
    Expr.mk_app g_ctx is_spec [ expr ]

  let is_unspecified (expr: Expr.expr) =
    assert (Sort.equal (Expr.get_sort expr) mk_sort);
    let recognizers = get_recognizers mk_sort in
    let is_unspec = List.nth recognizers 1 in
    Expr.mk_app g_ctx is_unspec [ expr ]

  let get_specified_value (expr: Expr.expr) =
    assert (Sort.equal (Expr.get_sort expr) mk_sort);
    let accessors = get_accessors mk_sort in
    let get_value = List.hd (List.nth accessors 0) in
    Expr.mk_app g_ctx get_value [ expr ]

  let get_unspecified_value (expr: Expr.expr) =
    assert (Sort.equal (Expr.get_sort expr) mk_sort);
    let accessors = get_accessors mk_sort in
    let get_value = List.hd (List.nth accessors 1) in
    Expr.mk_app g_ctx get_value [ expr ]

end

module LoadedInteger =
  LoadedSort (struct let obj_sort = integer_sort end)

module LoadedPointer =
  LoadedSort (struct let obj_sort = PointerSort.mk_sort end)

module CFunctionSort = struct
  open Z3.Datatype

  let mk_sort =
    mk_sort_s g_ctx "CFunction"
    [ mk_constructor_s g_ctx "cfun" (mk_sym g_ctx "isCfun")
        [mk_sym g_ctx "getId"] [Some integer_sort] [0]
    ]

  let mk_cfun (id: Expr.expr) =
    let sort = mk_sort in
    let constructors = get_constructors sort in
    let func_decl = List.nth constructors 0 in
    Expr.mk_app g_ctx func_decl [ id ]
end


(* =========== MISCELLANEOUS HELPER FUNCTIONS =========== *)
let mk_unspecified_expr (sort: Sort.sort) (ctype: Expr.expr)
                        : Expr.expr =
  if (Sort.equal (LoadedInteger.mk_sort) sort) then
    LoadedInteger.mk_unspecified ctype
  else if (Sort.equal (LoadedPointer.mk_sort) sort) then
    LoadedPointer.mk_unspecified ctype
  else
    assert false

(* =========== CUSTOM Z3 FUNCTIONS =========== *)
module ImplFunctions = struct
  open Z3.FuncDecl
  (* ---- Implementation ---- *)
  let sizeof_ity = Ocaml_implementation.Impl.sizeof_ity

  (* TODO: precision of Bool is currently 8... *)
  let impl : Implementation.implementation0 = {
    binary_mode = Two'sComplement;
    signed      = (function
                   | Char       -> Ocaml_implementation.Impl.char_is_signed
                   | Bool       -> false
                   | Signed _   -> true
                   | Unsigned _ -> false
                   | _          -> assert false);
    precision   = (fun i -> match sizeof_ity i with
                   | Some x -> x * 8
                   | None   -> assert false );
    size_t0     = Unsigned Long;
    ptrdiff_t1  = Signed Long
  }

  (* ---- Helper functions ---- *)
  let integer_range (impl: Implementation.implementation0)
                    (ity : AilTypes.integerType) =
    let prec = impl.precision ity in
    if impl.signed ity then
      let prec_minus_one = prec - 1 in
      (match impl.binary_mode with
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
               @ [Char; Bool]

  let ity_to_ctype (ity: AilTypes.integerType) : Core_ctype.ctype0 =
    Core_ctype.Basic0 (Integer ity)


  (* ---- HELPER MAP MAKING FUNCTION ---- *)
  let mk_ctype_map (name : string)
                   (types: Core_ctype.ctype0 list)
                   (sort : Sort.sort)
                   : (Core_ctype.ctype0, Expr.expr) Pmap.map =
    List.fold_left (fun acc ctype ->
      let ctype_expr = CtypeSort.mk_expr ctype in
      let expr = Expr.mk_fresh_const g_ctx
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
                               (Boolean.mk_sort g_ctx)
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

(* =========== PPRINTERS =========== *)
let pp_bmc_ret (bmc_ret: bmc_ret) =
  sprintf ">>Expr: %s\n>>Assume:%s\n>>VCs:%s\n"
          (Expr.to_string bmc_ret.expr)
          (List.fold_left (fun s expr -> s ^ "\n>>>>" ^ (Expr.to_string expr))
                          "" bmc_ret.assume
          )
          (List.fold_left (fun s expr -> s ^ "\n>>>>" ^ (Expr.to_string expr))
                          "" bmc_ret.vcs
          )

let rec pp_bmcz3sort (sort: bmcz3sort) =
  match sort with
  | CaseSortBase (expr, sort) ->
      sprintf "(%s,%s)" (Expr.to_string expr) (Sort.to_string sort)
  | CaseSortList sortlist ->
      "[" ^ (String.concat "," (List.map pp_bmcz3sort sortlist)) ^ "]"

let pp_addr (addr: int * int) =
  sprintf "(%d,%d)" (fst addr) (snd addr)

(* =========== CORE TYPES -> Z3 SORTS =========== *)
let cot_to_z3 (cot: core_object_type) : Sort.sort =
  match cot with
  | OTy_integer     -> integer_sort
  | OTy_pointer     -> PointerSort.mk_sort
  | OTy_floating
  | OTy_array _
  | OTy_struct _ ->
      assert false
  | OTy_cfunction _ -> CFunctionSort.mk_sort (* TODO *)
  | OTy_union _ ->
      assert false

let cbt_to_z3 (cbt: core_base_type) : Sort.sort =
  match cbt with
  | BTy_unit                -> UnitSort.mk_sort
  | BTy_boolean             -> Boolean.mk_sort g_ctx
  | BTy_ctype               -> CtypeSort.mk_sort
  | BTy_list _              -> assert false
  | BTy_tuple cbt_list      -> assert false
  | BTy_object obj_type     -> cot_to_z3 obj_type
  | BTy_loaded OTy_integer  -> LoadedInteger.mk_sort
  | BTy_loaded OTy_pointer  -> LoadedPointer.mk_sort
  | BTy_loaded _            -> assert false

let sorts_to_tuple (sorts: Sort.sort list) : Sort.sort =
  let tuple_name =
    "(" ^ (String.concat "," (List.map Sort.to_string sorts)) ^ ")" in
  let arg_list = List.mapi
    (fun i _ -> mk_sym g_ctx ("#" ^ (string_of_int i))) sorts in
  Tuple.mk_sort g_ctx (mk_sym g_ctx tuple_name) arg_list sorts

let ctor_to_z3 (ctor  : typed_ctor)
               (exprs : Expr.expr list)
               (bTy   : core_base_type) =
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
      if (bTy = BTy_loaded OTy_integer) then
        LoadedInteger.mk_specified (List.hd exprs)
      else if (bTy = BTy_loaded OTy_pointer) then
        LoadedPointer.mk_specified (List.hd exprs)
      else
        assert false
  | Cunspecified ->
      assert (List.length exprs = 1);
      if (bTy = BTy_loaded OTy_integer) then
        LoadedInteger.mk_unspecified (List.hd exprs)
      else
        assert false
  | _ ->
      assert false

let integer_value_to_z3 (ival: Ocaml_mem.integer_value) : Expr.expr =
  (* TODO: check which is the correct ival->big num function *)
  match eval_integer_value ival with
  | None -> assert false
  | Some i -> big_num_to_z3 i


let object_value_to_z3 (oval: object_value) : Expr.expr =
  match oval with
  | OVinteger ival -> integer_value_to_z3 ival
  | OVfloating _
  | OVpointer _ ->
      assert false
  | OVcfunction (Sym sym) ->
      CFunctionSort.mk_cfun (int_to_z3 (symbol_to_int sym))
  | OVcfunction _ ->
      assert false
  | OVarray _
  | OVstruct _
  | OVunion _
  | OVcomposite _ ->
      assert false

let value_to_z3 (value: value)
                : Expr.expr =
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
       | _ -> assert false
      end
  | Vloaded (LVunspecified ctype) ->
      begin
      match ctype with
      | Basic0 (Integer _) ->
          LoadedInteger.mk_unspecified (CtypeSort.mk_expr ctype)
      | _ -> assert false
      end

let rec ctype_to_bmcz3sort (ty: Core_ctype.ctype0)
                          : bmcz3sort =
  match ty with
  | Void0     -> assert false
  | Basic0(Integer i) ->
      CaseSortBase (CtypeSort.mk_expr ty, LoadedInteger.mk_sort)
  | Basic0 _ -> assert false
  | Array0(ty2, Some n) ->
      let sort = ctype_to_bmcz3sort ty2 in
      CaseSortList (repeat_n (Nat_big_num.to_int n) sort)
  | Array0(_, None) ->
      assert false
  | Function0 _ -> assert false
  | Pointer0 _ ->
      CaseSortBase (CtypeSort.mk_expr ty, LoadedPointer.mk_sort)
  | Atomic0 _
  | Struct0 _
  | Union0 _
  | Builtin0 _ -> assert false

(* =========== SOME MONAD FUN =========== *)

module BmcM = struct
  type sym_table_ty = (sym_ty, Expr.expr) Pmap.map
  type run_depth_table_ty = (name, int) Pmap.map
  type alloc_ty = int
  type memory_table_ty = (addr_ty, Expr.expr) Pmap.map

  type bmc_state = {
    file            : unit typed_file;

    sym_supply      : sym_supply_ty;
    sym_table       : sym_table_ty;

    (* Map from Erun symbol to number of times Erun encountered.
     * Used to control depth of Erun *)
    run_depth_table : run_depth_table_ty;

    (* Allocation and address supplies *)
    alloc_supply    : alloc_ty;
    memory          : memory_table_ty;

    (* Procedure-local state *)
    proc_expr       : (unit typed_expr) option;
    ret_const       : Expr.expr option; (* Expression returned *)
  }

  (* =========== MONADIC FUNCTIONS =========== *)
  type 'a eff =
    Eff of (bmc_state -> 'a * bmc_state)

  let return (a: 't) : 't eff = Eff (fun st -> (a, st))

  let bind ((Eff ma): 'a eff) (f: 'a -> 'b eff) : 'b eff =
    Eff begin
      fun st ->
        let (a, st') = ma st in
        let Eff mb = f a in
        mb st'
    end

  let (>>=) = bind

  let (>>) m m' = bind m (fun _ -> bind m' (fun x' -> return x'))

  let run : bmc_state -> 'a eff -> 'a * bmc_state =
    fun st (Eff ma) -> ma st

  let sequence ms =
    List.fold_right (
      fun m m' ->
      m  >>= fun x  ->
      m' >>= fun xs ->
      return (x :: xs)
    ) ms (return [])

  let sequence_ ms = List.fold_right (>>) ms (return ())
  let mapM  f ms = sequence (List.map f ms)
  let mapMi f ms = sequence (List.mapi f ms)
  let mapM2 f ms1 ms2  = sequence (List.map2 f ms1 ms2)
  let mapM_ f ms = sequence_ (List.map f ms)

  let get : bmc_state eff =
    Eff (fun st -> (st, st))

  let put (st' : bmc_state) : unit eff =
    Eff (fun _ -> ((), st'))

  (* =========== STATE ACCESSORS =========== *)
  (* file *)
  let get_file : (unit typed_file) eff =
    get >>= fun st ->
    return st.file
  (* sym table *)
  let get_sym_table : sym_table_ty eff =
    get >>= fun st ->
    return st.sym_table

  let lookup_sym (sym: sym_ty) : Expr.expr eff =
    get_sym_table >>= fun sym_table ->
    return (Pmap.find sym sym_table)

  let update_sym_table (new_table: sym_table_ty)
                       : unit eff =
    get >>= fun st ->
    put {st with sym_table = new_table}

  let add_sym_to_sym_table (sym: sym_ty) (expr: Expr.expr)
                           : unit eff =
    get_sym_table >>= fun sym_table ->
    update_sym_table (Pmap.add sym expr sym_table)

  (* run depth table *)
  let get_run_depth_table : run_depth_table_ty eff =
    get >>= fun st ->
    return st.run_depth_table

  let lookup_run_depth (label: name) : int eff =
    get_run_depth_table >>= fun table ->
    match Pmap.lookup label table with
    | None  -> return 0
    | Some i -> return i

  let update_run_depth_table (new_table: run_depth_table_ty)
                             : unit eff =
    get >>= fun st ->
    put {st with run_depth_table = new_table}

  let increment_run_depth (label: name) : unit eff =
    lookup_run_depth label  >>= fun depth ->
    get_run_depth_table    >>= fun table ->
    update_run_depth_table (Pmap.add label (depth+1) table)

  let decrement_run_depth (label: name) : unit eff =
    lookup_run_depth label >>= fun depth ->
    get_run_depth_table    >>= fun table ->
    update_run_depth_table (Pmap.add label (depth-1) table)

  (* allocation *)
  let get_new_alloc_and_update_supply : alloc_ty eff =
    get                    >>= fun st ->
    return st.alloc_supply >>= fun alloc ->
    put {st with alloc_supply = alloc + 1} >>= fun () ->
    return alloc

  (* memory *)
  let get_memory : memory_table_ty eff =
    get >>= fun st ->
    return st.memory

  let update_memory (addr: addr_ty) (expr: Expr.expr) : unit eff =
    get >>= fun st ->
    put {st with memory = Pmap.add addr expr st.memory}

  let update_memory_table (memory: memory_table_ty) : unit eff =
    get >>= fun st ->
    put {st with memory = memory}

  let lookup_memory (addr: addr_ty) : Expr.expr eff =
    get_memory >>= fun memory ->
    return (Pmap.find addr memory)

  let get_all_addresses : (addr_ty list) eff =
    get >>= fun st ->
    return (List.map fst (Pmap.bindings_list st.memory))

  (* proc expr *)
  let get_proc_expr : (unit typed_expr) eff =
    get >>= fun st ->
    return (Option.get st.proc_expr)

  let update_proc_expr (proc_expr: unit typed_expr) : unit eff =
    get >>= fun st ->
    put {st with proc_expr = Some proc_expr}

  (* ret_const*)
  let get_ret_const : Expr.expr eff =
    get >>= fun st ->
    return (Option.get st.ret_const)

  let update_ret_const (expr: Expr.expr) =
    get >>= fun st ->
    put {st with ret_const = Some expr}

  (* =========== STATE INIT =========== *)
  let mk_initial_state (file       : unit typed_file)
                       (sym_supply : sym_supply_ty)
                       : bmc_state =
    { file            = file

    ; sym_supply      = sym_supply
    ; sym_table       = Pmap.empty sym_cmp

    ; run_depth_table = Pmap.empty name_cmp

    ; alloc_supply    = 0
    ; memory          = Pmap.empty Pervasives.compare

    ; proc_expr       = None
    ; ret_const       = None
    }

  (* =========== Manipulating functions ========== *)
  let merge_memory (base     : memory_table_ty)
                   (mod_addr : AddrSet.t)
                   (tables   : memory_table_ty list)
                   (guards   : Expr.expr list) =
    let guarded_tables : (memory_table_ty * Expr.expr) list =
      List.combine tables guards in
    (* for each modified addr... *)
    AddrSet.fold (fun addr acc ->
      match Pmap.lookup addr acc with
      | None -> acc
      | Some expr_base ->
        let new_expr =
          List.fold_right (fun (table, guard) acc_expr ->
            match Pmap.lookup addr table with
            | None      -> acc_expr
            | Some expr -> mk_ite guard expr acc_expr
         ) guarded_tables expr_base in
        (* TODO: create new seq variable? *)
        Pmap.add addr new_expr acc
    ) mod_addr base

  (* =========== Pprinters =========== *)
  let pp_sym_table (table: sym_table_ty) =
    Pmap.fold (fun sym expr acc ->
      sprintf "%s\n%s -> %s" acc (symbol_to_string sym) (Expr.to_string expr))
      table ""

  let pp_addr ((x,y): addr_ty) =
    sprintf "(%d,%d)" x y

  let pp_memory (memory: memory_table_ty) =
    Pmap.fold (fun addr expr acc ->
      sprintf "%s\n%s -> %s" acc (pp_addr addr) (Expr.to_string expr))
    memory ""
end

let (>>=)  = BmcM.bind
let return = BmcM.return

(* =========== SYMBOL TABLE MAINTENANCE FUNCTIONS =========== *)
let symbol_to_fresh_z3_const (sym: sym_ty) (sort: Sort.sort) : Expr.expr =
  Expr.mk_fresh_const g_ctx (symbol_to_string sym) sort

let add_sym_to_sym_table (sym: sym_ty) (ty: core_base_type)
                         : unit BmcM.eff =
  let z3_sort = cbt_to_z3 ty in
  let z3_sym  = symbol_to_fresh_z3_const sym z3_sort in
  BmcM.add_sym_to_sym_table sym z3_sym

let initialise_param ((sym, ty) : sym_ty * core_base_type)
                     : unit BmcM.eff =
  assert (not (is_core_ptr_bty ty));
  dprintf "Initialising param: %s %s\n"
          (symbol_to_string sym)
          (pp_to_string (Pp_core.Basic.pp_core_base_type ty));
  (* TODO: do not handle pointers for now.
   *       Pointers: need to do a create maybe. *)
  add_sym_to_sym_table sym ty

let rec add_pattern_to_sym_table (pattern: typed_pattern)
                                 : unit BmcM.eff =
  match pattern with
  | CaseBase(None, _) ->
      return () (* Do nothing; wildcard => no symbol *)
  | CaseBase(Some sym, ty) ->
      add_sym_to_sym_table sym ty
  | CaseCtor (ctor, patlist) ->
      BmcM.mapM_ add_pattern_to_sym_table patlist

(* =========== Z3 LET BINDINGS =========== *)
let mk_let_binding (maybe_sym: sym_ty option)
                   (expr: Expr.expr)
                   : Expr.expr BmcM.eff =
  match maybe_sym with
  | None -> return mk_true
  | Some sym ->
      BmcM.lookup_sym sym >>= fun sym_expr ->
      (* TODO: hack for C functions... *)
      if (Sort.equal CFunctionSort.mk_sort (Expr.get_sort expr)) then
        BmcM.add_sym_to_sym_table sym expr >>= fun () ->
        return (mk_eq sym_expr expr)
      else
        return (mk_eq sym_expr expr)

let rec mk_let_bindings (pat: typed_pattern) (expr: Expr.expr)
                        : Expr.expr BmcM.eff =
  match pat with
  | CaseBase(maybe_sym, _) ->
      mk_let_binding maybe_sym expr
  | CaseCtor(Ctuple, patlist) ->
      assert (Expr.get_num_args expr = List.length patlist);
      BmcM.mapM (fun (pat, e) -> mk_let_bindings pat e)
                (List.combine patlist (Expr.get_args expr)) >>= fun bindings ->
      return (mk_and bindings)
  | CaseCtor(Cspecified, [CaseBase(sym, BTy_object OTy_integer)]) ->
      let is_specified = LoadedInteger.is_specified expr in
      let specified_value = LoadedInteger.get_specified_value expr in
      mk_let_binding sym specified_value >>= fun is_eq_value ->
      return (mk_and [is_specified; is_eq_value])
  | CaseCtor(Cspecified, [CaseBase(sym, BTy_object OTy_pointer)]) ->
      let is_specified = LoadedPointer.is_specified expr in
      let specified_value = LoadedPointer.get_specified_value expr in
      mk_let_binding sym specified_value >>= fun is_eq_value ->
      return (mk_and [is_specified; is_eq_value])
  | CaseCtor(Cspecified, _) ->
      assert false
  | CaseCtor(Cunspecified, [CaseBase(sym, BTy_ctype)]) ->
      let (is_unspecified, unspecified_value) =
        if (Sort.equal (Expr.get_sort expr) (LoadedInteger.mk_sort)) then
          let is_unspecified = LoadedInteger.is_unspecified expr in
          let unspecified_value = LoadedInteger.get_unspecified_value expr in
          (is_unspecified, unspecified_value)
        else if (Sort.equal (Expr.get_sort expr) (LoadedPointer.mk_sort)) then
          let is_unspecified = LoadedPointer.is_unspecified expr in
          let unspecified_value = LoadedPointer.get_unspecified_value expr in
          (is_unspecified, unspecified_value)
        else
          assert false
      in
      mk_let_binding sym unspecified_value >>= fun is_eq_value ->
      return (mk_and [is_unspecified; is_eq_value])
  | CaseCtor(Cunspecified, _) ->
      assert false
  | CaseCtor(_, _) ->
      assert false

(* =========== PATTERN MATCHING =========== *)
let rec pattern_match (pattern: typed_pattern)
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
  | CaseCtor(Cspecified, [CaseBase(_, BTy_object OTy_integer)]) ->
      LoadedInteger.is_specified expr
  | CaseCtor(Cspecified, [CaseBase(_, BTy_object OTy_pointer)]) ->
      LoadedPointer.is_specified expr
  | CaseCtor(Cspecified, _) ->
      assert false
  | CaseCtor(Cunspecified, [CaseBase(_, BTy_ctype)]) ->
      if (Sort.equal (Expr.get_sort expr) (LoadedInteger.mk_sort)) then
        LoadedInteger.is_unspecified expr
      else if (Sort.equal (Expr.get_sort expr) (LoadedPointer.mk_sort)) then
        LoadedPointer.is_unspecified expr
      else
        assert false
  | _ -> assert false

(* Compute conditions for matching cases.
 * Returns (vc, case_guard list) where vc asserts that some pattern is matched.
 *)
let compute_case_guards (patterns: typed_pattern list)
                        (to_match: Expr.expr)
                        : Expr.expr * Expr.expr list =
  let pattern_guards =
    List.map (fun pat -> pattern_match pat to_match) patterns in
  let case_guards = List.mapi (
      fun i expr ->
        mk_and [ mk_not (mk_or (list_take i pattern_guards))
               ; expr]) pattern_guards in
  let vc = mk_or pattern_guards in
  (vc, case_guards)

(* =========== MODEL CHECKING FUNCTIONS =========== *)
let rec bmc_pexpr (Pexpr(_, bTy, pe) as pexpr: typed_pexpr) :
                  bmc_pret BmcM.eff =
  match pe with
  | PEsym sym ->
      BmcM.lookup_sym sym >>= fun sym_expr ->
      return { expr   = sym_expr
             ; assume = []
             ; vcs    = []
             }
  | PEimpl const ->
      BmcM.get_file >>= fun file ->
      begin match Pmap.lookup const file.impl with
      | Some (Def (_, pe)) ->
          bmc_pexpr pe
      | _ -> assert false
      end
  | PEval cval ->
      return { expr   = value_to_z3 cval
             ; assume = []
             ; vcs    = []
             }
  | PEconstrained _
  | PEundef _ ->
      let sort = cbt_to_z3 bTy in
      return { expr   = Expr.mk_fresh_const g_ctx "undef" sort
             ; assume = []
             ; vcs    = [ mk_false ]
             }
  | PEerror _ ->
      let sort = cbt_to_z3 bTy in
      return { expr   = Expr.mk_fresh_const g_ctx "error" sort
             ; assume = []
             ; vcs    = [ mk_false ]
             }
  | PEctor(Civmin, [Pexpr(_, BTy_ctype, PEval (Vctype ctype))]) ->
      return { expr   = Pmap.find ctype ImplFunctions.ivmin_map
             ; assume = []
             ; vcs    = []
             }
  | PEctor(Civmax, [Pexpr(_, BTy_ctype, PEval (Vctype ctype))]) ->
      return { expr   = Pmap.find ctype ImplFunctions.ivmax_map
             ; assume = []
             ; vcs    = []
             }
  | PEctor(Civsizeof, [Pexpr(_, BTy_ctype, PEval (Vctype ctype))]) ->
      return { expr   = Pmap.find ctype ImplFunctions.sizeof_map
             ; assume = []
             ; vcs    = []
             }
  | PEctor (ctor, pelist) ->
      BmcM.mapM bmc_pexpr pelist >>= fun res_pelist ->
      return { expr   = ctor_to_z3 ctor (List.map pget_expr res_pelist) bTy
             ; assume = List.concat (List.map pget_assume res_pelist)
             ; vcs    = List.concat (List.map pget_vcs res_pelist)
             }
  | PEcase (pe, caselist) ->
      assert (List.length caselist > 0);
      bmc_pexpr pe >>= fun res_pe ->
      (* match_vc = assert some case is matched *)
      let (match_vc, case_guards) =
        compute_case_guards (List.map fst caselist) res_pe.expr in

      BmcM.get_sym_table >>= fun old_sym_table ->

      BmcM.mapM (fun (pat, case_pexpr) ->
                  add_pattern_to_sym_table pat    >>= fun () ->
                  mk_let_bindings pat res_pe.expr >>= fun let_binding ->
                  bmc_pexpr case_pexpr            >>= fun res_case_pexpr ->
                  BmcM.update_sym_table old_sym_table >>= fun () ->
                  return (let_binding, res_case_pexpr)
                ) caselist >>= fun res_caselist ->
      let guarded_bindings = List.map2 (
        fun guard (let_binding, _) -> mk_implies guard let_binding)
        case_guards res_caselist in
      let case_assumes =
        List.concat (List.map (fun (_, res) -> res.assume) res_caselist) in
      let guarded_vcs = List.map2 (
        fun guard (_, res) -> mk_implies guard (mk_and res.vcs))
        case_guards res_caselist in
      let ite_expr =
        if List.length caselist = 1 then
          pget_expr (snd (List.hd res_caselist))
        else
          let rev_list = List.rev (List.map snd res_caselist) in
          let rev_case_guards = List.rev case_guards in
          let last_case_expr = pget_expr (List.hd rev_list) in
          List.fold_left2 (fun acc guard res -> mk_ite guard res.expr acc)
                          last_case_expr
                          (List.tl rev_case_guards)
                          (List.tl rev_list)
      in
      return { expr   = ite_expr
             ; assume =   res_pe.assume
                          @ guarded_bindings
                          @ case_assumes
             ; vcs    = match_vc :: (res_pe.vcs @ guarded_vcs)
             }
  | PEarray_shift (ptr, ty, index) ->
      bmc_pexpr ptr   >>= fun res_ptr ->
      bmc_pexpr index >>= fun res_index ->
      let ty_size = bmcz3sort_size (ctype_to_bmcz3sort ty) in
      let shift_size = binop_to_z3 OpMul res_index.expr (int_to_z3 ty_size) in
      let addr     = PointerSort.get_addr res_ptr.expr in
      let new_addr = AddressSort.shift_index_by_n addr shift_size in
      return { expr   = PointerSort.mk_ptr new_addr
             ; assume = res_ptr.assume @ res_index.assume
             ; vcs    = res_ptr.vcs @ res_index.vcs
             }
  | PEmember_shift _
  | PEmemberof _  ->
      assert false
  | PEnot pe ->
      bmc_pexpr pe >>= fun res ->
      return {res with expr = mk_not res.expr}
  | PEop (binop, pe1, pe2) ->
      (* TODO: symbols added in pe1 visible in pe2 *)
      bmc_pexpr pe1 >>= fun res1 ->
      bmc_pexpr pe2 >>= fun res2 ->
      return { expr   = binop_to_z3 binop res1.expr res2.expr
             ; assume = res1.assume @ res2.assume
             ; vcs    = res1.vcs @ res2.vcs
             }
  | PEstruct _
  | PEunion _ ->
      assert false
  | PEcall (name, pelist) ->
      BmcM.get_file >>= fun file ->
      BmcM.lookup_run_depth name >>= fun depth ->
      (* Get the function called; either from stdlib or impl constants *)
      let (ty, args, fun_expr) =
        match name with
        | Sym sym ->
            begin match Pmap.lookup sym file.stdlib with
            | Some (Fun(ty, args, fun_expr)) ->
                (ty, args, fun_expr)
            | _ -> assert false
            end
        | Impl impl ->
            begin match Pmap.lookup impl file.impl with
            | Some (IFun (ty, args, fun_expr)) ->
                (ty, args, fun_expr)
            | _ -> assert false
            end
      in
      if depth >= g_max_run_depth then
        return { expr   = Expr.mk_fresh_const g_ctx
                              "call_depth_exceeded" (cbt_to_z3 ty)
               ; assume = []
               ; vcs    = [ mk_false ]
               }
      else begin
      (* Bmc each argument *)
      BmcM.mapM (fun pe -> bmc_pexpr pe) pelist >>= fun arg_retlist ->
      (* Substitute arguments in function call *)
      let sub_map = List.fold_right2
          (fun (sym, _) pe table -> Pmap.add sym pe table)
          args pelist (Pmap.empty sym_cmp) in
      (* Bmc the function body *)
      let expr_to_check = substitute_pexpr sub_map fun_expr in
      BmcM.increment_run_depth name       >>= fun () ->
      BmcM.get_sym_table                  >>= fun old_sym_table ->
      bmc_pexpr expr_to_check             >>= fun ret_call ->
      BmcM.decrement_run_depth name       >>= fun () ->
      BmcM.update_sym_table old_sym_table >>= fun () ->

      (* Alias for function call for debug purposes.
       * Using this may increase the time needed by the solver. *)
      (*
      let arg_names = List.map (fun ret -> Expr.to_string ret.expr)
                               arg_retlist in

      let const =
        Expr.mk_fresh_const g_ctx
             (sprintf "%s(%s)" (name_to_string name)
                               (String.concat "," arg_names))
             (cbt_to_z3 ty) in
      let eq_expr = mk_eq const ret_call.expr in
      *)

      return { expr   = ret_call.expr (*const*)
             ; assume =               (*[eq_expr] @ *)
                           ret_call.assume
                        @ (List.concat (List.map pget_assume arg_retlist))
             ; vcs    = ret_call.vcs
                        @ (List.concat (List.map pget_vcs arg_retlist))
             }
      end
  | PElet (pat, pe1, pe2) ->
      bmc_pexpr pe1                 >>= fun res1 ->
      add_pattern_to_sym_table pat  >>= fun () ->
      mk_let_bindings pat res1.expr >>= fun let_binding ->
      bmc_pexpr pe2                 >>= fun res2 ->
      return { expr    = res2.expr
             ; assume  = let_binding::(res1.assume @ res2.assume)
             ; vcs     = res1.vcs @ res2.vcs
             }
  | PEif (pe_cond, pe1, pe2) ->
      (* TODO: symbols added in pe1 visible in pe2 *)
      bmc_pexpr pe_cond       >>= fun res_cond ->
      bmc_pexpr pe1           >>= fun res1 ->
      bmc_pexpr pe2           >>= fun res2 ->
      let new_vcs =
          res_cond.vcs
        @ (List.map (fun vc -> mk_implies res_cond.expr vc) res1.vcs)
        @ (List.map (fun vc -> mk_implies (mk_not res_cond.expr) vc)
                    res2.vcs)
      in
      return { expr   = mk_ite res_cond.expr res1.expr res2.expr
             ; assume = res_cond.assume @ res1.assume @ res2.assume
             ; vcs    = new_vcs
             }
  | PEis_scalar _
  | PEis_integer _ ->
      assert false
  | PEis_signed _ ->
      assert false
  | PEis_unsigned (Pexpr(_, BTy_ctype, PEval (Vctype ctype))) ->
      return { expr   = Pmap.find ctype ImplFunctions.is_unsigned_map
             ; assume = []
             ; vcs = []
             }

  | PEis_unsigned _ ->
      assert false

let bmc_paction (Paction(pol, Action(_, _, action_)): unit typed_paction)
                : bmc_ret BmcM.eff =
  match action_ with
  | Create (align, Pexpr(_, BTy_ctype, PEval (Vctype ctype)), prefix) ->
      (* TODO: non-basic types? *)
      let sortlist = ctype_to_bmcz3sort ctype in
      let flat_sortlist = flatten_bmcz3sort sortlist in
      let allocation_size = bmcz3sort_size sortlist in
      BmcM.get_new_alloc_and_update_supply >>= fun alloc_id ->

      BmcM.mapMi (fun i (ctype_expr, sort) ->
        (* make new address *)
        let addr = (alloc_id, i) in
        let addr_expr = AddressSort.mk_expr_from_addr addr in
        (* initialise to unspecified *)
        let seq_var =
          Expr.mk_fresh_const g_ctx (Expr.to_string addr_expr) sort in
        let init_unspec =
          mk_eq seq_var (mk_unspecified_expr sort ctype_expr) in
        (* track in state that mem[addr] = seq_var *)
        BmcM.update_memory (alloc_id, i) seq_var >>= fun () ->
        return (addr, init_unspec)
        ) flat_sortlist >>= fun retlist ->

      (* Assert alloc_size(alloc_id) = allocation_size *)
      let alloc_size_expr =
        mk_eq (Expr.mk_app g_ctx AddressSort.alloc_size_decl
                                 [int_to_z3 alloc_id])
              (int_to_z3 allocation_size) in
      let assume = alloc_size_expr :: (List.map snd retlist) in
      let first_addr = AddressSort.mk_expr_from_addr (fst (List.hd retlist)) in
      return { expr      = PointerSort.mk_ptr first_addr
             ; assume    = assume
             ; vcs       = []
             ; drop_cont = mk_false
             ; mod_addr  = AddrSet.of_list (List.map fst retlist)
             ; ret_cond  = mk_true
             }
  | Create _ -> assert false
  | CreateReadOnly _
  | Alloc0 _ ->
      assert false
  | Kill pe ->
      (* TODO: kill currently ignored *)
      bmc_pexpr pe >>= fun res_pe ->
      return { expr      = UnitSort.mk_unit
             ; assume    = res_pe.assume
             ; vcs       = res_pe.vcs
             ; drop_cont = mk_false
             ; mod_addr  = AddrSet.empty
             ; ret_cond  = mk_true
             }
  | Store0 (Pexpr(_, _, PEval (Vctype ty)), Pexpr(_, _, PEsym sym),
            to_store, memorder) ->
      (* TODO: do alias analysis *)
      (* TODO: check alignment *)
      BmcM.lookup_sym sym         >>= fun sym_expr ->
      bmc_pexpr to_store          >>= fun res_to_store ->
      BmcM.get_memory             >>= fun possible_addresses ->
      (* BmcM.get_address_type_table >>= fun possible_addresses -> *)

      let flat_sortlist = flatten_bmcz3sort (ctype_to_bmcz3sort ty) in
      let (ctype_expr, sort) = List.hd flat_sortlist in
      assert (List.length flat_sortlist = 1);

      BmcM.mapM (fun (addr, expr_in_memory) ->
        let addr_sort = Expr.get_sort expr_in_memory in
        if (Sort.equal sort addr_sort) then
          begin
          (*BmcM.lookup_memory addr >>= fun expr_in_memory -> *)
          let addr_expr = AddressSort.mk_expr_from_addr addr  in
          let new_seq_var =
            Expr.mk_fresh_const g_ctx (Expr.to_string addr_expr) addr_sort in
          (* new_seq_var is equal to to_store if addr_eq, else old value *)
          let addr_eq = mk_eq (PointerSort.get_addr sym_expr) addr_expr in
          let new_val = mk_eq new_seq_var res_to_store.expr in
          let old_val = mk_eq new_seq_var expr_in_memory in
          BmcM.update_memory addr new_seq_var >>= fun () ->
          return (Some (addr, mk_ite addr_eq new_val old_val))
          end
        else
          return None
        ) (Pmap.bindings_list possible_addresses) >>= fun update_list ->

      let filtered =
        List.map Option.get (List.filter is_some update_list) in
      assert (List.length filtered > 0);

      return { expr      = UnitSort.mk_unit
             ; assume    = List.map snd filtered @ res_to_store.assume
             ; vcs       = res_to_store.vcs
             ; drop_cont = mk_false
             ; mod_addr  = AddrSet.of_list (List.map fst filtered)
             ; ret_cond  = mk_true
             }
  | Store0 _ ->
      assert false
  | Load0 (Pexpr(_, _, PEval (Vctype ty)), Pexpr(_,_, PEsym sym), memorder) ->
      BmcM.lookup_sym sym         >>= fun sym_expr ->
      assert (Sort.equal (Expr.get_sort sym_expr) PointerSort.mk_sort);
      let flat_sortlist = flatten_bmcz3sort (ctype_to_bmcz3sort ty) in
      let (ctype_expr, sort) = List.hd flat_sortlist in
      assert (List.length flat_sortlist = 1);

      let ret_expr =
        Expr.mk_fresh_const g_ctx ("load_" ^ (symbol_to_string sym)) sort in

      BmcM.get_memory             >>= fun possible_addresses ->
      (* sym_addr = addr => ret_expr = mem[addr] *)
      BmcM.mapM (fun (addr, expr_in_memory) ->
        let addr_sort = Expr.get_sort expr_in_memory in
        if (Sort.equal sort addr_sort) then
          let addr_expr = AddressSort.mk_expr_from_addr addr in
          let addr_eq = mk_eq addr_expr (PointerSort.get_addr sym_expr) in
          let impl_expr = mk_implies addr_eq (mk_eq ret_expr expr_in_memory) in
          return (Some (impl_expr, addr_eq))
        else
          return None
      ) (Pmap.bindings_list possible_addresses) >>= fun retlist ->
      let filtered = List.map Option.get (List.filter is_some retlist) in

      return { expr      = ret_expr
             ; assume    = List.map fst filtered
             ; vcs       = [mk_or (List.map snd filtered)]
             ; drop_cont = mk_false
             ; mod_addr  = AddrSet.empty
             ; ret_cond  = mk_true
             }
  | Load0 _
  | RMW0 _
  | Fence0 _ ->
      assert false

let rec bmc_expr (Expr(_, expr_): unit typed_expr)
                 : bmc_ret BmcM.eff =
  match expr_ with
  | Epure pe ->
      bmc_pexpr pe >>= fun pres ->
      return (bmc_pret_to_ret pres)
  | Ememop (PtrValidForDeref, [ptr])  ->
      bmc_pexpr ptr >>= fun res_ptr ->
      let addr     : Expr.expr = PointerSort.get_addr res_ptr.expr in
      let range_assert = AddressSort.valid_index_range addr in
      return { expr      = range_assert
             ; assume    = res_ptr.assume
             ; vcs       = res_ptr.vcs
             ; drop_cont = mk_false
             ; mod_addr  = AddrSet.empty
             ; ret_cond  = mk_true
             }
  | Ememop _ ->
      assert false
  | Eaction paction ->
      bmc_paction paction
  | Ecase (pe, caselist) ->
      (* TODO: code duplication from PEcase *)
      assert (List.length caselist > 0);
      bmc_pexpr pe >>= fun res_pe ->
      let (match_vc, case_guards) =
        compute_case_guards (List.map fst caselist) res_pe.expr in
      BmcM.get_sym_table >>= fun old_sym_table ->
      BmcM.get_memory    >>= fun old_memory ->

      BmcM.mapM (fun (pat, case_expr) ->
                  add_pattern_to_sym_table pat    >>= fun () ->
                  mk_let_bindings pat res_pe.expr >>= fun let_binding ->
                  bmc_expr case_expr              >>= fun res_case_expr ->
                  BmcM.get_memory                 >>= fun mem ->
                  BmcM.update_sym_table old_sym_table >>= fun () ->
                  BmcM.update_memory_table old_memory >>= fun () ->
                  return (let_binding, mem, res_case_expr)
                ) caselist >>= fun res_caselist ->
      let reslist = List.map (fun (_, _, a) -> a) res_caselist in
      (* Update memory table *)
      let mod_addr = List.fold_right (
        fun res acc -> AddrSet.union acc res.mod_addr) reslist AddrSet.empty in
      let new_memory =
        BmcM.merge_memory old_memory mod_addr
                          (List.map (fun (_, m, _) -> m) res_caselist)
                          case_guards in
      BmcM.update_memory_table new_memory >>= fun () ->

      let guarded_bindings = List.map2 (
        fun guard (binding, _, _) -> mk_implies guard binding)
        case_guards res_caselist in
      let case_assumes = List.concat (List.map eget_assume reslist) in
      let guarded_vcs = List.map2 (
        fun guard res -> mk_implies guard (mk_and (eget_vcs res)))
        case_guards reslist in
      let ite_expr =
        if List.length caselist = 1 then
          eget_expr (List.hd reslist)
        else
          let rev_list = List.rev reslist in
          let rev_case_guards = List.rev case_guards in
          let last_case_expr = eget_expr (List.hd rev_list) in
          List.fold_left2 (fun acc guard res -> mk_ite guard (eget_expr res) acc)
                          last_case_expr
                          (List.tl rev_case_guards)
                          (List.tl rev_list) in
      let assume = res_pe.assume @ guarded_bindings @ case_assumes in
      let drop_cont = mk_or
        (List.map2 (fun guard res -> mk_and [guard; res.drop_cont])
                   case_guards reslist) in
      let ret_cond_list = List.map2 mk_implies case_guards
                                               (List.map eget_ret reslist) in
      return { expr      = ite_expr
             ; assume    = assume
             ; vcs       = match_vc :: (res_pe.vcs @ guarded_vcs)
             ; drop_cont = drop_cont
             ; mod_addr  = mod_addr
             ; ret_cond  = mk_and ret_cond_list
             }
  | Eskip ->
      return { expr      = UnitSort.mk_unit
             ; assume    = []
             ; vcs       = []
             ; drop_cont = mk_false
             ; mod_addr  = AddrSet.empty
             ; ret_cond = mk_true
             }
  | Eproc _ ->
      assert false
  | Eccall (_, Pexpr(_, BTy_object (OTy_cfunction (retTy, numArgs, var)),
                        PEval(Vobject (OVcfunction (Sym sym)))), arglist)
    (* fall through *)
  | Eccall (_, Pexpr(_, BTy_object (OTy_cfunction (retTy, numArgs, var)),
                        PEsym sym), arglist) ->
      BmcM.lookup_sym sym >>= fun sym_expr ->
      BmcM.get_file       >>= fun file ->
      assert (Expr.get_num_args sym_expr = 1);
      let sym_id = z3num_to_int (List.hd (Expr.get_args sym_expr)) in
      let func_sym = Sym.Symbol(sym_id, None) in
      let (fun_ty, fun_args, fun_expr) =
        match Pmap.lookup func_sym file.funs with
        | Some (Proc(_, ty, params, e)) -> (ty, params, e)
        | _    -> assert false in
      BmcM.lookup_run_depth (Sym func_sym) >>= fun depth ->
      if depth >= g_max_run_depth then
        return { expr      = Expr.mk_fresh_const g_ctx
                                 "call_depth_exceeded" (cbt_to_z3 fun_ty)
               ; assume    = []
               ; vcs       = [ mk_false ]
               ; drop_cont = mk_false
               ; mod_addr  = AddrSet.empty
               ; ret_cond  = mk_true
               }
      else begin
        BmcM.mapM bmc_pexpr arglist >>= fun arg_retlist ->
        let sub_map = List.fold_right2
          ( fun (sym, _) pe table -> Pmap.add sym pe table)
          fun_args arglist (Pmap.empty sym_cmp) in
        let expr_to_check = substitute_expr sub_map fun_expr in
        let new_ret_const =
          mk_fresh_const (sprintf "ret_%d" sym_id) (cbt_to_z3 fun_ty) in
        BmcM.get_proc_expr                      >>= fun old_proc_expr ->
        BmcM.get_ret_const                      >>= fun old_ret_const ->
        BmcM.get_sym_table                      >>= fun old_sym_table ->
        BmcM.update_proc_expr expr_to_check     >>= fun () ->
        BmcM.update_ret_const new_ret_const     >>= fun () ->
        BmcM.increment_run_depth (Sym func_sym) >>= fun () ->
        bmc_expr expr_to_check                  >>= fun ret_call ->
        BmcM.update_ret_const old_ret_const     >>= fun () ->
        BmcM.update_proc_expr old_proc_expr     >>= fun () ->
        BmcM.update_sym_table old_sym_table     >>= fun () ->
        BmcM.decrement_run_depth (Sym func_sym) >>= fun () ->

        let proc_ret_cond =
          mk_and [mk_implies (mk_not ret_call.drop_cont)
                             (mk_eq new_ret_const ret_call.expr)
                 ; ret_call.ret_cond] in

        return { expr      = new_ret_const
               ; assume    = proc_ret_cond
                             ::ret_call.assume
                             @ (List.concat (List.map pget_assume arg_retlist))
               ; vcs       = ret_call.vcs
                             @ (List.concat (List.map pget_vcs arg_retlist))
               ; drop_cont = mk_false
               ; mod_addr  = ret_call.mod_addr
               ; ret_cond  = mk_true
               }
      end
  | Eccall _
  | Eunseq _
  | Eindet _ -> assert false
  | Ebound (n, e1) ->
      (* TODO: Ebound currently ignored
       * assert n=0 only because have not worked with C where n!=0
       *)
      assert (n = 0);
      bmc_expr e1
  | End elist ->
      assert (List.length elist > 1);
      BmcM.get_sym_table >>= fun old_sym_table ->
      BmcM.get_memory    >>= fun old_memory ->
      BmcM.mapM (fun expr ->
        bmc_expr expr                       >>= fun res_expr ->
        BmcM.get_memory                     >>= fun mem ->
        BmcM.update_sym_table old_sym_table >>= fun () ->
        BmcM.update_memory_table old_memory >>= fun () ->
        return (mem, res_expr)
      ) elist >>= fun res_elist ->

      let bmc_retlist = List.map snd res_elist in
      let choice_vars = List.mapi (
        fun i _ -> Expr.mk_fresh_const g_ctx
                        ("seq_" ^ (string_of_int i))
                        (Boolean.mk_sort g_ctx)) elist in

      let mod_addr = List.fold_right (
        fun res acc -> AddrSet.union acc res.mod_addr)
        bmc_retlist AddrSet.empty in
      let new_memory =
        BmcM.merge_memory old_memory mod_addr
                          (List.map fst res_elist)
                          choice_vars in
      BmcM.update_memory_table new_memory >>= fun () ->

      (* Assert exactly one choice is taken *)
      let xor_expr = List.fold_left mk_xor mk_false choice_vars in
      let vcs = List.map2
          (fun choice res -> mk_implies choice (mk_and (eget_vcs res)))
          choice_vars bmc_retlist in
      let drop_cont = mk_or (List.map2
          (fun choice res -> mk_and [choice; res.drop_cont])
          choice_vars bmc_retlist) in
      let ret_expr = List.fold_left2
          (fun acc choice res -> mk_ite choice (eget_expr res) acc)
          (eget_expr (List.hd bmc_retlist))
          (List.tl choice_vars)
          (List.tl bmc_retlist) in
      return { expr      = ret_expr
             ; assume    = xor_expr
                           :: (List.concat (List.map eget_assume bmc_retlist))
             ; vcs       = vcs
             ; drop_cont = drop_cont
             ; mod_addr  = mod_addr
             ; ret_cond  = mk_and (List.map eget_ret bmc_retlist)
             }
  | Erun (_, label, pelist) ->
      BmcM.lookup_run_depth (Sym label) >>= fun depth ->
      if depth >= g_max_run_depth then
        (* TODO: flag as special vc? *)
        return { expr      = UnitSort.mk_unit
               ; assume    = []
               ; vcs       = [mk_false]
               ; drop_cont = mk_true
               ; mod_addr  = AddrSet.empty
               ; ret_cond  = mk_true
               }
      else begin
        BmcM.get_proc_expr >>= fun proc_expr ->
        let (cont_syms, cont_expr) = Option.get (find_labeled_continuation
                          Sym.instance_Basic_classes_Eq_Symbol_sym_dict
                          label proc_expr) in
        assert (List.length pelist = List.length cont_syms);
        (* TODO: rename symbols in continuation? *)
        let sub_map = List.fold_right2 (fun sym pe map -> Pmap.add sym pe map)
                                       cont_syms pelist (Pmap.empty sym_cmp) in
        let cont_to_check = substitute_expr sub_map cont_expr in
        BmcM.increment_run_depth (Sym label) >>= fun () ->
        bmc_expr cont_to_check               >>= fun run_res ->
        BmcM.decrement_run_depth (Sym label) >>= fun () ->
        BmcM.get_ret_const                   >>= fun ret_const ->
        return { expr      = UnitSort.mk_unit
               ; assume    = run_res.assume
               ; vcs       = run_res.vcs
               ; drop_cont = mk_true
               ; mod_addr  = run_res.mod_addr
               ; ret_cond  = mk_and [mk_implies (mk_not run_res.drop_cont)
                                                (mk_eq ret_const run_res.expr)
                                    ; run_res.ret_cond]
               }
      end
  | Epar _
  | Ewait _ ->
      assert false
  | Eif (pe, e1, e2) ->
      bmc_pexpr pe                        >>= fun res_pe ->
      BmcM.get_sym_table                  >>= fun old_sym_table ->
      BmcM.get_memory                     >>= fun old_memory ->
      bmc_expr e1                         >>= fun res_e1 ->
      BmcM.get_memory                     >>= fun mem_e1 ->
      BmcM.update_sym_table old_sym_table >>= fun () ->
      BmcM.update_memory_table old_memory >>= fun () ->
      bmc_expr e2                         >>= fun res_e2 ->
      BmcM.get_memory                     >>= fun mem_e2 ->
      BmcM.update_sym_table old_sym_table >>= fun () ->

      let mod_addr = AddrSet.union res_e1.mod_addr res_e2.mod_addr in
      let new_memory =
        BmcM.merge_memory old_memory
                          mod_addr
                          [mem_e1     ; mem_e2]
                          [res_pe.expr; mk_not res_pe.expr] in
      BmcM.update_memory_table new_memory >>= fun () ->

      let vcs =
          res_pe.vcs
        @ (List.map (fun vc -> mk_implies res_pe.expr vc) res_e1.vcs)
        @ (List.map (fun vc -> mk_implies (mk_not res_pe.expr) vc)
                    res_e2.vcs) in
      let drop_cont = mk_or
        [ mk_and [res_pe.expr       ; res_e1.drop_cont]
        ; mk_and [mk_not res_pe.expr; res_e2.drop_cont]
        ] in
      return { expr      = mk_ite res_pe.expr res_e1.expr res_e2.expr
             ; assume    = res_pe.assume @ res_e1.assume @ res_e2.assume
             ; vcs       = vcs
             ; drop_cont = drop_cont
             ; mod_addr  = mod_addr
             ; ret_cond  = mk_and
                           [ mk_implies res_pe.expr          res_e1.ret_cond
                           ; mk_implies (mk_not res_pe.expr) res_e2.ret_cond
                           ]
             }
  | Elet _
  | Easeq _ ->
      assert false
  | Ewseq (pat, e1, e2) (* TODO: fall through for now *)
  | Esseq (pat, e1, e2) ->
      bmc_expr e1                   >>= fun res1 ->
      add_pattern_to_sym_table pat  >>= fun () ->
      mk_let_bindings pat res1.expr >>= fun let_binding ->
      bmc_expr e2                   >>= fun res2 ->

      (* TODO: do we care about properly maintaining the memory table ?*)
      (* TODO: do optimization based on drop_cont *)
      return { expr      = res2.expr
             ; assume    = let_binding::(res1.assume @ res2.assume)
             ; vcs       = (mk_or [ res1.drop_cont; mk_and res2.vcs ])
                           :: res1.vcs
             ; drop_cont = mk_or [res1.drop_cont; res2.drop_cont]
             ; mod_addr  = AddrSet.union res1.mod_addr res2.mod_addr
             ; ret_cond  = mk_and [ res1.ret_cond
                                  ; mk_implies (mk_not res1.drop_cont)
                                               res2.ret_cond
                                  ]
             }
  | Esave (_, varlist, e) ->
        let sub_map = List.fold_right (fun (sym, (cbt, pe)) map ->
          Pmap.add sym pe map) varlist (Pmap.empty sym_cmp) in
        let to_check = substitute_expr sub_map e in
        bmc_expr to_check

let initialise_solver (solver: Solver.solver) =
  print_endline "Initialising solver.";
  Solver.add solver ImplFunctions.all_asserts

let bmc_file (file              : unit typed_file)
             (sym_supply        : sym_supply_ty)
             (function_to_check : sym_ty) =
  (* Create an initial model checking state *)
  let initial_state : BmcM.bmc_state =
    BmcM.mk_initial_state file sym_supply in
  initialise_solver g_solver;

  (* TODO: temporarily assume there are no globals *)
  assert (List.length file.globs = 0);

  let to_run =
    match Pmap.lookup function_to_check file.funs with
    | Some (Proc (_, ty, params, e)) ->
        (* TODO: handle args to procedure. May be of pointer type *)
        assert (List.length params = 0);
        let ret_const = mk_fresh_const "ret_main" (cbt_to_z3 ty) in
        BmcM.update_proc_expr e         >>= fun () ->
        BmcM.update_ret_const ret_const >>= fun () ->
        bmc_expr e                      >>= fun ret ->
        let new_ret_cond =
          mk_implies (mk_not ret.drop_cont) (mk_eq ret_const ret.expr) in
        return {ret with ret_cond = mk_and [new_ret_cond; ret.ret_cond]}

    | Some (Fun (ty, params, pe)) ->
        BmcM.mapM_ initialise_param params >>= fun () ->
        bmc_pexpr pe >>= fun pret ->
        return (bmc_pret_to_ret pret)

    | _ -> failwith "Function to check must be a Core Proc or Fun"
  in
  let (result, new_state) = BmcM.run initial_state to_run in

  (*print_endline "==== FINAL BMC_RET";*)
  (*print_string (pp_bmc_ret result);*)

  (* TODO: assert and track based on annotation *)
  (* TODO: multiple expressions or one expression? *)

  print_endline "==== DONE BMC_EXPR ROUTINE ";
  (* Assumptions *)
  Solver.add g_solver (List.map (fun e -> Expr.simplify e None) result.assume);
  (*
  Solver.assert_and_track
    g_solver
    (Expr.simplify (mk_and result.assume) None)
    (Expr.mk_fresh_const g_ctx "assume" (Boolean.mk_sort g_ctx));
    *)
  (* Return conditions *)
  Solver.assert_and_track
    g_solver
    (Expr.simplify result.ret_cond None)
    (Expr.mk_fresh_const g_ctx "ret_cond" (Boolean.mk_sort g_ctx));

  (* Extract return value *)
  (match Solver.check g_solver [] with
  | SATISFIABLE ->
      let final_expr =
        match new_state.ret_const with
        | Some expr -> expr
        | None      -> result.expr in
      let model = Option.get (Solver.get_model g_solver) in
      let return_value = Option.get (Model.eval model final_expr false) in
      printf "==== RETURN VALUE: %s\n" (Expr.to_string return_value)
  | _ -> assert false)
  ;

  (* VCs *)
  Solver.assert_and_track
    g_solver
    (Expr.simplify (mk_not (mk_and result.vcs)) None)
    (Expr.mk_fresh_const g_ctx "negated_vcs" (Boolean.mk_sort g_ctx));

  (*
  print_endline "====FINAL SOLVER";
  print_endline (Solver.to_string g_solver);
  *)

  print_endline "==== CHECKING";
  match Solver.check g_solver [] with
  | UNKNOWN ->
      printf "STATUS: unknown. Reason: %s\n"
             (Solver.get_reason_unknown g_solver)
  | UNSATISFIABLE ->
      print_endline "STATUS: unsatisfiable :)"
  | SATISFIABLE ->
      begin
      print_endline "STATUS: satisfiable";
      let model = Option.get (Solver.get_model g_solver) in
      print_endline (Model.to_string model)
      end

(* Main bmc function: typechecks and sequentialises file.
 e The symbol supply is used to ensure fresh symbols when renaming.
 *)
let bmc (core_file  : unit file)
        (sym_supply : sym_supply_ty) =

  match Core_typing.typecheck_program core_file with
    | Result typed_core ->
        begin
          let core_to_check =
            if g_sequentialise then
              Core_sequentialise.sequentialise_file typed_core
            else
              typed_core in

          pp_file core_to_check;
          bmc_debug_print 1 "START: model checking";
          match core_to_check.main with
          | None ->
              (* Currently only check main function *)
              failwith "ERROR: fail does not have a main"
          | Some main_sym ->
              bmc_file core_to_check sym_supply main_sym
        end
    | Exception msg ->
        printf "Typechecking error: %s\n" (Pp_errors.to_string msg)
