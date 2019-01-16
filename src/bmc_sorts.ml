open Bmc_globals
open Bmc_utils
open Z3
open Z3.Arithmetic


type addr_ty = int * int
type ctype = Core_ctype.ctype0

(* =========== CUSTOM SORTS =========== *)
let mk_ctor str =
  Datatype.mk_constructor_s g_ctx str (mk_sym ("is_" ^ str)) [] [] []

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
    ; mk_constructor_s g_ctx "signed_ity" (mk_sym "is_signed_ity")
        [mk_sym "_signed_ity"] [Some IntegerBaseTypeSort.mk_sort] [0]
    ; mk_constructor_s g_ctx "unsigned_ity" (mk_sym "is_unsigned_ity")
        [mk_sym "_unsigned_ity"] [Some IntegerBaseTypeSort.mk_sort] [0]
    ; mk_ctor "size_t_ity"
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
    | Size_t ->
        Expr.mk_app g_ctx (List.nth fdecls 4) []
    | _ -> assert false
end

module BasicTypeSort = struct
  open Z3.Datatype
  let mk_sort = mk_sort_s g_ctx "BasicType"
      [ mk_constructor_s g_ctx "integer_bty" (mk_sym "is_integer_bty")
        [mk_sym "_integer_bty"] [Some IntegerTypeSort.mk_sort] [0]
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
    ; mk_constructor_s g_ctx "basic_ty" (mk_sym "is_basic_ty")
        [mk_sym "_basic_ty"] [Some BasicTypeSort.mk_sort] [0]
    ; mk_constructor_s g_ctx "ptr_ty" (mk_sym "is_ptr_ty")
        [] [] []
        (* TODO: recursive data types can not be nested in other types
         * such as tuple  *)
        (*[mk_sym g_ctx "_ptr_ty"] [None] [0] *)
    ]

  let rec mk_expr (ctype: ctype) : Expr.expr =
    let fdecls = get_constructors mk_sort in
    match ctype with
    | Void0  ->
        Expr.mk_app g_ctx (List.nth fdecls 0) []
    | Basic0 bty ->
        Expr.mk_app g_ctx (List.nth fdecls 1) [BasicTypeSort.mk_expr bty]
    | Pointer0 (_, ty) ->
        Expr.mk_app g_ctx (List.nth fdecls 2) []
    | _ -> assert false

  let mk_nonatomic_expr (ctype: ctype) : Expr.expr =
    match ctype with
    | Atomic0 ty -> mk_expr ty
    | _ -> mk_expr ctype
end

module AddressSort = struct
  open Z3.Datatype
  open Z3.FuncDecl

  let mk_sort =
    mk_sort_s g_ctx ("Addr")
      [ mk_constructor_s g_ctx "addr"
            (mk_sym ("_addr"))
            [mk_sym ("get_alloc"); mk_sym ("get_index")]
            [Some integer_sort; Some integer_sort] [0; 0]
      ]

  let mk_expr (alloc_id: Expr.expr) (index: Expr.expr) =
    let ctor = List.nth (get_constructors mk_sort) 0 in
    Expr.mk_app g_ctx ctor [alloc_id; index]

  let mk_from_addr ((alloc_id, index) : int * int) : Expr.expr =
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

  (* ====== Atomic ====== *)
  let is_atomic_decl =
    mk_fresh_func_decl g_ctx "is_atomic" [mk_sort] boolean_sort

  let mk_is_atomic (addr: Expr.expr) =
    Expr.mk_app g_ctx is_atomic_decl [addr]

  let assert_is_atomic (addr: Expr.expr) (is_atomic: Expr.expr) =
    mk_eq (mk_is_atomic addr) is_atomic
end

module PointerSort = struct
  open Z3.Datatype
  open Z3.FuncDecl

  let mk_sort =
    mk_sort_s g_ctx ("Ptr")
      [ mk_constructor_s g_ctx "ptr"
            (mk_sym "_ptr")
            [mk_sym ("get_addr")]
            [Some AddressSort.mk_sort] [0]
      ; mk_constructor_s g_ctx "null"
            (mk_sym "is_null")
            [] [] []
      ]

  let mk_ptr (addr: Expr.expr) =
    let ctor = List.nth (get_constructors mk_sort) 0 in
    Expr.mk_app g_ctx ctor [addr]

  let mk_null =
    let ctor = List.nth (get_constructors mk_sort) 1 in
    Expr.mk_app g_ctx ctor []

  let is_null (expr: Expr.expr) =
    let recognizer = List.nth (get_recognizers mk_sort) 1 in
    Expr.mk_app g_ctx recognizer [expr]

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
                                (mk_sym ("is_specified_" ^ obj_name))
                                [mk_sym ("get_" ^ obj_name)]
                                [Some M.obj_sort] [0]
             ;  mk_constructor_s g_ctx
                                ("unspecified_" ^ obj_name)
                                (mk_sym ("is_unspecified_" ^ obj_name))
                                [mk_sym ("get_" ^ obj_name)]
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

module Loaded = struct
  open Z3.Datatype

  let mk_sort  =
    mk_sort_s g_ctx "Loaded_ty"
      [ mk_constructor_s g_ctx "loaded_int" (mk_sym "is_loaded_int")
                         [mk_sym "_loaded_int"]
                         [Some LoadedInteger.mk_sort] [0]
      ; mk_constructor_s g_ctx "loaded_ptr" (mk_sym "is_loaded_ptr")
                         [mk_sym "_loaded_ptr"]
                         [Some LoadedPointer.mk_sort] [0]
      ]

  let mk_expr (expr: Expr.expr) =
    let ctors = get_constructors mk_sort in
    if (Sort.equal LoadedInteger.mk_sort (Expr.get_sort expr)) then
      Expr.mk_app g_ctx (List.nth ctors 0) [expr]
    else if (Sort.equal LoadedPointer.mk_sort (Expr.get_sort expr)) then
      Expr.mk_app g_ctx (List.nth ctors 1) [expr]
    else
      assert false
end

(* TODO: CFunctions are currently just identifiers *)
module CFunctionSort = struct
  open Z3.Datatype
  let mk_sort =
    mk_sort_s g_ctx "CFunction"
    [ mk_constructor_s g_ctx "cfun" (mk_sym "isCfun")
        [mk_sym "getId"] [Some integer_sort] [0]
    ]

  let mk_cfun (id: Expr.expr) =
    let sort = mk_sort in
    let constructors = get_constructors sort in
    let func_decl = List.nth constructors 0 in
    Expr.mk_app g_ctx func_decl [ id ]
end
