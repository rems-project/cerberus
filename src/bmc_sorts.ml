open Bmc_globals
open Bmc_utils
open Core
open Printf
open Util
open Z3
open Z3.Arithmetic

type addr_ty = int * int
type ctype = Core_ctype.ctype0

type permission_flag =
  | ReadWrite
  | ReadOnly


type alloc = int
  (* We assume for now we always know the ctype of what we're allocating *)
type allocation_metadata =
    (* size *) int * ctype option * (* alignment *) int * (* base address *) Expr.expr * permission_flag *
    (* C prefix *) Sym.prefix

let get_metadata_size (sz,_,_,_,_,_) : int = sz
let get_metadata_base (_,_,_,base,_,_) : Expr.expr = base
let get_metadata_ctype (_,ctype,_,_,_,_) : ctype option = ctype
let get_metadata_align (_,_,align,_,_,_) : int = align
let get_metadata_permission (_,_,_,_,perm,_) : permission_flag = perm
let get_metadata_prefix (_,_,_,_,_,pref) : Sym.prefix = pref



let print_metadata (size, cty, align, expr, _, pref) =
  sprintf "Size: %d, Base: %s, Align %d, prefix: %s"
              size (Expr.to_string expr) align
              (prefix_to_string pref)




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
    ; mk_ctor "intptr_t_ibty"
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
    | Intptr_t ->
        Expr.mk_app g_ctx (List.nth fdecls 5) []
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
    ; mk_ctor "ptrdiff_t_ity"
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
    | Ptrdiff_t ->
        Expr.mk_app g_ctx (List.nth fdecls 5) []
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
    | Floating _ ->
        failwith "Floats are not supported."
end

(* The Z3 tuple doesn't cooperate well with recursive datatypes for some reason.
 * It throws a Z3Error("Invalid argument") when calling, e.g., Tuple.get_mk_decl
 * sort, where sort is created from Tuple.mk_sort *)
module CustomTuple = struct
  open Z3.Datatype

  let mk_sort (tuple_name: string)
              (arg_names: Symbol.symbol list)
              (sorts: Sort.sort list) : Sort.sort =
    mk_sort_s g_ctx tuple_name
    [mk_constructor_s g_ctx
      (sprintf "tuple_%s" tuple_name)
      (mk_sym (sprintf "is_%s" tuple_name))
      arg_names
      (List.map (fun sort -> Some sort) sorts)
      (List.map (fun _ -> 0) arg_names)
    ]

  let mk_tuple (sort: Sort.sort) (exprs: Expr.expr list) : Expr.expr =
    let constructors = get_constructors sort in
    Expr.mk_app g_ctx (List.hd constructors) exprs

end

module CtypeSort = struct
  open Z3.Datatype
  let mk_sort_helper : Sort.sort list = mk_sorts_s g_ctx
    [ "Ctype" ]
    [[ mk_ctor "void_ty"
     ; mk_constructor_s g_ctx "basic_ty" (mk_sym "is_basic_ty")
         [mk_sym "_basic_ty"] [Some BasicTypeSort.mk_sort] [0]
     ; mk_constructor_s g_ctx "ptr_ty" (mk_sym "is_ptr_ty")
         [mk_sym "_ptr_ty"] [None] [0]
     ; mk_constructor_s g_ctx "array_ty" (mk_sym "is_array_ty")
         [mk_sym "_array_ty_n"]
         [Some integer_sort] [0]
     ; mk_constructor_s g_ctx "struct_ty" (mk_sym "is_struct_ty")
         [mk_sym "_struct_ty"]
         [Some integer_sort] [0]
     ; mk_constructor_s g_ctx "atomic_ty" (mk_sym "is_atomic_ty")
         [mk_sym "_atomic_ty"]
         [None] [0]
     ]
    ]

  let mk_sort = List.nth mk_sort_helper 0

  let rec mk_expr (ctype: ctype) : Expr.expr =
    let fdecls = get_constructors mk_sort in
    match ctype with
    | Void0  ->
        Expr.mk_app g_ctx (List.nth fdecls 0) []
    | Basic0 bty ->
        Expr.mk_app g_ctx (List.nth fdecls 1) [BasicTypeSort.mk_expr bty]
    | Pointer0 (_, ty) ->
        Expr.mk_app g_ctx (List.nth fdecls 2) [mk_expr ty]
    | Array0(cty, Some n) ->
        (* TODO: cty ignored b/c recursive types and tuples *)
        (* Sort of assumed it's always integer for now... *)
        Expr.mk_app g_ctx (List.nth fdecls 3) [big_num_to_z3 n]
    | Struct0 (Symbol (_, n, _))->
        Expr.mk_app g_ctx (List.nth fdecls 4) [int_to_z3 n]
    | Atomic0 ty ->
        Expr.mk_app g_ctx (List.nth fdecls 5) [mk_expr ty]
    | Union0 _ -> failwith "TODO: unions"
    | _ -> assert false

  let mk_nonatomic_expr (ctype: ctype) : Expr.expr =
    match ctype with
    | Atomic0 ty -> mk_expr ty
    | _ -> mk_expr ctype
end

let rec alignof_type (ctype: ctype) (file: unit typed_file) : int =
  match ctype with
  | Void0 -> assert false
  | Basic0 (Integer ity) ->
      Option.get (Ocaml_implementation.Impl.alignof_ity ity)
  | Array0(ty, _) -> alignof_type ty file
  | Function0 _ -> assert false
  | Pointer0 _ ->
      Option.get (Ocaml_implementation.Impl.sizeof_pointer)
  | Atomic0 (Basic0 _ as _ty) ->
      alignof_type _ty file
  | Atomic0 (Pointer0 _ as _ty) ->
      Option.get (Ocaml_implementation.Impl.alignof_pointer)
  | Struct0 sym ->
      begin match Pmap.lookup sym file.tagDefs with
      | Some (StructDef members) ->
          (* Let alignment be max alignment of a member? *)
          let alignments =
            List.map (fun (_, mem_ctype) -> alignof_type mem_ctype file)
                     members in
          assert (List.length alignments > 0);
          List.fold_left max (List.hd alignments) (List.tl alignments)
      | _ -> assert false
      end
  | Union0 _ -> failwith "TODO: unions"
  | _ -> assert false



module AddressSortPNVI = struct
  open Z3.Datatype
  open Z3.FuncDecl
  type base_ty = Expr.expr

  let mk_sort =
    mk_sort_s g_ctx ("Addr_PNVI")
      [ mk_constructor_s g_ctx "addr_pnvi"
            (mk_sym ("_addr_pnvi"))
            [mk_sym ("get_index_pnvi")]
            [Some integer_sort] [0]
      ]

  let mk_nd_addr (alloc: int) : Expr.expr =
    mk_fresh_const (sprintf "base_addr_%d" alloc) mk_sort

  let mk_expr (index: Expr.expr) =
    let ctor = List.nth (get_constructors mk_sort) 0 in
    Expr.mk_app g_ctx ctor [index]

  let mk_from_addr ((alloc_id, index) : int * int) : Expr.expr =
    mk_expr (int_to_z3 index)

  let get_index (expr: Expr.expr) : Expr.expr =
    assert (Sort.equal (Expr.get_sort expr) mk_sort);
    let accessors = get_accessors mk_sort in
    let get_value = List.hd (List.nth accessors 0) in
    Expr.mk_app g_ctx get_value [ expr ]

  (* ======== *)
  (* Map from address to provenance *)
  let alloc_min_decl =
    mk_fresh_func_decl g_ctx "__alloc_min" [integer_sort] integer_sort

  let alloc_max_decl =
    mk_fresh_func_decl g_ctx "__alloc_max" [integer_sort] integer_sort

  let valid_index_range (alloc: Expr.expr) (addr: Expr.expr) : Expr.expr =
    let index = get_index addr in
    let alloc_min = Expr.mk_app g_ctx alloc_min_decl [alloc] in
    let alloc_max = Expr.mk_app g_ctx alloc_max_decl [alloc] in
    mk_and [ binop_to_z3 OpGe index alloc_min
           ; binop_to_z3 OpLt index alloc_max
           ]

  let valid_index_range_plus_one (alloc: Expr.expr) (addr: Expr.expr) : Expr.expr =
    let index = get_index addr in
    let alloc_min = Expr.mk_app g_ctx alloc_min_decl [alloc] in
    let alloc_max = Expr.mk_app g_ctx alloc_max_decl [alloc] in
    mk_and [ binop_to_z3 OpGe index alloc_min
           ; binop_to_z3 OpLe index alloc_max
           ]


  let shift_index_by_n (addr: Expr.expr) (n: Expr.expr) : Expr.expr =
    let index = get_index addr in
    mk_expr (binop_to_z3 OpAdd index n)

  (* TODO: extend this so x is a range of addresses *)
  let addr_subset (x: Expr.expr) (min_addr: Expr.expr) (max_addr: Expr.expr)
                  : Expr.expr =
    mk_and [binop_to_z3 OpLe (get_index min_addr) (get_index x)
           ;binop_to_z3 OpLe (get_index x) (get_index max_addr)
           ]

  (* ====== Atomic ====== *)
  let is_atomic_decl =
    mk_fresh_func_decl g_ctx "is_atomic" [mk_sort] boolean_sort

  let mk_is_atomic (addr: Expr.expr) =
    Expr.mk_app g_ctx is_atomic_decl [addr]

  let assert_is_atomic (addr: Expr.expr) (is_atomic: Expr.expr) =
    mk_eq (mk_is_atomic addr) is_atomic

  (* TODO: This really uses bmc_common; need to toggle based on global conf *)
  let sizeof_ity ity = Option.get (Ocaml_implementation.Impl.sizeof_ity ity)

  (* TODO: Move this elsewhere *)
  let rec type_size (ctype: ctype) (file: unit typed_file): int =
    match ctype with
    | Void0 -> assert false
    | Basic0 (Integer ity) ->
        sizeof_ity ity
    | Array0(ty, Some n) -> (Nat_big_num.to_int n) * (type_size ty file)
    | Array0 _ -> assert false
    | Function0 _ -> assert false
    | Pointer0 _ -> Option.get (Ocaml_implementation.Impl.sizeof_pointer)
    | Atomic0 (Basic0 _ as _ty) (* fall through *)
    | Atomic0 (Pointer0 _ as _ty) ->
        type_size _ty file
    | Struct0 tag ->
        fst (struct_member_index_list tag file)
    | _ -> assert false
  and struct_member_index_list tag (file: unit typed_file) =
    (* Compute offset of member from base addr *)
    begin match Pmap.lookup tag file.tagDefs with
    | Some (StructDef members) ->
        let rec helper rest total_size acc : int * ((int list) * int list) =
          begin match rest with
          | [] -> (total_size, acc)
          | (_, ty) :: tl ->
            let (ty_size, flat_indices) =
              match ty with
              | Core_ctype.Struct0 tag_inner ->
                let (ty_size, (_, flat_indices)) =
                  struct_member_index_list tag_inner file in
                (ty_size, flat_indices)
              | _ ->
                let ty_size = type_size ty file in
                (ty_size, [0])
              in
            let align = alignof_type ty file in
            (* Add padding to total size *)
            let padding = (align - (total_size mod align)) mod align in
            let start_index = total_size + padding in

            (* Coarse: just gives start index *)
            (* Fine: includes start index of subobjects *)
            let (coarse,fine) = acc in
            let adjusted = List.map (fun i -> i + start_index) flat_indices in
            helper tl (start_index + ty_size)
                      (start_index::coarse,
                       (List.rev adjusted) @ fine
                      )
            (*((total_size+padding)::acc)*)
          end
        in
        let (total_size, (rev_indices, rev_flat_indices)) =
          helper members 0 ([],[]) in
        (* TODO: Padding at the end to the largest member (alignment?) *)
        let largest_align = List.fold_left (fun acc (_, ty) ->
          max acc (alignof_type ty file)
        ) 0 members in
        let last_padding =
          (largest_align - (total_size mod largest_align)) mod largest_align in
        (total_size + last_padding, (List.rev rev_indices, List.rev rev_flat_indices))
    | _ -> assert false
    end

  let get_provenance (ival_min: Expr.expr)
                     (ival_max: Expr.expr)
                     (data: (int,allocation_metadata) Pmap.map)
                     : Expr.expr option =
      Some (Pmap.fold (fun alloc_id metadata base ->
        let addr_size : int = get_metadata_size metadata in
        let addr_base : Expr.expr = get_metadata_base metadata in
        let addr_min = get_index addr_base in
        let addr_max = binop_to_z3 OpAdd addr_min (int_to_z3 (addr_size - 1)) in
        let ival_in_range =
          mk_and [binop_to_z3 OpGe ival_min addr_min
                 ;binop_to_z3 OpLe ival_max addr_max] in
        mk_ite ival_in_range
               (int_to_z3 alloc_id)
               base
      ) data (int_to_z3 0))

  let pp (expr: Expr.expr) : string =
    assert (Sort.equal (Expr.get_sort expr) mk_sort);
    match Expr.get_args expr with
    | [a] ->
        if Arithmetic.is_int a then
          sprintf "0x%x" (Big_int.int_of_big_int (Integer.get_big_int a))
        else Expr.to_string expr
    | _ -> Expr.to_string expr

end

(*
module AddressSortConcrete = struct
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

  let mk_nd_addr (alloc: int) =
    mk_from_addr (alloc, 0)

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
  let alloc_min_decl =
    mk_fresh_func_decl g_ctx "alloc_min" [integer_sort] integer_sort

  let alloc_max_decl =
    mk_fresh_func_decl g_ctx "alloc_max" [integer_sort] integer_sort

  let valid_index_range (addr: Expr.expr) : Expr.expr =
    let alloc = get_alloc addr in
    let index = get_index addr in
    let alloc_min = Expr.mk_app g_ctx alloc_min_decl [alloc] in
    let alloc_max = Expr.mk_app g_ctx alloc_max_decl [alloc] in
    (*
    let alloc_size = Expr.mk_app g_ctx alloc_size_decl [alloc] in
    *)
    mk_and [ binop_to_z3 OpGe index alloc_min (* should be 0 *)
           ; binop_to_z3 OpLt index alloc_max
           ]

  let shift_index_by_n (addr: Expr.expr) (n: Expr.expr) : Expr.expr =
    let alloc = get_alloc addr in
    let index = get_index addr in
    mk_expr alloc (binop_to_z3 OpAdd index n)

  (* TODO: extend this so x is a range of addresses *)
  let addr_subset (x: Expr.expr) (min_addr: Expr.expr) (max_addr: Expr.expr)
                  : Expr.expr =
    (* assume: max_addr >= min_addr *)
    (* Checks alloc are equal and index(min) <= index(x) <= index(max) *)
    mk_and [mk_eq (get_alloc x) (get_alloc min_addr)
           ;mk_eq (get_alloc x) (get_alloc max_addr)
           ;binop_to_z3 OpLe (get_index min_addr) (get_index x)
           ;binop_to_z3 OpLe (get_index x) (get_index max_addr)
           ]

  (* ====== Atomic ====== *)
  let is_atomic_decl =
    mk_fresh_func_decl g_ctx "is_atomic" [mk_sort] boolean_sort

  let mk_is_atomic (addr: Expr.expr) =
    Expr.mk_app g_ctx is_atomic_decl [addr]

  let assert_is_atomic (addr: Expr.expr) (is_atomic: Expr.expr) =
    mk_eq (mk_is_atomic addr) is_atomic

  (* TODO *)
  let rec type_size (ctype: ctype) (file: unit typed_file) : int =
    match ctype with
    | Void0 -> assert false
    | Basic0 _ -> 1
    | Array0(ty, Some n) -> (Nat_big_num.to_int n) * (type_size ty file)
    | Array0 _ -> assert false
    | Function0 _ -> assert false
    | Pointer0 _ -> 1
    | Atomic0 (Basic0 _ as _ty) (* fall through *)
    | Atomic0 (Pointer0 _ as _ty) ->
        type_size _ty file
    | Struct0 _ ->
        assert false
    | _ -> assert false

  let get_provenance _ _ _ = None
end
*)
(* PNVI ptr:
   | Null
   | Ptr of provenance * addr

  Provenance:
   | Empty
   | Prov of int

  Let's just define 0 = empty provenance
*)

module type PointerSortAPI = sig
  val mk_sort : Sort.sort

  val mk_ptr : Expr.expr -> Expr.expr -> Expr.expr
  val mk_ptr_from_int_addr : Expr.expr -> Expr.expr -> Expr.expr

  val mk_null : Expr.expr
  val mk_fn_ptr : Expr.expr

  val is_null : Expr.expr -> Expr.expr
  val get_addr : Expr.expr -> Expr.expr
  val get_prov : Expr.expr -> Expr.expr (* TODO: only for PNVI *)

  val shift_by_n : Expr.expr -> Expr.expr -> Expr.expr
  val provenance_of_decl : FuncDecl.func_decl
  val is_dynamic_alloc_decl : FuncDecl.func_decl

  val valid_ptr : Expr.expr -> Expr.expr

  val ptr_comparable : Expr.expr -> Expr.expr -> Expr.expr
  val ptr_in_range : Expr.expr -> Expr.expr
  val ptr_in_range_plus_one : Expr.expr -> Expr.expr

  val ptr_eq : Expr.expr -> Expr.expr -> Expr.expr
  val ptr_diff_raw : Expr.expr -> Expr.expr -> Expr.expr

  val type_size : ctype -> unit typed_file -> int
  val struct_member_index_list : sym_ty -> unit typed_file ->
    int * (int list * int list)

  val mk_nd_addr : int -> Expr.expr
  val get_index_from_addr : Expr.expr -> Expr.expr
  val get_addr_index : Expr.expr -> Expr.expr
  val alloc_min_decl : FuncDecl.func_decl
  val alloc_max_decl : FuncDecl.func_decl

  val get_provenance : Expr.expr -> Expr.expr ->
                      (int, allocation_metadata) Pmap.map -> Expr.expr option
  val shift_index_by_n : Expr.expr -> Expr.expr -> Expr.expr

  val mk_addr_sort : Sort.sort
  val addr_subset : Expr.expr -> Expr.expr -> Expr.expr -> Expr.expr
  val mk_from_alloc_index  : (int * int) -> Expr.expr
  val mk_is_atomic : Expr.expr -> Expr.expr
  val assert_is_atomic : Expr.expr -> Expr.expr -> Expr.expr

  val pp : Expr.expr -> string
end

module PointerSortPNVI : PointerSortAPI = struct
  open Z3.Datatype
  open Z3.FuncDecl

  module AddrModule = AddressSortPNVI

  let mk_sort =
    mk_sort_s g_ctx ("Ptr_PNVI")
      [ mk_constructor_s g_ctx "ptr_pnvi"
            (mk_sym "_ptr")
            [mk_sym "get_prov"; mk_sym ("get_addr")]
            [Some integer_sort; Some AddressSortPNVI.mk_sort] [0; 0]
      ; mk_constructor_s g_ctx "null_pnvi"
            (mk_sym "is_null")
            [] [] []
      (* TODO: Just a placeholder *)
      ; mk_constructor_s g_ctx "fn_pnvi"
            (mk_sym "is_fn")
            [] [] []
      ]

  let mk_ptr (prov: Expr.expr) (addr: Expr.expr) =
    let ctor = List.nth (get_constructors mk_sort) 0 in
    Expr.mk_app g_ctx ctor [prov;addr]

  let mk_ptr_from_int_addr (prov: Expr.expr) (int_addr: Expr.expr) =
      mk_ptr prov (AddressSortPNVI.mk_expr int_addr)

  let mk_null =
    let ctor = List.nth (get_constructors mk_sort) 1 in
    Expr.mk_app g_ctx ctor []

  let mk_fn_ptr =
    let ctor = List.nth (get_constructors mk_sort) 2 in
    Expr.mk_app g_ctx ctor []

  let is_null (expr: Expr.expr) =
    let recognizer = List.nth (get_recognizers mk_sort) 1 in
    Expr.mk_app g_ctx recognizer [expr]

  let get_prov (expr: Expr.expr) =
    assert (Sort.equal (Expr.get_sort expr) mk_sort);
    let accessors = get_accessors mk_sort in
    let get_value = List.nth (List.nth accessors 0) 0 in
    Expr.mk_app g_ctx get_value [ expr ]

  let get_addr (expr: Expr.expr) =
    assert (Sort.equal (Expr.get_sort expr) mk_sort);
    let accessors = get_accessors mk_sort in
    let get_value = List.nth (List.nth accessors 0) 1 in
    Expr.mk_app g_ctx get_value [ expr ]

  let shift_by_n (ptr: Expr.expr) (n: Expr.expr) =
    mk_ptr (get_prov ptr)
           (AddressSortPNVI.shift_index_by_n (get_addr ptr) n)

  (* TODO: domain should really be address *)
  let provenance_of_decl =
    mk_fresh_func_decl g_ctx "prov_of" [integer_sort] integer_sort

  let has_provenance (ptr: Expr.expr) : Expr.expr =
    binop_to_z3 OpGt (get_prov ptr) (int_to_z3 0)

  let is_dynamic_alloc_decl =
    mk_fresh_func_decl g_ctx "is_dynamic_alloc" [integer_sort] boolean_sort

  (* Not null
   * Provenance of ptr is > 0
   * Not out of bounds
   * >>>Need to check alignment? No type-casting yet
   * TODO: would be nice to check lifetime here using some interface function
   * to concurrency model
   *)
  let valid_ptr (ptr: Expr.expr) =
    mk_and [mk_not (is_null ptr)
           ;has_provenance ptr
           ]

  let ptr_comparable (p1: Expr.expr) (p2: Expr.expr) =
    mk_eq (get_prov p1) (get_prov p2)

  let ptr_in_range (ptr: Expr.expr) =
    AddressSortPNVI.valid_index_range (get_prov ptr) (get_addr ptr)

  let ptr_in_range_plus_one (ptr: Expr.expr) =
    AddressSortPNVI.valid_index_range_plus_one (get_prov ptr) (get_addr ptr)



  (* PNVI semantics:
   * - if p1 = p2, true
   * - if different provenance, {a=a', false}
   * - else false *)
  let ptr_eq (p1: Expr.expr) (p2: Expr.expr) =
    mk_ite (mk_eq p1 p2) mk_true
           (mk_ite (mk_and[mk_not (is_null p1); mk_not (is_null p2)
                          ;mk_not (mk_eq (get_prov p1) (get_prov p2))
                          ;mk_eq (get_addr p1) (get_addr p2)
                          ])
                   (mk_fresh_const (sprintf "ptr_eq(%s,%s)"
                                            (Expr.to_string p1)
                                            (Expr.to_string p2)) boolean_sort)
                   mk_false)

  let ptr_diff_raw (p1: Expr.expr) (p2: Expr.expr) =
    binop_to_z3 OpSub (AddressSortPNVI.get_index (get_addr p1))
                      (AddressSortPNVI.get_index (get_addr p2))

  let pp (expr: Expr.expr) =
    assert (Sort.equal (Expr.get_sort expr) mk_sort);
    match Expr.get_args expr with
    | [prov;addr] ->
        let pp_prov =
          if Arithmetic.is_int prov
          then (Big_int.string_of_big_int (Integer.get_big_int prov))
          else Expr.to_string prov in
        let pp_addr = AddressSortPNVI.pp addr in
        sprintf (*"ptr(@%s, %s)"*) "(@%s, %s)" pp_prov pp_addr
    | _ -> Expr.to_string expr

  (* TODO: Do this properly with signatures *)
  let type_size = AddrModule.type_size
  let struct_member_index_list = AddrModule.struct_member_index_list
  let mk_nd_addr = AddrModule.mk_nd_addr
  let get_index_from_addr addr =
    AddrModule.get_index addr
  let get_addr_index ptr =
    get_index_from_addr (get_addr ptr)
  let alloc_min_decl = AddrModule.alloc_min_decl
  let alloc_max_decl = AddrModule.alloc_max_decl
  let get_provenance = AddrModule.get_provenance
  let shift_index_by_n = AddrModule.shift_index_by_n

  let mk_addr_sort = AddrModule.mk_sort
  let addr_subset = AddrModule.addr_subset
  let mk_from_alloc_index = AddrModule.mk_from_addr
  let mk_is_atomic = AddrModule.mk_is_atomic
  let assert_is_atomic = AddrModule.assert_is_atomic
end

(*
module PointerSortConcrete : PointerSortAPI = struct
  open Z3.Datatype
  open Z3.FuncDecl

  module AddrModule = AddressSortConcrete

  let mk_sort =
    mk_sort_s g_ctx ("Ptr_concrete")
      [ mk_constructor_s g_ctx "ptr_concrete"
            (mk_sym "_ptr")
            [mk_sym ("get_addr")]
            [Some AddressSortConcrete.mk_sort] [0]
      ; mk_constructor_s g_ctx "null_concrete"
            (mk_sym "is_null")
            [] [] []
      (* TODO: Just a placeholder *)
      ; mk_constructor_s g_ctx "fn_concrete"
            (mk_sym "is_fn")
            [] [] []
      ]

  (* TODO: Ignore provenance *)
  let mk_ptr (_: Expr.expr) (addr: Expr.expr) =
    let ctor = List.nth (get_constructors mk_sort) 0 in
    Expr.mk_app g_ctx ctor [addr]

  let mk_ptr_from_int_addr (prov: Expr.expr) (int_addr: Expr.expr) =
      mk_ptr prov (AddressSortConcrete.mk_expr prov int_addr)

  let mk_null =
    let ctor = List.nth (get_constructors mk_sort) 1 in
    Expr.mk_app g_ctx ctor []

  let mk_fn_ptr =
    let ctor = List.nth (get_constructors mk_sort) 2 in
    Expr.mk_app g_ctx ctor []

  let is_null (expr: Expr.expr) =
    let recognizer = List.nth (get_recognizers mk_sort) 1 in
    Expr.mk_app g_ctx recognizer [expr]

  let get_addr (expr: Expr.expr) =
    assert (Sort.equal (Expr.get_sort expr) mk_sort);
    let accessors = get_accessors mk_sort in
    let get_value = List.hd (List.nth accessors 0) in
    Expr.mk_app g_ctx get_value [ expr ]

  let get_prov (expr: Expr.expr) : Expr.expr =
    AddressSortConcrete.get_alloc (get_addr expr)

  let shift_by_n (ptr: Expr.expr) (n: Expr.expr) =
    let addr = get_addr ptr in
    mk_ptr (AddressSortConcrete.get_alloc addr)
          (AddressSortConcrete.shift_index_by_n addr n)

  let valid_ptr (ptr: Expr.expr) =
    mk_and [mk_not (is_null ptr)]

  let ptr_in_range (ptr: Expr.expr) =
    AddressSortConcrete.valid_index_range (get_addr ptr)

  let ptr_comparable (p1: Expr.expr) (p2: Expr.expr) =
    mk_true

  let ptr_eq (p1: Expr.expr) (p2: Expr.expr) =
    mk_eq p1 p2

  let ptr_diff_raw (p1: Expr.expr) (p2: Expr.expr) =
    assert false

  (* TODO: should not exist *)
  let provenance_of_decl =
    mk_fresh_func_decl g_ctx "prov_of" [integer_sort] integer_sort

  let is_dynamic_alloc_decl =
    mk_fresh_func_decl g_ctx "is_dynamic_alloc" [integer_sort] boolean_sort

  let pp expr = Expr.to_string expr

  (* TODO: Do this properly with signatures *)
  let type_size = AddrModule.type_size
  let struct_member_index_list tag file = assert false(* easy TODO *)
  let mk_nd_addr = AddrModule.mk_nd_addr
  let get_index_from_addr addr =
    AddrModule.get_index addr
  let get_addr_index ptr =
    get_index_from_addr (get_addr ptr)
  let alloc_min_decl = AddrModule.alloc_min_decl
  let alloc_max_decl = AddrModule.alloc_max_decl
  let get_provenance = AddrModule.get_provenance
  let shift_index_by_n = AddrModule.shift_index_by_n
  let mk_addr_sort = AddrModule.mk_sort
  let addr_subset = AddrModule.addr_subset
  let mk_from_alloc_index = AddrModule.mk_from_addr
  let mk_is_atomic = AddrModule.mk_is_atomic
  let assert_is_atomic = AddrModule.assert_is_atomic
end
*)

let pointer_sort =
  if g_pnvi then
    (module PointerSortPNVI : PointerSortAPI)
  else
    failwith "TODO: Only PNVI mode supported"
    (*(module PointerSortConcrete : PointerSortAPI)*)


module PointerSort = (val pointer_sort : PointerSortAPI)
(*module AddressSort = PointerSort.AddrModule*)


module type LoadedSortTy = sig
  val mk_sort : Sort.sort
  val mk_specified : Expr.expr -> Expr.expr
  val mk_unspecified: Expr.expr -> Expr.expr
  val is_specified : Expr.expr -> Expr.expr
  val is_unspecified : Expr.expr -> Expr.expr
  val get_specified_value : Expr.expr -> Expr.expr
  val get_unspecified_value : Expr.expr -> Expr.expr
end

(* NOTE: not a functor anymore because I don't want to deal with module
 * packing and unpacking everywhere
 *)
module TODO_LoadedSort = struct
  open Z3.Datatype
  let mk_sort (obj_sort: Sort.sort) =
    let obj_name = Sort.to_string obj_sort in
    mk_sort_s g_ctx ("Loaded_" ^ obj_name)
             [ mk_constructor_s g_ctx
                                ("specified_" ^ obj_name)
                                (mk_sym ("is_specified_" ^ obj_name))
                                [mk_sym ("get_" ^ obj_name)]
                                [Some obj_sort] [0]
             ; mk_constructor_s g_ctx
                                ("unspecified_" ^ obj_name)
                                (mk_sym ("is_unspecified_" ^ obj_name))
                                [mk_sym ("get_" ^ obj_name)]
                                [Some CtypeSort.mk_sort] [0]
             ]

  let mk_specified (expr: Expr.expr) =
    let ctors = get_constructors (mk_sort (Expr.get_sort expr)) in
    assert (List.length ctors = 2);
    let loaded_ctor = List.nth ctors 0 in
    Expr.mk_app g_ctx loaded_ctor [expr]

  let mk_unspecified (obj_sort: Sort.sort) (expr: Expr.expr) =
    assert (Sort.equal (Expr.get_sort expr) CtypeSort.mk_sort);
    let ctors = get_constructors (mk_sort obj_sort) in
    assert (List.length ctors = 2);
    let unspec_ctor = List.nth ctors 1 in
    Expr.mk_app g_ctx unspec_ctor [expr]

  let is_specified (expr: Expr.expr) =
    let recognizers = get_recognizers (Expr.get_sort expr) in
    assert (List.length recognizers = 2);
    let is_spec = List.nth recognizers 0 in
    Expr.mk_app g_ctx is_spec [ expr ]

  let is_unspecified (obj_sort: Sort.sort) (expr: Expr.expr) =
    let recognizers = get_recognizers (Expr.get_sort expr) in
    assert (List.length recognizers = 2);
    let is_unspec = List.nth recognizers 1 in
    Expr.mk_app g_ctx is_unspec [ expr ]

  let get_specified_value (expr: Expr.expr) =
    let accessors = get_accessors (Expr.get_sort expr) in
    assert (List.length accessors = 2);
    let get_value = List.hd (List.nth accessors 0) in
    Expr.mk_app g_ctx get_value [ expr ]

  let get_unspecified_value (expr: Expr.expr) =
    let accessors = get_accessors (Expr.get_sort expr) in
    assert (List.length accessors = 2);
    let get_value = List.hd (List.nth accessors 1) in
    Expr.mk_app g_ctx get_value [ expr ]

  let extract_obj_sort (sort: Sort.sort) : Sort.sort =
    let ctors = get_constructors sort in
    let domain = FuncDecl.get_domain (List.hd ctors) in
    assert (List.length domain = 1);
    List.hd domain
end

(* Hack for now to access the value associated with the first constructor *)
(* TODO: should create once using fresh names and reuse.
 * Current scheme may be susceptible to name reuse => bugs. *)
module LoadedSort (M : sig val obj_sort : Sort.sort end) : LoadedSortTy = struct
  open Z3.Datatype

  let mk_sort = TODO_LoadedSort.mk_sort M.obj_sort

  let mk_specified (expr: Expr.expr) =
    assert (Sort.equal (Expr.get_sort expr) M.obj_sort);
    TODO_LoadedSort.mk_specified expr

  let mk_unspecified (expr: Expr.expr) =
    assert (Sort.equal (Expr.get_sort expr) CtypeSort.mk_sort);
    TODO_LoadedSort.mk_unspecified M.obj_sort expr

  let is_specified (expr: Expr.expr) =
    assert (Sort.equal (Expr.get_sort expr) mk_sort);
    TODO_LoadedSort.is_specified expr

  let is_unspecified (expr: Expr.expr) =
    assert (Sort.equal (Expr.get_sort expr) mk_sort);
    TODO_LoadedSort.is_unspecified M.obj_sort expr

  let get_specified_value (expr: Expr.expr) =
    assert (Sort.equal (Expr.get_sort expr) mk_sort);
    TODO_LoadedSort.get_specified_value expr

  let get_unspecified_value (expr: Expr.expr) =
    assert (Sort.equal (Expr.get_sort expr) mk_sort);
    TODO_LoadedSort.get_unspecified_value expr

  (*
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
  *)
end


module LoadedInteger =
  LoadedSort (struct let obj_sort = integer_sort end)

module LoadedPointer =
  LoadedSort (struct let obj_sort = PointerSort.mk_sort end)

module LoadedByte = LoadedInteger

module OptionSort (M : sig val obj_sort : Sort.sort end) = struct
  open Z3.Datatype
  let mk_sort =
    let obj_name = Sort.to_string M.obj_sort in
    mk_sort_s g_ctx ("Option_" ^ obj_name)
              [ mk_constructor_s g_ctx
                                 ("some_" ^ obj_name)
                                 (mk_sym ("is_specified_" ^ obj_name))
                                 [mk_sym ("get_" ^ obj_name)]
                                 [Some M.obj_sort] [0]
              ; mk_ctor ("none_" ^ obj_name)
              ]

  let mk_some (expr: Expr.expr) =
    let ctors = get_constructors mk_sort in
    let some_ctor = List.nth ctors 0 in
    Expr.mk_app g_ctx some_ctor [expr]

  let mk_none =
    let ctors = get_constructors mk_sort in
    let none_ctor = List.nth ctors 1 in
    Expr.mk_app g_ctx none_ctor []
end

module IntOption = OptionSort (struct let obj_sort = integer_sort end)

module PNVIByte = struct
  (* Triples of (provenance, value, byte index *)
  open Z3.Datatype
  let mk_sort =
    mk_sort_s g_ctx ("Byte")
      [mk_constructor_s g_ctx "byte"
        (mk_sym "_byte")
        [mk_sym "_prov"; mk_sym "_val"; mk_sym "_index"]
        [Some integer_sort; Some LoadedByte.mk_sort; Some IntOption.mk_sort]
        [0;0;0]
      ]

  let mk_byte (prov: Expr.expr) (value: Expr.expr) (index_opt: Expr.expr) =
    let ctor = List.hd (get_constructors mk_sort) in
    Expr.mk_app g_ctx ctor [prov;value;index_opt]

  let get_provenance (expr: Expr.expr) =
    let accessors = get_accessors mk_sort in
    let get_value = List.nth (List.hd accessors) 0 in
    Expr.mk_app g_ctx get_value [ expr ]

  let get_value (expr: Expr.expr) =
    let accessors = get_accessors mk_sort in
    let get_value = List.nth (List.hd accessors) 1 in
    Expr.mk_app g_ctx get_value [ expr ]

  let get_index(expr: Expr.expr) =
    let accessors = get_accessors mk_sort in
    let get_value = List.nth (List.hd accessors) 2 in
    Expr.mk_app g_ctx get_value [ expr ]

  let is_unspec (expr: Expr.expr) =
    LoadedByte.is_unspecified (get_value expr)

  let get_spec_value (expr: Expr.expr) =
    LoadedByte.get_specified_value (get_value expr)

  let unspec_byte : Expr.expr =
    let byte_ctype = CtypeSort.mk_expr (Basic0 (Integer Char)) in
    mk_byte (int_to_z3 0)
            (LoadedByte.mk_unspecified byte_ctype)
            (IntOption.mk_none)
end

(* TODO: duplicate with IntArray *)
module PNVIByteArray = struct
  let mk_sort = Z3Array.mk_sort g_ctx integer_sort PNVIByte.mk_sort

  let mk_const_s (sym: string) =
    Z3Array.mk_const_s g_ctx sym integer_sort PNVIByte.mk_sort

  let mk_select (array: Expr.expr) (index: Expr.expr) =
    Z3Array.mk_select g_ctx array index

  let mk_store (array: Expr.expr) (index: Expr.expr) (value: Expr.expr) : Expr.expr =
    Z3Array.mk_store g_ctx array index value
end

module IntArray = struct
  let default_value = LoadedInteger.mk_specified (int_to_z3 0)

  let mk_sort = Z3Array.mk_sort g_ctx integer_sort (LoadedInteger.mk_sort)

  let mk_const_s (sym: string) =
    Z3Array.mk_const_s g_ctx sym integer_sort (LoadedInteger.mk_sort)

  (*let mk_const_array =
    Z3Array.mk_const_array g_ctx mk_sort default_value *)

  (* TODO: deprecate this *)
  let mk_select (array: Expr.expr) (index: Expr.expr) =
    Z3Array.mk_select g_ctx array index

  let mk_store (array: Expr.expr) (index: Expr.expr) (value: Expr.expr) : Expr.expr =
    Z3Array.mk_store g_ctx array index value

  (*let mk_array_from_exprs (values: Expr.expr list) : Expr.expr =
    let indexed_values = List.mapi (fun i value -> (i,value)) values in
    List.fold_left (fun array (i,value) -> mk_store array (int_to_z3 i) value)
                   mk_const_array indexed_values *)
end

(* TODO: switch this to use GenericArrays *)
module LoadedIntArray = struct
  include LoadedSort (struct let obj_sort = IntArray.mk_sort end)
end

module LoadedPointerArray = struct
  include LoadedSort (struct
    let obj_sort = Z3Array.mk_sort g_ctx integer_sort LoadedPointer.mk_sort end)
end

(*
(* TODO: special case for now *)
module LoadedIntArrayArray = struct
  include LoadedSort (
    struct
      let obj_sort = Z3Array.mk_sort g_ctx integer_sort (LoadedIntArray.mk_sort)
    end)
end
*)
let sorts_to_tuple (sorts: Sort.sort list) : Sort.sort =
  let tuple_name =
    "(" ^ (String.concat "," (List.map Sort.to_string sorts)) ^ ")" in
  let arg_list = List.mapi
    (fun i _ -> mk_sym ("#" ^ (string_of_int i))) sorts in
  CustomTuple.mk_sort tuple_name arg_list sorts
  (*Tuple.mk_sort g_ctx (mk_sym tuple_name) arg_list sorts*)

(* NOTE: we actually kind of have two functions from ctype -> z3 sort that
 * differ for multi-dimensional arrays currently. The first, below, gives the
 * Z3 Sort through recursing through the array subtypes and is used in the
 * intermediate representation. E.g. int[][] maps to LoadedIntArrayArray
 *
 * The second just treats multi-dimensional arrays as a flat array and is
 * currently used for the memory model representation for simplicity. E.g.
 * int[][] maps to LoadedIntArray
 *)
module CtypeToZ3 = struct
  let rec ctype_to_z3_sort (ty: Core_ctype.ctype0)
                           (file: unit typed_file)
                           : Sort.sort =
     match ty with
    | Void0     -> assert false
    | Basic0(Integer i) -> LoadedInteger.mk_sort
    | Basic0 _ -> assert false
    | Array0(ty', _) ->
        mk_array_sort_from_ctype ty' file
    | Function0 _ -> assert false
    | Pointer0 _ -> LoadedPointer.mk_sort
    | Atomic0 (Basic0 _ as _ty) (* fall through *)
    | Atomic0 (Pointer0 _ as _ty) ->
        ctype_to_z3_sort _ty file
    | Atomic0 _ ->
        assert false
    | Struct0 tagdef ->
        struct_sym_to_z3_sort tagdef file
        (*
        begin match Pmap.lookup tagdef file.tagDefs with
        | Some (StructDef memlist) ->
            let tuple_sort = (struct_to_sort (tagdef, Tags.StructDef memlist) file) in
            let module Loaded_tuple_sort = (val tuple_sort : LoadedSortTy) in
            Loaded_tuple_sort.mk_sort
            (*
            let sortlist =
              List.map (fun (_, mem_ty) -> ctype_to_z3_sort mem_ty file) memlist in
            (* TODO: Does Z3 allow tuples to contain tuples? *)
            let tuple_sort = sorts_to_tuple sortlist in
            let module Loaded_tuple_sort =
              LoadedSort(struct let obj_sort = tuple_sort end) in
            Loaded_tuple_sort.mk_sort
            *)
        | _ -> assert false
        end
        *)
    | Union0 _ ->
      failwith "Error: unions are not supported."
    | Builtin0 _ -> assert false
  and struct_sym_to_z3_sort (struct_sym: sym_ty)
                            (file: unit typed_file)
                            : Sort.sort =
    match Pmap.lookup struct_sym file.tagDefs with
    | Some (StructDef memlist) ->
        let sortlist =
            List.map (fun (_,ctype) -> ctype_to_z3_sort ctype file)
                     memlist in
        sorts_to_tuple sortlist
    | _ ->
      failwith (sprintf "Struct %s not found" (symbol_to_string struct_sym))
  and mk_array_sort (cot: core_object_type)
                    (file: unit typed_file): Sort.sort =
      match cot with
      | OTy_integer -> (* Loaded Integer *)
          let sort = Z3Array.mk_sort g_ctx integer_sort (LoadedInteger.mk_sort) in
          TODO_LoadedSort.mk_sort sort
      | OTy_pointer ->
          let sort = Z3Array.mk_sort g_ctx integer_sort (LoadedPointer.mk_sort) in
          TODO_LoadedSort.mk_sort sort
      | OTy_floating ->
          failwith "Error: floats are not supported."
      | OTy_array cot' ->
          let inner_sort = mk_array_sort cot' file in
          let sort = Z3Array.mk_sort g_ctx integer_sort inner_sort in
          TODO_LoadedSort.mk_sort sort
      | OTy_struct sym ->
          let inner_sort = TODO_LoadedSort.mk_sort (struct_sym_to_z3_sort sym file) in
          let sort = Z3Array.mk_sort g_ctx integer_sort inner_sort in
          TODO_LoadedSort.mk_sort sort
      | OTy_union _ ->
          failwith "Error: unions are not supported."
  and mk_array_sort_from_ctype (ty: Core_ctype.ctype0)
                               (file: unit typed_file): Sort.sort =
      match ty with
      | Void0 -> failwith "TODO: void arrays"
      | Basic0 (Integer i) ->
          let sort = Z3Array.mk_sort g_ctx integer_sort (LoadedInteger.mk_sort) in
          TODO_LoadedSort.mk_sort sort
      | Pointer0 _ ->
          let sort = Z3Array.mk_sort g_ctx integer_sort (LoadedPointer.mk_sort) in
          TODO_LoadedSort.mk_sort sort
      | Array0(ty', _) ->
          let inner_sort = mk_array_sort_from_ctype ty' file in
          let sort = Z3Array.mk_sort g_ctx integer_sort inner_sort in
          TODO_LoadedSort.mk_sort sort
      | Struct0 tag ->
          let inner_sort = TODO_LoadedSort.mk_sort (struct_sym_to_z3_sort tag file) in
          let sort = Z3Array.mk_sort g_ctx integer_sort inner_sort in
          TODO_LoadedSort.mk_sort sort
      | _ ->
          failwith "TODO: generic arrays"
end


module type LoadedSig = sig
  val mk_sort : Sort.sort
  val mk_expr : Expr.expr -> Expr.expr

  val get_loaded_int : Expr.expr -> Expr.expr

  val is_specified   : Expr.expr -> Expr.expr
  val is_unspecified : Expr.expr -> Expr.expr
  val get_ith_in_loaded_2  : Expr.expr -> Expr.expr -> Expr.expr
end

(*module Loaded (M: sig val user_defd_sorts : (module LoadedSortTy) list end)*)
module Loaded : LoadedSig = struct
  open Z3.Datatype

  let mk_sort  =
    mk_sort_s g_ctx "Loaded_ty"
      [ mk_constructor_s g_ctx "loaded_int" (mk_sym "is_loaded_int")
                         [mk_sym "_loaded_int"]
                         [Some LoadedInteger.mk_sort] [0]
      ; mk_constructor_s g_ctx "loaded_ptr" (mk_sym "is_loaded_ptr")
                         [mk_sym "_loaded_ptr"]
                         [Some LoadedPointer.mk_sort] [0]
      ; mk_constructor_s g_ctx "loaded_int[]" (mk_sym "is_loaded_int[]")
                         [mk_sym "_loaded_int[]"]
                         [Some LoadedIntArray.mk_sort] [0]
      ; mk_constructor_s g_ctx "loaded_ptr[]" (mk_sym "is_loaded_ptr[]")
                         [mk_sym "_loaded_ptr[]"]
                         [Some LoadedPointerArray.mk_sort] [0]

      ]

  let mk_expr (expr: Expr.expr) =
    let ctors = get_constructors mk_sort in
    if (Sort.equal LoadedInteger.mk_sort (Expr.get_sort expr)) then
      Expr.mk_app g_ctx (List.nth ctors 0) [expr]
    else if (Sort.equal LoadedPointer.mk_sort (Expr.get_sort expr)) then
      Expr.mk_app g_ctx (List.nth ctors 1) [expr]
    else if (Sort.equal LoadedIntArray.mk_sort (Expr.get_sort expr)) then
      Expr.mk_app g_ctx (List.nth ctors 2) [expr]
    else if (Sort.equal LoadedPointerArray.mk_sort (Expr.get_sort expr)) then
      Expr.mk_app g_ctx (List.nth ctors 3) [expr]
    else
      assert false

  let is_loaded_int (expr: Expr.expr) =
    let recognizer = List.nth (get_recognizers mk_sort) 0 in
    Expr.mk_app g_ctx recognizer [expr]

  let get_loaded_int (expr: Expr.expr) =
    let accessors = get_accessors mk_sort in
    let get_value = List.hd (List.nth accessors 0) in
    Expr.mk_app g_ctx get_value [ expr ]

  let is_loaded_ptr (expr: Expr.expr) =
    let recognizer = List.nth (get_recognizers mk_sort) 1 in
    Expr.mk_app g_ctx recognizer [expr]

  let get_loaded_ptr (expr: Expr.expr) =
    let accessors = get_accessors mk_sort in
    let get_value = List.hd (List.nth accessors 1) in
    Expr.mk_app g_ctx get_value [ expr ]

  let is_loaded_int_array (expr: Expr.expr) =
    let recognizer = List.nth (get_recognizers mk_sort) 2 in
    Expr.mk_app g_ctx recognizer [expr]

  let get_loaded_intarray (expr: Expr.expr) =
    let accessors = get_accessors mk_sort in
    let get_value = List.hd (List.nth accessors 2) in
    Expr.mk_app g_ctx get_value [ expr ]

  let is_loaded_ptr_array (expr: Expr.expr) =
    let recognizer = List.nth (get_recognizers mk_sort) 3 in
    Expr.mk_app g_ctx recognizer [expr]

  let get_loaded_ptrarray (expr: Expr.expr) =
    let accessors = get_accessors mk_sort in
    let get_value = List.hd (List.nth accessors 3) in
    Expr.mk_app g_ctx get_value [ expr ]


  (* TODO: do this not as a big ite *)
  let is_specified (expr: Expr.expr) =
     mk_ite (is_loaded_int expr) (LoadedInteger.is_specified (get_loaded_int expr))
    (mk_ite (is_loaded_ptr expr) (LoadedPointer.is_specified (get_loaded_ptr expr))
    (mk_ite (is_loaded_int_array expr) (LoadedIntArray.is_specified (get_loaded_intarray expr))
    (* else *) (LoadedPointerArray.is_specified (get_loaded_ptrarray expr))))

  let is_unspecified (expr: Expr.expr) =
     mk_ite (is_loaded_int expr) (LoadedInteger.is_unspecified (get_loaded_int expr))
    (mk_ite (is_loaded_ptr expr) (LoadedPointer.is_unspecified (get_loaded_ptr expr))
    (mk_ite (is_loaded_int_array expr) (LoadedIntArray.is_specified (get_loaded_intarray expr))
    (* else *) (LoadedPointerArray.is_specified (get_loaded_ptrarray expr))))

  (* TODO: pretty bad code *)
  let get_ith_in_loaded_2 (i: Expr.expr) (loaded: Expr.expr) : Expr.expr =
    assert (Sort.equal (Expr.get_sort loaded) mk_sort);

    let spec_int_array =
      LoadedIntArray.get_specified_value (get_loaded_intarray loaded) in
    let spec_ptr_array =
      LoadedPointerArray.get_specified_value (get_loaded_ptrarray loaded) in
    mk_ite (mk_or [is_loaded_int loaded; is_loaded_ptr loaded])
           loaded
    (mk_ite (is_loaded_int_array loaded)
            (mk_expr (Z3Array.mk_select g_ctx spec_int_array i))
            (* else pointer array *)
            (mk_expr (Z3Array.mk_select g_ctx spec_ptr_array i)))

end

(* Get ith index in loaded value *)
(* TODO: This will change once we switch to byte representation *)
(* TODO: duplicate from above right now for testing and assertion purposes *)
(*
let get_ith_in_loaded (i: int) (loaded: Expr.expr) : Expr.expr =
  if (Sort.equal (Expr.get_sort loaded) LoadedInteger.mk_sort) then
    (assert (i = 0); loaded)
  else if (Sort.equal (Expr.get_sort loaded) LoadedPointer.mk_sort) then
    (assert (i = 0); loaded)
  else if (Sort.equal (Expr.get_sort loaded) (LoadedIntArray.mk_sort)) then
    (* TODO: What if unspecified? *)
    begin
      let spec_value = LoadedIntArray.get_specified_value loaded in
      Z3Array.mk_select g_ctx spec_value (int_to_z3 i)
    end
  else if (Sort.equal (Expr.get_sort loaded) (LoadedPointerArray.mk_sort)) then
    begin
      let spec_value = LoadedPointerArray.get_specified_value loaded in
      Z3Array.mk_select g_ctx spec_value (int_to_z3 i)
    end
  else
    assert false
*)

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

module CtypeListSort = struct
  let mk_sort =
    Z3List.mk_list_s g_ctx "[ctype]" CtypeSort.mk_sort

  let mk_cons x xs =
    let cons_decl = Z3List.get_cons_decl mk_sort in
    FuncDecl.apply cons_decl [x; xs]

  let mk_nil = Z3List.nil mk_sort

  let is_nil expr =
    let is_nil_decl = Z3List.get_is_nil_decl mk_sort in
    FuncDecl.apply is_nil_decl [expr]

  let is_cons expr =
    let is_cons_decl = Z3List.get_is_cons_decl mk_sort in
    FuncDecl.apply is_cons_decl [expr]

  let get_head expr =
    let get_head_decl = Z3List.get_head_decl mk_sort in
    FuncDecl.apply get_head_decl [expr]

  let get_tail expr =
    let get_tail_decl = Z3List.get_tail_decl mk_sort in
    FuncDecl.apply get_tail_decl [expr]

end
