open Z3
open Z3.Arithmetic

open Bmc_utils
open Bmc_globals
open Core

(*
module type CustomSort =
  sig
    val mk_sort: context -> Sort.sort
  end
*)

(* TODO: make sorts once only and keep in state *)

(* COPIED FROM src/ocaml_defacto.ml *)
let mk_ctor ctx str =
  Datatype.mk_constructor_s ctx str (Symbol.mk_string ctx ("is_" ^ str)) [] [] [] 

let integerBaseTypeSort ctx = Datatype.mk_sort_s ctx "IntegerBaseType"
      [ mk_ctor ctx "ichar_ibty"
      ; mk_ctor ctx "short_ibty"
      ; mk_ctor ctx "int_ibty"
      ; mk_ctor ctx "long_ibty"
      ; mk_ctor ctx "long_long_ibty"
      ; Datatype.mk_constructor_s ctx "intN_t_ibty" (Symbol.mk_string ctx "is_intN_t_ibty")
          [Symbol.mk_string ctx "intN_size"] [Some (Arithmetic.Integer.mk_sort ctx)]
          [0(*TODO: no idea with I'm doing*)]
      ; mk_ctor ctx "intmax_t_ibty"
      ; mk_ctor ctx "intptr_t_ibty" ]

let integerTypeSort ctx =
  Datatype.mk_sort_s ctx "IntegerType"
    [ mk_ctor ctx "char_ity"
    ; mk_ctor ctx "bool_ity"
    ; Datatype.mk_constructor_s ctx "Signed_ity" (Symbol.mk_string ctx "is_Signed_ity")
        [Symbol.mk_string ctx "_Signed_ity"] [Some (integerBaseTypeSort ctx)]
        [0(*TODO: no idea with I'm doing*)]
    ; Datatype.mk_constructor_s ctx "Unsigned_ity" (Symbol.mk_string ctx "is_Unsigned_ity")
        [Symbol.mk_string ctx "_Unsigned_ity"] [Some (integerBaseTypeSort ctx)]
        [0(*TODO: no idea with I'm doing*)]
    ; mk_ctor ctx "size_t_ity"
    ; mk_ctor ctx "ptrdiff_t_ity" ]

let basicTypeSort ctx =
  Datatype.mk_sort_s ctx "BasicType"
    [ Datatype.mk_constructor_s ctx "Integer_bty" (Symbol.mk_string ctx "is_Integer_bty")
        [Symbol.mk_string ctx "_Integer_bty"] [Some (integerTypeSort ctx)]
        [0(*TODO: no idea with I'm doing*)]
    ; Datatype.mk_constructor_s ctx "Floating"
        (Symbol.mk_string ctx "is_Floating") [] [] []
    ] 
(*
let ctype_is_signed ctx expr =
  let ctype_sort = ctypeSort ctx in
  let integertype_sort = integerTypeSort ctx in

  let isBasicTy_rec = List.nth (Datatype.get_recognizers ctype_sort) 0 in
  let isBasicTy = Expr.mk_app ctx isBasicTy_rec [expr] in

  let basicTy_fd = Expr.mk_app ctx (Datatype.get_accessors ctype_sort) 0 in
  let basicTy = Expr.mk_app ctx basicTy_fd [expr] in

  let isSigned_rec = List.nth (Datatype.get_constructors integertype_sort) 2 in
*)


let ctypeSort ctx = 
  Datatype.mk_sort_s ctx "Ctype"
    [ mk_ctor ctx "void_ty"
    ; Datatype.mk_constructor_s ctx "Basic_ty" (Symbol.mk_string ctx "is_Basic_ty")
        [Symbol.mk_string ctx "_Basic_ty"] [Some (basicTypeSort ctx)]
        [0(*TODO: no idea with I'm doing*)]
    (* TODO: This doesn't work when making tuple. Probably b/c of None *)
        (*
    ; Datatype.mk_constructor_s ctx "Array_ty" (Symbol.mk_string ctx "is_Array_ty")
        [Symbol.mk_string ctx "elem_Array_ty"; Symbol.mk_string ctx "size_Array_ty"]
        [None; Some (Arithmetic.Integer.mk_sort ctx)]
        [0; 0(*TODO: no idea with I'm doing*)]
    *)
    ; Datatype.mk_constructor_s ctx "Pointer_ty" (Symbol.mk_string ctx "is_Pointer_ty")
        [] [] []
        (*
        [Symbol.mk_string ctx "_Pointer_ty"] [None]
        [0(*TODO: no idea with I'm doing*)] 
    *)
    ]

let integerBaseType_to_expr ibty ctx =
  let fdecls = Datatype.get_constructors (integerBaseTypeSort ctx) in
  AilTypes.(match ibty with
    | Ichar ->
        Expr.mk_app ctx (List.nth fdecls 0) []
    | Short ->
        Expr.mk_app ctx (List.nth fdecls 1) []
    | Int_ ->
        Expr.mk_app ctx (List.nth fdecls 2) []
    | Long ->
        Expr.mk_app ctx (List.nth fdecls 3) []
    | LongLong ->
        Expr.mk_app ctx (List.nth fdecls 4) []
    | IntN_t n ->
        Expr.mk_app ctx (List.nth fdecls 5) [Arithmetic.Integer.mk_numeral_i ctx n]
    | Int_leastN_t _ ->
        assert false
    | Int_fastN_t _ ->
        assert false
    | Intmax_t ->
        Expr.mk_app ctx (List.nth fdecls 6) []
    | Intptr_t ->
        Expr.mk_app ctx (List.nth fdecls 7) []
  )

let integerType_to_expr (ity: AilTypes.integerType) ctx =
  let fdecls = Datatype.get_constructors (integerTypeSort ctx) in
  AilTypes.(match ity with
    | Char ->
        Expr.mk_app ctx (List.nth fdecls 0) []
    | Bool ->
        Expr.mk_app ctx (List.nth fdecls 1) []
    | Signed ibty ->
        Expr.mk_app ctx (List.nth fdecls 2) [integerBaseType_to_expr ibty ctx]
    | Unsigned ibty ->
        Expr.mk_app ctx (List.nth fdecls 3) [integerBaseType_to_expr ibty ctx]
    | IBuiltin str ->
        assert false
    | Enum _ ->
        assert false
    | Size_t ->
        Expr.mk_app ctx (List.nth fdecls 4) []
    | Ptrdiff_t ->
        Expr.mk_app ctx (List.nth fdecls 5) []
)
let basicType_to_expr (bty: AilTypes.basicType) ctx =
  let fdecls = Datatype.get_constructors (basicTypeSort ctx) in
  AilTypes.(match bty with
    | Integer ity ->
        Expr.mk_app ctx (List.nth fdecls 0) [integerType_to_expr ity ctx]
    | Floating _ ->
        assert false;
      (* TODO: this is probably wrong *)
        Expr.mk_app ctx (List.nth fdecls 1) []
      (*  failwith "Smt.basicType_to_expr, Floating" *)
)

let rec ctype_to_expr ty ctx =
  let fdecls = Datatype.get_constructors (ctypeSort ctx) in
  Core_ctype.(
    match ty with
      | Void0 ->
        Expr.mk_app ctx (List.nth fdecls 0) []
      | Basic0 bty ->
        Expr.mk_app ctx (List.nth fdecls 1) [basicType_to_expr bty ctx]
      | Array0 (_, None) ->
          (* Ail type error *)
          assert false
      | Array0 (elem_ty, Some n) ->
          assert false
          (*
        Expr.mk_app ctx (List.nth fdecls 2)
            [ctype_to_expr elem_ty ctx; Arithmetic.Integer.mk_numeral_i ctx (Nat_big_num.to_int n)]
*)
      | Pointer0 (_, ref_ty) ->
        Expr.mk_app ctx (List.nth fdecls 2) []
            (*[ctype_to_expr ref_ty ctx] *)

      | Function0 _ ->
          assert false
      | Atomic0 _ ->
          assert false
      | Struct0 tag_sym ->
          assert false
      | Union0 _ ->
          assert false
      | Builtin0 _ ->
          assert false
  )


(* TODO: rename to "alloc id" or something more correct *)
(* Also abstraction is unnecessary and not maintained throughout code *)
module type AddressType =
  sig
    type addr
    val is_eq: addr -> addr -> bool

    (* Given previous addr, make a new one *)
    val mk_fresh: addr ref -> addr
    val mk_n : addr ref -> int -> addr list

    val mk_sort: context -> Sort.sort
    val mk_initial: addr
    val to_string: addr -> string
    val mk_expr: context -> addr -> Expr.expr
    val is_atomic : context -> Expr.expr -> Expr.expr

    val get_alloc_id : addr -> int

    val is_raw_addr : Expr.expr -> bool
    val to_addr : Expr.expr -> addr

    val apply_getAllocSize : context -> Expr.expr -> Expr.expr

    val get_alloc : context -> Expr.expr -> Expr.expr
    val get_index : context -> Expr.expr -> Expr.expr

    val shift_n : context -> Expr.expr -> Expr.expr -> Expr.expr
  end

module PairAddress : AddressType = 
  struct
    type addr = int * int (* alloc_id, index *)
    let is_eq = (==)

    let mk_fresh st = 
      let (alloc, _) = !st in
      st := (succ alloc, 0);
      (succ alloc, 0)

    let mk_n st n =
      let (alloc_id, _)= mk_fresh st in 
      let rec aux m =
        match m with
        | 0 -> []
        | k -> (alloc_id, n-k) :: (aux (k-1)) in
      aux n

    let get_alloc_id (aid, _) = aid

    let mk_initial = (0,0)
    let to_string (l1,l2) = Printf.sprintf "(%d,%d)" l1 l2

    let mk_sort (ctx: context) =
      if g_bv then
        Tuple.mk_sort ctx (mk_sym ctx "pair_addr")
        [ mk_sym ctx "alloc"; mk_sym ctx "index"]
        [ Integer.mk_sort ctx; BitVector.mk_sort ctx g_max_precision ]
      else
        Tuple.mk_sort ctx (mk_sym ctx "pair_addr")
        [ mk_sym ctx "alloc"; mk_sym ctx "index"]
        [ Integer.mk_sort ctx; Integer.mk_sort ctx ]

    let mk_expr ctx (alloc,index) =
      let mk_decl = Tuple.get_mk_decl (mk_sort ctx) in
      let index_expr = 
        if g_bv then
          BitVector.mk_numeral ctx (string_of_int index) g_max_precision
        else
          Integer.mk_numeral_i ctx index
      in
      FuncDecl.apply mk_decl 
        [Integer.mk_numeral_i ctx alloc; index_expr]

    let fn_isAtomic ctx = FuncDecl.mk_func_decl_s ctx
                        "isAtomic" [mk_sort ctx] (Boolean.mk_sort ctx) 

    let is_atomic ctx expr = FuncDecl.apply (fn_isAtomic ctx) [expr]

    let is_raw_addr expr = 
      match Expr.get_args expr with
      | [a; b] ->
          Expr.is_numeral a && Expr.is_numeral b
      | _ -> false

    let to_addr expr = 
      match Expr.get_args expr with
      | [a; b] ->
          if g_bv then
            (Integer.get_int a, BitVector.get_int b)
          else
            (Integer.get_int a, Integer.get_int b)
      | _ -> assert false

    let apply_getAllocSize ctx (alloc : Expr.expr) = 
      let ret_sort = if g_bv then BitVector.mk_sort ctx g_max_precision
                             else Integer.mk_sort ctx in
      let fn = FuncDecl.mk_func_decl_s ctx
                  "!_allocSize" [Integer.mk_sort ctx] (ret_sort) in
      FuncDecl.apply fn [ alloc ]

    let get_alloc ctx expr =
      let fields = Tuple.get_field_decls (mk_sort ctx) in
      FuncDecl.apply (List.hd fields) [expr]
   
    let get_index ctx expr =  
      let fields = Tuple.get_field_decls (mk_sort ctx) in
      FuncDecl.apply (List.nth fields 1) [expr]

    let shift_n ctx addr n =
      let mk_decl = Tuple.get_mk_decl (mk_sort ctx) in
      let alloc = get_alloc ctx addr in
      let index = get_index ctx addr in
      if g_bv then
        FuncDecl.apply mk_decl
          [alloc; BitVector.mk_add ctx index n]
      else
      FuncDecl.apply mk_decl
        [alloc; Arithmetic.mk_add ctx [index; n]]

  end

module IntAddress : AddressType = 
  struct
    type addr = int
    let is_eq = (==)
    let mk_fresh st = (let ret = succ !st in (st := ret; ret))
    let mk_sort = Integer.mk_sort
    let mk_initial = 0

    (* what even is tail recursion... *)
    let mk_n st n =
      let rec aux m =
        match n with
        | 0 -> []
        | k -> (mk_fresh st) :: (aux (k-1))
      in
        List.rev (aux n)

    let get_alloc_id addr = addr

    let to_string = string_of_int
    let mk_expr ctx ad = Integer.mk_numeral_i ctx ad

    let fn_isAtomic ctx = FuncDecl.mk_func_decl_s ctx
                        "isAtomic" [mk_sort ctx] (Boolean.mk_sort ctx) 

    let is_atomic ctx expr = FuncDecl.apply (fn_isAtomic ctx) [expr]
    let is_raw_addr expr = Expr.is_numeral expr
    let to_addr expr = Integer.get_int expr
    let apply_getAllocSize ctx (alloc : Expr.expr) = 
      let fn = FuncDecl.mk_func_decl_s ctx
                  "!_getAllocSize" [Integer.mk_sort ctx] (Integer.mk_sort ctx) in
      FuncDecl.apply fn [ alloc ]

    let get_alloc _ expr = expr

    let shift_n _ _ _ = assert false
    let get_index _ _ = assert false
  end

(* module Address = (IntAddress : AddressType)  *)
module Address = (PairAddress : AddressType) 

module PointerSort =
  struct
    let mk_sort (ctx: context) = 
      Datatype.mk_sort_s ctx ("ptr")
      [ Datatype.mk_constructor_s ctx ("addr") (mk_sym ctx "isPointer")
          [ mk_sym ctx "get_addr" ] [ Some (Address.mk_sort ctx)] [0]
      (*
      ; Datatype.mk_constructor_s ctx ("null") (mk_sym ctx "isNull")
          [] [] []
      *)
      ]

    let mk_ptr (ctx: context) (addr: Expr.expr) =
      let sort = mk_sort ctx in
      let constructors = Datatype.get_constructors sort in
      let func_decl = List.nth constructors 0 in
      Expr.mk_app ctx func_decl [ addr ]

    (*
      (* TODO: nonsensical for concurrency model right now *)
    let mk_null ctx =
      let sort = mk_sort ctx in
      let constructors = Datatype.get_constructors sort in
      let func_decl = List.nth constructors 1 in
      Expr.mk_app ctx func_decl []

    let is_null ctx expr =
      let sort = mk_sort ctx in
      let recognizers = Datatype.get_recognizers sort in
      let func_decl = List.nth recognizers 1 in
      Expr.mk_app ctx func_decl [expr]

    *)


    let mk_addr (ctx: context) (n: Address.addr) =
      Address.mk_expr ctx n

    let get_addr (ctx: context) (expr: Expr.expr) =
      let sort = mk_sort ctx in
      let accessors = Datatype.get_accessors sort in
      let func_decl = List.hd (List.nth accessors 0) in
      Expr.mk_app ctx func_decl [ expr ]

  end

module CFunctionSort =
  struct
    (* TODO: a cfunction is just an identifier *)
    let mk_sort (ctx: context) = 
      Datatype.mk_sort_s ctx ("cfunction")
      [ Datatype.mk_constructor_s ctx ("fun") (mk_sym ctx "isFunction")
          [ mk_sym ctx "getId" ] [ Some (Integer.mk_sort ctx)] [0]
      ]

    let mk_cfn (ctx: context) (id: Expr.expr) =
      let sort = mk_sort ctx in
      let constructors = Datatype.get_constructors sort in
      let func_decl = List.nth constructors 0 in
      Expr.mk_app ctx func_decl [ id ]
    (*
    let get_id (ctx: context) (expr: Expr.expr) =
      let sort = mk_sort ctx in
      let accessors = Datatype.get_accessors sort in
      let func_decl = List.hd (List.nth accessors 0) in
      Expr.mk_app ctx func_decl [ expr ]
    *)

  end


let core_object_type_to_z3_sort (ctx: context) 
                                (cot: core_object_type) 
                                : Z3.Sort.sort =
  match cot with
   | OTy_integer ->
       if g_bv then
         BitVector.mk_sort ctx g_max_precision
       else
         Integer.mk_sort ctx
   | OTy_floating  -> assert false
   | OTy_pointer -> 
       PointerSort.mk_sort ctx
   | OTy_cfunction (cot_opt, numArgs, variadic) -> 
       CFunctionSort.mk_sort ctx
   | OTy_array _
   | OTy_struct _
   | OTy_union _ ->
       assert false


module UnitSort = 
  struct
    let mk_sort (ctx: context) =
      Datatype.mk_sort_s ctx ("unit")
        [ Datatype.mk_constructor_s ctx ("unit") 
                                    (mk_sym ctx "isUnit") [] [] []]

    let mk_unit (ctx: context) =
      let sort = mk_sort ctx in
      let constructors = Datatype.get_constructors sort in
      Expr.mk_app ctx (List.hd constructors) []

  end


module LoadedSort (M : sig val cot : core_object_type end) =
struct
  (* ---- should be private *)
  let obj_sort (ctx: context) = core_object_type_to_z3_sort ctx (M.cot)

  let oty_name (ctx: context) = 
    pp_to_string (Pp_core.Basic.pp_core_object_type M.cot)
  let sort_name (ctx: context) = "loaded_" ^ (oty_name ctx)
  
  let unspec_name (ctx: context) = "Loaded_" ^ (oty_name ctx) ^ "_unspec"
  let loaded_name (ctx: context) = "Loaded_" ^ (oty_name ctx) ^ "_spec"

  let unspec_ctor (ctx: context) = 
    Datatype.mk_constructor_s ctx (unspec_name ctx)
                              (mk_sym ctx ("is"^ (unspec_name ctx)))
                              [mk_sym ctx ("getType")] 
                              [Some (ctypeSort ctx)] [0]           
  let loaded_ctor (ctx: context) = 
    Datatype.mk_constructor_s ctx (loaded_name ctx)
                              (mk_sym ctx ("is" ^ (loaded_name ctx)))
                              [mk_sym ctx ("get_" ^ oty_name ctx)] 
                              [Some (obj_sort ctx)] [0]
                                
  (* ---- end private *)
  let mk_sort (ctx: context) = 
    Datatype.mk_sort_s ctx (sort_name ctx) 
        [unspec_ctor ctx; loaded_ctor ctx]

  let is_unspec (ctx: context) (expr: Expr.expr) =
    let sort = mk_sort ctx in
    let recognizers = Datatype.get_recognizers sort in
    let func_decl = List.nth recognizers 0 in
    Expr.mk_app ctx func_decl [ expr ]

  let is_loaded (ctx: context) (expr: Expr.expr) =
    let sort = mk_sort ctx in
    let recognizers = Datatype.get_recognizers sort in
    let func_decl = List.nth recognizers 1 in
    Expr.mk_app ctx func_decl [ expr ]

 let get_unspec_value (ctx: context) (expr: Expr.expr) =
    let sort = mk_sort ctx in
    let accessors = Datatype.get_accessors sort in
    let func_decl = List.hd (List.nth accessors 0) in
    Expr.mk_app ctx func_decl [ expr ]


  let get_loaded_value (ctx: context) (expr: Expr.expr) =
    let sort = mk_sort ctx in
    let accessors = Datatype.get_accessors sort in
    let func_decl = List.hd (List.nth accessors 1) in
    Expr.mk_app ctx func_decl [ expr ]

  
  let mk_unspec (ctx: context) (expr: Expr.expr) : Expr.expr =
    let sort = mk_sort ctx in
    let constructors = Datatype.get_constructors sort in
    let func_decl = List.nth constructors 0 in
    Expr.mk_app ctx func_decl [ expr ]

  let mk_loaded (ctx: context) (expr: Expr.expr) =
    let sort = mk_sort ctx in
    let constructors = Datatype.get_constructors sort in
    let func_decl = List.nth constructors 1 in
    Expr.mk_app ctx func_decl [ expr ]
end

(* TODO: Functorize *)
module LoadedInteger = LoadedSort (struct let cot = OTy_integer end)

module LoadedPointer = LoadedSort (struct let cot = OTy_pointer end)

module Loaded = 
  struct
    let mk_sort (ctx: context) =
      Datatype.mk_sort_s ctx ("loaded_ty")
        [ Datatype.mk_constructor_s ctx 
            ("Loaded_integer") (mk_sym ctx "is_Loaded_integer") 
            [ mk_sym ctx "_Loaded_integer"] [Some (LoadedInteger.mk_sort ctx)] [0]
        ; Datatype.mk_constructor_s ctx 
            ("Loaded_pointer") (mk_sym ctx "is_Loaded_pointer") 
            [ mk_sym ctx "_Loaded_pointer"] [Some (LoadedPointer.mk_sort ctx)] [0]
        ]

    let mk_integer (ctx: context) (expr: Expr.expr) : Expr.expr =
      let sort = mk_sort ctx in
      let constructors = Datatype.get_constructors sort in
      let func_decl = List.nth constructors 0 in
      Expr.mk_app ctx func_decl [ expr ]

    let mk_pointer (ctx: context) (expr: Expr.expr) : Expr.expr =
      let sort = mk_sort ctx in
      let constructors = Datatype.get_constructors sort in
      let func_decl = List.nth constructors 1 in
      Expr.mk_app ctx func_decl [ expr ]

    let mk_loaded (ctx: context) (expr: Expr.expr) =
      if (Sort.equal (Expr.get_sort expr) (LoadedInteger.mk_sort ctx)) then
        mk_integer ctx expr 
      else if (Sort.equal (Expr.get_sort expr) (LoadedPointer.mk_sort ctx)) then
        mk_pointer ctx expr
      else
        assert false

    let is_loaded (ctx: context) (expr: Expr.expr) : bool =
      Sort.equal (mk_sort ctx) (Expr.get_sort expr)

  end


(* ============== Function declarations (and definitions?) *)

(*
let z3_sizeof_ibty ctx =
  FuncDecl.mk_func_decl ctx
  (mk_sym ctx "sizeof_ibty") 
  [ integerBaseTypeSort ctx ] (* Sort list *)
  (Integer.mk_sort ctx) (* Ret sort *)

let sizeof_ibty ibty = 
  match Ocaml_implementation.Impl.sizeof_ity (Signed ibty) with
  | Some x -> x
  | None -> assert false

let ivmin_ocaml ibty = 
  match Ocaml_implementation.Impl.sizeof_ity (Signed ibty) with
  | Some x -> - (1 lsl (x-1))
  | None -> assert false

let ivmax_ocaml ibty = 
  match Ocaml_implementation.Impl.sizeof_ity (Signed ibty) with
  | Some x -> (1 lsl (x-1)) - 1
  | None -> assert false



let sizeof_ibty_goals ctx =
  let sizeof_ibty_decl = z3_sizeof_ibty ctx in
  let ibty_recs = Datatype.get_recognizers (integerBaseTypeSort ctx) in
  let names = [ mk_sym ctx "ty" ] in
  let types = [ integerBaseTypeSort ctx ] in
  let var =  Quantifier.mk_bound ctx 0 (List.nth types 0) in
  let quantifiers = 
  [
    (* Forall ty: ibty, is_Int_ (ty) =>  sizeof_ibty (ty) == ... *)
    Quantifier.mk_forall ctx 
      types  names (* ty: ibty *)
      (Boolean.mk_implies ctx 
          (Expr.mk_app ctx (List.nth ibty_recs 2) [ var ]) 
          (Boolean.mk_eq ctx 
              (Expr.mk_app ctx sizeof_ibty_decl [ var ])
              (Integer.mk_numeral_i ctx (sizeof_ibty (Int_) ))
          )
      ) None [] [] None None 
  ] in
  let stuff = Quantifier.get_bound_variable_names (List.hd quantifiers) in
  Printf.printf "TEST %s\n" (Symbol.to_string (List.hd stuff));

  List.map (fun q -> Quantifier.expr_of_quantifier q) quantifiers

let z3_ivmin ctx =
  FuncDecl.mk_func_decl ctx 
    (mk_sym ctx "Ivmin") 
    [ ctypeSort ctx ] (* Sort list *)
    (Integer.mk_sort ctx) (* Ret sort *)

let z3_ivmax ctx =
  FuncDecl.mk_func_decl ctx 
    (mk_sym ctx "Ivmax") 
    [ ctypeSort ctx ] (* Sort list *)
    (Integer.mk_sort ctx) (* Ret sort *)


let ivmin_goals ctx =
  let ctype_recs = Datatype.get_recognizers (ctypeSort ctx) in
  let ctype_accessors = Datatype.get_accessors (ctypeSort ctx) in
  let basic_recs = Datatype.get_recognizers (basicTypeSort ctx) in
  let basic_accessors = Datatype.get_accessors (basicTypeSort ctx) in
  let integer_recs = Datatype.get_recognizers (integerTypeSort ctx) in
  let integer_accessors = Datatype.get_accessors (integerTypeSort ctx) in

  (* TODO: define isBasic, is etc *)
  let isBasic = List.nth ctype_recs 1 in
  let isInteger = List.nth basic_recs 0 in
  let get_basic = List.hd (List.nth ctype_accessors 1) in
  let isSigned = List.nth integer_recs 2 in
  let getInteger = List.hd(List.nth basic_accessors 0) in
  let getSigned = List.hd (List.nth integer_accessors 2) in
  let isInt_ = List.nth (Datatype.get_recognizers (integerBaseTypeSort
  ctx)) 2 in
  let get_signed x = 
    Expr.mk_app ctx getSigned [Expr.mk_app ctx getInteger 
          [(Expr.mk_app ctx get_basic [x])]] in

  let isSignedIntegerInt x =  
      (Boolean.mk_and ctx 
            [ Expr.mk_app ctx isBasic [ x ];
              Expr.mk_app ctx isInteger  (* is integer *)
                              [Expr.mk_app ctx get_basic [ x ]];
              Expr.mk_app ctx isSigned 
                              [Expr.mk_app ctx getInteger 
                                  [(Expr.mk_app ctx get_basic [ x ])]];
              Expr.mk_app ctx isInt_  [get_signed x]
            ]
      )
  in

  (*
  let get_min sz_expr = 
    mk_unary_minus ctx 
        (mk_power ctx (Integer.mk_numeral_i ctx 2) 
                      (mk_sub ctx [sz_expr; Integer.mk_numeral_i ctx 1]) )
  in
  let get_max sz_expr = 
    mk_sub ctx [
        (mk_power ctx (Integer.mk_numeral_i ctx 2) 
                      (mk_sub ctx [sz_expr; Integer.mk_numeral_i ctx 1])) ;
        Integer.mk_numeral_i ctx 1 ]
  in
  *)

  let ivmin_decl = z3_ivmin ctx in
  let ivmax_decl = z3_ivmax ctx in
  let names = [ mk_sym ctx "ty" ] in
  let types = [ ctypeSort ctx ] in
  let var =  Quantifier.mk_bound ctx 0 (List.nth types 0) in
  let quantifiers = 
  [
    (*isBasic, isInteger, bool => *)

    (*isBasic, isInteger, signed x=> *) 
    (* TODO: HORRIBLE *)
    Quantifier.mk_forall ctx
      types names
      (Boolean.mk_implies ctx
        (isSignedIntegerInt var)
        (Boolean.mk_and ctx 
            [Boolean.mk_eq ctx (Expr.mk_app ctx ivmin_decl [ var ]) 
                                (Integer.mk_numeral_i ctx (ivmin_ocaml Int_));
             Boolean.mk_eq ctx (Expr.mk_app ctx ivmax_decl [ var ]) 
                                (Integer.mk_numeral_i ctx (ivmax_ocaml Int_))
            ]
      
      )) None [] [] None None
  ] in

  List.map (fun q -> Quantifier.expr_of_quantifier q) quantifiers

*)
