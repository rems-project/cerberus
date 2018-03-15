open Z3
open Z3.Arithmetic

open Bmc_utils
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
    ; Datatype.mk_constructor_s ctx "Pointer_ty" (Symbol.mk_string ctx "is_Pointer_ty")
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
          (*)
        Expr.mk_app ctx (List.nth fdecls 2)
            [ctype_to_expr elem_ty ctx; Arithmetic.Integer.mk_numeral_i ctx (Nat_big_num.to_int n)]
*)
      | Pointer0 (_, ref_ty) ->
          assert false
          (*
        Expr.mk_app ctx (List.nth fdecls 3)
            [ctype_to_expr ref_ty ctx]
          *)
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
    val mk_sort: context -> Sort.sort
    val mk_initial: addr
    val to_string: addr -> string
    val mk_expr: context -> addr -> Expr.expr
  end 

module IntAddress : AddressType = 
  struct
    type addr = int
    let is_eq = (==)
    let mk_fresh st = (let ret = succ !st in (st := ret; ret))
    let mk_sort = Integer.mk_sort
    let mk_initial = 0
    let to_string = string_of_int
    let mk_expr ctx ad = Integer.mk_numeral_i ctx ad
  end

module Address = (IntAddress : AddressType)


module PointerSort =
  struct
    let mk_sort (ctx: context) = 
      Datatype.mk_sort_s ctx ("ptr")
      [ Datatype.mk_constructor_s ctx ("addr") (mk_sym ctx "isPointer")
          [ mk_sym ctx "get_addr" ] [ Some (Address.mk_sort ctx)] [0]
      ]

    let mk_ptr (ctx: context) (addr: Expr.expr) =
      let sort = mk_sort ctx in
      let constructors = Datatype.get_constructors sort in
      let func_decl = List.nth constructors 0 in
      Expr.mk_app ctx func_decl [ addr ]

    let mk_addr (ctx: context) (n: Address.addr) =
      Address.mk_expr ctx n

    let get_addr (ctx: context) (expr: Expr.expr) =
      let sort = mk_sort ctx in
      let accessors = Datatype.get_accessors sort in
      let func_decl = List.hd (List.nth accessors 0) in
      Expr.mk_app ctx func_decl [ expr ]

  end

let core_object_type_to_z3_sort (ctx: context) 
                                (cot: core_object_type) 
                                : Z3.Sort.sort =
  match cot with
   | OTy_integer ->
       Integer.mk_sort ctx
   | OTy_floating  -> assert false
   | OTy_pointer -> 
       PointerSort.mk_sort ctx
   | OTy_cfunction _ -> assert false
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
