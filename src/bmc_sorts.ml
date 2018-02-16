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
                              [] [] []           
  let loaded_ctor (ctx: context) = 
    Datatype.mk_constructor_s ctx (loaded_name ctx)
                              (mk_sym ctx ("is" ^ (loaded_name ctx)))
                              [mk_sym ctx (oty_name ctx)] [Some (obj_sort ctx)] [0]
                                
  (* ---- end private *)
  let mk_sort (ctx: context) = 
    Datatype.mk_sort_s ctx (sort_name ctx) 
        [unspec_ctor ctx; loaded_ctor ctx]

  let is_loaded (ctx: context) (expr: Expr.expr) =
    let sort = mk_sort ctx in
    let recognizers = Datatype.get_recognizers sort in
    let func_decl = List.nth recognizers 1 in
    Expr.mk_app ctx func_decl [ expr ]

  let get_loaded_value (ctx: context) (expr: Expr.expr) =
    let sort = mk_sort ctx in
    let accessors = Datatype.get_accessors sort in
    let func_decl = List.hd (List.nth accessors 1) in
    Expr.mk_app ctx func_decl [ expr ]
  
  let mk_unspec (ctx: context) : Expr.expr =
    let sort = mk_sort ctx in
    let constructors = Datatype.get_constructors sort in
    let func_decl = List.nth constructors 0 in
    Expr.mk_app ctx func_decl [ ]

  let mk_loaded (ctx: context) (expr: Expr.expr) =
    let sort = mk_sort ctx in
    let constructors = Datatype.get_constructors sort in
    let func_decl = List.nth constructors 1 in
    Expr.mk_app ctx func_decl [ expr ]


end

(* TODO: Functorize *)
module LoadedInteger = LoadedSort (struct let cot = OTy_integer end)

module LoadedPointer = LoadedSort (struct let cot = OTy_pointer end)
