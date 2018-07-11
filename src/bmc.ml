open Bmc_substitute
open Bmc_utils
open Z3
open Z3.Arithmetic
open Z3.Boolean

open AilTypes
open Core
open Core_aux
open Ocaml_mem
open Printf
open Util

(* TODO:
 *  - Maintain symbol table properly
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
let g_bv = false

let g_max_run_depth = 2

(* =========== TYPES =========== *)
(* Pure return *)

type bmc_ret = {
  expr              : Expr.expr;
  assume            : Expr.expr list;
  vcs               : Expr.expr list;
  drop_cont         : Expr.expr; (* drop continuation; e.g. after Erun *)
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

let bmc_pret_to_ret (pret: bmc_pret) : bmc_ret =
  { expr      = pret.expr
  ; assume    = pret.assume
  ; vcs       = pret.vcs
  ; drop_cont = mk_false g_ctx
  }

(* =========== CUSTOM SORTS =========== *)
let integer_sort = if g_bv then assert false
                   else Integer.mk_sort g_ctx

let mk_ctor str =
  Datatype.mk_constructor_s g_ctx str (mk_sym g_ctx ("is_" ^ str)) [] [] []

module UnitSort = struct
  let mk_sort =
    Datatype.mk_sort_s g_ctx "Unit"
      [ Datatype.mk_constructor_s g_ctx "unit"
                                  (Symbol.mk_string g_ctx "isUnit")
                                  [] [] []
      ]

  let mk_unit =
    let constructors = Datatype.get_constructors mk_sort in
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
    ]

  let mk_expr (ctype: Core_ctype.ctype0) : Expr.expr =
    let fdecls = get_constructors mk_sort in
    match ctype with
    | Void0  ->
        Expr.mk_app g_ctx (List.nth fdecls 0) []
    | Basic0 bty ->
        Expr.mk_app g_ctx (List.nth fdecls 1) [BasicTypeSort.mk_expr bty]
    | _ -> assert false
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

(* =========== Z3 HELPER FUNCTIONS =========== *)
let big_num_to_z3 (i: Nat_big_num.num) : Expr.expr =
  if g_bv then assert false
  else Integer.mk_numeral_s g_ctx (Nat_big_num.to_string i)


(* =========== CUSTOM Z3 FUNCTIONS =========== *)
module ImplFunctions = struct
  open Z3.FuncDecl
  (* ---- Implementation ---- *)
  (* TODO: precision of Bool is currently 8... *)
  let impl : Implementation.implementation = {
    binary_mode = Two'sComplement;
    signed      = (function
                   | Char       -> Ocaml_implementation.Impl.char_is_signed
                   | Bool       -> false
                   | Signed _   -> true
                   | Unsigned _ -> false
                   | _          -> assert false);
    precision   = (fun i -> match Ocaml_implementation.Impl.sizeof_ity i with
                   | Some x -> x * 8
                   | None   -> assert false );
    size_t      = Unsigned Long;
    ptrdiff_t0  = Signed Long
  }

  (* ---- Helper functions ---- *)
  let integer_range (impl: Implementation.implementation)
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

  (* ---- FuncDecls ---- *)
  let ivmin = mk_fresh_func_decl
                  g_ctx "ivmin" [CtypeSort.mk_sort] (integer_sort)

  let ivmax = mk_fresh_func_decl
                  g_ctx "ivmax" [CtypeSort.mk_sort] (integer_sort)

  let is_unsigned = mk_fresh_func_decl
                  g_ctx "is_unsigned"
                  [CtypeSort.mk_sort] (Boolean.mk_sort g_ctx)

  (* ---- Assertions ---- *)
  let ivmin_asserts =
    let ivmin_assert (ctype: Core_ctype.ctype0) : Expr.expr =
      let ctype_expr = CtypeSort.mk_expr ctype in
      match ctype with
      | Basic0 (Integer ity) ->
          let (min, _) = integer_range impl ity in
          mk_eq g_ctx (Expr.mk_app g_ctx ivmin [ctype_expr])
                      (big_num_to_z3 min)
      | _ -> assert false
    in
    List.map (fun ity -> ivmin_assert (ity_to_ctype ity))
             ity_list

  let ivmax_asserts =
    let ivmax_assert (ctype: Core_ctype.ctype0) : Expr.expr =
      let ctype_expr = CtypeSort.mk_expr ctype in
      match ctype with
      | Basic0 (Integer ity) ->
          let (_, max) = integer_range impl ity in
          mk_eq g_ctx (Expr.mk_app g_ctx ivmax [ctype_expr])
                      (big_num_to_z3 max)
      | _ -> assert false
    in
    List.map (fun ity -> ivmax_assert (ity_to_ctype ity))
             ity_list

  (* TODO: char; other types *)
  let is_unsigned_asserts =
    let signed_tys   =
      List.map (fun ty -> CtypeSort.mk_expr (ity_to_ctype ty))
               signed_ibt_list in
    let unsigned_tys =
      List.map (fun ty -> CtypeSort.mk_expr (ity_to_ctype ty))
               unsigned_ibt_list in
    List.map (fun signed_ty ->
                mk_eq g_ctx (Expr.mk_app g_ctx is_unsigned [signed_ty])
                           (mk_false g_ctx)) signed_tys
    @ List.map (fun unsigned_ty ->
                mk_eq g_ctx (Expr.mk_app g_ctx is_unsigned [unsigned_ty])
                            (mk_true g_ctx)
      ) unsigned_tys

  (* ---- All assertions ---- *)
  let all_asserts =   ivmin_asserts
                    @ ivmax_asserts
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

(* =========== CORE TYPES -> Z3 SORTS =========== *)
let cot_to_z3 (cot: core_object_type) : Sort.sort =
  match cot with
  | OTy_integer -> integer_sort
  | OTy_pointer -> assert false
  | OTy_floating
  | OTy_array _
  | OTy_struct _
  | OTy_cfunction _
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
  | BTy_loaded _            -> assert false

let sorts_to_tuple (sorts: Sort.sort list)
                   : Sort.sort =
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
      Expr.mk_app g_ctx ImplFunctions.ivmax exprs
  | Civmin ->
      Expr.mk_app g_ctx ImplFunctions.ivmin exprs
  | Cspecified ->
      assert (List.length exprs = 1);
      if (bTy = BTy_loaded OTy_integer) then
        LoadedInteger.mk_specified (List.hd exprs)
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

let binop_to_z3 (binop: binop) (arg1: Expr.expr) (arg2: Expr.expr)
                : Expr.expr =
  if g_bv then assert false
  else begin
    match binop with
    | OpAdd   -> Arithmetic.mk_add g_ctx [arg1; arg2]
    | OpSub   -> Arithmetic.mk_sub g_ctx [arg1; arg2]
    | OpMul   -> Arithmetic.mk_mul g_ctx [arg1; arg2]
    | OpDiv   -> Arithmetic.mk_div g_ctx arg1 arg2
    | OpRem_t -> assert false
    | OpRem_f -> Integer.mk_mod g_ctx arg1 arg2 (* TODO: Rem_t vs Rem_f? *)
    | OpExp   -> assert false
    | OpEq    -> mk_eq g_ctx arg1 arg2
    | OpLt    -> Arithmetic.mk_lt g_ctx arg1 arg2
    | OpLe    -> Arithmetic.mk_le g_ctx arg1 arg2
    | OpGt    -> Arithmetic.mk_gt g_ctx arg1 arg2
    | OpGe    -> Arithmetic.mk_ge g_ctx arg1 arg2
    | OpAnd   -> mk_and g_ctx [arg1; arg2]
    | OpOr    -> mk_or  g_ctx [arg1; arg2]
  end

let integer_value_to_z3 (ival: Ocaml_mem.integer_value) : Expr.expr =
  (* TODO: check which is the correct ival->big num function *)
  match eval_integer_value ival with
  | None -> assert false
  | Some i -> big_num_to_z3 i


let object_value_to_z3 (oval: object_value) : Expr.expr =
  match oval with
  | OVinteger ival -> integer_value_to_z3 ival
  | OVfloating _
  | OVpointer _
  | OVcfunction _
  | OVarray _
  | OVstruct _
  | OVunion _
  | OVcomposite _ ->
      assert false

let value_to_z3 (value: value)
                : Expr.expr =
  match value with
  | Vunit        -> UnitSort.mk_unit
  | Vtrue        -> mk_true g_ctx
  | Vfalse       -> mk_false g_ctx
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

(* =========== SOME MONAD FUN =========== *)

module BmcM = struct
  type sym_table_ty = (sym_ty, Expr.expr) Pmap.map
  type run_depth_table_ty = (sym_ty, int) Pmap.map
  type func_decl_table_ty = (sym_ty generic_name, FuncDecl.func_decl) Pmap.map

  type bmc_state = {
    file            : unit typed_file;
    proc_expr       : (unit typed_expr) option;

    sym_supply      : sym_supply_ty;
    sym_table       : sym_table_ty;

    (* Map from Erun symbol to number of times Erun encountered.
     * Used to control depth of Erun *)
    run_depth_table : (sym_ty, int) Pmap.map;

    (* Map from Core function/impl constant name to Z3 FuncDecl *)
    func_decl_table : func_decl_table_ty;
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
  (* proc expr *)
  let get_proc_expr : (unit typed_expr) eff =
    get >>= fun st ->
    return (Option.get st.proc_expr)

  let update_proc_expr (proc_expr: unit typed_expr) : unit eff =
    get >>= fun st ->
    put {st with proc_expr = Some proc_expr}

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

  let update_run_depth_table (new_table: run_depth_table_ty)
                             : unit eff =
    get >>= fun st ->
    put {st with run_depth_table = new_table}

  (* func_decl_table *)
  let get_func_decl_table : func_decl_table_ty eff =
    get >>= fun st ->
    return st.func_decl_table

  let update_func_decl_table (new_table: func_decl_table_ty) :  unit eff =
    get >>= fun st ->
    put {st with func_decl_table = new_table}

  let get_or_make_func_decl (name         : sym_ty generic_name)
                            (arg_ty_list  : Sort.sort list)
                            (ret_ty       : Sort.sort)
                            : FuncDecl.func_decl eff =
    get_func_decl_table >>= fun func_table ->
    match Pmap.lookup name func_table with
    | Some func -> return func
    | None ->
        let decl = FuncDecl.mk_fresh_func_decl g_ctx
                    (name_to_string name)
                    (arg_ty_list)
                    (ret_ty) in
        let new_table = Pmap.add name decl func_table in
        update_func_decl_table new_table >>= fun () ->
        return decl

  (* =========== STATE INIT =========== *)
  let mk_initial_state (file       : unit typed_file)
                       (sym_supply : sym_supply_ty)
                       : bmc_state =
    { file            = file
    ; proc_expr       = None

    ; sym_supply      = sym_supply
    ; sym_table       = Pmap.empty sym_cmp

    ; run_depth_table = Pmap.empty sym_cmp
    ; func_decl_table = Pmap.empty name_cmp
    }

  (* =========== Pprinters =========== *)
  let pp_sym_table (table: sym_table_ty) =
  Pmap.fold (fun sym expr acc ->
    sprintf "%s\n%s->%s" acc (symbol_to_string sym) (Expr.to_string expr))
    table ""
end

let (>>=) = BmcM.bind

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
      BmcM.return () (* Do nothing; wildcard => no symbol *)
  | CaseBase(Some sym, ty) ->
      add_sym_to_sym_table sym ty
  | CaseCtor (ctor, patlist) ->
      BmcM.mapM_ add_pattern_to_sym_table patlist

(* =========== Z3 LET BINDINGS =========== *)
let mk_let_binding (maybe_sym: sym_ty option)
                   (expr: Expr.expr)
                   : Expr.expr BmcM.eff =
  match maybe_sym with
  | None -> BmcM.return (mk_true g_ctx)
  | Some sym ->
      BmcM.lookup_sym sym >>= fun sym_expr ->
      BmcM.return (mk_eq g_ctx sym_expr expr)

let rec mk_let_bindings (pat: typed_pattern) (expr: Expr.expr)
                        : Expr.expr BmcM.eff =
  match pat with
  | CaseBase(maybe_sym, _) ->
      mk_let_binding maybe_sym expr
  | CaseCtor(Ctuple, patlist) ->
      assert (Expr.get_num_args expr = List.length patlist);
      BmcM.mapM (fun (pat, e) -> mk_let_bindings pat e)
                (List.combine patlist (Expr.get_args expr)) >>= fun bindings ->
      BmcM.return (mk_and g_ctx bindings)
  | CaseCtor(Cspecified, [CaseBase(sym, BTy_object OTy_integer)]) ->
      let is_specified = LoadedInteger.is_specified expr in
      let specified_value = LoadedInteger.get_specified_value expr in
      mk_let_binding sym specified_value >>= fun is_eq_value ->
      BmcM.return (mk_and g_ctx [is_specified; is_eq_value])
  | CaseCtor(Cspecified, _) ->
      assert false
  | CaseCtor(Cunspecified, [CaseBase(sym, BTy_ctype)]) ->
      if (Sort.equal (Expr.get_sort expr) (LoadedInteger.mk_sort)) then
        let is_unspecified = LoadedInteger.is_unspecified expr in
        let unspecified_value = LoadedInteger.get_unspecified_value expr in
        mk_let_binding sym unspecified_value >>= fun is_eq_value ->
        BmcM.return (mk_and g_ctx [is_unspecified; is_eq_value])
      else
        assert false
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
      mk_true g_ctx
  | CaseCtor(Ctuple, patlist) ->
      assert (Expr.get_num_args expr = List.length patlist);
      let expr_list = Expr.get_args expr in
      let match_conditions =
        List.map2 (fun pat e -> pattern_match pat e)
                  patlist expr_list in
      mk_and g_ctx match_conditions
  | CaseCtor(Cspecified, [CaseBase(_, BTy_object OTy_integer)]) ->
      LoadedInteger.is_specified expr
  | CaseCtor(Cspecified, _) ->
      assert false
  | CaseCtor(Cunspecified, [CaseBase(_, BTy_ctype)]) ->
      if (Sort.equal (Expr.get_sort expr) (LoadedInteger.mk_sort)) then
        LoadedInteger.is_unspecified expr
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
  let case_guards = List.mapi (fun i expr ->
    mk_and g_ctx
           [ mk_not g_ctx (mk_or g_ctx (list_take i pattern_guards))
           ; expr
           ]) pattern_guards in
  let vc = mk_or g_ctx pattern_guards in
  (vc, case_guards)

(* =========== MODEL CHECKING FUNCTIONS =========== *)
let rec bmc_pexpr (Pexpr(_, bTy, pe) as pexpr: typed_pexpr) :
                  bmc_pret BmcM.eff =
  match pe with
  | PEsym sym ->
      BmcM.lookup_sym sym >>= fun sym_expr ->
      BmcM.return { expr   = sym_expr
                  ; assume = []
                  ; vcs    = []
                  }
  | PEimpl _ ->
      assert false
  | PEval cval ->
      BmcM.return { expr   = value_to_z3 cval
                  ; assume = []
                  ; vcs    = []
                  }
  | PEconstrained _
  | PEundef _ ->
      let sort = cbt_to_z3 bTy in
      BmcM.return { expr   = Expr.mk_fresh_const g_ctx "undef" sort
                  ; assume = []
                  ; vcs    = [ mk_false g_ctx ]
                  }
  | PEerror _ ->
      let sort = cbt_to_z3 bTy in
      BmcM.return { expr   = Expr.mk_fresh_const g_ctx "error" sort
                  ; assume = []
                  ; vcs    = [ mk_false g_ctx ]
                  }
  | PEctor (ctor, pelist) ->
      BmcM.mapM bmc_pexpr pelist >>= fun res_pelist ->
      BmcM.return { expr   = ctor_to_z3 ctor
                                        (List.map pget_expr res_pelist) bTy
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
                  BmcM.return (let_binding, res_case_pexpr)
                ) caselist >>= fun binding_res_list ->
      let guarded_let_bindings = List.map2 (
        fun guard (let_binding, _) -> mk_implies g_ctx guard let_binding)
        case_guards binding_res_list in
      let case_assumes =
        List.concat (List.map (fun (_, res) -> res.assume)
                              binding_res_list) in
      let guarded_vcs = List.map2 (
        fun guard (_, res) -> mk_implies g_ctx guard (mk_and g_ctx res.vcs))
        case_guards binding_res_list in
      let ite_expr =
        if List.length caselist = 1 then
          pget_expr (snd (List.hd binding_res_list))
        else
          let rev_list = List.rev (List.map snd binding_res_list) in
          let rev_case_guards = List.rev case_guards in
          let last_case_expr = pget_expr (List.hd rev_list) in
          List.fold_left2 (fun acc guard res ->
            mk_ite g_ctx guard res.expr acc)
            last_case_expr
            (List.tl rev_case_guards)
            (List.tl rev_list)
      in
      BmcM.return { expr   = ite_expr
                  ; assume =   res_pe.assume
                             @ guarded_let_bindings
                             @ case_assumes
                  ; vcs    = match_vc :: (res_pe.vcs @ guarded_vcs)
                  }
  | PEarray_shift _
  | PEmember_shift _
  | PEmemberof _  ->
      assert false
  | PEnot pe ->
      bmc_pexpr pe >>= fun res ->
      BmcM.return {res with expr = mk_not g_ctx res.expr}
  | PEop (binop, pe1, pe2) ->
      (* TODO: symbols added in pe1 visible in pe2 *)
      bmc_pexpr pe1 >>= fun res1 ->
      bmc_pexpr pe2 >>= fun res2 ->
      BmcM.return { expr   = binop_to_z3 binop res1.expr res2.expr
                  ; assume = res1.assume @ res2.assume
                  ; vcs    = res1.vcs @ res2.vcs
                  }
  | PEstruct _
  | PEunion _ ->
      assert false
  | PEcall (name, pelist) ->
      BmcM.get_file >>= fun file ->
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
      (* Get Z3 function declaration corresponding to the stdlib function *)
      BmcM.get_or_make_func_decl
          name (List.map (fun (_, ty) -> cbt_to_z3 ty) args) (cbt_to_z3 ty)
          >>= fun func_decl ->
      (* Bmc each argument *)
      BmcM.mapM (fun pe -> bmc_pexpr pe) pelist >>= fun arg_retlist ->
      (* Substitute arguments in function call *)
      let sub_map = List.fold_right2
          (fun (sym, _) pe table -> Pmap.add sym pe table)
          args pelist (Pmap.empty sym_cmp) in
      (* Bmc the function body *)
      let expr_to_check = substitute_pexpr sub_map fun_expr in
      bmc_pexpr expr_to_check >>= fun ret_call ->

      (* Function call application in Z3 *)
      let func_call = Expr.mk_app g_ctx func_decl
                        (List.map (fun ret -> ret.expr) arg_retlist) in

      (* Assert function call = function body *)
      let eq_expr = mk_eq g_ctx func_call ret_call.expr in

      BmcM.return { expr   = func_call
                  ; assume = [eq_expr]
                             @ ret_call.assume
                             @ (List.concat (List.map pget_assume arg_retlist))
                  ; vcs    = ret_call.vcs
                             @ (List.concat (List.map pget_vcs arg_retlist))
                  }
  | PElet (pat, pe1, pe2) ->
      bmc_pexpr pe1                 >>= fun res1 ->
      add_pattern_to_sym_table pat  >>= fun () ->
      mk_let_bindings pat res1.expr >>= fun let_binding ->
      bmc_pexpr pe2                 >>= fun res2 ->
      BmcM.return { expr    = res2.expr
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
        @ (List.map (fun vc -> mk_implies g_ctx res_cond.expr vc) res1.vcs)
        @ (List.map (fun vc -> mk_implies g_ctx (mk_not g_ctx res_cond.expr) vc)
                    res2.vcs)
      in
      BmcM.return { expr   = mk_ite g_ctx res_cond.expr res1.expr res2.expr
                  ; assume = res_cond.assume @ res1.assume @ res2.assume
                  ; vcs    = new_vcs
                  }
  | PEis_scalar _
  | PEis_integer _ ->
      assert false
  | PEis_signed _ ->
      assert false
  | PEis_unsigned pe ->
      bmc_pexpr pe >>= fun res_pe ->
      BmcM.return { expr   = Expr.mk_app g_ctx ImplFunctions.is_unsigned
                                               [res_pe.expr]
                  ; assume = res_pe.assume
                  ; vcs    = res_pe.vcs
                  }

let rec bmc_expr (Expr(_, expr_): unit typed_expr)
                 : bmc_ret BmcM.eff =
  match expr_ with
  | Epure pe ->
      bmc_pexpr pe >>= fun pres ->
      BmcM.return (bmc_pret_to_ret pres)
  | Ememop _
  | Eaction _ ->
      assert false
  | Ecase (pe, caselist) ->
      (* TODO: code duplication from PEcase *)
      assert (List.length caselist > 0);
      bmc_pexpr pe >>= fun res_pe ->
      let (match_vc, case_guards) =
        compute_case_guards (List.map fst caselist) res_pe.expr in
      BmcM.get_sym_table >>= fun old_sym_table ->
      BmcM.mapM (fun (pat, case_expr) ->
                  add_pattern_to_sym_table pat    >>= fun () ->
                  mk_let_bindings pat res_pe.expr >>= fun let_binding ->
                  bmc_expr case_expr              >>= fun res_case_expr ->
                  BmcM.update_sym_table old_sym_table >>= fun () ->
                  BmcM.return (let_binding, res_case_expr)
                ) caselist >>= fun binding_res_list ->
      let guarded_let_bindings = List.map2 (
        fun guard (let_binding, _) -> mk_implies g_ctx guard let_binding)
        case_guards binding_res_list in
      let case_assumes : Expr.expr list =
        List.concat (List.map (fun (_, res) -> eget_assume res)
                              binding_res_list) in
      let guarded_vcs = List.map2 (
        fun guard (_, res) ->
          mk_implies g_ctx guard (mk_and g_ctx (eget_vcs res)))
        case_guards binding_res_list in
      let ite_expr =
        if List.length caselist = 1 then
          eget_expr (snd (List.hd binding_res_list))
        else
          let rev_list = List.rev (List.map snd binding_res_list) in
          let rev_case_guards = List.rev case_guards in
          let last_case_expr = eget_expr (List.hd rev_list) in
          List.fold_left2 (fun acc guard res ->
            mk_ite g_ctx guard (eget_expr res) acc)
            last_case_expr
            (List.tl rev_case_guards)
            (List.tl rev_list) in
      let drop_cont =
        mk_or g_ctx (List.map2 (fun guard (_, res) ->
                                    mk_and g_ctx [guard; res.drop_cont])
                               case_guards binding_res_list) in
      BmcM.return { expr      = ite_expr
                  ; assume    =  res_pe.assume
                               @ guarded_let_bindings
                               @ case_assumes
                  ; vcs       = match_vc :: (res_pe.vcs @ guarded_vcs)
                  ; drop_cont = drop_cont
                  }
  | Eskip ->
      BmcM.return { expr      = UnitSort.mk_unit
                  ; assume    = []
                  ; vcs       = []
                  ; drop_cont = mk_false g_ctx
                  }
  | Eproc _
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
      BmcM.mapM bmc_expr elist >>= fun res_elist ->
      let choice_vars =
        List.mapi (fun i _ -> Expr.mk_fresh_const g_ctx
                              ("seq_" ^ (string_of_int i))
                              (Boolean.mk_sort g_ctx)) elist in
      (* Assert exactly one choice is taken *)
      let xor_expr = List.fold_left
          (fun acc choice -> mk_xor g_ctx acc choice)
          (mk_false g_ctx) choice_vars in
      let vcs = List.map2
          (fun choice res -> mk_implies g_ctx choice
                                              (mk_and g_ctx (eget_vcs res)))
          choice_vars res_elist in
      let drop_cont = mk_or g_ctx
          (List.map2 (fun choice res -> mk_and g_ctx [choice; res.drop_cont])
                     choice_vars res_elist) in
      let ret_expr = List.fold_left2
          (fun acc choice res -> mk_ite g_ctx choice (eget_expr res) acc)
          (eget_expr (List.hd res_elist))
          (List.tl choice_vars)
          (List.tl res_elist) in
      BmcM.return { expr      = ret_expr
                  ; assume    = xor_expr
                                :: (List.concat (List.map eget_assume res_elist))
                  ; vcs       = vcs
                  ; drop_cont = drop_cont
                  }
  | Erun (_, label, pelist) ->
      BmcM.get_run_depth_table >>= fun run_depth_table ->
      let depth = match Pmap.lookup label run_depth_table with
                  | None -> 0
                  | Some i -> i in
      if depth >= g_max_run_depth then
        assert false (* TODO: treat as PError *)

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
        BmcM.update_run_depth_table
            (Pmap.add label (depth+1) run_depth_table) >>= fun () ->
        bmc_expr cont_to_check >>= fun run_res ->

        BmcM.update_run_depth_table run_depth_table >>= fun () ->
        BmcM.return { expr      = run_res.expr
                    ; assume    = run_res.assume
                    ; vcs       = run_res.vcs
                    ; drop_cont = mk_true g_ctx
                    }
      end
  | Epar _
  | Ewait _ ->
      assert false
  | Eif (pe, e1, e2) ->
      bmc_pexpr pe >>= fun res_pe ->
      bmc_expr  e1 >>= fun res_e1 ->
      bmc_expr  e2 >>= fun res_e2 ->
      let vcs =
          res_pe.vcs
        @ (List.map (fun vc -> mk_implies g_ctx res_pe.expr vc) res_e1.vcs)
        @ (List.map (fun vc -> mk_implies g_ctx (mk_not g_ctx res_pe.expr) vc)
                    res_e2.vcs) in
      let drop_cont = mk_or g_ctx
        [ mk_and g_ctx [res_pe.expr             ; res_e1.drop_cont]
        ; mk_and g_ctx [mk_not g_ctx res_pe.expr; res_e2.drop_cont]
        ] in
      BmcM.return { expr      = mk_ite g_ctx res_pe.expr
                                             res_e1.expr res_e2.expr
                  ; assume    = res_pe.assume @ res_e1.assume @ res_e2.assume
                  ; vcs       = vcs
                  ; drop_cont = drop_cont
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
      (* TODO: do optimization based on drop_cont *)
      BmcM.return { expr      = res2.expr
                  ; assume    = let_binding::(res1.assume @ res2.assume)
                  ; vcs       = (mk_or g_ctx [ res1.drop_cont
                                             ; mk_and g_ctx res2.vcs ])
                                :: res1.vcs
                  ; drop_cont = mk_or g_ctx [res1.drop_cont; res2.drop_cont]
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
        BmcM.update_proc_expr e >>= fun () ->
        bmc_expr e

    | Some (Fun (ty, params, pe)) ->
        BmcM.mapM_ initialise_param params >>= fun () ->
        bmc_pexpr pe >>= fun pret ->
        BmcM.return (bmc_pret_to_ret pret)

    | _ -> failwith "Function to check must be a Core Proc or Fun"
  in
  let (result, new_state) = BmcM.run initial_state to_run in

  (*
  print_endline "====FINAL BMC_RET";
  print_string (pp_bmc_ret result);
  *)

  (* TODO: assert and track based on annotation *)
  (* TODO: multiple expressions or one expression? *)

  (* Assumptions *)
  Solver.assert_and_track
    g_solver
    (Expr.simplify (mk_and g_ctx result.assume) None)
    (Expr.mk_fresh_const g_ctx "assume" (Boolean.mk_sort g_ctx));

  assert (Solver.check g_solver [] = SATISFIABLE);
  (* VCs *)
  Solver.assert_and_track
    g_solver
    (Expr.simplify (mk_not g_ctx (mk_and g_ctx result.vcs)) None)
    (Expr.mk_fresh_const g_ctx "negated_vcs" (Boolean.mk_sort g_ctx));

  (*
  print_endline "====FINAL SOLVER";
  print_endline (Solver.to_string g_solver);
  *)

  match Solver.check g_solver [] with
  | UNKNOWN ->
      printf "STATUS: unknown. Reason: %s\n"
             (Solver.get_reason_unknown g_solver)
  | UNSATISFIABLE ->
      print_endline "STATUS: unsatisfiable :)"
  | SATISFIABLE ->
      print_endline "STATUS: satisfiable"

(* Main bmc function: typechecks and sequentialises file.
 * The symbol supply is used to ensure fresh symbols when renaming.
 *)
let bmc (core_file  : unit file)
        (sym_supply : sym_supply_ty) =

  match Core_typing.typecheck_program core_file with
    | Result typed_core ->
        begin
          let sequentialised_core =
            Core_sequentialise.sequentialise_file typed_core in

          pp_file sequentialised_core;
          bmc_debug_print 1 "START: model checking";
          match sequentialised_core.main with
          | None ->
              (* Currently only check main function *)
              failwith "ERROR: fail does not have a main"
          | Some main_sym ->
              bmc_file sequentialised_core sym_supply main_sym
        end
    | Exception msg ->
        printf "Typechecking error: %s\n" (Pp_errors.to_string msg)
