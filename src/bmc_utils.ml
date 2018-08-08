open Bmc_globals
open Core

module Sym = Symbol
open Z3
open Z3.Arithmetic


(* ========== TYPE ALIASES ============= *)

type sym_ty = Sym.sym
type sym_supply_ty = sym_ty UniqueId.supply


(* ========== Z3 ALIASES ============= *)
let mk_sym = Symbol.mk_string g_ctx

let mk_implies = Boolean.mk_implies g_ctx
let mk_and     = Boolean.mk_and g_ctx
let mk_not     = Boolean.mk_not g_ctx
let mk_or      = Boolean.mk_or g_ctx
let mk_true    = Boolean.mk_true g_ctx
let mk_false   = Boolean.mk_false g_ctx
let mk_bool    = Boolean.mk_val g_ctx
let mk_xor     = Boolean.mk_xor g_ctx
let mk_eq      = Boolean.mk_eq g_ctx
let mk_ite     = Boolean.mk_ite g_ctx

let mk_fresh_const = Expr.mk_fresh_const g_ctx

let mk_fresh_func_decl = FuncDecl.mk_fresh_func_decl g_ctx

let integer_sort = if g_bv
                   then BitVector.mk_sort g_ctx g_bv_precision
                   else Integer.mk_sort g_ctx
let boolean_sort = Boolean.mk_sort g_ctx

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
    | OpRem_t -> BitVector.mk_srem g_ctx arg1 arg2
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


(* =========== Z3 HELPER FUNCTIONS =========== *)
let big_num_to_z3 (i: Nat_big_num.num) : Expr.expr =
  if g_bv then
    BitVector.mk_numeral g_ctx (Nat_big_num.to_string i) g_bv_precision
  else Integer.mk_numeral_s g_ctx (Nat_big_num.to_string i)

let int_to_z3 (i: int) : Expr.expr =
  big_num_to_z3 (Nat_big_num.of_int i)

(* ========== Core symbol functions ============= *)
let sym_cmp = Sym.instance_Basic_classes_SetType_Symbol_sym_dict.Lem_pervasives.setElemCompare_method

let symbol_to_string (sym: sym_ty) =
  match sym with
  | Symbol (num, Some str) ->
      (str ^ "_" ^ (string_of_int num))
  | Symbol (num, None) ->
      ("?_" ^ (string_of_int num))

let symbol_to_int (Symbol(num, _): sym_ty) = num

let prefix_to_string (prefix: Sym.prefix) =
  match prefix with
  | PrefSource l -> "[" ^ (String.concat "," (List.map symbol_to_string l)) ^ "]"
  | PrefOther s -> s

let name_cmp = fun nm1 nm2 ->
  match (nm1, nm2) with
  | (Sym sym1, Sym sym2) -> sym_cmp sym1 sym2
  | (Impl impl1, Impl impl2) ->
      Implementation_.implementation_constant_compare impl1 impl2
  | (Sym _, Impl _) -> (-1)
  | (Impl _, Sym _) -> 1

let cabsid_cmp = fun ident1 ident2 ->
  let (Cabs.CabsIdentifier(_, str1)) = ident1 in
  let (Cabs.CabsIdentifier(_, str2)) = ident2 in
  compare str1 str2


(* ========== Core memory functions ============= *)
let is_null (ptr: Ocaml_mem.pointer_value) : bool =
  let (Nondeterminism.ND f) =
    Ocaml_mem.eq_ptrval ptr (Ocaml_mem.null_ptrval Void0) in
  match f (Ocaml_mem.initial_mem_state) with
  | (Nondeterminism.NDactive b,_) -> b
  | _ -> assert false

(* ========== Core type functions ============= *)
let is_core_ptr_bty (bTy: core_base_type) =
  match bTy with
  | BTy_object OTy_pointer | BTy_loaded OTy_pointer -> true
  | _ -> false

(* ========== HELPER FUNCTIONS ============= *)
let rec list_take k l =
  if k > 0 then
    match l with
    | [] -> assert false
    | x :: xs -> x :: (list_take (k-1) xs)
  else []

(* TODO: not tail recursive *)
let rec repeat_n n elem =
  if n <= 0 then []
  else elem :: (repeat_n (n-1) elem)

let range i j =
  let rec aux n acc =
    if n < i then acc else aux (n-1) (n :: acc)
  in aux (j-1) [] ;;

let is_some (opt: 'a option) =
  match opt with
  | Some _ -> true
  | _ -> false

let cartesian_product (xs: 'a list) (ys: 'b list) : ('a * 'b) list =
  List.fold_left (fun outer x ->
    List.fold_left (fun inner y ->
      (x,y)::inner
    ) outer ys
  ) [] xs

(* ========== Debug ========== *)
let debug_print level str =
  Debug_ocaml.print_debug level [] (fun () -> str)

let dprintf = Printf.printf

let bmc_debug_print level str =
  if !!bmc_conf.debug_lvl >= level then
    print_endline str

(* ========== Pretty printing ========== *)
let name_to_string (name: sym_ty generic_name) =
  match name with
  | Sym a  -> symbol_to_string a
  | Impl i -> Implementation_.string_of_implementation_constant i

let print_expr (expr: Expr.expr) =
  print_endline (Expr.to_string expr)

let pp_to_stdout (doc: PPrint.document) =
  PPrint.ToChannel.pretty 1.0 150 (Pervasives.stdout) doc

let pp_to_string (doc: PPrint.document) : string =
  Pp_utils.to_plain_string doc

let pp_file (core_file: ('a, 'b) generic_file) =
  pp_to_stdout (Pp_core.Basic.pp_file core_file)

let pp_ctype (ctype: Core_ctype.ctype0) =
  pp_to_string (Pp_core_ctype.pp_ctype ctype)

let save_to_file file str =
  let channel = open_out file in
  output_string channel str;
  close_out channel
