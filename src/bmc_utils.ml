open Core

module Sym = Symbol
open Z3

let g_bmc_debug = 10

(* ========== TYPE ALIASES ============= *)

type sym_ty = Sym.sym
type sym_supply_ty = sym_ty UniqueId.supply

(* ========== Z3 ALIASES ============= *)
let mk_sym (ctx:context) = Symbol.mk_string ctx

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

(* ========== Debug ========== *)
let debug_print level str =
  Debug_ocaml.print_debug level [] (fun () -> str)

let dprintf = Printf.printf

let bmc_debug_print level str =
  if g_bmc_debug >= level then
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
  let doc = Pp_core.Basic.pp_file core_file in
  pp_to_stdout doc

let pp_ctype (ctype: Core_ctype.ctype0) =
  pp_to_string (Pp_core_ctype.pp_ctype ctype)
