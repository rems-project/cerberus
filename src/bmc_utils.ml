open Bmc_globals
open Annot
open Core

module Sym = Symbol
open Z3
open Z3.Arithmetic


(* ========== TYPE ALIASES ============= *)

type sym_ty = Sym.sym


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

let mk_const = Expr.mk_const g_ctx
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
    | OpRem_t -> assert false (*BitVector.mk_srem g_ctx arg1 arg2*)
    | OpRem_f -> BitVector.mk_smod g_ctx arg1 arg2
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

let sym_eq sym1 sym2 = sym_cmp sym1 sym2 = 0

let symbol_to_string (sym: sym_ty) =
  match sym with
  | Symbol (_, num, Some str) ->
      (str ^ "_" ^ (string_of_int num))
  | Symbol (_, num, None) ->
      ("?_" ^ (string_of_int num))

let symbol_to_int (Symbol(_, num, _): sym_ty) = num

let symbol_to_string_simple (sym: sym_ty) =
  match sym with
  | Symbol (_, _, Some str) -> str
  | Symbol (_, num, None) ->
      ("?_" ^ (string_of_int num))

let prefix_to_string (prefix: Sym.prefix) =
  match prefix with
  | PrefSource (_, l) -> "[" ^ (String.concat "," (List.map symbol_to_string_simple l)) ^ "]"
  | PrefOther s -> s
  | PrefStringLiteral _ -> "string literal"
  | PrefFunArg (_, _, n) -> "arg" ^ string_of_int n
  | PrefMalloc -> "malloc"


let prefix_to_string_short (prefix: Sym.prefix) =
  match prefix with
  | PrefSource (_, l) ->  symbol_to_string_simple (List.hd (List.rev l))
  | PrefOther s -> s
  | PrefStringLiteral _ -> "string literal"
  | PrefFunArg (_, _, n) -> "arg" ^ string_of_int n
  | PrefMalloc -> "malloc"

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

(* TODO: mini-hack to strip atomic *)
let strip_atomic = function ctype ->
  match ctype with
  | Core_ctype.Atomic0 ty -> ty
  | ty -> ty


(* ========== HELPER FUNCTIONS ============= *)
let rec list_take k l =
  if k > 0 then
    match l with
    | [] -> assert false
    | x :: xs -> x :: (list_take (k-1) xs)
  else []

let rec zip ls1 ls2 = match ls1,ls2 with
  | [], [] -> []
  | (x::xs), (y::ys) -> (x,y) :: (zip xs ys)
  | _,_ -> assert false

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

let pp_value value =
  pp_to_string (Pp_core.Basic.pp_value value)

let pp_expr = Pp_core.Basic.pp_expr
let pp_pexpr = Pp_core.Basic.pp_pexpr

let save_to_file file str =
  let channel = open_out file in
  output_string channel str;
  close_out channel

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let implode chars =
  let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) chars;
  Buffer.contents buf

let read_file filename =
  let lines = ref [] in
  let chan = open_in filename in
  try
    while true; do
      lines := input_line chan :: !lines
    done; !lines
  with End_of_file ->
    close_in chan;
    List.rev !lines ;;

(* ========== SET UIDs ============ *)
let rec set_uid_pe uid n (Pexpr( annots1, bty, pe_)) =
 (let uid' = (uid ^ string_of_int n) in
  let self n pe=  (set_uid_pe uid' n pe) in
  let selfs pes=  (Lem_list.mapi (fun i pe -> self (i+ 1) pe) pes) in
  Pexpr( Auid uid'::annots1, bty,
  (match pe_ with
  | PEsym s -> PEsym s
  | PEimpl impl1 -> PEimpl impl1
  | PEval v -> PEval v
  | PEconstrained cs ->
    PEconstrained (Lem_list.mapi (fun i (m, pe) -> (m, self (i+ 1) pe)) cs)
  | PEundef( loc, undef1) -> PEundef( loc, undef1)
  | PEerror( err, pe) -> PEerror( err, (self( 1) pe))
  | PEctor( ctor1, pes) -> PEctor( ctor1, (selfs pes))
  | PEcase( pe, cases) -> PEcase( (self( 0) pe),
                        (Lem_list.mapi (fun i (pat, pe) -> (pat, self (i+ 1) pe)) cases))
  | PEarray_shift( pe, cty, pes) -> PEarray_shift( (self( 1) pe), cty, (self( 2) pes))
  | PEmember_shift( pe, sym2, cid) -> PEmember_shift( (self( 1) pe), sym2, cid)
  | PEnot pe -> PEnot (self( 1) pe)
  | PEop( bop, pe1, pe2) -> PEop( bop, (self( 1) pe1), (self( 2) pe2))
  | PEstruct( sym2, fields) -> PEstruct( sym2,
                      (Lem_list.mapi (fun i (cid, pe) -> (cid, self (i+ 1) pe)) fields))
  | PEunion( sym2, cid, pe) -> PEunion( sym2, cid, (self( 1) pe))
  | PEcfunction pe -> PEcfunction (self( 1) pe)
  | PEmemberof( tag_sym, memb_ident, pe) -> PEmemberof( tag_sym, memb_ident, (self( 1) pe))
  | PEcall( name1, pes) -> PEcall( name1, (selfs pes))
  | PElet( pat, pe1, pe2) -> PElet( pat, (self( 1) pe1), (self( 2) pe2))
  | PEif( pe1, pe2, pe3) -> PEif( (self( 1) pe1), (self( 2) pe2), (self( 3) pe3))
  | PEis_scalar pe -> PEis_scalar (self( 1) pe)
  | PEis_integer pe -> PEis_integer (self( 1) pe)
  | PEis_signed pe -> PEis_signed (self( 1) pe)
  | PEis_unsigned pe -> PEis_unsigned (self( 1) pe)
  | PEbmc_assume pe -> PEbmc_assume (self( 1) pe)
  | PEare_compatible( pe1, pe2) -> PEare_compatible( (self( 1) pe1), (self( 2) pe2))
  )))

(*val     set_uid_e: forall 'a. string -> nat -> expr 'a -> expr 'a*)
let rec set_uid_e uid n (Expr( annots1, e_)) =
 (let uid' = (uid ^ string_of_int n) in
  let pure_uid n pe=  (set_uid_pe uid' n pe) in
  let pure_uids pes=  (Lem_list.mapi (fun i pe -> pure_uid (i+ 1) pe) pes) in
  let self n e=  (set_uid_e uid' n e) in
  let selfs es=  (Lem_list.mapi (fun i e -> self (i+ 1) e) es) in
  Expr( (Auid uid' :: annots1),
  (match e_ with
  | Epure pe -> Epure (set_uid_pe uid'( 0) pe)
  | Ememop( memop1, pes) -> Ememop( memop1, (pure_uids pes))
  | Eaction pact -> Eaction pact
  | Ecase( pe, cases) -> Ecase( (set_uid_pe uid'( 0) pe),
                        (Lem_list.mapi (fun i (pat, e) -> (pat, self (i+ 1) e)) cases))
  | Elet( pat, pe, e) -> Elet( pat, (set_uid_pe uid'( 0) pe), (self( 1) e))
  | Eif( pe, e1, e2) -> Eif( (set_uid_pe uid'( 0) pe), (self( 1) e1), (self( 2) e2))
  | Eskip -> Eskip
  | Eccall( x, pe1, pe2, args) -> Eccall( x, (set_uid_pe uid'( 0) pe1), (set_uid_pe uid'( 0) pe2), (pure_uids args))
  | Eproc( x, name1, args) -> Eproc( x, name1, (pure_uids args))
  | Eunseq es -> Eunseq (selfs es)
  | Ewseq( pat, e1, e2) -> Ewseq( pat, (self( 1) e1), (self( 2) e2))
  | Esseq( pat, e1, e2) -> Esseq( pat, (self( 1) e1), (self( 2) e2))
  | Easeq( bty, act, pact) -> Easeq( bty, act, pact)
  | Eindet( n, e) -> Eindet( n, (self( 1) e))
  | Ebound( n, e) -> Ebound( n, (self( 1) e))
  | End es -> End (selfs es)
  | Esave( lab_bty, args, e) -> Esave( lab_bty,
      (Lem_list.mapi (fun i (s, (bty, pe)) -> (s, (bty, pure_uid (i+ 1) pe))) args),
      (self( 0) e))
  | Erun( x, lab, pes) -> Erun( x, lab, (pure_uids pes))
  | Epar es -> Epar (selfs es)
  | Ewait thid -> Ewait thid
  )))

(*val string_of_symbol: Symbol.sym -> string*)

let set_uid_fun fname =  ((function
  | Fun( bty, args, pe) -> Fun( bty, args, pe)
  | ProcDecl( loc, ret_bty, args_bty) -> ProcDecl( loc, ret_bty, args_bty)
  | BuiltinDecl (loc, ret_bty, args_bty) -> BuiltinDecl (loc, ret_bty, args_bty)
  | Proc( loc, bty, args, e) -> Proc( loc, bty, args, (set_uid_e (Pp_symbol.to_string_pretty fname)( 1) e))
))

let set_uid_globs (gname, glb) =
  (gname, match glb with
  | GlobalDef (bty, e) -> GlobalDef (bty, (set_uid_e (Pp_symbol.to_string_pretty gname) 1 e))
  | GlobalDecl bty -> GlobalDecl bty)

let set_uid file1 =
 ({
  main=    (file1.main);
  tagDefs= (file1.tagDefs);
  stdlib=  (file1.stdlib);
  impl=    (file1.impl);
  globs=   List.map set_uid_globs file1.globs;
  funs=    (Pmap.mapi set_uid_fun file1.funs);
  funinfo= (file1.funinfo);
  extern=  file1.extern;
 })

let get_uid_or_fail annots : string =
  match Annot.get_uid annots with
  | None -> failwith "Uid not found"
  | Some uid -> uid

let get_uid_pexpr (Pexpr(annots, _, _)): string =
  get_uid_or_fail annots

let get_uid_expr (Expr(annots, _)): string =
  get_uid_or_fail annots

(* ===== bmc_annots ===== *)

let rec get_id_or_fail annots : int =
  match annots with
  | [] -> failwith "Id not found"
  | (Abmc (Abmc_id id)) :: _ ->
      id
  | _ :: annots' ->
      get_id_or_fail annots'

let get_id_pexpr (Pexpr(annots, _, _)) : int =
  get_id_or_fail annots

let get_id_expr (Expr(annots, _)) : int =
  get_id_or_fail annots
