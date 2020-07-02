open Extra
open Rc_annot

type int_type =
  | ItSize_t of bool (* signed *)
  | ItI8     of bool (* signed *)
  | ItI16    of bool (* signed *)
  | ItI32    of bool (* signed *)
  | ItI64    of bool (* signed *)
  | ItBool

type layout =
  | LVoid
  | LPtr
  | LStruct of string * bool (* Union? *)
  | LInt of int_type
  | LArray of layout * string (* size *)

type op_type =
  | OpInt of int_type
  | OpPtr of layout

type un_op =
  | NotBoolOp
  | NotIntOp
  | NegOp
  | CastOp of op_type

type bin_op =
  | AddOp | SubOp | MulOp | DivOp | ModOp | AndOp | OrOp | XorOp | ShlOp
  | ShrOp | EqOp | NeOp | LtOp | GtOp | LeOp | GeOp | RoundDownOp | RoundUpOp

type value =
  | Null
  | Void
  | Int of string * int_type
  | SizeOf of layout

let coq_locs : Location.Pool.t = Location.Pool.make ()

type expr = expr_aux Location.located
and expr_aux =
  | Var       of string option * bool (* Global? *)
  | Val       of value
  | UnOp      of un_op * op_type * expr
  | BinOp     of bin_op * op_type * op_type * expr * expr
  | Deref     of bool (* Atomic? *) * layout * expr
  | CAS       of op_type * expr * expr * expr
  | SkipE     of expr
  | Use       of bool (* Atomic? *) * layout * expr
  | AddrOf    of expr
  | GetMember of expr * string * bool (* From_union? *) * string
  | AnnotExpr of int * coq_expr * expr
  | Struct    of string * (string * expr) list

type stmt = stmt_aux Location.located
and stmt_aux =
  | Goto   of string (* Block index in the [IMap.t]. *)
  | Return of expr
  | Switch of int_type * expr * (string * int) list * stmt list * stmt
  | Assign of bool (* Atomic? *) * layout * expr * expr * stmt
  | Call   of string option * expr * expr list * stmt
  | SkipS  of stmt
  | If     of expr * stmt * stmt
  | Assert of expr * stmt
  | ExprS  of expr_annot option * expr * stmt

(* The integers are respecively the alignment and the size. *)
type field_data = member_annot option * (int * int) * layout

type struct_decl =
  { struct_name     : string
  ; struct_annot    : struct_annot option
  ; struct_deps     : string list
  ; struct_is_union : bool
  ; struct_members  : (string * field_data) list }

type block_annot =
  | BA_none
  | BA_loop of loop_annot option

type func_def =
  { func_name   : string
  ; func_annot  : function_annot option
  ; func_args   : (string * layout) list
  ; func_vars   : (string * layout) list
  ; func_init   : string
  ; func_deps   : string list * string list (* global vars/functions used. *)
  ; func_blocks : (block_annot * stmt) SMap.t }

type func_def_or_decl =
  | FDef of func_def
  | FDec of function_annot option

type t =
  { source_file : string
  ; entry_point : string option
  ; global_vars : (string * global_annot option) list
  ; structs     : (string * struct_decl) list
  ; functions   : (string * func_def_or_decl) list }

let proof_kind : func_def -> proof_kind = fun def ->
  match def.func_annot with
  | None        -> Proof_normal
  | Some(annot) -> annot.fa_proof_kind
