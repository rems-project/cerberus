open Extra
open Rc_annot

module Loc :
  sig
    type t

    type loc_data =
      { loc_file  : string
      ; loc_line1 : int
      ; loc_col1  : int
      ; loc_line2 : int
      ; loc_col2  : int }

    val none : unit -> t
    val make : string -> int -> int -> int -> int -> t
    val get : t -> loc_data option
  end =
  struct
    type t = int

    type loc_data =
      { loc_file  : string
      ; loc_line1 : int
      ; loc_col1  : int
      ; loc_line2 : int
      ; loc_col2  : int }

    let htbl = Hashtbl.create 97
    let counter = ref (-1)

    let none : unit -> t = fun _ ->
      incr counter; !counter

    let make : string -> int -> int -> int -> int -> t = fun f l1 c1 l2 c2 ->
      let data =
        { loc_file = f
        ; loc_line1 = l1 ; loc_col1 = c1
        ; loc_line2 = l2 ; loc_col2 = c2 }
      in
      let key = incr counter; !counter in
      Hashtbl.add htbl key data; key

    let get : t -> loc_data option = fun key ->
      try Some(Hashtbl.find htbl key) with Not_found -> None
  end

type 'a located = { elt : 'a ; loc : Loc.t }

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

type expr = expr_aux located
and expr_aux =
  | Var       of string option * bool (* Global? *)
  | Val       of value
  | UnOp      of un_op * op_type * expr
  | BinOp     of bin_op * op_type * op_type * expr * expr
  | Deref     of layout * expr
  | CAS       of op_type * expr * expr * expr
  | SkipE     of expr
  | Use       of layout * expr
  | AddrOf    of expr
  | GetMember of expr * string * bool (* From_union? *) * string
  | AnnotExpr of int * coq_expr * expr

type stmt = stmt_aux located
and stmt_aux =
  | Goto   of string (* Block index in the [IMap.t]. *)
  | Return of expr
(*| Switch (it : int_type) (e : expr) (m : gmap Z nat) (bs : list stmt) (def : * stmt)*)
  | Assign of layout * expr * expr * stmt
  | Call   of string option * expr * expr list * stmt
  | SkipS  of stmt
  | If     of expr * stmt * stmt
  | Assert of expr * stmt
  | ExprS  of expr_annot option * expr * stmt

type struct_decl =
  { struct_name     : string
  ; struct_annot    : struct_annot option
  ; struct_deps     : string list
  ; struct_is_union : bool
  ; struct_members  : (string * (type_expr option option * layout)) list }

type func_def =
  { func_name   : string
  ; func_annot  : function_annot option
  ; func_args   : (string * layout) list
  ; func_vars   : (string * layout) list
  ; func_init   : string
  ; func_deps   : string list * string list (* global vars/functions used. *)
  ; func_blocks : (block_annot option * stmt) SMap.t }

type func_def_or_decl =
  | FDef of func_def
  | FDec of function_annot option

type t =
  { source_file : string
  ; entry_point : string option
  ; global_vars : string list
  ; structs     : (string * struct_decl) list
  ; functions   : (string * func_def_or_decl) list }
