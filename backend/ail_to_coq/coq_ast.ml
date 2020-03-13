open Extra

type rc_attr =
  { rc_attr_id   : string
  ; rc_attr_args : string list }

type int_type =
  | ItInt of { size : int ; signed : bool }
  | ItSize_t
  | ItIntptr_t of bool (* signed *)

type op_type =
  | OpInt of int_type
  | OpPtr

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

type layout =
  | LPtr
  | LStruct of string * bool (* Union? *)
  | LInt of int_type

type expr =
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
(*| AnnotExpr (n : nat) {A} (a : A) (e : expr)*)

type stmt =
  | Goto   of string (* Block index in the [IMap.t]. *)
  | Return of expr
(*| Switch (it : int_type) (e : expr) (m : gmap Z nat) (bs : list stmt) (def : * stmt)*)
  | Assign of layout * expr * expr * stmt
  | Call   of string option * expr * expr list * stmt
  | SkipS  of stmt
  | If     of expr * stmt * stmt
(*| AnnotStmt (n : nat) {A} (a : A) (s : stmt)*)
  | Assert of expr * stmt
  | ExprS  of expr * stmt

type struct_decl =
  { struct_name     : string
  ; struct_deps     : string list
  ; struct_is_union : bool
  ; struct_members  : (string * layout) list }

type func_def =
  { func_name   : string
  ; func_attrs  : rc_attr list
  ; func_args   : (string * layout) list
  ; func_vars   : (string * layout) list
  ; func_init   : string
  ; func_blocks : stmt SMap.t }

type t =
  { source_file : string
  ; entry_point : string option
  ; global_vars : string list
  ; structs     : (string * struct_decl) list
  ; functions   : (string * func_def   ) list }
