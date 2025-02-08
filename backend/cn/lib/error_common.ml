(** Common error types shared by TypeErrors and other modules *)

module Loc = Locations

type access =
  | Load
  | Store
  | Deref
  | Kill
  | Free
  | To_bytes
  | From_bytes

type call_situation =
  | FunctionCall of Sym.t
  | LemmaApplication of Sym.t
  | LabelCall of Where.label
  | Subtyping

(* Adjust this definition to match the one from TypeErrors *)
type situation =
  | Access of access
  | Call of call_situation
