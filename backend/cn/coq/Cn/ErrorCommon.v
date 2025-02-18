Require Import Coq.Strings.String.

Require Import Sym.

Definition label_kind := unit. (* TODO: placeholder *)

(* Corresponds to OCaml type access *)
Inductive access : Type :=
  | Load
  | Store
  | Deref
  | Kill
  | Free
  | To_bytes
  | From_bytes.

  (* Corresponds to OCaml type call_situation *)
Inductive call_situation : Type :=
 | FunctionCall : Sym.t -> call_situation
 | LemmaApplication : Sym.t -> call_situation
 | LabelCall : label_kind -> call_situation
 | Subtyping : call_situation.

  (* Corresponds to OCaml type situation *)
Inductive situation : Type :=
  | Access : access -> situation
  | Call : call_situation -> situation.

