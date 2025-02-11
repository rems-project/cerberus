Require Import String.
Require Import Symbol.
Require Import Location.

(* Type definition for identifiers *)
Definition t := Symbol.identifier.

(* Get the string from an identifier *)
Definition get_string (id: t) : string :=
  match id with
  | Symbol.Identifier _ s => s
  end.

(* Get the location from an identifier *)
Definition get_loc (id: t) : Location.t :=
  match id with
  | Symbol.Identifier loc _ => loc
  end.

(* Create a new identifier *)
Definition make (loc: Location.t) (s: string) : t :=
  Symbol.Identifier loc s.

(* Compare two identifiers for equality *)
Definition equal (id1 id2: t) : bool :=
  Symbol.ident_equal id1 id2.

(* Compare an identifier with a string *)
Definition equal_string (s: string) (id: t) : bool :=
  String.eqb s (get_string id).

(* Compare two identifiers *)
Definition compare (id1 id2: t) : comparison :=
  String.compare (get_string id1) (get_string id2).

(* Identity substitution *)
Definition subst {A: Type} (_: A) (id: t) : t := id. 