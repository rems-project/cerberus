(*
LR(1) parser validator
Copyright (C) 2011 INRIA

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>

Jacques-Henri Jourdan <jacques-henri.jourdan@ens.fr>
*)

Require Import List.
Require Import Coq.Program.Syntax.

(** A tuple is a heterogeneous list. For convenience, we use pairs, and
    we allow the user to specify explicitly the type of nil. **)
Definition tuple (types:list Type) : Type :=
  fold_right prod unit types.

Fixpoint tuple_rev_app (types1:list Type) (tuple1:tuple types1)
                       (types2:list Type) (tuple2:tuple types2)
           : tuple (rev_append types1 types2) :=
  match types1 return tuple types1 -> tuple (rev_append types1 types2) with
    | [] => fun _ => tuple2
    | _::tq => fun tuple1 =>
      let (t, q) := tuple1 in
      tuple_rev_app tq q (_::types2) (t, tuple2)
  end tuple1.

(** A curryfied function with multiple parameters **)
Definition arrows (args:list Type) (res:Type): Type :=
  fold_right (fun A B => A -> B) res args.

Fixpoint uncurry {args:list Type} {res:Type}:
  arrows args res -> tuple args -> res :=
  match args with
    | [] => fun f _ => f
    | t::q => fun f p => let (d, t) := p in
                uncurry (f d) t
  end.