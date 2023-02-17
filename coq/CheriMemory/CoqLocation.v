Require Import Coq.Strings.String.

Record lexing_position := {
    pos_fname : string;
    pos_lnum : nat;
    pos_bol : nat;
    pos_cnum : nat;
  }.

Inductive location_cursor :=
| NoCursor: location_cursor
| PointCursor: lexing_position -> location_cursor
| RegionCursor: lexing_position -> lexing_position -> location_cursor.

Inductive location_ocaml :=
| Loc_unknown: location_ocaml
| Loc_other: string -> location_ocaml
| Loc_point: lexing_position -> location_ocaml
(* start, end, cursor *)
| Loc_region: lexing_position -> lexing_position -> location_cursor -> location_ocaml
| Loc_regions: list (lexing_position * lexing_position) -> location_cursor -> location_ocaml.
