Require Import String.

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

Inductive Locations_t :=
| Loc_unknown: Locations_t
| Loc_other: string -> Locations_t
| Loc_point: lexing_position -> Locations_t
(* start, end, cursor *)
| Loc_region: lexing_position -> lexing_position -> location_cursor -> Locations_t
| Loc_regions: list (lexing_position * lexing_position) -> location_cursor -> Locations_t.
