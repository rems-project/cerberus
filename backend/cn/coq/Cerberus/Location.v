(* Cerberus location type *)

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

Inductive Location_t :=
| Loc_unknown: Location_t
| Loc_other: string -> Location_t
| Loc_point: lexing_position -> Location_t
(* start, end, cursor *)
| Loc_region: lexing_position -> lexing_position -> location_cursor -> Location_t
| Loc_regions: list (lexing_position * lexing_position) -> location_cursor -> Location_t.

Definition t := Location_t.