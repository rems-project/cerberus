type state_entry = {
  loc_e : Pp.document option;
  loc_v : Pp.document option;
  state : Pp.document option;
}

type term_entry = { term : Pp.document; value : Pp.document; }

type predicate_clause_entry = {
  cond : Pp.document;
  clause : Pp.document;
}

type resource_entry = {
  res : Pp.document;
  res_span : Pp.document;
}

type where_report = {
<<<<<<< HEAD
  fnction : string option;
  section : string option;
=======
  fnction : string;
  section : string;
>>>>>>> 859b4d7b6db6a6ff3877c39c7f0b83f7dda60f93
  loc_cartesian : ((int * int) * (int * int)) option;
  loc_head : string;
}

type state_report = {
  where : where_report;
  resources : Pp.document list * Pp.document list;
  constraints : Pp.document list * Pp.document list;
  terms : term_entry list * term_entry list;
}

type report = {
  trace : state_report list;
  requested : Pp.document option;
  unproven : Pp.document option;
  predicate_hints : predicate_clause_entry list;
}

<<<<<<< HEAD
val make : string -> string Option.m -> report -> string
=======
val make : string -> report -> string

val make2 : string -> string Option.m -> report -> string
>>>>>>> 859b4d7b6db6a6ff3877c39c7f0b83f7dda60f93
