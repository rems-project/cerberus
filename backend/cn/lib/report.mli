(** Definition of something *)
type term_entry =
  { term : Pp.document; (** The term being evaluated *)
    value : Pp.document (** Its value in the current context *)
  }

(** A clause for a resource *)
type predicate_clause_entry =
  { cond : Pp.document; (** Guard on the resource *)
    clause : Pp.document (** The actual resource *)
  }

type resource_entry =
  { res : Pp.document;
    res_span : Pp.document
  }

type where_report =
  { fnction : string option;
    section : string option;
    loc_cartesian : ((int * int) * (int * int)) option;
    (** Where in the source file we are *)
    loc_head : string (** Name of what we are currently processing *)
  }

(** Different forms of a document. *)
type simp_view =
  { original : Pp.document; (* original view *)
    simplified : Pp.document list (* simplified based on model *)
  }

(** Labels for classifying itesm in a view *)
type label

(** Interesting things that are shown by default *)
val lab_interesting : label

(** Uninteresting things that are hidden by default *)
val lab_uninteresting : label

(** A collection of labeled things *)
type 'a labeled_view

(** Empty collection of labeld things *)
val labeled_empty : 'a labeled_view

(** Set the entities associated with a label *)
val add_labeled : label -> 'a list -> 'a labeled_view -> 'a labeled_view

(** Get any entities associated with a label *)
val get_labeled : 'a labeled_view -> label -> 'a list option

(** Information about a specific state of the computation.
    The resources, constraints, and terms are pairs because they classify
    how relevant the thing might be:
    the first component is "interesting", the second is not. *)
type state_report =
  { where : where_report; (** Location information *)
    not_given_to_solver : simp_view labeled_view;
    resources : simp_view labeled_view;
    constraints : simp_view labeled_view;
    terms : term_entry labeled_view
  }

(** Parts of an HTML rendering of an error. *)
type report =
  { trace : state_report list; (** The states we went through to get here *)
    requested : Pp.document option; (** Resource that we failed to construct *)
    unproven : Pp.document option; (** Fact we failed to prove *)
    predicate_hints : predicate_clause_entry list
    (** Definitions of resource predicates related to the requested one. *)
  }

(** Save a report to a file.
    The first argument is the name of the file where the report should be saved.
    It is also returned as the result of the function.

    The second argument is the C source code for the report, which is used
    to highlight locations.

    The third argument is information about the various things that need to be saved. *)
val make : string -> string Option.m -> report -> string
