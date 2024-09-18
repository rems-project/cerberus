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

(** Information about a specific state of the computation.
    The resources, constraints, and terms are pairs because they classify
    how relevant the thing might be:
    the first component is "interesting", the second is not. *)
type state_report =
  { where : where_report; (** Location information *)
    not_given_to_solver : Pp.document list * Pp.document list; (* Interesting/uninteresting definitions and constraints not given to solver *)
    resources : Pp.document list * Pp.document list; (** Resources *)
    constraints : Pp.document list * Pp.document list; (** Constraints *)
    terms : term_entry list * term_entry list (** Term values *)
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
