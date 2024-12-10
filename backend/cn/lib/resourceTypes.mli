module LCSet :
  Set.S with type elt = LogicalConstraints.t and type t = Set.Make(LogicalConstraints).t

type init =
  | Init
  | Uninit

type predicate_name =
  | Owned of Sctypes.t * init
  | PName of Sym.t
[@@deriving eq]

val alloc : predicate_name

val pp_predicate_name : predicate_name -> Pp.document

type predicate_type =
  { name : predicate_name;
    pointer : IndexTerms.t;
    iargs : IndexTerms.t list
  }

val make_alloc : IndexTerms.t -> predicate_type

type qpredicate_type =
  { name : predicate_name;
    pointer : IndexTerms.t;
    q : Sym.t * BaseTypes.t;
    q_loc : Locations.t;
    step : IndexTerms.t;
    permission : IndexTerms.t;
    iargs : IndexTerms.t list
  }

val subsumed : predicate_name -> predicate_name -> bool

type resource_type =
  | P of predicate_type
  | Q of qpredicate_type

type t = resource_type

val predicate_name : resource_type -> predicate_name

val pp_aux : resource_type -> 'a Terms.annot option -> Pp.document

val pp : resource_type -> Pp.document

val equal : resource_type -> resource_type -> bool

val json : resource_type -> Yojson.Safe.t

val alpha_rename_qpredicate_type_ : Sym.t -> qpredicate_type -> qpredicate_type

val alpha_rename_qpredicate_type : qpredicate_type -> qpredicate_type

val subst_predicate_type
  :  [ `Rename of Sym.t | `Term of IndexTerms.t ] Subst.t ->
  predicate_type ->
  predicate_type

val subst
  :  [ `Rename of Sym.t | `Term of IndexTerms.t ] Subst.t ->
  resource_type ->
  resource_type

val free_vars_bts : resource_type -> BaseTypes.t Sym.Map.t

val free_vars : resource_type -> Sym.Set.t

val same_predicate_name : resource_type -> resource_type -> bool

val alpha_equivalent : resource_type -> resource_type -> bool

val steps_constant : resource_type -> bool

val dtree_of_predicate_type : predicate_type -> Cerb_frontend.Pp_ast.doc_tree

val dtree : resource_type -> Cerb_frontend.Pp_ast.doc_tree
