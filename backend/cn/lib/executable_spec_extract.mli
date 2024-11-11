type statement = Locations.t * Cnprog.t list

type statements = statement list

type loop =
  Locations.t * statements ArgumentTypes.t (* location is for the loop condition *)

type loops = loop list

type fn_body = statements * loops

type fn_args_and_body = (ReturnTypes.t * fn_body) ArgumentTypes.t

type fn_largs_and_body = (ReturnTypes.t * fn_body) LogicalArgumentTypes.t

(* type fn_spec_instrumentation = (ReturnTypes.t * statements) ArgumentTypes.t *)
(* type fn_spec_instrumentation_lat = (ReturnTypes.t * statements) LogicalArgumentTypes.t *)

val sym_subst : Sym.t * BaseTypes.t * Sym.t -> [`Rename of Sym.t | `Term of IndexTerms.t] Subst.t

val fn_args_and_body_subst : [`Rename of Sym.t | `Term of IndexTerms.t] Subst.t -> fn_args_and_body -> fn_args_and_body

val fn_largs_and_body_subst
  :  [`Rename of Sym.t | `Term of IndexTerms.t] Subst.t ->
  fn_largs_and_body ->
  fn_largs_and_body

type instrumentation =
  { fn : Sym.t;
    fn_loc : Locations.t;
    internal : fn_args_and_body option
  }

val collect_instrumentation
  :  'a Mucore.file ->
  instrumentation list * BaseTypes.Surface.t Hashtbl.Make(Sym).t
