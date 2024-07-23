(* Module Core_to_mucore - Translate Cerberus Core to CN Mucore *)

(** Entry point *)
val normalise_file
  :  inherit_loc:bool ->
  Cerb_frontend.Cabs_to_ail_effect.fin_markers_env * 'a Cerb_frontend.AilSyntax.sigma ->
  ('b, unit) Cerb_frontend.Milicore.mi_file ->
  unit Mucore.mu_file Resultat.m

(* TODO(RB) - Do these belong here? Looks like they can/should be factored out *)
type statements = (Locations.t * Cnprog.cn_prog list) list

type fn_spec_instrumentation = (ReturnTypes.t * statements) ArgumentTypes.t

val arguments_of_at : ('a -> 'b) -> 'a ArgumentTypes.t -> 'b Mucore.mu_arguments

val fn_spec_instrumentation_sym_subst_lrt
  :  Sym.t * BaseTypes.t * Sym.t ->
  LogicalReturnTypes.t ->
  LogicalReturnTypes.t

val fn_spec_instrumentation_sym_subst_lat
  :  Sym.t * BaseTypes.t * Sym.t ->
  (ReturnTypes.t * statements) LogicalArgumentTypes.t ->
  (ReturnTypes.t * statements) LogicalArgumentTypes.t

val fn_spec_instrumentation_sym_subst_at
  :  Sym.t * BaseTypes.t * Sym.t ->
  fn_spec_instrumentation ->
  fn_spec_instrumentation

type instrumentation =
  { fn : Sym.t;
    fn_loc : Locations.t;
    internal : fn_spec_instrumentation option
  }

val collect_instrumentation
  :  'a Mucore.mu_file ->
  instrumentation list * SurfaceBaseTypes.t Hashtbl.Make(Sym).t
