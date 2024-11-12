(* Module Core_to_mucore - Translate Cerberus Core to CN Mucore *)

(** Entry point *)
val normalise_file
  :  inherit_loc:bool ->
  Cerb_frontend.Cabs_to_ail_effect.fin_markers_env * 'a Cerb_frontend.AilSyntax.sigma ->
  ('b, unit) Cerb_frontend.Milicore.mi_file ->
  unit Mucore.file Resultat.m

val arguments_of_at : ('a -> 'b) -> 'a ArgumentTypes.t -> 'b Mucore.arguments

val at_of_arguments : ('b -> 'a) -> 'b Mucore.arguments -> 'a ArgumentTypes.t
