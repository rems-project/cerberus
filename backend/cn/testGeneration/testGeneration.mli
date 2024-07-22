type test_framework = Codify.test_framework

val test_frameworks : (string * test_framework) list

(** The entrypoint into test generation.
    @param output_dir Directory to place generated test files
    @param filename File with specifications to generate tests for
    @param max_unfolds The maximum number of times that predicates will be unfolded
                       **)
val run
  :  output_dir:string ->
  filename:string ->
  max_unfolds:int ->
  Cerb_frontend.GenTypes.genTypeCategory Cerb_frontend.AilSyntax.sigma ->
  unit Mucore.mu_file ->
  Codify.test_framework ->
  unit
