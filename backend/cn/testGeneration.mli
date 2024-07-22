module CF = Cerb_frontend

type test_framework = GTest

(** The entrypoint into test generation.
    @param output_dir Directory to place generated test files
    @param filename File with specifications to generate tests for
    @param max_unfolds The maximum number of times that predicates will be unfolded
                       **)
val main
  :  output_dir:string ->
  filename:string ->
  max_unfolds:int ->
  CF.GenTypes.genTypeCategory CF.AilSyntax.sigma ->
  unit Mucore.mu_file ->
  test_framework ->
  unit
