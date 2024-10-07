(** Test Generation
    Generates RapidCheck tests for functions with CN specifications, where test inputs are
    guaranteed to satisfy the CN precondition.

    Below is a high-level overview of the entire system.

    We begin by making a new file in the [output-dir] named "test_[FILE].cpp".
    Then we insert [#include]s for the test libraries ([Codify.codify_prelude]).
    We go over each function with a CN specficiation and body defined in the current file.

    The majority of the work occurs per-function via [TestGeneration.generate_pbt]

    We have 3 main stages in [TestGeneration.generate_pbt]:
    1. Collecting of constraints
    2. Compiling constraints into generators in a DSL
    3. Convert the generators into C++

    These 3 stages break down into 5 function calls:
    1a. [Constraints.collect]- Takes CN specifications and produce a [goal] summarizing the constraints
    1b. [Constraints.simplify] - Rewrite our [goal] via various passes
    2a. [Dsl.compile] - Compiles our [goal] into a [gen_context] in our DSL
    2b. [Dsl.optimize] - Performs program optimizations on our [gen_context]
    3. [Codify.codify_pbt] - Converts our [gen_context] into RapidCheck generators *)

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
  unit Mucore.file ->
  Codify.test_framework ->
  unit
