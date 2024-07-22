(** Test Generation
    Generates RapidCheck tests for functions
    with CN specifications, where inputs are
    guaranteed to satisfy the CN precondition.
    **)

type test_framework = Codify.test_framework

let test_frameworks = [ ("gtest", Codify.GTest) ]

let run = Generate.run
