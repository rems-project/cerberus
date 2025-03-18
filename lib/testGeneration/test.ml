type kind =
  | Constant (* Run function without arguments nor `accesses` once *)
  | Generator (* Run function with random inputs satisfying the precondition *)

type t =
  { kind : kind;
    suite : string;
    test : string
  }

let registration_macro (test : t) : string =
  match test.kind with
  | Constant -> "CN_REGISTER_UNIT_TEST_CASE"
  | Generator -> "CN_REGISTER_RANDOM_TEST_CASE"
