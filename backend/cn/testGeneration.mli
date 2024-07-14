module CF = Cerb_frontend

type test_framework = GTest

val main
  :  string
  -> string
  -> int
  -> _ CF.AilSyntax.sigma
  -> unit Mucore.mu_file
  -> test_framework
  -> unit
