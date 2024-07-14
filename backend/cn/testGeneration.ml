module CF = Cerb_frontend
open CF

type test_framework = GTest

let main
  (_output_dir : string)
  (_filename : string)
  (_max_depth : int)
  (_sigma : _ AilSyntax.sigma)
  (_prog5 : unit Mucore.mu_file)
  (_tf : test_framework)
  : unit
  =
  ()
;;
