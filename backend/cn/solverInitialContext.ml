let context =
  Z3.mk_context [
      ("model", "true");
      ("well_sorted_check","true");
      ("unsat_core", "true");
    ] 

