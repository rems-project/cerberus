module CF = Cerb_frontend

val main
  :  string
  -> CF.GenTypes.genTypeCategory CF.AilSyntax.sigma
  -> unit Mucore.mu_file
  -> unit
