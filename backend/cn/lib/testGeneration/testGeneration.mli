type config = TestGenConfig.t

val default_cfg : config

val run
  :  output_dir:string ->
  filename:string ->
  without_ownership_checking:bool ->
  config ->
  Cerb_frontend.GenTypes.genTypeCategory Cerb_frontend.AilSyntax.sigma ->
  unit Mucore.file ->
  unit
