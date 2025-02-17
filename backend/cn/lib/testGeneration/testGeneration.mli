type config = TestGenConfig.t

val default_cfg : config

val set_config : config -> unit

module Options = TestGenConfig.Options

val functions_under_test
  :  with_warning:bool ->
  Cerb_frontend.Cabs.translation_unit ->
  Cerb_frontend.GenTypes.genTypeCategory Cerb_frontend.AilSyntax.sigma ->
  unit Mucore.file ->
  Executable_spec_extract.instrumentation list

val run
  :  output_dir:string ->
  filename:string ->
  without_ownership_checking:bool ->
  Cerb_frontend.Cabs.translation_unit ->
  Cerb_frontend.GenTypes.genTypeCategory Cerb_frontend.AilSyntax.sigma ->
  unit Mucore.file ->
  unit
