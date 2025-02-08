type config = TestGenConfig.t

type seq_config = SeqTestGenConfig.t

val default_cfg : config

val default_seq_cfg : seq_config

val set_config : config -> unit

val set_seq_config : seq_config -> unit

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

val run_seq
  :  output_dir:string ->
  filename:string ->
  Cerb_frontend.GenTypes.genTypeCategory Cerb_frontend.AilSyntax.sigma ->
  unit Mucore.file ->
  unit
