module Config = TestGenConfig

type config = Config.t

let default_cfg : config = Config.default

let run
  ~output_dir
  ~filename
  ~with_ownership_checking
  (cfg : config)
  (sigma : Cerb_frontend.GenTypes.genTypeCategory Cerb_frontend.AilSyntax.sigma)
  (prog5 : unit Mucore.file)
  : unit
  =
  Config.initialize cfg;
  if Option.is_some prog5.main then
    failwith "Cannot test a file with a `main` function";
  Cerb_debug.begin_csv_timing ();
  SpecTests.generate ~output_dir ~filename ~with_ownership_checking sigma prog5;
  Cerb_debug.end_csv_timing "specification test generation"
