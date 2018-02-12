open Core

open Z3
open Z3.Arithmetic

open Bmc_utils
open Bmc_normalize


let bmc_file (file: 'a typed_file) = 
  assert false


let run_bmc (core_file : 'a typed_file) 
            (sym_supply: ksym_supply)    = 
  print_string "ENTER: BMC PIPELINE \n";
  pp_file core_file;
  let (normalized_file, _) = normalize_file core_file sym_supply in
  pp_file normalized_file;
  bmc_file normalized_file; 


  print_string "EXIT: BMC PIPELINE \n";
