open Core

open Bmc_utils

let normalize_fun_map (fun_map: ('a, 'b typed_fun_map_decl) Pmap.map) 
                      (sym_supply: ksym_supply) =
  fun_map, sym_supply

let normalize_file (file : 'a typed_file) (sym_supply: ksym_supply) =
  let (normed_map, supply1) = normalize_fun_map file.funs sym_supply in
  ({file with funs = normed_map;
  }, supply1)
