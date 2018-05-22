open Core

open Bmc_utils
open Bmc_globals
open Bmc_inline
open Bmc_renaming
open Bmc_ssa

let bmc_normalize_fn 
           (fn : 'a typed_fun_map_decl) 
           (file: 'a typed_file)
           (sym_supply: ksym_supply) =
  let table_with_globals = List.fold_left (fun table (sym, _, _) ->
    Pmap.add sym sym table) (Pmap.empty sym_cmp) file.globs in

  let initial_state : SSA.kssa_state = 
    { supply = sym_supply;
      sym_table = table_with_globals} in
  let (fn, st) = SSA.run initial_state (ssa_fn fn) in
  fn, st.supply
  (*
  let (inlined_fn, inlined_supply) = inline_fn fn file st.supply in
  let (rewritten_fn, rewritten_supply) = rewrite_fn fn file inlined_supply in
  (rewritten_fn, rewritten_supply)
*)


let bmc_normalize_file (f: 'a file) (sym_supply : ksym_supply) =
  (* Rename user variables that are repeated *)

  let (f, sym_supply) = ssa_file f sym_supply in

  let (>>=) = Exception.except_bind in

  (*
  pp_file f;
  print_endline "HERE";
  match Core_typing.typecheck_program f  with
   | Result _ -> assert false
   | Exception s -> assert false
  ;
  *)
  bmc_debug_print 1 "INLINING FUNCTION CALLS";
  let (inlined_file, inlined_supply) = inline_file f sym_supply in

  if g_print_files then
    (pp_file inlined_file; 
     print_string "\n"
    );

  bmc_debug_print 1 "Rewriting Ivmin/Ivmax/issigned/etc \n";

  let (rewritten_file, rewritten_supply) = 
    rewrite_file inlined_file inlined_supply in

  (rewritten_file, rewritten_supply)
