open Ocamlbuild_plugin;;

ocaml_lib ~extern:true "llvm";;
ocaml_lib ~extern:true "llvm_analysis";;
ocaml_lib ~extern:true "llvm_executionengine";;
ocaml_lib ~extern:true "llvm_target";;
ocaml_lib ~extern:true "llvm_bitreader";;
ocaml_lib ~extern:true "llvm_bitwriter";;
ocaml_lib ~extern:true "llvm_scalar_opts";;
ocaml_lib ~extern:true "ssa_def";;
ocaml_lib ~extern:true "ssa_lib";;
ocaml_lib ~extern:true "ssa_dynamic";;
ocaml_lib ~extern:true "trace";;
ocaml_lib ~extern:true "str";; 
ocaml_lib ~extern:true "coqllvm";;
ocaml_lib ~extern:true "globalstates";;
ocaml_lib ~extern:true "eq_tv";;
(* adding str before sub_tv is important, because sub_tv needs str, and
 * ocamlbuild links libs in term of the order in the file. *)
ocaml_lib ~extern:true "sub_tv";;
ocaml_lib ~extern:true "sb_db_trans";;
ocaml_lib ~extern:true "gvn";;

flag ["link"; "ocaml"; "g++"] (S[A"-cc"; A"g++"]);;
dep ["link"; "ocaml"; "use_bindings"] ;;
