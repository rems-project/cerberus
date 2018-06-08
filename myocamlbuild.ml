(*
open Ocamlbuild_plugin
 let () = dispatch Bisect_ppx_plugin.dispatch
*)

open Ocamlbuild_plugin

let () =
  dispatch begin function
  | After_rules ->
      flag_and_dep ["link"; "ocaml"; "link_cstubs"]
        (A "src/cerberus_cstubs.o");
(*
      flag ["link"; "ocaml"; "use_cstubs"]
        (S [A "-ccopt"; A "-Lsrc"]);
*)
  | _ ->
      ()
end
