open Ocamlbuild_plugin

let () =
  (*Bisect_ppx_plugin.handle_coverage ();*)
  dispatch begin function
  | After_rules ->
      flag_and_dep ["link"; "ocaml"; "link_cstubs"]
        (A "common/cerberus_cstubs.o");
  | _ ->
      ()
end
