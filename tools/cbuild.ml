(* ocamlbuild wrapper for Cerberus *)
open Printf

(* Verify UNIX-like system *)
let () =
  if not Sys.unix then (
    fprintf stderr "Cbuild wrapper only works on unix-like systems.";
    exit 1;
  )

(* Get paths *)
let cerb_path =
  let path = Sys.getenv "CERB_PATH" in
  if path = "" then (
    fprintf stderr "CERB_PATH not defined!";
    exit 1;
  ); path

let fatal_error (msg : string) =
  fprintf stderr "Fatal error: %s" msg; exit 1

let cerberus v args files out =
  let files = String.concat " " files in
  let cmd =
    sprintf "cerberus-ocaml --nolibc %s %s -o %s" args files out in
  if v then print_endline cmd;
  Sys.command cmd

let ocamlc v file =
  let cmd =
    sprintf "OCAMLPATH=$CERB_PATH/_lib ocamlfind ocamlopt $CERB_PATH/backend/driver/_build/common/cerberus_cstubs.o -linkpkg -package pprint,yojson,unix,lem,util,ppx_sexp_conv,sexplib,sibylfs,concrete,rt-ocaml %s -o %s" (file ^ ".ml") file in
  if v then print_endline cmd;
  Sys.command cmd

let rm_tmp v f =
  let cmd = sprintf "rm -rf %s.o %s.cmx %s.cmi" f f f in
  if v then print_endline cmd;
  Sys.command cmd

let cbuild v c args out files =
  (* runs cerberus *)
  if cerberus v args files (out ^ ".ml") != 0 then
    fatal_error "Cerberus failed.";
  if not c then begin
    ignore (ocamlc v out);
    ignore (rm_tmp v out)
  end

(* Command line interface *)

open Cmdliner

let fc =
  let doc = "Run cerberus only, generating '.ml'" in
  Arg.(value & flag & info ["c"] ~doc)

let args =
  let doc = "Pass the arguments $(docv) to cerberus." in
  Arg.(value & opt string "" & info ["args"] ~docv:"ARGS" ~doc)

let verbose =
  let doc = "Verbose mode. It shows all the commands being executed." in
  Arg.(value & flag & info ["v"] ~docv:"ARGS" ~doc)

let output =
  let doc = "Write output to $(docv)." in
  Arg.(value & opt string "a.out" & info ["o"; "output"] ~docv:"FILE" ~doc)

let files =
  let doc = "C files to compile."
  in
  Arg.(non_empty & pos_all file [] & info [] ~docv:"FILE" ~doc)

let cmd_exit = function
  | `Error _ -> exit 1
  | `Ok _
  | `Version
  | `Help -> exit 0

let cbuild_t =
  Term.(const cbuild $ verbose $ fc $ args $ output $ files)

let info =
  let doc = "the Cerberus compiler" in
  Term.info "cbuild" ~version:"%%VERSION%%" ~doc

let () = Term.eval (cbuild_t, info) |> cmd_exit