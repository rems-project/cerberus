(* ocamlbuild wrapper for Cerberus *)
open Printf

(* Verify UNIX-like system *)
let () =
  if not Sys.unix then (
    fprintf stderr "Cbuild wrapper only works on unix-like systems.";
    exit 1;
  )

let perm = 0o755

(* Get paths *)
let cerb_path =
  let path = Sys.getenv "CERB_PATH" in
  if path = "" then (
    fprintf stderr "CERB_PATH not defined!";
    exit 1;
  ); path

let cur_path = Sys.getenv "PWD"
let cbuild_path = cur_path ^ "/_cbuild"
let src_path = cbuild_path ^ "/src"

let csmith_runtime = cerb_path ^ "/tests/csmith/runtime"
let clib_path = cerb_path ^ "/include/c/libc"
let posix_path = cerb_path ^ "/include/c/posix"

let cpp_cmd args =
  sprintf "--cpp=\"cc -E -nostdinc -undef -I .. -I %s -I %s %s\""
    clib_path posix_path args

let csmith_args =
  sprintf "-I %s -DCSMITH_MINIMAL" csmith_runtime

let cerberus args filename =
  let cmd = sprintf "cerberus --ocaml %s %s" args filename in
  print_endline cmd;
  Sys.command cmd

(* Copied from Filename 4.04 *)
let extension_len name =
  let is_dir_sep s i = s.[i] = '/' in
  let rec check i0 i =
    if i < 0 || is_dir_sep name i then 0
    else if name.[i] = '.' then check i0 (i - 1)
    else String.length name - i0
  in
  let rec search_dot i =
    if i < 0 || is_dir_sep name i then 0
    else if name.[i] = '.' then check i (i - 1)
    else search_dot (i - 1)
  in
  search_dot (String.length name - 1)

let extension name =
  let l = extension_len name in
  if l = 0 then "" else String.sub name (String.length name - l) l

let chop_extension name =
  let l = extension_len name in
  if l = 0 then invalid_arg "Filename.chop_extension"
  else String.sub name 0 (String.length name - l)

let last xs = List.rev xs |> List.hd

let fatal_error (msg : string) =
  fprintf stderr "Fatal error: %s" msg; exit 1

let run x = Sys.command x |> ignore

let copy path src dest =
  sprintf "cp -f %s/%s %s" path src dest |> run

let move src dest =
  sprintf "mv -f %s %s" src dest |> run

let create_file name contents =
  let lines = List.fold_left (sprintf "%s\n%s") "" contents in
  sprintf "echo '%s' > %s/%s" lines cbuild_path name |> run

let create_tags () = create_file "_tags"
    ["true: -traverse";
     "\"src\":include"]

let create_merlin () = create_file ".merlin"
    ["S .";
     "S src";
     "B _build";
     "B _build/src"]

let create_cbuild () =
  copy cerb_path "ocaml_generated/*.{ml,mli}" src_path;
  copy cerb_path "pprinters/*.{ml,mli}" src_path;
  copy cerb_path "parsers/core/core_parser_util.ml" src_path;
  copy cerb_path "src/codegen/*.ml" src_path;
  copy cerb_path "src/*.{ml,mli}" src_path;
  copy cerb_path "parsers/coreparser/core_parser_util.ml" src_path;
  create_tags ();
  create_merlin ()

let run_ocamlbuild file =
  sprintf "ocamlbuild -use-ocamlfind -pkgs pprint,lem,Z3 -libs unix,str %s" file |> run

let run_clink files =
  List.fold_left (fun acc f -> acc ^ chop_extension f ^ ".sym ") "" files
  |> sprintf "clink %s"
  |> run

let build filename mode =
  let basename = Filename.basename (chop_extension filename) in
  copy cur_path (basename ^ ".ml") cbuild_path;
  run_ocamlbuild (basename ^ mode)

let check_and_build fforce =
  if fforce
  || not (Sys.file_exists cbuild_path)
  || not (Sys.is_directory cbuild_path)
  then begin
    Unix.mkdir cbuild_path perm;
    Unix.mkdir src_path perm;
    create_cbuild ()
  end

let rm_cbuild () =
  sprintf "rm -rf %s" cbuild_path |> run

let rm_stdcore () =
  try Sys.remove (cbuild_path ^ "/stdCore.ml") with _ -> ()

let set_basic_mem () =
  sprintf
    "sed -i '' 's/Defacto\\_memory\\_types/Basic\\_mem\\_types/g' %s/*.{ml,mli}"
    src_path |> run;
  sprintf
    "sed -i '' 's/Defacto\\_memory/Basic\\_mem/g' %s/*.{ml,mli}"
    src_path |> run;
  sprintf
    "sed -i '' 's/defacto\\_memory/basic\\_mem/g' %s/pp_mem.ml"
    src_path |> run

let cmdmap (f : 'a -> unit) xs = List.map f xs |> ignore

let is_uppercase c = 'A' <= c && c <= 'Z'

let is_lowercase c = 'a' <= c && c <= 'z'

let is_letter c =
  is_uppercase c || is_lowercase c

let rename_ocaml_mod_name rfile =
  (* Add 'n' if name starts with any symbol *)
  (if is_letter (String.get rfile 0) then rfile else "n" ^ rfile)
  (* - is not supported by Ocaml *)
  |> Str.global_replace (Str.regexp "-") "_"
  (* Rename files if needed *)
  |> fun mfile -> if not (mfile = rfile) then move rfile mfile; mfile

let cbuild c b f basic corestd csmith cargs o rfiles =
  (* check _cbuild *)
  check_and_build f;
  (* set memory model *)
  if basic then set_basic_mem ();
  (* copy source to _cbuild *)
  cmdmap (fun file -> copy cur_path file cbuild_path) rfiles;
  (* change directory *)
  Sys.chdir cbuild_path;
  (* rename unsupported names *)
  let files = List.map rename_ocaml_mod_name rfiles in
  (* get main file *)
  let main = last files |> Filename.basename in
  (* check byte extension *)
  (* Check stdCore.ml exists, otherwise create *)
  if corestd || not (Sys.file_exists "stdCore.ml") then
    sprintf "cerberus --ocaml-corestd" |> run;
  (* runs cerberus *)
  if compare (extension main) ".c" = 0 then begin
    let args = if csmith then cpp_cmd csmith_args else cpp_cmd cargs in
    cmdmap begin fun file ->
        if cerberus args file != 0 then
          fatal_error ("Cerberus failed on file " ^ file)
    end files
  end;
  (* compile *)
  if not c then begin
    let mainext =
      if compare (extension main) ".byte" != 0 then
        chop_extension main ^ if b then ".byte" else ".native" 
      else main
    in
    (* run linker *)
    run_clink files;
    (* run ocamlbuild *)
    run_ocamlbuild mainext;
    (* copy output file *)
    sprintf "cp -L %s/%s %s/%s" cbuild_path mainext cur_path o |> run
  end

(* Command line interface *)

open Cmdliner

let fc =
  let doc = "Run cerberus only, generating '.ml' and '.sym' files." in
  Arg.(value & flag & info ["c"] ~doc)

let fbyte =
  let doc = "Output Ocaml bytecode." in
  Arg.(value & flag & info ["b"; "byte"] ~doc)

let fforce =
  let doc = "Force the re-creation of '_cbuild'" in
  Arg.(value & flag & info ["f"; "force"] ~doc)

let fbasic =
  let doc = "Use basic memory model." in
  Arg.(value & flag & info ["fbasic"] ~doc)

let fcorestd =
  let doc = "Rebuild coreStd.ml" in
  Arg.(value & flag & info ["fcorestd"] ~doc)

let fcsmith =
  let doc = "Add necessary flags to run csmith files." in
  Arg.(value & flag & info ["fcsmith"] ~doc)

let cargs =
  let doc = "Pass the arguments $(docv) for Cerberus C preprocesor." in
  Arg.(value & opt string "" & info ["args"] ~docv:"ARGS" ~doc)

let output =
  let doc = "Write output to $(docv)." in
  Arg.(value & opt string "a.out" & info ["o"; "output"] ~docv:"FILE" ~doc)

let files =
  let doc = "Files to compile. Last file should be \
             the one that implements function 'main'. \
             If $(docv) extension is '.ml', it skips \
             Cerberus ocaml generation. \
             If '.byte', it compiles to Ocaml bytecode."
  in
  Arg.(non_empty & pos_all file [] & info [] ~docv:"FILE" ~doc)

let cmd_exit = function
  | `Error _ -> exit 1
  | `Ok _
  | `Version
  | `Help -> exit 0

let cbuild_t =
  Term.(const cbuild $ fc $ fbyte $ fforce $ fbasic $ fcorestd $ fcsmith
        $ cargs $ output $ files)

let info =
  let doc = "the Cerberus compiler" in
  Term.info "cbuild" ~version:"%%VERSION%%" ~doc

let () = Term.eval (cbuild_t, info) |> cmd_exit