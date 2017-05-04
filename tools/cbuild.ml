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
  sprintf "--cpp=\"cc -E -nostdinc -undef -I %s -I %s %s\""
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

let run x = Sys.command x |> ignore

let copy ?path:(path="$CERB_PATH") src dest =
  sprintf "cp -f %s/%s %s" path src dest |> run

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
  copy "ocaml_generated/*.{ml,mli}" src_path;
  copy "pprinters/*.{ml,mli}" src_path;
  copy "src/codegen/*.ml" src_path;
  copy "src/*.{ml,mli}" src_path;
  copy "parsers/coreparser/core_parser_util.ml" src_path;
  create_tags ();
  create_merlin ()

let run_ocamlbuild filename =
  Sys.chdir cbuild_path;
  (* Check stdCore.ml exists, otherwise create *)
  if not (Sys.file_exists "stdCore.ml") then
    sprintf "cerberus --ocaml-corestd" |> run;
  sprintf
    "ocamlbuild -pkgs pprint,zarith -libs nums,unix,str %s" filename |> run;
  sprintf
    "cp -L %s/%s %s/%s" cbuild_path filename cur_path filename |> run

let build filename mode =
  let basename = Filename.basename (chop_extension filename) in
  copy ~path:cur_path (basename ^ ".ml") cbuild_path;
  run_ocamlbuild (basename ^ mode)


let check_and_build () =
  if not (Sys.file_exists cbuild_path) || not (Sys.is_directory cbuild_path) then (
    Unix.mkdir cbuild_path perm;
    Unix.mkdir src_path perm;
    create_cbuild ()
  )

(* Flags *)
let csmith = ref false

let set_force () =
  sprintf "rm -rf %s" cbuild_path |> run

let rm_stdcore () =
  try Sys.remove (cbuild_path ^ "/stdCore.ml") with _ -> ()

let set_basic_mem () =
  check_and_build ();
  sprintf
    "sed -i '' 's/Defacto\\_memory\\_types/Basic\\_mem\\_types/g' %s/*.{ml,mli}"
    src_path |> run;
  sprintf
    "sed -i '' 's/Defacto\\_memory/Basic\\_mem/g' %s/*.{ml,mli}"
    src_path |> run;
  sprintf
    "sed -i '' 's/defacto\\_memory/basic\\_mem/g' %s/pp_mem.ml"
    src_path |> run

let main arg =
  check_and_build();
  let filename = cur_path ^ "/" ^ arg in
  (match extension filename with
   | ".c" ->
     let args = if !csmith then cpp_cmd csmith_args else "" in
     if cerberus args filename = 0 then (
       build filename ".native"
     ) else (
       fprintf stderr "Cerberus failed!"; exit 1
     )
   | ".ml"
   | ".native" -> build filename ".native"
   | ".byte" -> build filename ".byte"
   | _ -> fprintf stderr "Unknown action for file: %s" filename; exit 1
  )

let () =
  let spec = [
    ("--corestd", Arg.Unit rm_stdcore, "Rebuild StdCore.ml");
    ("--basic", Arg.Unit set_basic_mem, "Use basic memory model");
    ("-f", Arg.Unit set_force, "Force the creation of _cbuild");
    ("--csmith", Arg.Set csmith, "Add necesary flags to run csmith files");
    ("--clean", Arg.Unit set_force, "Clean cbuild files")
  ] in
  let usage = "Ocaml wrapper for Cerberus: cbuild [file.{c,ml,native,byte}]" in
  Arg.parse spec main usage