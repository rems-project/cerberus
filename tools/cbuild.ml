(* ocamlbuild wrapper for Cerberus *)

let perm = 0o755
let cur_path = Sys.getenv "PWD"
let cbuild_path = cur_path ^ "/_cbuild"
let src_path = cbuild_path ^ "/src"

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
  Printf.sprintf "cp -f %s/%s %s" path src dest |> run

let create_tags () =
  let tags =
    ["true: -traverse";
     "\"src\":include"]
    |> List.fold_left (Printf.sprintf "%s\n%s") ""
  in Printf.sprintf "echo '%s' > %s/_tags" tags cbuild_path |> run

let create_cbuild () =
  let cerb_path = Sys.getenv "CERB_PATH" in
  if cerb_path = "" then (
    Printf.fprintf stderr "CERB_PATH not defined!";
    exit 1;
  ) else (
    copy "ocaml_generated/*.{ml,mli}" src_path;
    copy "pprinters/*.{ml,mli}" src_path;
    copy "src/codegen/*.ml" src_path;
    copy "src/*.{ml,mli}" src_path;
    copy "parsers/coreparser/core_parser_util.ml" src_path;
    create_tags ()
  )

let ocamlbuild filename =
  Sys.chdir cbuild_path;
  (* Check stdCore.ml exists, otherwise create *)
  if not (Sys.file_exists "stdCore.ml") then
    Printf.sprintf "cerberus --ocaml-corestd" |> run;
  Printf.sprintf
    "ocamlbuild -pkgs pprint,zarith -libs nums,unix,str %s" filename |> run;
  Printf.sprintf
    "ln -sf %s/%s %s/%s" cbuild_path filename cur_path filename |> run

let build filename mode =
  let basename = Filename.basename (chop_extension filename) in
  copy ~path:cur_path (basename ^ ".ml") cbuild_path;
  ocamlbuild (basename ^ mode)

let cerberus filename =
  Printf.sprintf "cerberus --ocaml %s" filename |> Sys.command

let () =
  (* Check if UNIX system *)
  if not Sys.unix then (
    Printf.fprintf stderr "Cbuild wrapper only works on unix-like systems.";
    exit 1;
  );
  (* Check and create _cbuild directory *)
  if not (Sys.file_exists cbuild_path) || not (Sys.is_directory cbuild_path) then (
    Unix.mkdir cbuild_path perm;
    Unix.mkdir src_path perm;
    create_cbuild ()
  );
  (* Check and compile file *)
  if Array.length Sys.argv > 1 then (
    let filename = cur_path ^ "/" ^ Sys.argv.(1) in
    (match extension filename with
     | ".c" ->
       if cerberus filename = 0 then (
         build filename ".native"
       ) else (
         Printf.fprintf stderr "Cerberus failed!"; exit 1
       )
     | ".ml"
     | ".native" -> build filename ".native"
     | ".byte" -> build filename ".byte"
     | _ -> Printf.fprintf stderr "Unknown action for file: %s" filename; exit 1
    )
  )