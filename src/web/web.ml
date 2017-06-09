open Global_ocaml
open Util
open Frontend
open Lwt
open XmlHttpRequest
open Sys_js

(* folding Lwt monad *)
let foldM xs = List.fold_left (fun m1 m2 -> m1 >>= fun _ -> m2) return_unit xs
let mapM f xs = foldM (List.map f xs)

(* External JS wrap *)
let setupFS () =
  Js.Unsafe.fun_call (Js.Unsafe.variable "setupFS") [||] |> ignore

let saveFile ~name ~content =
  [| Js.Unsafe.inject $ Js.string name; Js.Unsafe.inject $ Js.string content |]
  |> Js.Unsafe.fun_call (Js.Unsafe.variable "saveFile")
  |> ignore

(* returns a string *)
let readFile name =
  [| Js.Unsafe.inject $ Js.string name |]
  |> Js.Unsafe.fun_call (Js.Unsafe.variable "readFile")

let invokeCpp input =
  [| Js.Unsafe.inject $ Js.string input |]
  |> Js.Unsafe.fun_call (Js.Unsafe.variable "invokeCpp")

let onLoadCerberus () =
  Js.Unsafe.fun_call (Js.Unsafe.variable "onLoadCerberus") [||]

let download fs_save filename =
  get filename
  >>= fun res ->
  fs_save ~name:filename ~content:res.content;
  return_unit

let buffile = "../buffer.c"
let libcore = "../include/core/std.core"
let impl = "../include/core/impls/gcc_4.9.0_x86_64-apple-darwin10.8.0.impl"

let libc = List.map (fun s -> "../include/c/libc/" ^ s) [
    "complex.h";
    "inttypes.h";
    "setjump.h";
    "stdbool.h";
    "stdnoreturn.h";
    "uchar.h";
    "ctype.h";
    "iso646.h";
    "signal.h";
    "stddef.h";
    "string.h";
    "wchar.h";
    "errno.h";
    "limits.h";
    "stdalign.h";
    "stdint.h";
    "tgmath.h";
    "wctype.h";
    "fenv.h";
    "locale.h";
    "stdarg.h";
    "stdio.h";
    "threads.h"
]

let posix = List.map (fun s -> "../include/c/posix/" ^ s) [
    "stdio.h";
  ]

let exec exhaustive =
  let mode = if exhaustive then Exhaustive else Random in
  Tags.reset_tagDefs();
  cerberus 0 "" "gcc_4.9.0_x86_64-apple-darwin10.8.0"
    true mode [] (Some buffile) false false
    false false false [] false false true false false

let string_of_core core=
  let buf = Buffer.create 4096 in
  PPrint.ToBuffer.pretty 1.0 80 buf (Pp_core.pp_file false core);
  Buffer.contents buf

type ('a, 'b) result = Success of 'a | Fail of 'b

let run source exhaustive =
  let js_stderr = ref "" in
  let js_stdout = ref "" in
  set_channel_flusher stderr (fun s -> js_stderr := !js_stderr ^ s);
  set_channel_flusher stdout (fun s -> js_stdout := !js_stdout ^ s);
  let cpp_source = invokeCpp source in
  update_file ~name:buffile ~content:cpp_source;
  match exec exhaustive with
  | Some file -> Success (string_of_core file, js_stdout)
  | None -> Fail (!js_stderr)

let _ =
  setupFS();
  (* Download files to js_of_ocaml FS *)
  mapM (download register_file) [buffile; libcore; impl]
  >>= fun _ ->
  (* Download files to mcpp.js FS *)
  mapM (download saveFile) libc
  >>= fun _ ->
  mapM (download saveFile) posix
  >>= fun _ ->
  return $ onLoadCerberus ()

let _ =
  Js.export "cerberus"
  (object%js
    method run source exhaustive = run source exhaustive
    method buffer = file_content buffile
  end)
