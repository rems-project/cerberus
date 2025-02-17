open Cerb_backend.Pipeline
module StringSet = Set.Make (String)

let io = default_io_helpers

let impl_name = "gcc_4.9.0_x86_64-apple-darwin10.8.0"

(* adapting code from backend/driver/main.ml *)
let cpp_str macros_def incl_dirs incl_files =
  String.concat
    " "
    ([ "cc -std=c11 -E -CC -Werror -nostdinc -undef -D__cerb__";
       "-I " ^ Cerb_runtime.in_runtime "libc/include";
       "-I " ^ Cerb_runtime.in_runtime "libcore";
       "-include " ^ Cerb_runtime.in_runtime "libc/include/builtins.h"
     ]
     @ List.map
         (function
           | str1, None -> "-D" ^ str1 | str1, Some str2 -> "-D" ^ str1 ^ "=" ^ str2)
         macros_def
     @ List.map (fun str -> "-I " ^ str) incl_dirs
     @ List.map (fun str -> "-include " ^ str) incl_files
     @ [ " -DDEBUG -DCN_MODE" ])


let conf macros incl_dirs incl_files astprints save_cpp =
  { debug_level = 0;
    pprints = [];
    astprints;
    ppflags = [];
    ppouts = [];
    typecheck_core = true;
    rewrite_core = true;
    sequentialise_core = true;
    cpp_cmd = cpp_str macros incl_dirs incl_files;
    cpp_stderr = true;
    cpp_save = save_cpp
  }
