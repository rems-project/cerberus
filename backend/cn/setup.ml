open Cerb_backend.Pipeline
module StringSet = Set.Make(String)


let io = default_io_helpers

let impl_name = "gcc_4.9.0_x86_64-apple-darwin10.8.0"

(* adapting code from backend/driver/main.ml *)
let cpp_str incl_dirs incl_files =
  String.concat " "
    (["cc -std=c11 -E -CC -Werror -nostdinc -undef -D__cerb__";
      "-I " ^ Cerb_runtime.in_runtime "libc/include";
      "-I " ^ Cerb_runtime.in_runtime "libcore";
      "-include " ^ Cerb_runtime.in_runtime "libc/include/builtins.h"
     ]
     @
       List.map (fun str -> "-I " ^ str) incl_dirs
     @ List.map (fun str -> "-include " ^ str) incl_files
     @
       [" -DDEBUG -DCN_MODE";]

    )

let with_cn_keywords str =
  let cn_keywords =
    [ "predicate"
    ; "lemma"
    ; "function"
    ; "datatype"
    ; "pack"
    ; "unpack"
    ; "pack_struct"
    ; "unpack_struct"
    ; "have"
    ; "show"
    ; "instantiate"
    ]
  in
  List.fold_left (fun acc kw ->
    acc ^ " -D" ^ kw ^ "=__cerb_" ^ kw
  ) str cn_keywords


let conf incl_dirs incl_files astprints =
  { debug_level = 0
  ; pprints = []
  ; astprints = astprints
  ; ppflags = []
  ; ppouts = []
  ; typecheck_core = true
  ; rewrite_core = true
  ; sequentialise_core = true
  ; cpp_cmd = with_cn_keywords (cpp_str incl_dirs incl_files)
  ; cpp_stderr = true
  }

let unfold_proxies = StringSet.of_list [
    "ffs_proxy"; "ffsl_proxy"; "ffsll_proxy"; "ctz_proxy";
  ]

let unfold_stdlib_name s = StringSet.mem s unfold_proxies

