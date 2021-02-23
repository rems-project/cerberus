open Cerb_backend.Pipeline

let impl_name = "gcc_4.9.0_x86_64-apple-darwin10.8.0"

let cpp_str =
    "cc -E -C -Werror -nostdinc -undef -D__cerb__"
    ^ " -I " ^ Cerb_runtime.in_runtime "libc/include"
    ^ " -I " ^ Cerb_runtime.in_runtime "libcore"
    ^ " -DDEBUG"


let conf (* cpp_str *) = 
  { debug_level = 0
  ; pprints = []
  ; astprints = []
  ; ppflags = []
  ; typecheck_core = true
  ; rewrite_core = true
  ; sequentialise_core = true
  ; cpp_cmd = cpp_str
  ; cpp_stderr = true
  }
