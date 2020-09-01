open Cerb_backend
open Pipeline
open Cerb_frontend.Exception

let return = except_return


let cpp_str =
    "cc -E -C -Werror -nostdinc -undef -D__cerb__"
    ^ " -I " ^ Cerb_runtime.in_runtime "libc/include"
    ^ " -I " ^ Cerb_runtime.in_runtime "libcore"
    ^ " -DDEBUG"

let io =
  let open Pipeline in
  { pass_message = begin
        let ref = ref 0 in
        fun str -> Debug_ocaml.print_success (string_of_int !ref ^ ". " ^ str);
                   incr ref;
                   return ()
      end;
    set_progress = begin
      fun str -> return ()
      end;
    run_pp = begin
      fun opts doc -> run_pp opts doc;
                      return ()
      end;
    print_endline = begin
      fun str -> print_endline str;
                 return ();
      end;
    print_debug = begin
      fun n mk_str -> Debug_ocaml.print_debug n [] mk_str;
                      return ()
      end;
    warn = begin
      fun mk_str -> Debug_ocaml.warn [] mk_str;
                    return ()
      end;
  }


let impl_name = "gcc_4.9.0_x86_64-apple-darwin10.8.0"



let conf (* cpp_str *) = {
    debug_level = 0
  ; pprints = []
  ; astprints = []
  ; ppflags = []
  ; typecheck_core = true
  ; rewrite_core = true
  ; sequentialise_core = true
  ; cpp_cmd = cpp_str
  ; cpp_stderr = true
}
