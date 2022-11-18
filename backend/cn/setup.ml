open Cerb_backend.Pipeline


let io =
  let return = Cerb_frontend.Exception.except_return in
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

(* adapting code from backend/driver/main.ml *)
let cpp_str incl_dirs =
  String.concat " " 
    (["cc -std=c11 -E -CC -Werror -nostdinc -undef -D__cerb__";
      "-I " ^ Cerb_runtime.in_runtime "libc/include";
      "-I " ^ Cerb_runtime.in_runtime "libcore";]
     @
       List.map (fun str -> "-I " ^ str) incl_dirs
     @
       [" -DDEBUG -DCN_MODE";]
    )

let with_cn_keywords str =
  let cn_keywords =
    [ "predicate"
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


let conf incl_dirs astprints = 
  { debug_level = 0
  ; pprints = []
  ; astprints = astprints
  ; ppflags = []
  ; typecheck_core = true
  ; rewrite_core = true
  ; sequentialise_core = true
  ; cpp_cmd = with_cn_keywords (cpp_str incl_dirs)
  ; cpp_stderr = true
  }
