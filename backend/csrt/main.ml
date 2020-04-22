open Cerb_frontend
open Cerb_backend
open Pipeline

let (>>=) = Exception.except_bind
let (>>) m f = m >>= fun _ -> f
let return = Exception.except_return

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


let conf cpp_str = {
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




let print_core_file core_file filename = 
  let pp = Pp_core.Basic.pp_file core_file in
  Pipeline.run_pp (Some (filename,"core")) pp

let print_mu_core_file mu_file filename = 
  let pp = Pp_mucore.Basic.pp_file mu_file in
  Pipeline.run_pp (Some (filename,"core")) pp


(* let pcff core_file_name core_file = 
 *   print_endline (Printf.sprintf "%s.funinfo: %d entries" 
 *     core_file_name
 *     (List.length (Pmap.bindings_list core_file.Core.funinfo))) *)

let process core_file0 =
  Colour.do_colour := false;
  print_core_file core_file0 "0_original";
  let core_file1 = Core_peval.rewrite_file core_file0 in
  print_core_file core_file1 "1_after_peval";
  let core_file2 = Core_remove_unused_functions.remove_unused_functions core_file1 in
  print_core_file core_file2 "2_after_removing_unused_functions";
  let mu_file3 = Core_anormalise.normalise_file core_file2 in
  print_mu_core_file mu_file3 "3_after_anf";
  print_core_file (Mucore.mu_to_core__file mu_file3) "4_back_to_core";
  Colour.do_colour := true;
  return mu_file3

let frontend conf filename = 
  Global_ocaml.(set_cerb_conf false Random false Basic false false false);
  Ocaml_implementation.(set (HafniumImpl.impl));
  load_core_stdlib () >>= fun stdlib ->
  load_core_impl stdlib impl_name >>= fun impl ->
  match Filename.extension filename with
  | ".c" ->
     c_frontend (conf, io) (stdlib, impl) ~filename >>= fun (_,_,core_file) ->
     Tags.set_tagDefs core_file.Core.tagDefs;
     process core_file
  | ".core" ->
     core_frontend (conf, io) (stdlib, impl) ~filename >>= fun core_file ->
     process core_file
  | ext ->
     failwith (Printf.sprintf "wrong file extension %s" ext)



let cpp_str =
    "cc -E -C -Werror -nostdinc -undef -D__cerb__"
  ^ " -I$(HOME)/Sources/rems-project/cerberus-private/runtime/libc/include"
  ^ " -DDEBUG"




let check filename =
  match frontend (conf cpp_str) filename with
  | Exception.Exception err ->
     prerr_endline (Pp_errors.to_string err)
  | Exception.Result core_file ->
     Check.check_and_report core_file


open Cmdliner

let file =
  let doc = "source C file" in
  Arg.(required & pos ~rev:true 0 (some string) None & info [] ~docv:"FILE" ~doc)


let () =
  let check_t = Term.(pure check $ file) in
  Term.exit @@ Term.eval (check_t, Term.info "csrt")
