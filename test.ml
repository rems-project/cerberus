open Pipeline
let (>>=)  = Exception.except_bind
let return = Exception.except_return


let impl_file =
  "gcc_4.9.0_x86_64-apple-darwin10.8.0"


let conf = {
  debug_level= 0;
  pprints= [];
  astprints= [];
  ppflags= [];
  typecheck_core= true;
  rewrite_core= false;
  sequentialise_core= false;
  cpp_cmd= "";
  cpp_stderr= false;
}


let io =  {
  pass_message= begin fun _ -> Exception.except_return () end;
  set_progress= begin fun _ -> Exception.except_return () end;
  run_pp= begin fun _ _ -> Exception.except_return () end;
  print_endline= begin fun _ -> Exception.except_return () end;
  print_debug= begin fun _ _ -> Exception.except_return () end;
  warn= begin fun _ -> Exception.except_return () end;
}


let () =
  let act =
    load_core_stdlib ()                  >>= fun core_stdlib ->
    load_core_impl core_stdlib impl_file >>= fun core_impl   ->
    core_frontend (conf,io) (core_stdlib, core_impl)
        "/Users/catzilla/Sandbox/test.core" >>= Core_typing.typecheck_program in
  match act with
    | Exception.Result file ->
        print_endline begin
          Pp_utils.to_plain_pretty_string (Pp_core.Basic.pp_file file)
        end;
        print_endline "============================================================================================";
        let file' = Core_unstruct.explode_file file in
        print_endline begin
          Pp_utils.to_plain_pretty_string (Pp_core.Basic.pp_file file')
        end
(*        let Some sym = file.main in
        begin match Pmap.lookup sym file.funs with
          | Some (Proc (_, _, _, e)) ->
          | _ ->
              ()
        end
*)
    | _ ->
        print_endline "FAIL"
