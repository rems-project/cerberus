open Cerb_frontend
open Cerb_backend
open Pipeline
open Setup

let (>>=) = Exception.except_bind
let (>>) m f = m >>= fun _ -> f
let return = Exception.except_return


type core_file = (unit,unit) Core.generic_file
type mu_file = (unit,unit) Mucore.mu_file
type file = 
  | CORE of core_file
  | MUCORE of mu_file


let print_file ?(remove_path = false) filename file =
  match file with
  | CORE file ->
     Pipeline.run_pp ~remove_path (Some (filename,"core")) 
       (Pp_core.Basic.pp_file file);
  | MUCORE file ->
     Pipeline.run_pp ~remove_path (Some (filename,"mucore")) 
       (Pp_mucore.Basic.pp_file file);


module Log : sig 
  val print_log_file : string -> file -> unit
end = struct
  let print_count = ref 0
  let print_log_file filename file =
    let count = !print_count in
    print_file ("/tmp/" ^ string_of_int count ^ "__" ^ filename) file;
    print_count := 1 + !print_count;
end

open Log


type rewrite = core_file -> (core_file, Errors.error) Exception.exceptM
type named_rewrite = string * rewrite


let remove_unspecified : named_rewrite =
  ("unspec_removal",
   fun core_file -> 
   return (Remove_unspecs.rewrite_file core_file))

let partial_evaluation : named_rewrite = 
  ("partial_evaluation", 
   fun core_file -> 
   return (Core_peval.rewrite_file core_file))

let remove_unused : named_rewrite = 
  ("unused_functions_removal",
   fun core_file -> 
   return (Core_remove_unused_functions.remove_unused_functions core_file))

let hackish_order : named_rewrite = 
  ("hackish_order",
   fun core_file -> 
   return (Core_indet.hackish_order core_file))

let sequentialise : named_rewrite = 
  ("sequentialisation",
   fun core_file -> 
   Core_typing.typecheck_program core_file >>= fun core_file ->
   let core_file = Core_sequentialise.sequentialise_file core_file in
   return (Pipeline.untype_file core_file)
)

let rec do_rewrites_and_log named_rewrites core_file =
  match named_rewrites with
  | [] -> return core_file
  | (name,rw) :: named_rewrites ->
     rw core_file >>= fun core_file -> 
     print_log_file ("after_" ^ name) (CORE core_file);
     do_rewrites_and_log named_rewrites core_file
  

let process core_file =
  Colour.do_colour := false;
  print_log_file "original" (CORE core_file);
  do_rewrites_and_log
    [ remove_unspecified
    ; partial_evaluation
    ; remove_unused
    ; hackish_order ]
    (* ; sequentialise ] *)
    core_file >>= fun core_file ->
  let mu_file = Core_anormalise.normalise_file core_file in
  print_log_file "after_anf" (MUCORE mu_file);
  print_log_file "back_to_core" (CORE (Mucore.mu_to_core__file mu_file));
  Colour.do_colour := true;
  return mu_file

let frontend filename = 
  Global_ocaml.(set_cerb_conf false Random false Basic false false false);
  Ocaml_implementation.(set (HafniumImpl.impl));
  load_core_stdlib () >>= fun stdlib ->
  load_core_impl stdlib Setup.impl_name >>= fun impl ->
  match Filename.extension filename with
  | ".c" ->
     c_frontend (conf, io) (stdlib, impl) ~filename >>= fun (_,_,core_file) ->
     Tags.set_tagDefs core_file.Core.tagDefs;
     process core_file
  | ext ->
     failwith (Printf.sprintf "wrong file extension %s" ext)




let check filename debug_level =
  match frontend filename with
  | Exception.Exception err ->
     prerr_endline (Pp_errors.to_string err)
  | Exception.Result core_file ->
     Check.check_and_report core_file debug_level


open Cmdliner

let file =
  let doc = "Source C file" in
  Arg.(required & pos ~rev:true 0 (some string) None & info [] ~docv:"FILE" ~doc)

let debug_level =
  (* stolen from backend/driver *)
  let doc = "Set the debug message level to $(docv) (should range over [0-3])." in
  Arg.(value & opt int 0 & info ["d"; "debug"] ~docv:"N" ~doc)


let () =
  let check_t = Term.(pure check $ file $ debug_level) in
  Term.exit @@ Term.eval (check_t, Term.info "csrt")
