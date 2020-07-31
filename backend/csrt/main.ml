module CF=Cerb_frontend
module CB=Cerb_backend
open CB.Pipeline
open Setup

let (>>=) = CF.Exception.except_bind
let (>>) m f = m >>= fun _ -> f
let return = CF.Exception.except_return



type core_file = (unit,unit) CF.Core.generic_file
type mu_file = (CF.Ctype.ctype CF.Mucore.mu_funinfo_type,
                CF.Ctype.ctype,
                CF.Core.core_base_type,
                CF.Ctype.ctype CF.Mucore.mu_struct_def,
                CF.Ctype.ctype CF.Mucore.mu_union_def,
                unit) CF.Mucore.mu_file
type file = 
  | CORE of core_file
  | MUCORE of mu_file


let print_file ?(remove_path = false) filename file =
  match file with
  | CORE file ->
     CB.Pipeline.run_pp ~remove_path (Some (filename,"core")) 
       (CF.Pp_core.Basic.pp_file file);
  | MUCORE file ->
     CB.Pipeline.run_pp ~remove_path (Some (filename,"mucore")) 
       (CF.Pp_mucore.Basic_CBT.pp_file None file);


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


type rewrite = core_file -> (core_file, CF.Errors.error) CF.Exception.exceptM
type named_rewrite = string * rewrite


let remove_unspecified : named_rewrite =
  ("unspec_removal",
   fun core_file -> 
   return (CF.Remove_unspecs.rewrite_file core_file))

let partial_evaluation : named_rewrite = 
  ("partial_evaluation", 
   fun core_file -> 
   return (CF.Core_peval.rewrite_file core_file))

let remove_unused : named_rewrite = 
  ("unused_functions_removal",
   fun core_file -> 
   return (CF.Core_remove_unused_functions.remove_unused_functions core_file))

let hackish_order : named_rewrite = 
  ("hackish_order",
   fun core_file -> 
   return (CF.Core_indet.hackish_order core_file))

let sequentialise : named_rewrite = 
  ("sequentialisation",
   fun core_file -> 
   CF.Core_typing.typecheck_program core_file >>= fun core_file ->
   let core_file = CF.Core_sequentialise.sequentialise_file core_file in
   return (CB.Pipeline.untype_file core_file)
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
    ; hackish_order
    ; sequentialise ]
    core_file >>= fun core_file ->
  let mu_file = CF.Core_anormalise.normalise_file core_file in
  print_log_file "after_anf" (MUCORE mu_file);
  print_log_file "back_to_core" (CORE (CF.Mucore_to_core.mu_to_core__file mu_file));
  Colour.do_colour := true;
  return mu_file

let frontend filename = 
  Global_ocaml.(set_cerb_conf false Random false Basic false false false);
  CF.Ocaml_implementation.(set (HafniumImpl.impl));
  load_core_stdlib () >>= fun stdlib ->
  load_core_impl stdlib Setup.impl_name >>= fun impl ->
  match Filename.extension filename with
  | ".c" ->
     c_frontend (conf, io) (stdlib, impl) ~filename >>= fun (_,_,core_file) ->
     CF.Tags.set_tagDefs core_file.CF.Core.tagDefs;
     process core_file
  | ext ->
     failwith (Printf.sprintf "wrong file extension %s" ext)




let main filename debug_level type_debug_level =
  Debug_ocaml.debug_level := debug_level;
  Pp.debug_level := type_debug_level;
  match frontend filename with
  | CF.Exception.Exception err ->
     prerr_endline (CF.Pp_errors.to_string err)
  | CF.Exception.Result core_file ->
     Process.process_and_report core_file


open Cmdliner

let file =
  let doc = "Source C file" in
  Arg.(required & pos ~rev:true 0 (some string) None & info [] ~docv:"FILE" ~doc)

let debug_level =
  (* stolen from backend/driver *)
  let doc = "Set the debug message level for cerberus to $(docv) (should range over [0-3])." in
  Arg.(value & opt int 0 & info ["d"; "debug"] ~docv:"N" ~doc)

let type_debug_level =
  (* stolen from backend/driver *)
  let doc = "Set the debug message level for the type system to $(docv) (should range over [0-3])." in
  Arg.(value & opt int 0 & info ["td"; "type-debug"] ~docv:"N" ~doc)


let () =
  let check_t = Term.(pure main $ file $ debug_level $ type_debug_level) in
  Term.exit @@ Term.eval (check_t, Term.info "csrt")
