module CF=Cerb_frontend
module CB=Cerb_backend
open CB.Pipeline

module CA=CF.Core_anormalise

let (>>=) = CF.Exception.except_bind
let (>>) m f = m >>= fun _ -> f
let return = CF.Exception.except_return



type core_file = (unit,unit) CF.Core.generic_file
type mu_file = (CA.ft, CA.lt, CA.ct, CA.bt,
                CA.ct CF.Mucore.mu_struct_def,
                CA.ct CF.Mucore.mu_union_def,
                unit) CF.Mucore.mu_file
type file = 
  | CORE of core_file
  | MUCORE of mu_file







let io =
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


open Setup



let print_file ?(remove_path = false) filename file =
  match file with
  | CORE file ->
     CB.Pipeline.run_pp ~remove_path (Some (filename,"core")) 
       (CF.Pp_core.WithLocations.pp_file file);
  | MUCORE file ->
     CB.Pipeline.run_pp ~remove_path (Some (filename,"mucore")) 
       (CF.Pp_mucore.WithLocations_standard_typ.pp_file None file);


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
   return (CF.Core_remove_unused_functions.remove_unused_functions true core_file))

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
  let mu_file = CF.Mucore_inline_break.ib_file mu_file in
  print_log_file "after_inlining_break" (MUCORE mu_file);
  Colour.do_colour := true;
  return mu_file

let frontend filename = 
  Global_ocaml.(set_cerb_conf false Random false Basic false false false false);
  CF.Ocaml_implementation.(set (HafniumImpl.impl));
  load_core_stdlib () >>= fun stdlib ->
  load_core_impl stdlib impl_name >>= fun impl ->
  c_frontend (conf, io) (stdlib, impl) ~filename >>= fun (_,_,core_file) ->
  CF.Tags.set_tagDefs core_file.CF.Core.tagDefs;
  process core_file






let main filename jsonfile debug_level print_level =
  if debug_level > 0 then Printexc.record_backtrace true else ();
  Debug_ocaml.debug_level := debug_level;
  Pp.print_level := print_level;
  if not (Sys.file_exists filename) then
    CF.Pp_errors.fatal ("file \""^filename^"\" does not exist")
  else if not (String.equal (Filename.extension filename) ".c") then
    CF.Pp_errors.fatal ("file \""^filename^"\" has wrong file extension")
  else
    let json_channel = Pp.maybe_open_channel jsonfile in
    try
      begin match frontend filename with
      | CF.Exception.Exception err ->
         prerr_endline (CF.Pp_errors.to_string err);
         Pp.maybe_close_channel json_channel;
         exit 1
      | CF.Exception.Result file ->
         if !Pp.print_level > 0 then Printexc.record_backtrace true else ();
         match Process.process file with
         | Ok () -> 
            Pp.maybe_close_channel json_channel;
            exit 0
         | Error (loc,ostacktrace,err) ->
            TypeErrors.report loc ostacktrace err;
            Pp.maybe_close_channel json_channel;
            exit 1
      end
    with
    | exc -> 
       Pp.maybe_close_channel json_channel; 
       raise exc


open Cmdliner


(* some of these stolen from backend/driver *)
let file =
  let doc = "Source C file" in
  Arg.(required & pos ~rev:true 0 (some string) None & info [] ~docv:"FILE" ~doc)

let debug_level =
  let doc = "Set the debug message level for cerberus to $(docv) (should range over [0-3])." in
  Arg.(value & opt int 0 & info ["d"; "debug"] ~docv:"N" ~doc)

let print_level =
  let doc = "Set the debug message level for the type system to $(docv) (should range over [0-3])." in
  Arg.(value & opt int 0 & info ["p"; "print-level"] ~docv:"N" ~doc)

let json_file =
  let doc = "Output typing context information to JSON file" in
  Arg.(value & opt (some string) None & info ["json"] ~doc)


let () =
  let check_t = Term.(pure main $ file $ json_file $ debug_level $ print_level) in
  Term.exit @@ Term.eval (check_t, Term.info "csrt")
