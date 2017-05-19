open Util
open Global_ocaml

(* == Environment variables ================================================= *)
let cerb_path = ""

let corelib_path =
  Filename.concat cerb_path "include/core"


(* == Symbol counter for the Core parser ==================================== *)
let core_sym_counter = ref 0


(* == load the Core standard library ======================================== *)
let load_stdlib () =
  let filepath = Filename.concat corelib_path "std.core" in
  if not (Sys.file_exists filepath) then
    error ("couldn't find the Core standard library file\n (looked at: `"
           ^ filepath ^ "').")
  else
    Debug_ocaml.print_debug 5 [] (fun () -> "reading Core standard library from `"
                                  ^ filepath ^ "'.");
    (* An preliminary instance of the Core parser *)
    let module Core_std_parser_base = struct
      include Core_parser.Make (struct
                                 let sym_counter = core_sym_counter
                                 let mode = Core_parser_util.StdMode
                                 let std = Pmap.empty Core_parser_util._sym_compare
                               end)
(*      type token = Core_parser_util.token *)
      type result = Core_parser_util.result
    end in
    let module Core_std_parser =
      Parser_util.Make (Core_std_parser_base) (Lexer_util.Make (Core_lexer)) in
    (* TODO: yuck *)
    match Core_std_parser.parse (Input.file filepath) with
    | Exception.Result (Core_parser_util.Rstd (ailnames, std_funs)) ->
      (ailnames, std_funs)
    | Exception.Result _ ->
      error "while parsing the Core stdlib, the parser didn't recognise\
             it as a stdlib."
    | Exception.Exception (loc, err) ->
      begin match err with
        | Errors.PARSER msg ->
          error ("Core parsing error @ " ^ Pp_errors.location_to_string loc
                 ^ ": " ^ msg)
        | _ ->
          assert false
      end


(* == load the implementation file ============================================ *)
let load_impl core_parse impl_name =
  let iname = Filename.concat corelib_path ("impls/" ^ impl_name ^ ".impl") in
  if not (Sys.file_exists iname) then
    error ("couldn't find the implementation file\n (looked at: `" ^ iname ^ "').")
  else
    (* TODO: yuck *)
    match core_parse (Input.file iname) with
      | Exception.Result (Core_parser_util.Rimpl impl_map) ->
          impl_map
      | Exception.Result (Core_parser_util.Rfile _ | Core_parser_util.Rstd _) ->
          assert false
      | Exception.Exception err ->
          error ("[Core parsing error: impl-file]" ^ Pp_errors.to_string err)


(* use this when calling a pretty printer *)
let run_pp =
  (* TODO(someday): dynamically get the width of the terminal *)
  PPrint.ToChannel.pretty 1.0 150 Pervasives.stdout

let set_progress n =
  Exception.fmap (fun v -> progress_sofar := n; v)


(* == parse a C translation-unit and elaborate it into a Core program =========*)
let c_frontend f =
  (* NOTE: skipping c_preprcessor for the moment *)
  Exception.except_return f
  |> Exception.rbind Cparser_driver.parse
  |> set_progress 10
  |> pass_message "1. C Parsing completed!"
  |> pass_through_test
    (List.mem Cabs !!cerb_conf.pps) (run_pp -| Pp_cabs.pp_translate_unit)
  |> Exception.rbind (fun z ->
      let ret = Cabs_to_ail.desugar !core_sym_counter
          begin
            let (ailnames, std_lib_fun_map) = !!cerb_conf.core_stdlib in
            (ailnames, std_lib_fun_map,
             match !!cerb_conf.core_impl_opt with
             | Some x -> x
             | None -> assert false
            )
          end "main" z
      in ret)
  |> set_progress 11
  |> pass_message "2. Cabs -> Ail completed!"
  |> Exception.rbind (fun (counter, z) ->
      Exception.except_bind
        (ErrorMonad.to_exception
           (fun (loc, err) -> (loc, Errors.AIL_TYPING err))
           (GenTyping.annotate_program z))
        (fun z -> Exception.except_return (counter, z)))
  |> pass_through_test
    (List.mem Ail !!cerb_conf.pps) (run_pp -| Pp_ail.pp_program_with_annot -| snd)
  |> set_progress 12
  |> pass_message "3. Ail typechecking completed!"
  |> Exception.fmap
    (Translation.translate !!cerb_conf.core_stdlib !!cerb_conf.sequentialise
       (match !!cerb_conf.core_impl_opt with Some x -> x | None -> assert false))
  |> set_progress 13
  |> pass_message "4. Translation to Core completed!"

let (>>=) = Exception.except_bind

let backend sym_supply core_file args =
  match !!cerb_conf.exec_mode_opt with
  | None -> 0
  | Some Interactive ->
    print_endline "Interactive mode not yet supported";
    exit 1
  | Some (Exhaustive | Random) ->
    if !!cerb_conf.batch then
      begin
        Exhaustive_driver.batch_drive sym_supply core_file
          ("cmdname" :: args) !!cerb_conf; 0
      end
    else
      (* TODO: temporary hack for the command name *)
      Core.(match Exhaustive_driver.drive sym_supply core_file
                    ("cmdname" :: args) !!cerb_conf with
           | Exception.Result
               (Pexpr (_, PEval (Vloaded (LVspecified (OVinteger ival)))) :: _) ->
             begin
              (* TODO: yuck *)
              try
                int_of_string (String_mem.string_pretty_of_integer_value ival)
              with | _ ->
                Debug_ocaml.warn [] (fun () -> "Return value was not a (simple) \
                                     specified integer");
                0
             end
          | Exception.Result (pe :: _) ->
              Debug_ocaml.warn [] (fun () -> "HELLO> " ^ String_core.string_of_pexpr pe); 0
          | Exception.Result [] ->
              Debug_ocaml.warn [] (fun () -> "BACKEND FOUND EMPTY RESULT");
              0
          | Exception.Exception _ ->
              Debug_ocaml.warn [] (fun () -> "BACKEND FOUND EXCEPTION");
              0
           )

(* NOTE: Supporting only C frontend *)
let pipeline filename args =
  if not (Sys.file_exists filename) then
    error ("The file `" ^ filename ^ "' doesn't exist.");
  let f = Input.file filename in
  Debug_ocaml.print_debug 2 [] (fun () -> "Using the C frontend");
  c_frontend f
  >>= fun ((sym_supply : Symbol.sym UniqueId.supply), core_file) ->
  begin
    if !!cerb_conf.typecheck_core then
      Core_typing.typecheck_program core_file |>
        pass_message "5. Core typechecking completed!" >>= fun _ ->
      Exception.except_return ()
    else
      Exception.except_return ()
  end >>= fun _ ->

  (* TODO: for now assuming a single order comes from indet expressions *)
  let rewritten_core_file = Core_indet.hackish_order
      (if !!cerb_conf.rewrite then
         Core_rewrite.rewrite_file core_file
       else core_file)
  in
  if !!cerb_conf.rewrite && !Debug_ocaml.debug_level >= 5 then
    if List.mem Core !!cerb_conf.pps then begin
      print_endline "BEFORE CORE REWRITE:";
      run_pp $ Pp_core.pp_file core_file;
      print_endline "===================="
    end;

  (* TODO: do the sequentialised properly *)
  if List.mem Core !!cerb_conf.pps then (
    if !!cerb_conf.sequentialise then begin
      Debug_ocaml.warn [] (fun () -> "The normal backend is not actually \
                           using the sequentialised Core");
      match (Core_typing.typecheck_program rewritten_core_file) with
      | Exception.Result z ->
        run_pp $ Pp_core.pp_file (Core_sequentialise.sequentialise_file z);
      | Exception.Exception _ ->
        ();
    end else
      run_pp $ Pp_core.pp_file rewritten_core_file;
    if !!cerb_conf.rewrite && !Debug_ocaml.debug_level >= 5 then
      print_endline "====================";
   );
  Exception.except_return rewritten_core_file
  (*

  if !!cerb_conf.ocaml then
    Core_typing.typecheck_program rewritten_core_file
    >>= Codegen_ocaml.gen filename !!cerb_conf.ocaml_corestd sym_supply
    -| Core_sequentialise.sequentialise_file
  else
    Exception.except_return (backend sym_supply rewritten_core_file args)
*)
let cerberus debug_level cpp_cmd impl_name exec exec_mode pps file_opt progress rewrite
             sequentialise concurrency preEx args ocaml ocaml_corestd batch experimental_unseq typecheck_core =
  Debug_ocaml.debug_level := debug_level;
  (* TODO: move this to the random driver *)
  Random.self_init ();

  (* Looking for and parsing the core standard library *)
  let core_stdlib = load_stdlib () in
  Debug_ocaml.print_success "0.1. - Core standard library loaded.";

  (* An instance of the Core parser knowing about the stdlib functions \
     we just parsed *)
  let module Core_parser_base = struct
    include Core_parser.Make (struct
        let sym_counter = core_sym_counter
        let mode = Core_parser_util.ImplORFileMode
        let std = List.fold_left (fun acc (fsym, _) ->
            match fsym with
            | Symbol.Symbol (_, Some str) ->
              let std_pos =
                {Lexing.dummy_pos with Lexing.pos_fname= "core_stdlib"}
              in Pmap.add (str, (std_pos, std_pos)) fsym acc
            | Symbol.Symbol (_, None) -> acc
          ) (Pmap.empty Core_parser_util._sym_compare) $
                  Pmap.bindings_list (snd core_stdlib)
      end)
    type result = Core_parser_util.result
  end in
  let module Core_parser =
    Parser_util.Make (Core_parser_base) (Lexer_util.Make (Core_lexer)) in
  set_cerb_conf cpp_cmd pps core_stdlib None exec exec_mode Core_parser.parse progress rewrite
    sequentialise concurrency preEx ocaml ocaml_corestd (* TODO *) RefStd batch experimental_unseq typecheck_core;
  
  (* Looking for and parsing the implementation file *)
  let core_impl = load_impl Core_parser.parse impl_name in
  Debug_ocaml.print_success "0.2. - Implementation file loaded.";

  set_cerb_conf cpp_cmd pps ((*Pmap.union impl_fun_map*) core_stdlib) (Some core_impl) exec
    exec_mode Core_parser.parse progress rewrite sequentialise concurrency preEx ocaml ocaml_corestd
    (* TODO *) RefStd batch experimental_unseq typecheck_core;

  match file_opt with
    | None ->
      prerr_endline "No filename given";
      exit 1
    | Some file ->
      match pipeline file args with
      | Exception.Exception err ->
        prerr_endline (Pp_errors.to_string err);
        if progress then
          exit !progress_sofar
        else
          exit 1
      | Exception.Result n -> n
        (*
        if progress then 14 else n *)

(* web wrapper *)

open Lwt
open XmlHttpRequest
open Sys_js

(* folding Lwt monad *)
let foldM xs = List.fold_left (fun m1 m2 -> m1 >>= fun _ -> m2) return_unit xs
let mapM f xs = foldM (List.map f xs)

let download file =
  get file
  >>= fun res ->
  register_file file res.content;
  return_unit

let buffile = "buffer.c"
let libcore = "include/core/std.core"
let impl = "include/core/impls/gcc_4.9.0_x86_64-apple-darwin10.8.0.impl"

(* TODO: add libc files *)
let libc = List.map (fun s -> "include/c/libc/" ^ s) [
  "assert.h";
  "complex.h"
]

let location_to_string loc =
  let string_of_pos pos =
    Printf.sprintf "%s:%d:%d" pos.Lexing.pos_fname pos.Lexing.pos_lnum (1+pos.pos_cnum-pos.pos_bol) in
  match loc with
    | Location_ocaml.Loc_unknown ->
        "unknown location"
    | Location_ocaml.Loc_point pos ->
        string_of_pos pos ^ ":"
    | Location_ocaml.Loc_region (pos1, pos2, _) ->
        (* TODO *)
        string_of_pos pos1 ^ "-" ^ string_of_pos pos2 ^ ":"

let run () = cerberus 0
    "cc -E -nostdinc -undef -I /include/c/libc -I /include/c/posix"
    "gcc_4.9.0_x86_64-apple-darwin10.8.0"
    true Random [Core] (Some buffile) false false
    false false false [] false false true false false

open Core

let rec print_expr e =
  match e with
  | Esave (_, _, e) -> print_expr e
  | Eif (pe1, e2, e3) -> print_expr e2; print_expr e3
  | Ecase (pe, cases) -> List.map snd cases
                         |> List.fold_left (fun _ -> print_expr) ()
  | Esseq (_, e1, e2) -> print_expr e1; print_expr e2
  | End es -> List.fold_left (fun _ -> print_expr) () es
  | Ewseq (_, e1, e2)  -> print_expr e1; print_expr e2
  | Eunseq es -> List.fold_left (fun _ -> print_expr) () es
  | Eaction (Paction (_, Action (loc, _, _))) ->
      prerr_endline "Action:";
      prerr_endline (location_to_string loc)
  | Eloc (loc, e) ->
    prerr_endline (location_to_string loc); print_expr e
  | _ -> ()

let print_core core =
  prerr_endline "Printing Core";
  Pmap.fold begin fun s decl () ->
    match decl with
    | Core.Fun (bty, args, pe) -> ()
    | Core.Proc (bty, args, e) -> print_expr e
    | _ -> ()
  end core.Core.funs ()

let _ =
  List.rev_append libc [libcore; impl; buffile]
  |> mapM download

let string_of_core core=
  let buf = Buffer.create 4096 in
  PPrint.ToBuffer.pretty 1.0 80 buf (Pp_core.pp_file core);
  Buffer.contents buf

let _ =
  Js.export "cerberus"
  (object%js
    method run = run () |> string_of_core
    method log cb = Sys_js.set_channel_flusher stderr cb
    method update c = Sys_js.update_file ~name:buffile ~content:c
    method buffer = Sys_js.file_content buffile
  end)
