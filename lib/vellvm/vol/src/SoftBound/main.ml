open Interpreter
(* open Sb_db_trans *)
open Sb_ds_trans
open Printf
open Llvm
open Trace

let nosbpass = ref false

let main in_filename =
  (* Read bitcode [in_filename] into LLVM module [im] *)
  let ic = global_context () in
  let imbuf = MemoryBuffer.of_file in_filename in
  let im = Llvm_bitreader.parse_bitcode ic imbuf in
  let ist = SlotTracker.create_of_module im in

  (* Print [im] by LLVM pinter *)
  (if !Globalstates.debug then dump_module im);
  (* Print [im] by My pinter *)
  (if !Globalstates.debug then Llvm_pretty_printer.travel_module ist im);
  (* Translate LLVM module [im] to Coq module [coqim] *)
  let coqim = Llvm2coq.translate_module !Globalstates.debug ist im in
  (* Print [coqim] *)
  (if !Globalstates.debug then Coq_pretty_printer.travel_module coqim);

  (if !nosbpass then 
    (* Translate [coqim] to a *.ll file *)
    Coq2ll.travel_module coqim
  else
    (* Instrument [coqim], output [coqom]  *)
    match SB_ds_pass.trans_module coqim with
    | Some coqom -> 
       (* Print [coqom] *)
       (if !Globalstates.debug then Coq_pretty_printer.travel_module coqom);
       (* Translate [coqom] to a *.ll file *)
       Coq2ll.travel_module coqom
    | None -> failwith "failed");

  SlotTracker.dispose ist;
  dispose_module im

let () = match Sys.argv with
  | [| _; "-d" ; in_filename |] -> 
       Globalstates.debug := true; main in_filename
  | [| _; "-no-sbpass" ; in_filename |] -> 
       nosbpass := true; main in_filename
  | [| _; in_filename |] -> main in_filename
  | _ -> main "input.bc"
