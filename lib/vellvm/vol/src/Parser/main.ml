open Printf
open Llvm

let debug = false

let metadata_to_file (md:Sub_tv_infer.flnbeps) (addr:Sub_tv_infer.fabes) 
  (fn:string): unit =
  let fo = open_out_gen [Open_creat;Open_trunc;Open_wronly] 0o666 fn in
  List.iter (fun (fid, lnbeps) ->
    List.iter (fun (lb, nbeps) ->
      List.iter (fun (i, beps) ->
        List.iter (fun (((b, e), p),im) ->
          output_string fo (Printf.sprintf "%s %s %i %s %s %s %b\n" fid lb 
            (Camlcoq.camlint_of_nat i) b e p im)
	  ) beps
        ) nbeps
      ) lnbeps
    ) md;
  List.iter (fun (fid, abes) ->
    List.iter (fun (ab, ae) ->
        output_string fo (Printf.sprintf "%s entry 0 %s %s -1 true\n" fid ab ae)
      ) abes
    ) addr;
  close_out fo

let main in_filename out_filename =
  let ic = create_context () in
  let imbuf = MemoryBuffer.of_file in_filename in
  let im = Llvm_bitreader.parse_bitcode ic imbuf in
  let ist = SlotTracker.create_of_module im in
  
  (* dump_module im; *)
  (* Llvm_pretty_printer.travel_module ist im; *)
  let coqim = Llvm2coq.translate_module debug ist im in
  (* Coq_pretty_printer.travel_module coqim; *)

  let oc = create_context () in
  let ombuf = MemoryBuffer.of_file out_filename in
  let om = Llvm_bitreader.parse_bitcode oc ombuf in
  let ost = SlotTracker.create_of_module om in

  let coqom = Llvm2coq.translate_module debug ost om in
      
  (* eprintf "EqTV=%b\n" (Eq_tv.tv_module coqim coqom); *)

  let sbom = Sub_tv_def.SBsyntax.of_llvm_module coqom in  
  let md = Sub_tv_infer.metadata_from_module sbom 1000 1000 in
  let addr = Sub_tv_infer.addrofbe_from_module sbom in
  metadata_to_file md addr "metadata.db";
  eprintf "Meta=%b SubTV=%b RSubTV=%b MTV=%b\n" 
    (Sub_tv_infer.validate_metadata_from_module sbom md)
    (Sub_tv.tv_module coqim sbom) (Sub_tv.rtv_module coqim sbom) 
    (Sub_tv.mtv_module coqim sbom);
  
  (* Coq2llvm.translate_module coqom; *)
  
  (* write the module to a file *)
  (* if not (Llvm_bitwriter.write_bitcode_file m out_filename) then exit 1; *)
  
  SlotTracker.dispose ist;
  SlotTracker.dispose ost;
  dispose_module im;
  dispose_module om

let () = match Sys.argv with
  | [| _; in_filename; out_filename |] -> main in_filename out_filename
  | _ -> main "Input.bc" "Output.bc"

