module A = Cabs
module C = Cil
module F = Frontc
module E = Errormsg

open Cil

let cerb_path =
    try
      Sys.getenv "CERB_PATH"
    with Not_found ->
      prerr_endline "expecting the environment variable CERB_PATH \
                     set to point to the location cerberus.";
      exit 1

let clib_path = Filename.concat cerb_path "include/c/libc"

let c_preprocessing fname =
  let temp_name = (fname ^ ".temp")  in
  let ret = Sys.command
      ("cc -E " ^ fname ^ " > " ^ temp_name)
  in
  if ret <> 0 then (
    prerr_endline "C preprocssor error"; exit 1
  );
  temp_name

class myVisitor (vname: string) = object (self)
  inherit C.nopCilVisitor
  method vinst (i : C.instr) =
    match i with
    | _ -> C.SkipChildren
end


let parseFile (fname: string) : C.file =
  let c_pre_file = c_preprocessing fname in
  let cabs, cil = F.parse_with_cabs c_pre_file () in
  Rmtmps.removeUnusedTemps cil;
  cil

let outputFile (outFile: string) (f : C.file) : unit =
  try
    let c = open_out outFile in
    C.print_CIL_Input := false;
    Stats.time "printCIL"
      (C.dumpFile (!C.printerForMaincil) c outFile) f;
    close_out c
  with _ ->
    E.s (E.error "Couldn't open file %s" outFile)

let processFile (outFile:string) (f:C.file): unit =
  outputFile outFile f

let main () =
  if Array.length Sys.argv < 3 then (
    prerr_endline ("Usage: " ^ Sys.argv.(0) ^ " <file> <output>");
    exit 1
  );
  C.print_CIL_Input := true;
  C.insertImplicitCasts := false;
  C.lineLength := 100000;
  C.warnTruncate := false;
  E.colorFlag := true;
  C.lineDirectiveStyle := None;
  C.useLogicalOperators := true;
  C.useComputedGoto := true;

  Sys.argv.(1)
  |> parseFile
  |> processFile Sys.argv.(2)

;;
begin
  try
    main () 
  with
  | F.CabsOnly -> ()
  | E.Error -> ()
end;
exit (if !E.hadErrors then 1 else 0)