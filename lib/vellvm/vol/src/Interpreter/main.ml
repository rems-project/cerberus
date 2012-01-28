open Opsem
open Dopsem
open Interpreter
open Printf
open Llvm
open Llvm_executionengine
open Trace

let interInsnLoop (cfg:OpsemAux.coq_Config) (s0:Opsem.coq_State) (tr0:trace) 
  : (Opsem.coq_State*trace) option =
  
  let s = ref s0 in
  let n = ref 0 in
  
  while not (Opsem.s_isFinialState coq_DGVs !s) do
    (if !Globalstates.debug then (eprintf "n=%d\n" !n;   flush_all()));    
    match interInsn cfg !s with
    | Some (s', _) ->
      begin 
        s := s';
        n := !n + 1
      end 
    | None -> failwith "Stuck!" 
  done;
  
  Some (!s, Coq_trace_nil)
  
let rec interInsnStar (cfg:OpsemAux.coq_Config) (s:Opsem.coq_State) (tr:trace) 
  (n:int) : (Opsem.coq_State*trace) option =
  if (Opsem.s_isFinialState coq_DGVs s) 
  then 
    begin
      (if !Globalstates.debug then (eprintf "Done!\n";flush_all()));
      Some (s, tr)
    end      
  else
    if n > 0 
    then
      begin
      (if !Globalstates.debug then (eprintf "n=%d\n" n;   flush_all()));    
      match interInsn cfg s with
      | Some (s', tr') -> interInsnStar cfg s' (trace_app tr tr') (n-1)  
      | None ->
        eprintf "Stuck!\n";flush_all(); 
        None
      end
    else 
      begin
        eprintf "Time up!\n";flush_all();
        Some (s, tr)
      end        
      
let main in_filename argv =

        let ic = global_context () in
        let imbuf = MemoryBuffer.of_file in_filename in
        let im = Llvm_bitreader.parse_bitcode ic imbuf in
        let ist = SlotTracker.create_of_module im in
        let imp = ModuleProvider.create im in

        (if !Globalstates.debug then dump_module im);
        (if !Globalstates.debug then Llvm_pretty_printer.travel_module ist im);
        let coqim = Llvm2coq.translate_module !Globalstates.debug ist im in
        (if !Globalstates.debug then Coq_pretty_printer.travel_module coqim);

        let li = ExecutionEngine.create_interpreter imp in

        let print() = Array.iter print_endline argv in
        
        if !Globalstates.debug then 
          (eprintf "main runs with arguments: \n"; print(); flush_all());

        let gargvs = (GenericValue.of_int 
                      (Llvm.integer_type ic 32) (Array.length argv))::
                      ExecutionEngine.to_argv argv ic li::
                      [] in

        (* FIXME: We need to call ctors/dtors before/after execution *)
        (* Do we also need to formalize them in Coq? They are implemented by*)
        (* llvm.global_ctors/llvm.global_dtors. Are they target-independent? *)
        ExecutionEngine.run_static_ctors li;

        (match Opsem.s_genInitState coq_DGVs (coqim::[]) "@main" 
          (Obj.magic gargvs) (li, im) with
          | Some (cfg, s) -> 
            (match interInsnLoop cfg s Coq_trace_nil with
              | Some (s', tr) -> (); ExecutionEngine.run_static_dtors li
              | None -> () )
          | None -> () );
        
        SlotTracker.dispose ist;
        ExecutionEngine.dispose li

let _ = let len = Array.length Sys.argv in
  
        if len < 1 then
          failwith "# of argv is 0";
                          
        let idx = ref 1 in        
        let set_flags = fun _ ->
          let finished = ref false in  
          while (not !finished) && (!idx < len) do
            let arg = Array.get Sys.argv !idx in
            
            if arg = "-d" then 
              Globalstates.debug := true;
          
            if String.get arg 0 != '-' 
            then
              finished := true
            else  
              idx := !idx + 1                     
          done in
                                
        set_flags ();
                                                                
        if !idx < len then
          main (Array.get Sys.argv !idx) (Array.sub Sys.argv !idx (len - !idx))
        else
          main "Input.bc" (Array.make 1 "")    
