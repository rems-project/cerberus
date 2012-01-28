(* This function used at the proof to generate a fresh atom, which should not be used at runtime. *)
let atom_fresh_for_list a = failwith "AtomImpl.atom_fresh_for_list cannot be used at runtime"

(* These conversion functions are very efficient, because the machine representation of
   nat is not practice. We should figure out if we can remove these functions later... *)
let int2nat i = failwith "int2nat is undef"

let nat2int i = failwith "nat2int is undef"

let llapint2nat i = failwith "llapint2nat is undef"

let nat2llapint i = failwith "nat2llapint is undef"

(* The functions below use the above conversion functions, I hope we wont use them at runtime. *)
let nth_list_typ i lt = failwith "nth_list_typ cannot be used at runtime"

let getCmdTyp c = failwith "getCmdtyp cannot be used at runtime"

let getTyp c = failwith "getTyp cannot be used at runtime"

let getPrimitiveSizeInBits t = failwith "getPrimitiveSizeInBits cannot be used at runtime"

let getNumElements t = failwith "getNumElements cannot be used at runtime"

(* Sub TV *)
let callLib m fid1 gvs = failwith "callLib: unreachable"

let isSysLib fid =
  match Coq_pretty_printer.getRealName fid with
    | "printf" | "__assert_fail" | "fprintf" | "vfprintf" | "_IO_putc"
    | "llvm.va_start" | "llvm.va_end" | "llvm.memset.i32" -> true
    | _ -> false

let isCallLib fid =
  match Coq_pretty_printer.getRealName fid with
    | "__loadDereferenceCheck"
    | "__shrinkBounds"
    | "__callDereferenceCheck"
    | "__storeDereferenceCheck"
    | "__memcopyCheck_i64"
    | "__memcopyCheck"
    | "__hashStoreBaseBound"
    | "__hashProbeAddrOfPtr"
    | "__hashLoadBaseBound"
    | "__hashLoadBase"
    | "__hashLoadBound"
    | "__softbound_abort"
    | "__softbound_printf"
    | "__softbound_global_init"
    | "__softbound_init" 
    | "__softbound_trie_allocate"
    | "__softboundcetswithss_copy_metadata"
    | "__softboundcetswithss_store_base_shadow_stack"
    | "__softboundcetswithss_store_bound_shadow_stack"
    | "__softboundcetswithss_store_lock_shadow_stack"
    | "__softboundcetswithss_store_key_shadow_stack"
    | "__softboundcetswithss_load_base_shadow_stack"
    | "__softboundcetswithss_load_bound_shadow_stack"
    | "__softboundcetswithss_load_lock_shadow_stack"
    | "__softboundcetswithss_load_key_shadow_stack"
    | "__softboundcetswithss_allocate_shadow_stack_space"
    | "__softboundcetswithss_deallocate_shadow_stack_space" -> true
    | _ -> false

let rename_fid fid = 
  let fn = Coq_pretty_printer.getRealName fid in
  match fn with
    | "main" -> "@softbound_pseudo_main"
    | _ -> if (isCallLib fid || isSysLib fid) then fid else "@softbound_" ^ fn

let rename_fid_inv fid = 
  let fn = Coq_pretty_printer.getRealName fid in
  match fn with
    | "softbound_pseudo_main" -> Some "@main"
    | _ ->
        if (isCallLib fid || isSysLib fid) then Some fid 
        else
          if (Str.string_match (Str.regexp "softbound_") fn 0) then
            if (Str.match_beginning() = 0) then
              let pos = Str.match_end () in
              Some ("@" ^ Str.string_after fn pos)
            else None
          else None

let smem_lib_sub = isCallLib

let is_hashLoadBaseBound fid =
  Coq_pretty_printer.getRealName fid = "__hashLoadBaseBound"

let is_hashStoreBaseBound fid =
  Coq_pretty_printer.getRealName fid = "__hashStoreBaseBound"

let is_loadStoreDereferenceCheck fid =
  Coq_pretty_printer.getRealName fid = "__loadDereferenceCheck" ||
  Coq_pretty_printer.getRealName fid = "__storeDereferenceCheck"
  
let is_callDereferenceCheck fid =
  Coq_pretty_printer.getRealName fid = "__callDereferenceCheck"

type metadata_t = { 
  init:bool; 
  data:((((((Syntax.LLVMsyntax.id*Syntax.LLVMsyntax.l)*Datatypes.nat)
           *Syntax.LLVMsyntax.id)*Syntax.LLVMsyntax.id)
           *Syntax.LLVMsyntax.id)*bool)list 
}

let metadata = ref {init=false; data=[]}

let get_metadata () =
  if !metadata.init then !metadata.data
  else
    try 
      let fin = open_in "metadata.db" in
      try 
        while true do
          let s = input_line fin in  
          Scanf.sscanf s "%s %s %i %s %s %s %b" (fun fid l i b e p im -> 
            if p <> "-1" then
              metadata := {!metadata with data=
                ((((((fid,l),(Camlcoq.nat_of_camlint (Int32.of_int i))),
                  b),e),p),im)::!metadata.data})
        done;
        metadata := {!metadata with init=true};
        !metadata.data
      with
        | End_of_file -> 
            close_in fin;
            metadata := {!metadata with init=true};
            !metadata.data
    with 
      | Sys_error _ -> [] 

type addrof_be_t = { 
  init:bool; 
  data:((Syntax.LLVMsyntax.id*Syntax.LLVMsyntax.id)*Syntax.LLVMsyntax.id)list 
}

let addrof_be = ref {init=false; data=[]}

let get_addrof_be () =
  if !addrof_be.init then !addrof_be.data
  else
    try 
      let fin = open_in "metadata.db" in
      try 
        while true do
          let s = input_line fin in  
          Scanf.sscanf s "%s %s %s %s %s %s %b" (fun fid l i ab ae p im -> 
            if (i = "0" && p = "-1") then
              addrof_be := {!addrof_be with data=((fid,ab),ae)::!addrof_be.data})
        done;
        addrof_be := {!addrof_be with init=true};
        !addrof_be.data
      with
        | End_of_file -> 
            close_in fin;
            addrof_be := {!addrof_be with init=true};
            !addrof_be.data
    with 
      | Sys_error _ -> [] 

let l_of_arg () = "_arg"

type renaming_t = { 
  init:bool; 
  data:((Syntax.LLVMsyntax.id*Syntax.LLVMsyntax.id)*Syntax.LLVMsyntax.id)list 
}

let renaming = ref {init=false; data=[]}

let get_renaming () =
  if !renaming.init then !renaming.data
  else
    try 
      let fin = open_in "renaming.db" in
      try 
        while true do
          let s = input_line fin in  
          Scanf.sscanf s "%s %s %s" (fun fid i1 i2 -> 
          renaming := {!renaming with data=((fid,i1),i2)::!renaming.data})
        done;
        renaming := {!renaming with init=true};
        !renaming.data
      with
        | End_of_file -> 
            close_in fin;
            renaming := {!renaming with init=true};
            !renaming.data
    with 
      | Sys_error _ -> [] 

let rec lookup_id fid id1 (renaming:((Syntax.LLVMsyntax.id*Syntax.LLVMsyntax.id)*Syntax.LLVMsyntax.id)list) : Syntax.LLVMsyntax.id option =
  match renaming with
    | [] -> None
    | ((f,i1),i2)::renaming' ->
        if (f = fid && i1 = id1) then Some i2
        else lookup_id fid id1 renaming'

let rename_id fid id1 = 
  match lookup_id fid id1 (get_renaming ()) with
    | Some id2 -> id2
    | None -> id1

let syscall_returns_pointer fid =
  match Coq_pretty_printer.getRealName fid with
    | "calloc" -> true
    | _ -> false

let is_tmp_var id =
  try 
    ignore (int_of_string (Coq_pretty_printer.getRealName id)); true
  with
    | Failure _ -> false

let eq_INT_Z x y = true
