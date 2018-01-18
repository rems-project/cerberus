open Core_ctype
open AilTypes

open Ocaml_implementation
open Memory_model
open Mem_common


module L = struct
  include List
  include Lem_list
end


(* TODO: get rid of this when we move to 4.06 *)
let list_init n f =
  let rec aux n acc =
    if n < 0 then
      acc
    else
      aux (n-1) (f n :: acc) in
  aux (n-1) []

module Eff : sig
  type ('a, 'err, 'cs, 'st) eff =
    ('a, 'err, 'cs, 'st) Nondeterminism.ndM
  val return: 'a -> ('a, 'err, 'cs, 'st) eff
  val (>>=): ('a, 'err, 'cs, 'st) eff -> ('a -> ('b, 'err, 'cs, 'st) eff) -> ('b, 'err, 'cs, 'st) eff
  val (>>): ('a, 'err, 'cs, 'st) eff -> ('b, 'err, 'cs, 'st) eff -> ('b, 'err, 'cs, 'st) eff
  val read: ('st -> 'a) -> ('a, 'err, 'cs, 'st) eff
  val update: ('st -> 'st) -> (unit, 'err, 'cs, 'st) eff
  val modify: ('st -> 'a * 'st) -> ('a, 'err, 'cs, 'st) eff
  val get: ('st, 'err, 'cs, 'st) eff
  val put: 'st -> (unit, 'err, 'cs, 'st) eff
  val fail: 'err -> ('a, 'err, 'cs, 'st) eff
  val mapM: ('a -> ('b, 'err, 'cs, 'st) eff) -> 'a list -> ('b list, 'err, 'cs, 'st) eff
  
end = struct
  type ('a, 'err, 'cs, 'st) eff =
    ('a, 'err, 'cs, 'st) Nondeterminism.ndM
  
  let return = Nondeterminism.nd_return
  let (>>=) = Nondeterminism.bind2
  let (>>) f g = f >>= (fun _ -> g)
  
  let read = Nondeterminism.read0
  let update = Nondeterminism.update0
  let modify f = 
    Nondeterminism.get0 >>= fun st ->
    let (ret, st') = f st in
    Nondeterminism.put0 st' >>= fun () ->
    return ret
  
  let get = Nondeterminism.get0
  let put = Nondeterminism.put0
  let fail err = Nondeterminism.kill (Other err)
  let mapM _ _ = failwith "mapM"
  
(*
  type ('a, 'st, 'err) eff = ('a, 'st, 'err) State_exception.stExceptM
  val return: 'a -> ('a, 'st, 'err) eff
  val (>>=): ('a, 'st, 'err) eff -> ('a -> ('b, 'st, 'err) eff) -> ('b, 'st, 'err) eff
  val (>>): ('a, 'st, 'err) eff -> ('b, 'st, 'err) eff -> ('b, 'st, 'err) eff
  val read: ('st -> 'a) -> ('a, 'st, 'err) eff
  val update: ('st -> 'st) -> (unit, 'st, 'err) eff
  val modify: ('st -> 'a * 'st) -> ('a, 'st, 'err) eff
  val get: ('st, 'st, 'err) eff
  val put: 'st -> (unit, 'st, 'err) eff
  val fail: 'err -> ('a, 'st, 'err) eff
  val mapM: ('a -> ('b, 'st, 'err) eff) -> 'a list -> ('b list, 'st, 'err) eff
end = struct
  type ('a, 'st, 'err) eff = ('a, 'st, 'err) State_exception.stExceptM
  let read     = State_exception.read1
  let update   = State_exception.update1
  let modify   = State_exception.modify0
(*  let eval     = State_exception.eval0 *)
  let get      = State_exception.get1
  let put      = State_exception.put1
  let fail err = fun _ -> Exception.fail err
  let return a = fun st -> Exception.except_return (a, st)
  let (>>=) m f = fun st -> Exception.except_bind (m st) (fun (a, st') -> (f a) st')
  let (>>) f g = f >>= (fun _ -> g)
  let rec mapM f = function
    | [] ->
        return []
    | x::xs ->
        f x       >>= fun b  ->
        mapM f xs >>= fun bs ->
        return (b::bs)
*)
end

module IntMap = Map.Make(struct
  type t = Nat_big_num.num
  let compare = Nat_big_num.compare
end)


let rec sizeof = function
  | Void0 | Array0 (_, None) | Function0 _ ->
      assert false
  | Basic0 (Integer ity) ->
      begin match Impl.sizeof_ity ity with
        | Some n ->
            n
        | None ->
            failwith "the concrete memory model requires a complete implementation"
      end
  | Basic0 (Floating fty) ->
      begin match Impl.sizeof_fty fty with
        | Some n ->
            n
        | None ->
            failwith "the concrete memory model requires a complete implementation"
      end
  | Array0 (elem_ty, Some n) ->
      (* TODO: what if too big? *)
      Nat_big_num.to_int n * sizeof elem_ty
  | Pointer0 (_, ref_ty) ->
      begin match Impl.sizeof_pointer with
        | Some n ->
            n
        | None ->
            failwith "the concrete memory model requires a complete implementation"
      end
  | Atomic0 atom_ty ->
      sizeof atom_ty
  | Struct0 tag_sym ->
      failwith "TODO: sizeof Struct"
(*
      let Tags.StructDef membrs = Pmap.find tag_sym (Tags.tagDefs ()) in
      List.fold_left (fun acc (ident, ty) ->
        (sizeof ty) + padding + acc
      ) 0 membrs
*)
  | Union0 tag_sym ->
     failwith "TODO: sizeof Union"
  | Builtin0 str ->
     failwith "TODO: sizeof Builtin"









let rec alignof = function
  | Void0 ->
      assert false
  | Basic0 (Integer ity) ->
      begin match Impl.alignof_ity ity with
        | Some n ->
            n
        | None ->
            failwith "the concrete memory model requires a complete implementation"
      end
  | Basic0 (Floating fty) ->
      begin match Impl.alignof_fty fty with
        | Some n ->
            n
        | None ->
            failwith "the concrete memory model requires a complete implementation"
      end
  | Array0 (_, None) ->
      assert false
  | Array0 (elem_ty, Some n) ->
      alignof elem_ty
  | Function0 _ ->
      assert false
  | Pointer0 _ ->
      begin match Impl.alignof_pointer with
        | Some n ->
            n
        | None ->
            failwith "the concrete memory model requires a complete implementation"
      end
  | Atomic0 atom_ty ->
      alignof atom_ty
  | Struct0 tag_sym ->
     failwith "TODO: sizeof Struct"
  | Union0 tag_sym ->
     failwith "TODO: sizeof Union"
  | Builtin0 str ->
     failwith "TODO: sizeof Builtin"


module Concrete : Memory = struct
  let name = "I am the concrete memory model"
  open Eff
(*  include Mem_common *)
  
  (* Note: using Z instead of int64 because we need to be able to have
     unsigned 64bits values *)
  type pointer_value =
    | PVnull of ctype0
    | PVfunction of Symbol.sym
    | PVconcrete of Nat_big_num.num
  
  type integer_value =
    | IV of Nat_big_num.num
  
  type floating_value =
    float
  
  type mem_value =
    | MVinteger of AilTypes.integerType * integer_value
    | MVpointer of Core_ctype.ctype0 * pointer_value
    | MVarray of mem_value list
    | MVstruct of Symbol.sym (*struct/union tag*) * (Cabs.cabs_identifier (*member*) * mem_value) list
    | MVunion of Symbol.sym (*struct/union tag*) * Cabs.cabs_identifier (*member*) * mem_value

  
  type mem_iv_constraint = integer_value mem_constraint
  let cs_module = (module struct
    type t = mem_iv_constraint
    let negate x = MC_not x
    
    type 'a eff = Eff of (bool -> ('a * bool))
    let return a = Eff (fun b -> (a, b))
    let bind (Eff ma) f =
      Eff (fun b -> let (a, b') = ma b in let Eff mb = f a in mb b')
    let rec foldlM f a = function
      | [] ->
          return a
      | x::xs ->
          bind (f a x) (fun fax -> foldlM f fax xs)
    
    let runEff (Eff ma) = fst (ma true)
    
(*    let init_solver = return () *)
    let string_of_solver = return []
    let check_sat =
      Eff (fun b -> ((if b then `SAT else `UNSAT), b))
    
    let with_constraints _ cs (Eff ma) =
      prerr_endline "HELLO: Concrete.with_constraints";
      let rec eval_cs = function
        | MC_empty ->
            true
        | MC_eq (IV n1, IV n2) ->
            Nat_big_num.equal n1 n2
        | MC_le (IV n1, IV n2) ->
            Nat_big_num.less_equal n1 n2
        | MC_lt (IV n1, IV n2) ->
            Nat_big_num.less n1 n2
        | MC_in_device _ ->
            failwith "Concrete, with_constraints: MC_in_device"
        | MC_or (cs1, cs2) ->
            eval_cs cs1 || eval_cs cs2
        | MC_conj css ->
            List.for_all (fun z -> eval_cs z) css
        | MC_not cs ->
            not (eval_cs cs)
      in
      Eff (fun b -> ma (b && eval_cs cs))
   end : Constraints with type t = mem_iv_constraint)
  
  
  type mem_state = {
    next_address: Nat_big_num.num;
    bytemap: char IntMap.t;
    
(*
    blocks: (Nat_big_num.t * Nat_big_num.t * (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t) list;
*)
  }
  
  let initial_mem_state = {
    next_address= Nat_big_num.(succ zero);
    bytemap= IntMap.empty;
(*
    blocks=
      (* starting with a block of 10M words *)
      let size = 10 * 1024 * 1024 * 8 in
      [(Nat_big_num.one, Nat_big_num.of_int size, Bigarray.Array1.create Bigarray.char Bigarray.c_layout size)];
*)
  }
  
  type footprint =
    | Footprint
  
  let do_overlap fp1 fp2 =
    failwith "TODO: do_overlap"
  
  type 'a memM = ('a, mem_error, integer_value mem_constraint, mem_state) Eff.eff
  
  let return = Eff.return
  let bind = Eff.(>>=)
  
  let allocate_static tid pref (IV align) ty =
    let size = Nat_big_num.of_int (sizeof ty) in
    modify (fun st ->
      let ptr' = Nat_big_num.(add st.next_address (sub align (modulus st.next_address align))) in
      ( PVconcrete ptr'
      , { st with next_address= Nat_big_num.add ptr' size } )
    )
  
  let allocate_dynamic tid pref (IV align_n) (IV size_n) =
    modify (fun st ->
      let ptr' = Nat_big_num.(add st.next_address (sub align_n (modulus st.next_address align_n))) in
      ( PVconcrete ptr'
      , { st with next_address= Nat_big_num.add ptr' size_n } )
    )
  
  let kill = function
    | PVnull _
    | PVfunction _ ->
        fail (MerrWIP "kill")
    | PVconcrete addr ->
        (* TODO: have an error when the pointer is dead *)
        return ()
(*
        update (fun st ->
          { st with bytemap= IntMap.remove addr st.allocations }
        )
*)
  
  let fetch_bytes base_addr n_bytes =
    get >>= fun st ->
    return (
      List.map (fun addr ->
        match IntMap.find_opt addr st.bytemap with
          | Some b ->
              b
          | None ->
              '\000'
      ) (list_init n_bytes (fun z ->
           (* NOTE: the reversal in the offset is to model little-endianness *)
           let offset = n_bytes - 1 - z in
           Nat_big_num.(add base_addr (of_int offset))
         ))
    )
(*
    let aux i =
      match L.fold_left (fun acc (min_addr, max_addr, arr) ->
        match acc with
          | Some _ ->
              acc
          | None ->
              if min_addr <= i && i <= max_addr then
                Some (Bigarray.Array1.get arr Nat_big_num.(to_int (sub i min_addr)))
              else
                None
      ) None st.blocks with
        | Some bs ->
            return bs
        | None ->
            fail MErr
    in
    Eff.mapM aux (list_init n_bytes (fun z -> Nat_big_num.(add addr (of_int z))))
*)
  
  
  let rec find_block addr = function
    | [] ->
        None
    | ((min_addr,max_addr,arr) as block) :: blocks ->
        if min_addr <= addr && addr <= max_addr then
          Some block
        else
          find_block addr blocks
  
  
  let write_bytes base_addr bs =
    get >>= fun st ->
    return (
      (* NOTE: the reversal caused by the fold_left is what we want because of little-endianness *)
      List.fold_left (fun acc (addr, b) ->
        IntMap.add addr b acc
      ) st.bytemap (list_init (List.length bs) (fun z -> (Nat_big_num.(add base_addr (of_int z), L.nth bs z))))
    )
    
(*
    let aux (addr, b) =
      match find_block addr st.blocks with
        | None ->
            fail MErr
        | Some (_, _, arr) ->
            failwith ""
    in
    Eff.mapM aux (list_init (List.length bs) (fun z -> (Nat_big_num.(add base_addr (of_int z), L.nth bs z))))
*)
  
  let int64_of_bytes is_signed = function
    | [] ->
        assert false
    | cs when L.length cs > 8 ->
        assert false
    | (first::_ as cs) ->
        (* NOTE: this is to preserve the binary signedness *)
        let init =
          if is_signed && Nat_big_num.(equal (succ zero) (extract_num (of_int (int_of_char first)) 7 1)) then
            Nat_big_num.of_int (-1)
          else
            Nat_big_num.zero in
        (*let init = if is_signed then *)
        let rec aux acc = function
          | [] ->
              acc
          | c::cs' ->
(*              "THIS NEEDS TO BE BITWISE OR?" *)
(*
              aux Nat_big_num.(add (of_int (int_of_char c)) (shift_left acc 8)) cs' in
*)
              aux Nat_big_num.(bitwise_xor (of_int (int_of_char c)) (shift_left acc 8)) cs' in
        aux init cs
  
(*
  let int64_of_bytes b cs =
    print_endline "BEGIN int64_of_bytes"; flush_all ();
    let ret = int64_of_bytes_ b cs in
    print_endline "END int64_of_bytes"; flush_all ();
    ret
*)

  
  let rec combine_bytes ty cs =
    match ty with
      | Void0
      | Array0 (_, None)
      | Function0 _ ->
          assert false
      | Basic0 (Integer ity) ->
          let (cs1, cs2) = L.split_at (sizeof ty) cs in
          (MVinteger (ity, IV (int64_of_bytes (AilTypesAux.is_signed_ity ity) cs1)), cs2)
      | Basic0 (Floating ity) ->
          failwith "WIP: combine_bytes"
      | Array0 (elem_ty, Some n) ->
          let rec aux n acc cs =
            if n < 0 then
              (MVarray acc, cs)
            else
              let (mval, cs') = combine_bytes elem_ty cs in
              aux (n-1) (mval :: acc) cs'
          in
          aux (Nat_big_num.to_int n) [] cs
      | Pointer0 (_, ref_ty) ->
          let (cs1, cs2) = L.split_at (sizeof ty) cs in
          prerr_endline "TODO: Concrete, assuming pointer repr is unsigned??";
          (MVpointer (ref_ty, PVconcrete (int64_of_bytes false cs1)), cs2)
      | Atomic0 atom_ty ->
          failwith "WIP: combine_bytes"
      | Struct0 tag_sym ->
          failwith "WIP: combine_bytes"
      | Union0 tag_sym ->
          failwith "WIP: combine_bytes"
      | Builtin0 str ->
          failwith "WIP: combine_bytes"

  let bytes_of_int64 is_signed size i : char list =
    let nbits = 8 * size in
    let (min, max) =
      if is_signed then
        (Nat_big_num.negate (Nat_big_num.pow_int (Nat_big_num.of_int 2) (nbits-1)), Nat_big_num.sub (Nat_big_num.pow_int (Nat_big_num.of_int 2) (nbits-1)) Nat_big_num.(succ zero))
      else
        (Nat_big_num.zero, Nat_big_num.sub (Nat_big_num.pow_int (Nat_big_num.of_int 2) nbits) Nat_big_num.(succ zero)) in
    if not (min <= i && i <= max) || nbits > 64 then
      (Printf.printf "failed: bytes_of_int64(%s), i= %s, nbits= %d, [%s ... %s]\n"
         (if is_signed then "signed" else "unsigned")
         (Nat_big_num.to_string i) nbits (Nat_big_num.to_string min) (Nat_big_num.to_string max);
      assert false)
    else
      list_init size (fun n ->
        char_of_int (Nat_big_num.to_int (Nat_big_num.extract_num i (8*n) 8))
      )
  
  let rec explode_bytes ty mval : char list =
    match mval with
      | MVinteger (_, IV n) ->
          let (Core_ctype.Basic0 (AilTypes.Integer ity)) = ty in
          bytes_of_int64
            (AilTypesAux.is_signed_ity ity)
            (sizeof (Basic0 (Integer ity))) n
      | MVpointer (_, ptrval) ->
          prerr_endline "NOTE: we fix the sizeof pointers to 8 bytes";
          let size = 8 in
          begin match ptrval with
            | PVnull _ ->
                prerr_endline "NOTE: we fix the representation of all NULL pointers to be 0x0";
                List.init size (fun _ -> '\000')
            | PVfunction _ ->
                failwith "TODO: explode_bytes, PVfunction"
            | PVconcrete i ->
                bytes_of_int64
                  false (* we model address as unsigned *)
                  (sizeof ty) i
          end
      | MVarray mvals ->
          let elem_ty = match ty with
            | Array0 (z, _) ->
                z
            | _ ->
                assert false in
          L.concat (
            List.map (explode_bytes elem_ty) mvals
          )
  
  let load loc ty = function
    | PVnull _ ->
        fail (MerrAccess (loc, LoadAccess, NullPtr))
    | PVfunction _ ->
        fail (MerrAccess (loc, LoadAccess, FunctionPtr))
    | PVconcrete addr ->
        get >>= fun st ->
        fetch_bytes addr (sizeof ty) >>= fun bs ->
(*
          print_endline "BEGIN LOAD BYTES";
          List.iter (fun b -> Printf.printf "%x\n" (int_of_char b)) bs;
          print_endline "END";
*)
        let (mval, bs') = combine_bytes ty bs in
        begin match bs' with
          | [] ->
              let str = match mval with
                | MVinteger (_, IV n) -> Nat_big_num.to_string n
                | _ -> "NOT INTEGER"
              in
(*              Printf.printf "Concrete.load (%s) ==> %s\n" (String_core_ctype.string_of_ctype ty) str; *)
              return (Footprint, mval)
          | _ ->
              fail (MerrWIP "load, bs' <> []")
        end
  
  let store loc ty ptrval mval =
    let str = match mval with
      | MVinteger (_, IV n) -> Nat_big_num.to_string n
      | _ -> "NOT INTEGER"
    in
(*    Printf.printf "Concrete.store ==> %s\n" str; *)
    match ptrval with
      | PVnull _ ->
          fail (MerrAccess (loc, StoreAccess, NullPtr))
      | PVfunction _ ->
          fail (MerrAccess (loc, StoreAccess, FunctionPtr))
      | PVconcrete addr ->
          let bs = List.mapi (fun i b ->
            (Nat_big_num.add addr (Nat_big_num.of_int i), b)
          ) (explode_bytes ty mval) in
(*
          print_endline "BEGIN STORE BYTES";
          List.iter (fun (_, b) -> Printf.printf "%x\n" (int_of_char b)) bs;
          print_endline "END";
*)
          update (fun st ->
            { st with bytemap=
              List.fold_left (fun acc (addr, b) ->
                IntMap.add addr b acc
              ) st.bytemap bs }
(*
            { st with allocations=
                List.fold_left (fun acc (ptr, ival) ->
                  IntMap.add ptr ival acc
                ) st.allocations xs }
*)
          ) >>
          return Footprint
  
  let null_ptrval ty =
    PVnull ty
  
  let fun_ptrval sym =
    PVfunction sym
  
  let eq_ptrval ptrval1 ptrval2 =
    match (ptrval1, ptrval2) with
      | (PVnull _, PVnull _) ->
          return true
      | (PVnull _, _)
      | (_, PVnull _) ->
          return false
      | (PVfunction sym1, PVfunction sym2) ->
          return (Symbol.instance_Basic_classes_Eq_Symbol_sym_dict.Lem_pervasives.isEqual_method sym1 sym2)
      | (PVfunction _, _)
      | (_, PVfunction _) ->
          return false
      | (PVconcrete n1, PVconcrete n2) ->
          return (Nat_big_num.equal n1 n2)
  
  let ne_ptrval ptrval1 ptrval2 =
    eq_ptrval ptrval1 ptrval2 >>= fun b ->
    return (not b)
  
  let lt_ptrval ptrval1 ptrval2 =
    match (ptrval1, ptrval2) with
      | (PVconcrete addr1, PVconcrete addr2) ->
          return (Nat_big_num.compare addr1 addr2 == -1)
      | _ ->
          fail (MerrWIP "lt_ptrval")
  
  let gt_ptrval ptrval1 ptrval2 =
    match (ptrval1, ptrval2) with
      | (PVconcrete addr1, PVconcrete addr2) ->
          return (Nat_big_num.compare addr1 addr2 == 1)
      | _ ->
          fail (MerrWIP "gt_ptrval")
  
  let le_ptrval ptrval1 ptrval2 =
    match (ptrval1, ptrval2) with
      | (PVconcrete addr1, PVconcrete addr2) ->
          let cmp = Nat_big_num.compare addr1 addr2 in
          return (cmp = -1 || cmp = 0)
      | _ ->
          fail (MerrWIP "le_ptrval")
  
  let ge_ptrval ptrval1 ptrval2 =
    match (ptrval1, ptrval2) with
      | (PVconcrete addr1, PVconcrete addr2) ->
          let cmp = Nat_big_num.compare addr1 addr2 in
          return (cmp = 1 || cmp = 0)
      | _ ->
          fail (MerrWIP "ge_ptrval")
  
  let diff_ptrval ty ptrval1 ptrval2 =
    failwith "TODO: diff_ptrval"
  
  let validForDeref_ptrval = function
    | PVnull _
    | PVfunction _ ->
        false
    | PVconcrete _ ->
        true
  
  let memcmp ptrvall1 ptrval2 ival =
    failwith "TODO: memcmp"
  
  let ptrcast_ival _ _ (IV n) =
    return (PVconcrete n)
  
  (* TODO: conversion? *)
  let intcast_ptrval _ ity = function
    | PVnull _ ->
        return (IV Nat_big_num.zero)
    | PVfunction _ ->
        failwith "TODO: intcast_ptrval PVfunction"
    | PVconcrete n ->
        return (IV n)
  
  let array_shift_ptrval ptrval ty (IV ival) =
    let offset = (Nat_big_num.(mul (of_int (sizeof ty)) ival)) in
    match ptrval with
      | PVnull _ ->
          prerr_endline "TODO(check): array_shift_ptrval, PVnull";
          PVconcrete offset
      | PVfunction _ ->
          failwith "array_shift_ptrval, PVfunction"
      | PVconcrete addr ->
          PVconcrete (Nat_big_num.add addr offset)
  
  let member_shift_ptrval ptrval tag_sym memb_ident =
    failwith "TODO: member_shift_ptrval"
  
  let concurRead_ival ity sym =
    failwith "TODO: concurRead_ival"
  
  let integer_ival n =
    IV n
  
  let max_ival ity =
    let open Nat_big_num in
    IV begin match Impl.sizeof_ity ity with
      | Some n ->
          let signed_max =
            sub (pow_int (of_int 2) (8*n-1)) (of_int 1) in
          let unsigned_max =
            sub (pow_int (of_int 2) (8*n)) (of_int 1) in
          begin match ity with
            | Char ->
                if Impl.char_is_signed then
                  signed_max
                else
                  unsigned_max
            | Bool ->
                (* TODO: not sure about this (maybe it should be 1 and not 255? *)
                unsigned_max
            | Size_t
            | Unsigned _ ->
                unsigned_max
            | Ptrdiff_t
            | Signed _ ->
                signed_max
            | Enum _ ->
                failwith "max_ival: Enum"
            | IBuiltin _ ->
                failwith "max_ival: IBuiltin"
          end
      | None ->
          failwith "the concrete memory model requires a complete implementation"
    end
  
  let min_ival ity =
    let open Nat_big_num in
    IV begin match ity with
      | Char ->
          if Impl.char_is_signed then
            negate (pow_int (of_int 2) (8-1))
          else
            zero
      | Bool
      | Size_t
      | Unsigned _ ->
          (* all of these are unsigned *)
          zero
      | Ptrdiff_t
      | Signed _ ->
          (* and all of these are signed *)
          begin match Impl.sizeof_ity ity with
            | Some n ->
                negate (pow_int (of_int 2) (8*n-1))
            | None ->
                failwith "the concrete memory model requires a complete implementation"
          end
      | Enum _
      | IBuiltin _ ->
          failwith "minv_ival: Enum, Builtin"
    end
  
  let op_ival iop (IV n1) (IV n2) =
    IV (begin match iop with
      | IntAdd ->
          Nat_big_num.add
      | IntSub ->
          Nat_big_num.sub
      | IntMul ->
          Nat_big_num.mul
      | IntDiv ->
          Nat_big_num.integerDiv_t
      | IntRem_t ->
          Nat_big_num.integerRem_t
      | IntRem_f ->
          Nat_big_num.integerRem_f
      | IntExp ->
          (* TODO: fail properly when y is too big? *)
          fun x y -> Nat_big_num.pow_int x (Nat_big_num.to_int y)
    end n1 n2)
    
  
  let offsetof_ival tag_Sym memb_ident =
    failwith "TODO: offsetof_ival"
  
  let sizeof_ival ty =
    IV (Nat_big_num.of_int (sizeof ty))
  let alignof_ival ty =
    IV (Nat_big_num.of_int (alignof ty))
  
  let bitwise_complement_ival _ (IV n) =
    (* TODO *)
    (* prerr_endline "Concrete.bitwise_complement ==> HACK"; *)
    IV (Nat_big_num.(sub (negate n) (of_int 1)))

  let bitwise_and_ival _ (IV n1) (IV n2) =
    IV (Nat_big_num.bitwise_and n1 n2)
  let bitwise_or_ival _ (IV n1) (IV n2) =
    IV (Nat_big_num.bitwise_or n1 n2)
  let bitwise_xor_ival _ (IV n1) (IV n2) =
    IV (Nat_big_num.bitwise_xor n1 n2)
  
  let case_integer_value (IV n) f_concrete _ =
    f_concrete n
  
  let is_specified_ival ival =
    true
  
  let zero_fval =
    0.0
  let str_fval str =
    float_of_string str
  
  let case_fval fval _ fconcrete =
    fconcrete fval
  
  let op_fval fop fval1 fval2 =
    failwith "TODO: op_fval"
  let eq_fval fval1 fval2 =
    failwith "TODO: eq_fval"
  let lt_fval fval1 fval2 =
    failwith "TODO: lt_fval"
  let le_fval fval1 fval2 =
    failwith "TODO: le_fval"
  
  let fvfromint ival =
    failwith "TODO: fvfromint"
  
  let ivfromfloat ity fval =
    failwith "TODO: ivfromfloat"
  
  let eq_ival _ (IV n1) (IV n2) =
    Some (Nat_big_num.equal n1 n2)
  let lt_ival _ (IV n1) (IV n2) =
    Some (Nat_big_num.compare n1 n2 = -1)
  let le_ival _ (IV n1) (IV n2) =
    let cmp = Nat_big_num.compare n1 n2 in
    Some (cmp = -1 || cmp = 0)
  
  let eval_integer_value (IV n) =
    Some n
  
  let unspecified_mval ty =
    failwith "TODO: unspecified_mval"
  let integer_value_mval ity ival =
    MVinteger (ity, ival)
  let floating_value_mval fty fval =
    failwith "TODO: floating_value_mval"
  let pointer_mval ref_ty ptrval =
    MVpointer (ref_ty, ptrval)
  let array_mval mvals =
    MVarray mvals
  let struct_mval tag_sym xs =
    MVstruct (tag_sym, xs)
  let union_mval tag_sym memb_ident mval =
    MVunion (tag_sym, memb_ident, mval)
  
  let case_mem_value mval f_unspec f_concur f_ival f_fval f_ptr f_array f_struct f_union =
    match mval with
      | MVinteger (ity, ival) ->
          f_ival ity ival
      | MVpointer (ref_ty, ptrval) ->
          f_ptr ref_ty ptrval
      | MVarray mvals ->
          f_array mvals
      | MVstruct (tag_sym, xs) ->
          f_struct tag_sym xs
      | MVunion (tag_sym, memb_ident, mval') ->
          f_union tag_sym memb_ident mval'
  
  let sequencePoint =
    return ()
  
  
  (* pretty printing *)
  open PPrint
  let pp_pointer_value = function
    | PVnull ty ->
        !^ "NULL"
    | PVfunction sym ->
        !^ ("<funptr:" ^ Symbol.instance_Show_Show_Symbol_sym_dict.show_method sym ^ ">")
    | PVconcrete n ->
        !^ (Nat_big_num.to_string n)
  
  let pp_integer_value (IV n) =
        !^ (Nat_big_num.to_string n)
    
  let pp_integer_value_for_core = pp_integer_value
    
  let rec pp_mem_value = function
    | MVinteger (_, ival) ->
        pp_integer_value ival
    | MVpointer (_, ptrval) ->
        pp_pointer_value ptrval
    | MVarray mvals ->
        braces (
         Pp_prelude.comma_list pp_mem_value mvals
        )


  let pp_pretty_pointer_value = pp_pointer_value
  let pp_pretty_integer_value _ = pp_integer_value
  let pp_pretty_mem_value _ = pp_mem_value


(*
  open Nondeterminism
  let runND m st0 =
    let rec aux (ND m_act) st =
      match m_act st with
        | (NDactive a, st') ->
            [(Active a, [], st')]
      | (NDkilled (Undef0 _ as reason), st') ->
          [(Killed reason, [], st')]
      | (NDkilled r, st') ->
          failwith "Concrete.runND NDkilled"
      | (NDnd (debug_str, str_ms), st') ->
          if true (* is_exhaustive *) then
            L.concat (
              L.map (fun (_, z) -> aux z st') str_ms 
            )
          else
            (* TODO: this is not really random (see http://okmij.org/ftp/Haskell/perfect-shuffle.txt) *)
            let suffled_str_ms =
              let with_index = List.map (fun z ->
                (Random.bits (), z)
              ) str_ms in
              List.map snd (List.sort (fun (x, _) (y, _) -> Pervasives.compare x y) with_index) in
            begin match suffled_str_ms with
              | [] ->
                  assert false
              | (_, m_act) :: _ ->
                  aux m_act st'
            end
      | (NDguard (debug_str, _, _), _) ->
          print_endline debug_str;
          assert false
      | (NDbranch (debug_str, _, _, _), _) ->
          print_endline debug_str;
          assert false
    in
    aux m st0
*)
end

include Concrete
