open Core_ctype
open AilTypes

open Ocaml_implementation
open Memory_model
open Mem_common

module N = Nat_big_num

module L = struct
  include List
  include Lem_list
end

let cabs_ident_equal x y =
       Cabs.instance_Basic_classes_Eq_Cabs_cabs_identifier_dict.isEqual_method x y

let ctype_equal ty1 ty2 =
  let rec unqualify ty =
    match ty with
      | Void0
      | Basic0 _
      | Struct0 _
      | Union0 _
      | Builtin0 _ ->
          ty
      | Function0 ((_, ret_ty), xs, b) ->
          Function0 (
            (AilTypes.no_qualifiers, unqualify ret_ty),
            List.map (fun (_, ty) -> (AilTypes.no_qualifiers, unqualify ty)) xs,
            b
         )
      | Array0 (elem_ty, n_opt) ->
          Array0 (unqualify elem_ty, n_opt)
      | Pointer0 (_, ref_ty) ->
          Pointer0 (AilTypes.no_qualifiers, unqualify ref_ty)
      | Atomic0 atom_ty ->
          Atomic0 (unqualify atom_ty)
  in
  Core_ctype.instance_Basic_classes_Eq_Core_ctype_ctype_dict.isEqual_method
    (unqualify ty1) (unqualify ty2)

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
  val msum: string -> (string * ('a, 'err, 'cs, 'st) eff) list -> ('a, 'err, 'cs, 'st) eff
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
  let mapM _ _ = failwith "TODO: mapM"
  
  let msum str xs =
    Nondeterminism.(
      msum Mem_common.instance_Nondeterminism_Constraints_Mem_common_mem_constraint_dict str xs
    )
end




module IntMap = Map.Make(struct
  type t = Nat_big_num.num
  let compare = Nat_big_num.compare
end)


(* TODO: memoise this, it's stupid to recompute this every time... *)
(* NOTE: returns ([(memb_ident, type, offset)], last_offset) *)
let rec offsetsof tag_sym =
  match Pmap.find tag_sym (Tags.tagDefs ()) with
    | Tags.StructDef membrs ->
        let (xs, maxoffset) =
          List.fold_left (fun (xs, last_offset) (membr, ty) ->
            let size = sizeof ty in
            let align = alignof ty in
            let x = last_offset mod align in
            let pad = if x = 0 then 0 else align - x in
            ((membr, ty, last_offset + pad) :: xs, last_offset + pad + size)
          ) ([], 0) membrs in
        (List.rev xs, maxoffset)
    | Tags.UnionDef membrs ->
        (List.map (fun (ident, ty) -> (ident, ty, 0)) membrs, 0)

and sizeof = function
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
  | Pointer0 _ ->
      begin match Impl.sizeof_pointer with
        | Some n ->
            n
        | None ->
            failwith "the concrete memory model requires a complete implementation"
      end
  | Atomic0 atom_ty ->
      sizeof atom_ty
  | Struct0 tag_sym as ty ->
      let (_, max_offset) = offsetsof tag_sym in
      let align = alignof ty in
      let x = max_offset mod align in
      if x = 0 then max_offset else max_offset + (align - x)
  | Union0 tag_sym ->
      begin match Pmap.find tag_sym (Tags.tagDefs ()) with
        | Tags.StructDef _ ->
            assert false
        | Tags.UnionDef membrs ->
            let (max_size, max_align) =
              List.fold_left (fun (acc_size, acc_align) (_, ty) ->
                (max acc_size (sizeof ty), max acc_align (alignof ty))
              ) (0, 0) membrs in
            (* NOTE: adding padding at the end to satisfy alignment constraints *)
            let x = max_size mod max_align in
            if x = 0 then max_size else max_size + (max_align - x)
      end
  | Builtin0 str ->
     failwith "TODO: sizeof Builtin"

and alignof = function
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
      begin match Pmap.find tag_sym (Tags.tagDefs ()) with
        | Tags.UnionDef _ ->
            assert false
        | Tags.StructDef membrs  ->
            (* NOTE: Structs (and unions) alignment is that of the maximum alignment
               of any of their components. *)
            List.fold_left (fun acc (_, ty) ->
              max (alignof ty) acc
            ) 0 membrs
(*
            (* TODO: remove the pattern matching, this is dumb ... *)
            begin match membrs with
              | [] ->
                  assert false
              | (_, ty0) :: xs ->
                  List.fold_left (fun acc (_, ty) ->
                    let n = alignof ty in if n > acc then n else acc
                                 ) (alignof ty0) xs
            end
*)
      end
  | Union0 tag_sym ->
      begin match Pmap.find tag_sym (Tags.tagDefs ()) with
        | Tags.StructDef _ ->
            assert false
        | Tags.UnionDef membrs ->
            (* NOTE: Structs (and unions) alignment is that of the maximum alignment
               of any of their components. *)
            List.fold_left (fun acc (_, ty) ->
              max (alignof ty) acc
            ) 0 membrs
(*
            (* TODO: remove the pattern matching, this is dumb ... *)
            begin match membrs with
              | [] ->
                  assert false
              | (_, ty0) :: xs ->
                  List.fold_left (fun acc (_, ty) ->
                    let n = alignof ty in if n > acc then n else acc
                  ) (alignof ty0) xs
            end
*)
      end
  | Builtin0 str ->
     failwith "TODO: sizeof Builtin"


module Concrete : Memory = struct
  let name = "I am the concrete memory model"

  type provenance =
    | Prov_none
    | Prov_some of Nat_big_num.num
    | Prov_device
  
  (* Note: using Z instead of int64 because we need to be able to have
     unsigned 64bits values *)
  type pointer_value_base =
    | PVnull of ctype0
    | PVfunction of Symbol.sym
    | PVconcrete of Nat_big_num.num
  
  type pointer_value =
    | PV of provenance * pointer_value_base
  
  type integer_value =
    | IV of provenance * Nat_big_num.num
  
  type floating_value =
    (* TODO: hack hack hack ==> OCaml's float are 64bits *)
    float
  
  type mem_value =
    | MVunspecified of Core_ctype.ctype0
    | MVinteger of AilTypes.integerType * integer_value
    | MVfloating of AilTypes.floatingType * floating_value
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
    
    let string_of_solver = return []
    let check_sat =
      Eff (fun b -> ((if b then `SAT else `UNSAT), b))
    
    let with_constraints _ cs (Eff ma) =
      Debug_ocaml.print_debug 1 [] (fun () -> "HELLO: Concrete.with_constraints");
      let rec eval_cs = function
        | MC_empty ->
            true
        | MC_eq (IV (prov1, n1), IV (prov2, n2)) ->
            Nat_big_num.equal n1 n2
        | MC_le (IV (prov1, n1), IV (prov2, n2)) ->
            Nat_big_num.less_equal n1 n2
        | MC_lt (IV (prov1, n1), IV (prov2, n2)) ->
            Nat_big_num.less n1 n2
        | MC_in_device _ ->
            failwith "TODO: Concrete, with_constraints: MC_in_device"
        | MC_or (cs1, cs2) ->
            eval_cs cs1 || eval_cs cs2
        | MC_conj css ->
            List.for_all (fun z -> eval_cs z) css
        | MC_not cs ->
            not (eval_cs cs)
      in
      Eff (fun b -> ma (b && eval_cs cs))
   end : Constraints with type t = mem_iv_constraint)
  
  open Eff
  
  (* INTERNAL: allocation_id *)
  type allocation_id = N.num
  
  (* INTERNAL: address *)
  type address = N.num
  
  (* INTERNAL: allocation *)
  type allocation = {
    base: address;
    size: N.num;
  }
  
  type mem_state = {
    next_alloc_id: allocation_id;
    allocations: allocation IntMap.t;
    next_address: address;
    bytemap: (provenance * char option) IntMap.t;
  }
  
  let initial_mem_state = {
    next_alloc_id= Nat_big_num.zero;
    allocations= IntMap.empty;
    next_address= Nat_big_num.(succ zero);
    bytemap= IntMap.empty;
  }
  
  type footprint =
    | Footprint
  
  let do_overlap fp1 fp2 =
    failwith "TODO: do_overlap"
  
  type 'a memM = ('a, mem_error, integer_value mem_constraint, mem_state) Eff.eff
  
  let return = Eff.return
  let bind = Eff.(>>=)
  




  (* pretty printing *)
  open PPrint
  open Pp_prelude
  let pp_pointer_value (PV (_, ptrval_))=
    match ptrval_ with
      | PVnull ty ->
          !^ "NULL"
      | PVfunction sym ->
          !^ ("<funptr:" ^ Symbol.instance_Show_Show_Symbol_sym_dict.show_method sym ^ ">")
      | PVconcrete n ->
          !^ (Nat_big_num.to_string n)
  
  let pp_integer_value (IV (_, n)) =
        !^ (Nat_big_num.to_string n)
    
  let pp_integer_value_for_core = pp_integer_value
    
  let rec pp_mem_value = function
    | MVunspecified _ ->
        PPrint.string "UNSPEC"
    | MVinteger (_, ival) ->
        pp_integer_value ival
    | MVfloating (_, fval) ->
        !^ (string_of_float fval)
    | MVpointer (_, ptrval) ->
        !^ "ptr" ^^ parens (pp_pointer_value ptrval)
    | MVarray mvals ->
        braces (
         comma_list pp_mem_value mvals
        )
    | MVstruct (tag_sym, xs) ->
        parens (!^ "struct" ^^^ !^ (Pp_symbol.to_string_pretty tag_sym)) ^^ braces (
          comma_list (fun (ident, mval) ->
            dot ^^ Pp_cabs.pp_cabs_identifier ident ^^ equals ^^^ pp_mem_value mval
          ) xs
        )
    | MVunion (tag_sym, membr_ident, mval) ->
        parens (!^ "union" ^^^ !^ (Pp_symbol.to_string_pretty tag_sym)) ^^ braces (
          dot ^^ Pp_cabs.pp_cabs_identifier membr_ident ^^ equals ^^^
          pp_mem_value mval
        )


  
  
  (* TODO: this is stupid, we need to allow the outside work to specify
     what memory range is is device *)
  let device_ranges : (address * address) list =
    (* TODO: these are some hardcoded ranges to match the Charon tests... *)
    (* NOTE: these two ranges only have 4 bytes (e.g. one int) *)
    [ (N.of_int64 0x40000000L, N.of_int64 0x40000004L)
    ; (N.of_int64 0xABCL, N.of_int64 0XAC0L) ]
  
  
  
  
  
  
  
  
  let string_of_provenance = function
    | Prov_none -> ""
    | Prov_some alloc_id ->
        N.to_string alloc_id
    | Prov_device ->
        "dev"





  (* TODO: DEBUG *)
  let print_bytemap str =
    if !Debug_ocaml.debug_level > 4 then begin
      Printf.fprintf stderr "BEGIN BYTEMAP ==> %s\n" str;
      get >>= fun st ->
      IntMap.iter (fun addr (prov, c_opt) ->
        Printf.fprintf stderr "@%s ==> %s: %s\n"
          (N.to_string addr)
          (string_of_provenance prov)
          (match c_opt with None -> "UNSPEC" | Some c -> string_of_int (int_of_char c))
      ) st.bytemap;
      prerr_endline "END";
    return ()
    end else
      return ()

  
  let get_allocation alloc_id : allocation memM =
    get >>= fun st ->
    match IntMap.find_opt alloc_id st.allocations with
      | Some ret ->
          return ret
      | None ->
          fail (MerrOutsideLifetime ("Concrete.get_allocation, alloc_id=" ^ N.to_string alloc_id))
  
  let is_within_bound alloc_id addr =
    get_allocation alloc_id >>= fun alloc ->
    return (N.less_equal alloc.base addr && N.less addr (N.add alloc.base alloc.size))
  
  let is_within_device ty addr =
    return begin
      List.exists (fun (min, max) ->
        N.less_equal min addr && N.less_equal (N.add addr (N.of_int (sizeof ty))) max
      ) device_ranges
    end
  
  let allocate_static tid pref (IV (_, align)) ty : pointer_value memM =
(*    print_bytemap "ENTERING ALLOC_STATIC" >>= fun () -> *)
    let size = N.of_int (sizeof ty) in
    modify begin fun st ->
      let alloc_id = st.next_alloc_id in
      let addr = Nat_big_num.(
        let m = modulus st.next_address align in
        if equal m zero then st.next_address else add st.next_address (sub align m)
      ) in
      
      Debug_ocaml.print_debug 1 [] (fun () ->
        "STATIC ALLOC - pref: " ^ String_symbol.string_of_prefix pref ^
        " --> alloc_id= " ^ N.to_string alloc_id ^
        ", size= " ^ N.to_string size ^
        ", addr= " ^ N.to_string addr
      );
      ( PV (Prov_some alloc_id, PVconcrete addr)
      , { st with
            next_alloc_id= Nat_big_num.succ st.next_alloc_id;
            allocations= IntMap.add alloc_id {base= addr; size= size} st.allocations;
            next_address= Nat_big_num.add addr size } )
    end
  
  
  let allocate_dynamic tid pref (IV (_, align_n)) (IV (_, size_n)) =
(*    print_bytemap "ENTERING ALLOC_DYNAMIC" >>= fun () -> *)
    modify (fun st ->
      let alloc_id = st.next_alloc_id in
      let addr = Nat_big_num.(add st.next_address (sub align_n (modulus st.next_address align_n))) in
      ( PV (Prov_some st.next_alloc_id, PVconcrete addr)
      , { st with
            next_alloc_id= Nat_big_num.succ st.next_alloc_id;
            allocations= IntMap.add alloc_id {base= addr; size= size_n} st.allocations;
            next_address= Nat_big_num.add addr size_n } )
    )
  
  
  let kill : pointer_value -> unit memM = function
    | PV (_, PVnull _) ->
          fail (MerrOther "attempted to kill with a null pointer")
    | PV (_, PVfunction _) ->
          fail (MerrOther "attempted to kill with a function pointer")
    | PV (Prov_none, PVconcrete _) ->
          fail (MerrOther "attempted to kill with a pointer lacking a provenance")
    | PV (Prov_device, PVconcrete _) ->
        (* TODO: should that be an error ?? *)
        return ()
    | PV (Prov_some alloc_id, PVconcrete addr) ->
        is_within_bound alloc_id addr >>= function
          | false ->
              fail (MerrOther "attempted to kill with an out-of-bound pointer")
          | true ->
              Debug_ocaml.print_debug 1 [] (fun () ->
                "KILLING alloc_id= " ^ N.to_string alloc_id
              );
              update begin fun st ->
                {st with allocations= IntMap.remove alloc_id st.allocations}
              end
  
  (* INTERNAL: fetch_bytes *)
  let fetch_bytes base_addr n_bytes =
    get >>= fun st ->
    return (
      List.map (fun addr ->
        match IntMap.find_opt addr st.bytemap with
          | Some b ->
              b
          | None ->
              (Prov_none, None)
      ) (List.init n_bytes (fun z ->
           (* NOTE: the reversal in the offset is to model
              little-endianness *)
(*           let offset = n_bytes - 1 - z in *)
(*KKK*)
           let offset = z in
           Nat_big_num.(add base_addr (of_int offset))
         ))
    )
  
  let write_bytes base_addr bs =
    get >>= fun st ->
    return begin
      (* NOTE: the reversal caused by the fold_left is what we want because of
         little-endianness *)
      List.fold_left (fun acc (addr, b) ->
        IntMap.add addr b acc
      ) st.bytemap begin
          List.init (List.length bs) (fun z ->
            (Nat_big_num.(add base_addr (of_int z), L.nth bs z))
          )
        end
    end
  
  let int64_of_bytes is_signed bs =
    (* NOTE: the reverse is from little-endianness *)
    match List.rev bs with
      | [] ->
          assert false
      | cs when L.length cs > 8 ->
          assert false
      | (first::_ as cs) ->
          (* NOTE: this is to preserve the binary signedness *)
          let init =
            if is_signed && N.(equal (succ zero) (extract_num (of_int (int_of_char first)) 7 1)) then
              N.of_int (-1)
            else
              N.zero in
          let rec aux acc = function
            | [] ->
                acc
            | c::cs' ->
                aux N.(bitwise_xor (of_int (int_of_char c)) (shift_left acc 8)) cs' in
          aux init cs
  
  let combine_provenances = function
    | [] ->
        failwith "combine_provenances ==> empty"
    | prov::xs ->
        if List.for_all (fun z -> z = prov) xs then prov else Prov_none
  
  let rec combine_bytes ty (bs : (provenance * char option) list) =
    let extract_unspec xs =
      List.fold_left (fun acc_opt c_opt ->
        match acc_opt, c_opt with
          | None, _ ->
              None
          | _, None ->
              None
          | (Some acc, Some c) ->
              Some (c :: acc)
      ) (Some []) (List.rev xs) in
    match ty with
      | Void0
      | Array0 (_, None)
      | Function0 _ ->
          assert false
      | Basic0 (Integer ity) ->
          let (bs1, bs2) = L.split_at (sizeof ty) bs in
          let (provs, bs1') = List.split bs1 in
          let prov = combine_provenances provs in
          (begin match extract_unspec bs1' with
            | Some cs ->
                MVinteger ( ity
                          , IV (prov, int64_of_bytes (AilTypesAux.is_signed_ity ity) cs))
            | None ->
                MVunspecified ty
          end , bs2)
      | Basic0 (Floating fty) ->
          let (bs1, bs2) = L.split_at (sizeof ty) bs in
          (* we don't care about provenances for floats *)
          let bs1' = List.map snd bs1 in
          (begin match extract_unspec bs1' with
            | Some cs ->
                MVfloating ( fty
                           , Int64.float_of_bits (N.to_int64 (int64_of_bytes true cs)) )
            | None ->
                MVunspecified ty
          end, bs2)
      | Array0 (elem_ty, Some n) ->
          let rec aux n acc cs =
            if n < 0 then
              (MVarray acc, cs)
            else
              let (mval, cs') = combine_bytes elem_ty cs in
              aux (n-1) (mval :: acc) cs'
          in
          aux (Nat_big_num.to_int n) [] bs
      | Pointer0 (_, ref_ty) ->
          let (bs1, bs2) = L.split_at (sizeof ty) bs in
          Debug_ocaml.print_debug 1 [] (fun () -> "TODO: Concrete, assuming pointer repr is unsigned??");
          let (provs, bs1') = List.split bs1 in
          let prov = combine_provenances provs in
          (begin match extract_unspec bs1' with
            | Some cs ->
                MVpointer (ref_ty, PV (prov, PVconcrete (int64_of_bytes false cs)))
            | None ->
                MVunspecified (Core_ctype.Pointer0 (AilTypes.no_qualifiers, ref_ty))
           end, bs2)
      | Atomic0 atom_ty ->
          failwith "TODO: combine_bytes, Atomic"
      | Struct0 tag_sym ->
          let (bs1, bs2) = L.split_at (sizeof ty) bs in
(*
          print_string "COMBINE: ";
          List.iter (fun (_, c_opt) ->
            match c_opt with
              | Some c -> print_string (string_of_int (int_of_char c) ^ " ")
              | None   -> print_string "U "
          ) bs1;
          print_newline ();
*)
          let (rev_xs, _, bs') = List.fold_left (fun (acc_xs, previous_offset, acc_bs) (memb_ident, memb_ty, memb_offset) ->
            let pad = memb_offset - previous_offset in
            let (mval, acc_bs') = combine_bytes memb_ty (L.drop pad acc_bs) in
            ((memb_ident, mval)::acc_xs, previous_offset + sizeof memb_ty, acc_bs')
          ) ([], 0, bs1) (fst (offsetsof tag_sym)) in
          (* TODO: check that bs' = last padding of the struct *)
(*          Printf.printf "|bs'| ==> %d\n" (List.length bs'); *)
          (MVstruct (tag_sym, List.rev rev_xs), bs2)
      | Union0 tag_sym ->
          failwith "TODO: combine_bytes, Union (as value)"
      | Builtin0 str ->
          failwith "TODO: combine_bytes, Builtin"
  
  
  (* INTERNAL bytes_of_int64 *)
  let bytes_of_int64 is_signed size i : (char option) list =
    let nbits = 8 * size in
    let (min, max) =
      if is_signed then
        ( N.negate (N.pow_int (N.of_int 2) (nbits-1))
        , N.sub (N.pow_int (N.of_int 2) (nbits-1)) N.(succ zero) )
      else
        ( N.zero
        , N.sub (N.pow_int (N.of_int 2) nbits) N.(succ zero) ) in
    if not (min <= i && i <= max) || nbits > 64 then begin
      Printf.printf "failed: bytes_of_int64(%s), i= %s, nbits= %d, [%s ... %s]\n"
        (if is_signed then "signed" else "unsigned")
        (N.to_string i) nbits (N.to_string min) (N.to_string max);
      assert false
    end else
      List.init size (fun n ->
        Some (char_of_int (N.to_int (N.extract_num i (8*n) 8)))
      )
  
  let rec typeof mval =
    let open Core_ctype in
    match mval with
      | MVunspecified ty ->
          ty
      | MVinteger (ity, _) ->
          Basic0 (AilTypes.Integer ity)
      | MVfloating (fty, _) ->
          Basic0 (AilTypes.Floating fty)
      | MVpointer (ref_ty, _) ->
          Pointer0 (AilTypes.no_qualifiers, ref_ty)
      | MVarray [] ->
          (* ill-formed value *)
          assert false
      | MVarray ((mval::_) as mvals) ->
          (* TODO: checking all the elements would be stupidly slow, but this
             feels wrong *)
          Array0 (typeof mval, Some (N.of_int (List.length mvals)))
      | MVstruct (tag_sym, _) ->
          Struct0 tag_sym
      | MVunion (tag_sym, _, _) ->
          Union0 tag_sym
  
  (* INTERNAL explode_bytes *)
  let rec explode_bytes mval : (provenance * char option) list =
    match mval with
      | MVunspecified ty ->
          List.init (sizeof ty) (fun _ -> (Prov_none, None))
      | MVinteger (ity, IV (prov, n)) ->
          List.map (fun z -> (prov, z)) begin
            bytes_of_int64
              (AilTypesAux.is_signed_ity ity)
              (sizeof (Basic0 (Integer ity))) n
          end
      | MVfloating (fty, fval) ->
          List.map (fun z -> (Prov_none, z)) begin
            bytes_of_int64
              true (* TODO: check that *)
              (sizeof (Basic0 (Floating fty))) (N.of_int64 (Int64.bits_of_float fval))
          end
      | MVpointer (_, PV (prov, ptrval_)) ->
          Debug_ocaml.print_debug 1 [] (fun () -> "NOTE: we fix the sizeof pointers to 8 bytes");
          let ptr_size = match Impl.sizeof_pointer with
            | None ->
                failwith "the concrete memory model requires a complete implementation"
            | Some z ->
                z in
          begin match ptrval_ with
            | PVnull _ ->
                Debug_ocaml.print_debug 1 [] (fun () -> "NOTE: we fix the representation of all NULL pointers to be 0x0");
                List.init ptr_size (fun _ -> (Prov_none, Some '\000'))
            | PVfunction _ ->
                failwith "TODO: explode_bytes, PVfunction"
            | PVconcrete addr ->
                List.map (fun z -> (prov, z)) begin
                  bytes_of_int64
                    false (* we model address as unsigned *)
                    ptr_size addr
                end
          end
      | MVarray mvals ->
          (* TODO: use a fold? *)
          L.concat (
            List.map explode_bytes mvals
          )
      | MVstruct (tag_sym, xs) ->
          let (offs, last_off) = offsetsof tag_sym in
          let final_pad = sizeof (Core_ctype.Struct0 tag_sym) - last_off in
          snd begin
            (* TODO: rewrite now that offsetsof returns the paddings *)
            List.fold_left2 (fun (last_off, acc) (ident, ty, off) (_, mval) ->
              let pad = off - last_off in
              ( off + sizeof ty
              , acc @
                List.init pad (fun _ -> (Prov_none, None)) @
                explode_bytes mval )
            ) (0, []) offs xs
          end @
          List.init final_pad (fun _ -> (Prov_none, None))
      | MVunion (tag_sym, memb_ident, mval) ->
          let size = sizeof (Core_ctype.Union0 tag_sym) in
          let bs = explode_bytes mval in
          bs @ List.init (size - List.length bs) (fun _ -> (Prov_none, None))

  
  
  let load loc ty (PV (prov, ptrval_)) =
(*    print_bytemap "ENTERING LOAD" >>= fun () -> *)
    let do_load addr =
      get >>= fun st ->
      fetch_bytes addr (sizeof ty) >>= fun bs ->
      let (mval, bs') = combine_bytes ty bs in
      begin match bs' with
        | [] ->
            return (Footprint, mval)
        | _ ->
            fail (MerrWIP "load, bs' <> []")
      end in
    match (prov, ptrval_) with
      | (_, PVnull _) ->
          fail (MerrAccess (loc, LoadAccess, NullPtr))
      | (_, PVfunction _) ->
          fail (MerrAccess (loc, LoadAccess, FunctionPtr))
      | (Prov_none, _) ->
          fail (MerrAccess (loc, LoadAccess, OutOfBoundPtr))
      | (Prov_device, PVconcrete addr) ->
          begin is_within_device ty addr >>= function
            | false ->
                fail (MerrAccess (loc, LoadAccess, OutOfBoundPtr))
            | true ->
                do_load addr
          end
      | (Prov_some alloc_id, PVconcrete addr) ->
          begin is_within_bound alloc_id addr >>= function
            | false ->
                Debug_ocaml.print_debug 1 [] (fun () ->
                  "LOAD out of bound, alloc_id=" ^ N.to_string alloc_id
                );
                fail (MerrAccess (loc, LoadAccess, OutOfBoundPtr))
            | true ->
                do_load addr
          end
  
  
  let store loc ty (PV (prov, ptrval_)) mval =
    Debug_ocaml.print_debug 3 [] (fun () ->
      "ENTERING STORE: ty=" ^
      String_core_ctype.string_of_ctype ty ^ "@" ^
      Pp_utils.to_plain_string (pp_pointer_value (PV (prov, ptrval_))) ^
      ", mval= " ^ Pp_utils.to_plain_string (pp_mem_value mval)
    );
    if not (ctype_equal ty (typeof mval)) then begin
      Printf.printf "STORE ty          ==> %s\n"
        (String_core_ctype.string_of_ctype ty);
      Printf.printf "STORE typeof mval ==> %s\n"
        (String_core_ctype.string_of_ctype (typeof mval));
      Printf.printf "STORE ==> %s\n" (Location_ocaml.location_to_string loc);
      Printf.printf "STORE mval ==> %s\n"
        (Pp_utils.to_plain_string (pp_mem_value mval));
      fail (MerrOther "store with an ill-typed memory value")
    end else
      let do_store addr =
        let bs = List.mapi (fun i b ->
          (Nat_big_num.add addr (Nat_big_num.of_int i), b)
        ) (explode_bytes mval) in
        update begin fun st ->
          { st with bytemap=
            List.fold_left (fun acc (addr, b) ->
              IntMap.add addr b acc
            ) st.bytemap bs }
        end >>
        print_bytemap ("AFTER STORE => " ^ Location_ocaml.location_to_string loc) >>= fun () ->
        return Footprint in
      match (prov, ptrval_) with
        | (_, PVnull _) ->
            fail (MerrAccess (loc, StoreAccess, NullPtr))
        | (_, PVfunction _) ->
            fail (MerrAccess (loc, StoreAccess, FunctionPtr))
        | (Prov_none, _) ->
            fail (MerrAccess (loc, StoreAccess, OutOfBoundPtr))
        | (Prov_device, PVconcrete addr) ->
            begin is_within_device ty addr >>= function
              | false ->
                  fail (MerrAccess (loc, StoreAccess, OutOfBoundPtr))
              | true ->
                  do_store addr
            end
        | (Prov_some alloc_id, PVconcrete addr) ->
            begin is_within_bound alloc_id addr >>= function
              | false ->
                  fail (MerrAccess (loc, StoreAccess, OutOfBoundPtr))
              | true ->
                  do_store addr
            end
  
  let null_ptrval ty =
    PV (Prov_none, PVnull ty)
  
  let fun_ptrval sym =
    PV (Prov_none, PVfunction sym)
  
  let eq_ptrval (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
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
      | (PVconcrete addr1, PVconcrete addr2) ->
          if prov1 <> prov2 then
            Eff.msum "pointer equality (different provenances)"
              [ ("true", return true)
              ; ("false", return false) ]
          else
            return (Nat_big_num.equal addr1 addr2)
  
  let ne_ptrval ptrval1 ptrval2 =
    eq_ptrval ptrval1 ptrval2 >>= fun b ->
    return (not b)
  
  let lt_ptrval (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
      | (PVconcrete addr1, PVconcrete addr2) ->
          (* TODO: provenance *)
          return (Nat_big_num.compare addr1 addr2 == -1)
      | _ ->
          fail (MerrWIP "lt_ptrval")
  
  let gt_ptrval (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
      | (PVconcrete addr1, PVconcrete addr2) ->
          (* TODO: provenance *)
          return (Nat_big_num.compare addr1 addr2 == 1)
      | _ ->
          fail (MerrWIP "gt_ptrval")
  
  let le_ptrval (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
      | (PVconcrete addr1, PVconcrete addr2) ->
          (* TODO: provenance *)
          let cmp = Nat_big_num.compare addr1 addr2 in
          return (cmp = -1 || cmp = 0)
      | _ ->
          fail (MerrWIP "le_ptrval")
  
  let ge_ptrval (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
      | (PVconcrete addr1, PVconcrete addr2) ->
          (* TODO: provenance *)
          let cmp = Nat_big_num.compare addr1 addr2 in
          return (cmp = 1 || cmp = 0)
      | _ ->
          fail (MerrWIP "ge_ptrval")
  
  
  let diff_ptrval diff_ty ptrval1 ptrval2 =
    match ptrval1, ptrval2 with
      | PV (Prov_some alloc_id1, (PVconcrete addr1)), PV (Prov_some alloc_id2, (PVconcrete addr2))
        when N.equal alloc_id1 alloc_id2 ->
          get_allocation alloc_id1 >>= fun alloc ->
          (* NOTE: this is not like "is_within_bound" because it allows one-past pointers *)
          if   N.less_equal alloc.base addr1
             && N.less_equal addr1 (N.add alloc.base alloc.size)
             && N.less_equal alloc.base addr2
             && N.less_equal addr2 (N.add alloc.base alloc.size) then
            (* NOTE: the result of subtraction of two pointer values is an integer value with
               empty provenance, irrespective of the operand provenances *)
            (* TODO: check that this is correct for arrays of arrays ... *)
            (* TODO: if not, sync with symbolic defacto *)
            let diff_ty' = match diff_ty with
              | Core_ctype.Array0 (elem_ty, _) ->
                  elem_ty
              | _ ->
                  diff_ty
              in
            return (IV (Prov_none, N.div (N.sub addr1 addr2) (N.of_int (sizeof diff_ty'))))
          else
            fail MerrPtrdiff
      | _ ->
          fail MerrPtrdiff
  
  
  let validForDeref_ptrval = function
    | PV (_, PVnull _)
    | PV (_, PVfunction _) ->
        false
    | PV (Prov_device, PVconcrete _) ->
        true
    | PV (Prov_some _, PVconcrete _) ->
        true
    | PV (Prov_none, _) ->
        false
  
  let isWellAligned_ptrval ref_ty = function
    | PV (_, PVnull _) ->
        return true
    | PV (_, PVfunction _) ->
        failwith "TODO (Concrete): isWellAligned_ptrval, PVfunction"
    | PV (_, PVconcrete addr) ->
        return (N.(equal (modulus addr (of_int (alignof ref_ty))) zero))
  
  let ptrcast_ival _ _ (IV (prov, n)) =
    if not (N.equal n N.zero) then
      (* STD §6.3.2.3#5 *)
      Debug_ocaml.warn [] (fun () ->
        "implementation defined cast from integer to pointer"
      );
    match prov with
      | Prov_none ->
          (* TODO: check (in particular is that ok to only allow device pointers when there is no provenance? *)
          if List.exists (fun (min, max) -> N.less_equal min n && N.less_equal n max) device_ranges then
            return (PV (Prov_device, PVconcrete n))
          else
            return (PV (Prov_none, PVconcrete n))
      | _ ->
          return (PV (prov, PVconcrete n))
  
  let offsetof_ival tag_sym memb_ident =
    let (xs, _) = offsetsof tag_sym in
    let pred (ident, _, _) =
      cabs_ident_equal ident memb_ident in
    match List.find_opt pred xs with
      | Some (_, _, offset) ->
          IV (Prov_none, N.of_int offset)
      | None ->
          failwith "Concrete.offsetof_ival: invalid memb_ident"
  
  let array_shift_ptrval (PV (prov, ptrval_)) ty (IV (_, ival)) =
    let offset = (Nat_big_num.(mul (of_int (sizeof ty)) ival)) in
    PV (prov, match ptrval_ with
      | PVnull _ ->
          Debug_ocaml.print_debug 1 [] (fun () -> "TODO(check): array_shift_ptrval, PVnull");
          PVconcrete offset
      | PVfunction _ ->
          failwith "Concrete.array_shift_ptrval, PVfunction"
      | PVconcrete addr ->
          PVconcrete (N.add addr offset))
  
  let member_shift_ptrval (PV (prov, ptrval_)) tag_sym memb_ident =
    let IV (_, offset) = offsetof_ival tag_sym memb_ident in
    PV (prov, match ptrval_ with
      | PVnull _ ->
          PVconcrete offset
      | PVfunction _ ->
          failwith "Concrete.member_shift_ptrval, PVfunction"
      | PVconcrete addr ->
          PVconcrete (N.add addr offset))
  
  let concurRead_ival ity sym =
    failwith "TODO: concurRead_ival"
  
  let integer_ival n =
    IV (Prov_none, n)
  
  let max_ival ity =
    let open Nat_big_num in
    IV (Prov_none, begin match Impl.sizeof_ity ity with
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
                failwith "TODO: max_ival: Enum"
            | IBuiltin _ ->
                failwith "TODO: max_ival: IBuiltin"
          end
      | None ->
          failwith "the concrete memory model requires a complete implementation"
    end)
  
  let min_ival ity =
    let open Nat_big_num in
    IV (Prov_none, begin match ity with
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
          failwith "TODO: minv_ival: Enum, Builtin"
    end)
  

  (* TODO: conversion? *)
  let intcast_ptrval _ ity (PV (prov, ptrval_)) =
    match ptrval_ with
      | PVnull _ ->
          return (IV (prov, Nat_big_num.zero))
      | PVfunction _ ->
          failwith "TODO: intcast_ptrval PVfunction"
      | PVconcrete addr ->
          let IV (_, ity_max) = max_ival ity in
          let IV (_, ity_min) = min_ival ity in
          if N.(less addr ity_min || less ity_max addr) then
            fail MerrIntFromPtr
          else
            return (IV (prov, addr))

let combine_prov prov1 prov2 =
  match (prov1, prov2) with
    | (Prov_none, Prov_none) ->
        Prov_none
    | (Prov_none, Prov_some id) ->
        Prov_some id
(*
    | (Prov_none, Prov_wildcard) ->
        Prov_wildcard
*)
    | (Prov_none, Prov_device) ->
        Prov_device
    | (Prov_some id, Prov_none) ->
        Prov_some id
    | (Prov_some id1, Prov_some id2) ->
        if id1 = id2 then
          Prov_some id1
        else
          Prov_none
(*
    | (Prov_some _, Prov_wildcard) ->
        Prov_wildcard
*)
    | (Prov_some _, Prov_device) ->
        Prov_device
    | (Prov_device, Prov_none) ->
        Prov_device
    | (Prov_device, Prov_some _) ->
        Prov_device
    | (Prov_device, Prov_device) ->
        Prov_device
(*
    | (Prov_device, Prov_wildcard) ->
        Prov_wildcard
    
    | (Prov_wildcard, _) ->
        Prov_wildcard
*)


  let op_ival iop (IV (prov1, n1)) (IV (prov2, n2)) =
    IV (combine_prov prov1 prov2, begin match iop with
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
  
  let sizeof_ival ty =
    IV (Prov_none, Nat_big_num.of_int (sizeof ty))
  let alignof_ival ty =
    IV (Prov_none, Nat_big_num.of_int (alignof ty))
  
  let bitwise_complement_ival _ (IV (prov, n)) =
    (* TODO *)
    (* prerr_endline "Concrete.bitwise_complement ==> HACK"; *)
    IV (prov, Nat_big_num.(sub (negate n) (of_int 1)))

  let bitwise_and_ival _ (IV (prov1, n1)) (IV (prov2, n2)) =
    IV (combine_prov prov1 prov2, Nat_big_num.bitwise_and n1 n2)
  let bitwise_or_ival _ (IV (prov1, n1)) (IV (prov2, n2)) =
    IV (combine_prov prov1 prov2, Nat_big_num.bitwise_or n1 n2)
  let bitwise_xor_ival _ (IV (prov1, n1)) (IV (prov2, n2)) =
    IV (combine_prov prov1 prov2, Nat_big_num.bitwise_xor n1 n2)
  
  let case_integer_value (IV (_, n)) f_concrete _ =
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
    match fop with
      | FloatAdd ->
          fval1 +. fval2
      | FloatSub ->
          fval1 +. fval2
      | FloatMul ->
          fval1 *. fval2
      | FloatDiv ->
          fval1 /. fval2
  
  let eq_fval fval1 fval2 =
    fval1 = fval2
  
  let lt_fval fval1 fval2 =
    fval1 < fval2
  
  let le_fval fval1 fval2 =
    fval1 <= fval2
  
  let fvfromint (IV (_, n)) =
    Int64.float_of_bits (N.to_int64 n)
  
  let ivfromfloat ity fval =
    IV (Prov_none, N.of_int64 (Int64.bits_of_float fval))
  
  let eq_ival _ (IV (_, n1)) (IV (_, n2)) =
    Some (Nat_big_num.equal n1 n2)
  let lt_ival _ (IV (_, n1)) (IV (_, n2)) =
    Some (Nat_big_num.compare n1 n2 = -1)
  let le_ival _ (IV (_, n1)) (IV (_, n2)) =
    let cmp = Nat_big_num.compare n1 n2 in
    Some (cmp = -1 || cmp = 0)
  
  let eval_integer_value (IV (_, n)) =
    Some n
  
  let unspecified_mval ty =
    MVunspecified ty
  let integer_value_mval ity ival =
    MVinteger (ity, ival)
  let floating_value_mval fty fval =
    MVfloating (fty, fval)
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
      | MVunspecified ty ->
          f_unspec ty
      | MVinteger (ity, ival) ->
          f_ival ity ival
      | MVfloating (fty, fval) ->
          f_fval fty fval
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
  
  


  let pp_pretty_pointer_value = pp_pointer_value
  let pp_pretty_integer_value _ = pp_integer_value
  let pp_pretty_mem_value _ = pp_mem_value
  
  
  (* TODO: validate more, but looks good *)
  let memcmp ptrval1 ptrval2 (IV (_, size_n)) =
    let unsigned_char_ty = Core_ctype.Basic0 (AilTypes.(Integer (Unsigned Ichar))) in
    let rec get_bytes ptrval acc = function
      | 0 ->
          return (List.rev acc)
      | size ->
          load Location_ocaml.unknown unsigned_char_ty ptrval >>= function
            | (_, MVinteger (_, (IV (byte_prov, byte_n)))) ->
                let ptr' = array_shift_ptrval ptrval unsigned_char_ty (IV (Prov_none, Nat_big_num.(succ zero))) in
                get_bytes ptr' (byte_n :: acc) (size-1)
            | _ ->
                assert false in
     get_bytes ptrval1 [] (Nat_big_num.to_int size_n) >>= fun bytes1 ->
     get_bytes ptrval2 [] (Nat_big_num.to_int size_n) >>= fun bytes2 ->
     
     let open Nat_big_num in
     return (IV (Prov_none, List.fold_left (fun acc (n1, n2) ->
                   if equal acc zero then of_int (Nat_big_num.compare n1 n2) else acc
                 ) zero (List.combine bytes1 bytes2)))


  (* JSON serialisation *)

  open Json

  let serialise_prov = function
    | Prov_none -> `String "None"
    | Prov_some n -> `Assoc [("Some", BigIntJSON.serialise n)]
    | Prov_device -> `String "Device"
  let parse_prov = function
    | `String "None" -> Prov_none
    | `Assoc [("Some", n)] -> Prov_some (BigIntJSON.parse n)
    | `String "Device" -> Prov_device
    | _ -> throw "Concrete.provenance"

  let serialise_ptrval_base = function
    | PVnull cty -> `Assoc [("PVnull", CtypeJSON.serialise cty)]
    | PVfunction sym -> `Assoc [("PVfunction", SymJSON.serialise sym)]
    | PVconcrete n -> `Assoc [("PVconcrete", BigIntJSON.serialise n)]
  let parse_ptrval_base = function
    | `Assoc [("PVnull", cty)] -> PVnull (CtypeJSON.parse cty)
    | `Assoc [("PVfunction", sym)] -> PVfunction (SymJSON.parse sym)
    | `Assoc [("PVconcrete", n)] -> PVconcrete (BigIntJSON.parse n)
    | _ -> throw "Concrete.pointer_value_base"

  let serialise_pointer_value = function
    | PV (prov, pvb) -> `List [serialise_prov prov; serialise_ptrval_base pvb]
  let parse_pointer_value = function
    | `List [prov; pvb] -> PV (parse_prov prov, parse_ptrval_base pvb)
    | _ -> throw "Concrete.pointer_value"

  let serialise_integer_value = function
    | IV (prov, n) -> `List [serialise_prov prov; BigIntJSON.serialise n]
  let parse_integer_value = function
    | `List [prov; n] -> IV (parse_prov prov, BigIntJSON.parse n)
    | _ -> throw "Concrete.integer_value"

  let serialise_floating_value f = `String (string_of_float f)
  let parse_floating_value = function
    | `String s -> float_of_string s
    | _ -> throw "Concrete.floating_value"

  let rec serialise_mem_value = function
    | MVunspecified cty ->
      `Assoc [("MVunspecified", CtypeJSON.serialise cty)]
    | MVinteger (ait, iv) ->
      `Assoc [("MVinteger", `List [AilIntJSON.serialise ait;
                                  serialise_integer_value iv])]
    | MVfloating (ft, fv) ->
      `Assoc [("MVfloating", `List [AilFloatingJSON.serialise ft;
                                    serialise_floating_value fv])]
    | MVpointer (cty, pv) ->
      `Assoc [("MVpointer", `List [CtypeJSON.serialise cty;
                                   serialise_pointer_value pv])]
    | MVarray mvs ->
      `List (List.map serialise_mem_value mvs)
    | MVstruct (sym, fs) ->
      `Assoc [("MVstruct", `List [SymJSON.serialise sym;
                                  `List (List.map serialise_field fs)])]
    | MVunion (sym, cid, mv) ->
      `Assoc [("MVunion", `List [SymJSON.serialise sym;
                                  serialise_field (cid, mv)])]
  and serialise_field (cid, mv) =
    `List [ CabsIdJSON.serialise cid; serialise_mem_value mv]
  let rec parse_mem_value = function
    | `Assoc [("MVunspecified", cty)] ->
      MVunspecified (CtypeJSON.parse cty)
    | `Assoc [("MVinteger", `List [ait; iv])] ->
      MVinteger (AilIntJSON.parse ait, parse_integer_value iv)
    | `Assoc [("MVfloating", `List [ft; fv])] ->
      MVfloating (AilFloatingJSON.parse ft, parse_floating_value fv)
    | `Assoc [("MVpointer", `List [cty; pv])] ->
      MVpointer (CtypeJSON.parse cty, parse_pointer_value pv)
    | `List mvs ->
      MVarray (List.map parse_mem_value mvs)
    | `Assoc [("MVstruct", `List [sym; `List fs])] ->
      MVstruct (SymJSON.parse sym, List.map parse_field fs)
    | `Assoc [("MVunion", `List [sym; `List [cid; mv]])] ->
      MVunion (SymJSON.parse sym, CabsIdJSON.parse cid, parse_mem_value mv)
    | _ -> throw "Concrete.mem_value"
  and parse_field = function
    | `List [cid; mv] -> (CabsIdJSON.parse cid, parse_mem_value mv)
    | _ -> throw "Concrete.mem_value"

  let serialise_map f m =
    let serialise_entry (k, v) =
      `List [BigIntJSON.serialise k; f v]
    in
    `List (List.map serialise_entry (IntMap.bindings m))

  let serialise_allocation alloc =
    `Assoc [
      ("base", BigIntJSON.serialise alloc.base);
      ("size", BigIntJSON.serialise alloc.size);
    ]

  let serialise_byte (p, c_opt) =
    let serialised_char = match c_opt with
      | None -> `Null
      | Some c -> `String (String.make 1 c)
    in `List [serialise_prov p; serialised_char]

  let serialise_mem_state st =
    `Assoc [
      ("next_alloc_id", BigIntJSON.serialise st.next_alloc_id);
      ("allocations",   serialise_map serialise_allocation st.allocations);
      ("next_address",  BigIntJSON.serialise st.next_address);
      ("bytemap",       serialise_map serialise_byte st.bytemap)
    ]


end

include Concrete
