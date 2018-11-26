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
      Function0
        begin
          (AilTypes.no_qualifiers, unqualify ret_ty),
          List.map (fun (_, ty) -> (AilTypes.no_qualifiers, unqualify ty)) xs,
          b
        end
    | Array0 (elem_ty, n_opt) -> Array0 (unqualify elem_ty, n_opt)
    | Pointer0 (_, ref_ty) ->
      Pointer0 (AilTypes.no_qualifiers, unqualify ref_ty)
    | Atomic0 atom_ty ->
      Atomic0 (unqualify atom_ty)
  in
  Core_ctype.instance_Basic_classes_Eq_Core_ctype_ctype_dict.isEqual_method
    (unqualify ty1) (unqualify ty2)

module Eff : sig
  type ('a, 'err, 'cs, 'st) eff = ('a, string, 'err, 'cs, 'st) Nondeterminism.ndM
  val return: 'a -> ('a, 'err, 'cs, 'st) eff
  val (>>=): ('a, 'err, 'cs, 'st) eff -> ('a -> ('b, 'err, 'cs, 'st) eff)
          -> ('b, 'err, 'cs, 'st) eff
  val (>>): ('a, 'err, 'cs, 'st) eff -> ('b, 'err, 'cs, 'st) eff
         -> ('b, 'err, 'cs, 'st) eff
  val read: ('st -> 'a) -> ('a, 'err, 'cs, 'st) eff
  val update: ('st -> 'st) -> (unit, 'err, 'cs, 'st) eff
  val modify: ('st -> 'a * 'st) -> ('a, 'err, 'cs, 'st) eff
  val get: ('st, 'err, 'cs, 'st) eff
  val put: 'st -> (unit, 'err, 'cs, 'st) eff
  val fail: 'err -> ('a, 'err, 'cs, 'st) eff
  val mapM: ('a -> ('b, 'err, 'cs, 'st) eff) -> 'a list
         -> ('b list, 'err, 'cs, 'st) eff
  val foldlM: ('a -> 'b -> ('a, string, 'err, 'cs, 'st) Nondeterminism.ndM) -> 'a
         -> 'b list -> ('a, string, 'err, 'cs, 'st) Nondeterminism.ndM
  val msum: string -> (string * ('a, 'err, 'cs, 'st) eff) list
         -> ('a, 'err, 'cs, 'st) eff
end = struct
  open Nondeterminism
  type ('a, 'err, 'cs, 'st) eff = ('a, string, 'err, 'cs, 'st) ndM
  let return = nd_return
  let (>>=) = nd_bind
  let (>>) f g = f >>= (fun _ -> g)
  let read = nd_read
  let update = nd_update
  let modify f =
    nd_get >>= fun st ->
    let (ret, st') = f st in
    nd_put st' >>= fun () ->
    return ret
  let get = nd_get
  let put = nd_put
  let fail err = kill (Other err)
  let mapM _ _ = failwith "TODO: mapM"
  let foldlM = nd_foldlM
  let msum str xs = msum Mem_common.instance_Nondeterminism_Constraints_Mem_common_mem_constraint_dict () str xs
end

module IntMap = Map.Make(struct
  type t = N.num
  let compare = N.compare
end)

let optfailwith str = function
  | Some n -> n
  | None -> failwith str

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

and sizeof ty =
  let err str b =
    let impl = "The Twin model requires a complete implementation of sizeof "
    in optfailwith (impl ^ str) b
  in
  match ty with
  | Void0 | Array0 (_, None) | Function0 _ ->
    assert false
  | Basic0 (Integer ity) as ty ->
    err ("INTEGER => " ^ String_core_ctype.string_of_ctype ty)
        (Impl.sizeof_ity ity)
  | Basic0 (Floating fty) ->
    err "FLOAT" (Impl.sizeof_fty fty)
  | Array0 (elem_ty, Some n) ->
    N.to_int n * sizeof elem_ty
  | Pointer0 _ ->
    err "POINTER" Impl.sizeof_pointer
  | Atomic0 atom_ty ->
    sizeof atom_ty
  | Struct0 tag_sym as ty ->
    let (_, max_offset) = offsetsof tag_sym in
    let align = alignof ty in
    let x = max_offset mod align in
    if x = 0 then max_offset else max_offset + (align - x)
  | Union0 tag_sym ->
    begin match Pmap.find tag_sym (Tags.tagDefs ()) with
      | Tags.StructDef _ -> assert false
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

and alignof ty =
  let err str b =
    let impl = "The Twin model requires a complete implementation of alignof "
    in optfailwith (impl ^ str) b
  in
  match ty with
  | Void0 ->
    assert false
  | Basic0 (Integer ity) ->
    err "INTEGER" (Impl.alignof_ity ity)
  | Basic0 (Floating fty) ->
    err "FLOAT" (Impl.alignof_fty fty)
  | Array0 (_, None) ->
    assert false
  | Array0 (elem_ty, Some n) ->
    alignof elem_ty
  | Function0 _ ->
    assert false
  | Pointer0 _ ->
    err "POINTER" Impl.alignof_pointer
  | Atomic0 atom_ty ->
    alignof atom_ty
  | Struct0 tag_sym ->
    begin match Pmap.find tag_sym (Tags.tagDefs ()) with
    | Tags.UnionDef _ -> assert false
    | Tags.StructDef membrs  ->
      (* NOTE: Structs (and unions) alignment is that of the maximum alignment
         of any of their components. *)
      List.fold_left (fun acc (_, ty) ->
        max (alignof ty) acc
      ) 0 membrs
    end
  | Union0 tag_sym ->
    begin match Pmap.find tag_sym (Tags.tagDefs ()) with
    | Tags.StructDef _ -> assert false
    | Tags.UnionDef membrs ->
      (* NOTE: Structs (and unions) alignment is that of the maximum alignment
         of any of their components. *)
      List.fold_left (fun acc (_, ty) ->
        max (alignof ty) acc
      ) 0 membrs
    end
  | Builtin0 str ->
    failwith "TODO: sizeof Builtin"

module Twin : Memory = struct
  let name = "I am the twin allocation memory model"

  type provenance =
    | Prov_none
    | Prov_some of N.num
    | Prov_double of N.num * N.num
    | Prov_device

  (* Note: using Z instead of int64 because we need to be able to have
     unsigned 64bits values *)
  type pointer_value_base =
    | PVnull of ctype0
    | PVfunction of Symbol.sym
    | PVconcrete of N.num

  type pointer_value =
    | PV of provenance * pointer_value_base

  type integer_value = N.num

  (* TODO: HACK using 64 bits Ocaml's float *)
  type floating_value = float

  type mem_value =
    | MVunspecified of Core_ctype.ctype0
    | MVinteger of AilTypes.integerType * integer_value
    | MVfloating of AilTypes.floatingType * floating_value
    | MVpointer of Core_ctype.ctype0 * pointer_value
    | MVarray of mem_value list
    | MVstruct of Symbol.sym (*struct/union tag*)
                  * (Cabs.cabs_identifier (*member*) * Core_ctype.ctype0 * mem_value) list
    | MVunion of Symbol.sym (*struct/union tag*)
                 * Cabs.cabs_identifier (*member*) * mem_value

  type mem_iv_constraint = integer_value mem_constraint
  let cs_module = (module struct
    type t = mem_iv_constraint
    let negate x = MC_not x
    type 'a eff = Eff of (bool -> ('a * bool))
    let return a = Eff (fun b -> (a, b))
    let bind (Eff ma) f =
      Eff (fun b -> let (a, b') = ma b in let Eff mb = f a in mb b')
    let rec foldlM f a = function
    | [] -> return a
    | x::xs -> bind (f a x) (fun fax -> foldlM f fax xs)
    let runEff (Eff ma) = fst (ma true)
    let string_of_solver = return []
    let check_sat =
      Eff (fun b -> ((if b then `SAT else `UNSAT), b))
    let with_constraints _ cs (Eff ma) =
      let rec eval_cs = function
      | MC_empty -> true
      | MC_eq (n1, n2) -> N.equal n1 n2
      | MC_le (n1, n2) -> N.less_equal n1 n2
      | MC_lt (n1, n2) -> N.less n1 n2
      | MC_in_device _ ->
        failwith "TODO: Twin, with_constraints: MC_in_device"
      | MC_or (cs1, cs2) -> eval_cs cs1 || eval_cs cs2
      | MC_conj css -> List.for_all (fun z -> eval_cs z) css
      | MC_not cs -> not (eval_cs cs)
      in Eff (fun b -> ma (b && eval_cs cs))
   end : Constraints with type t = mem_iv_constraint)

  open Eff

  (* INTERNAL: allocation_id *)
  type allocation_id = N.num

  (* INTERNAL: address *)
  type address = N.num
  
  (* INTERNAL: allocation *)
  type allocation = {
    base: address;
    size: N.num; (*TODO: this is probably unnecessary once we have the type *)
    ty: Core_ctype.ctype0 option; (* None when dynamically allocated *)
    is_readonly: bool;
  }

  type meta =
    | Mpointer of provenance (* the past write was a pointer with
                                the corresponding provenance *)
    | Mother (* the last write was any type other than a pointer *)

  type mem_state = {
    next_alloc_id: allocation_id;
    allocations: allocation IntMap.t;
    next_address: address;
    next_twin_address: address;
    twin_alloc_flag: bool;
    bytemap: (meta * char option) IntMap.t;
  }

  let max_address = N.of_int 2147483648
  let initial_mem_state = {
    next_alloc_id= N.zero;
    allocations= IntMap.empty;
    next_address= N.(succ zero);
    twin_alloc_flag= true;
    next_twin_address= max_address;
    bytemap= IntMap.empty;
  }

  type footprint = Footprint
  let do_overlap fp1 fp2 = failwith "TODO: do_overlap"

  type 'a memM = ('a, mem_error, integer_value mem_constraint, mem_state) Eff.eff
  let return = Eff.return
  let bind = Eff.(>>=)

  (* pretty printing *)
  open PPrint
  open Pp_prelude
  let pp_pointer_value (PV (_, ptrval_))=
    let show = Symbol.instance_Show_Show_Symbol_sym_dict.show_method in
    match ptrval_ with
    | PVnull ty -> !^ "NULL" ^^ P.parens (Pp_core_ctype.pp_ctype ty)
    | PVfunction sym -> !^ ("<funptr:" ^ show sym ^ ">")
    | PVconcrete n -> !^ (N.to_string n)

  let pp_integer_value n = !^ (N.to_string n)

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
      braces (comma_list pp_mem_value mvals)
  | MVstruct (tag_sym, xs) ->
    parens (!^ "struct" ^^^ !^ (Pp_symbol.to_string_pretty tag_sym))
    ^^ braces (
      comma_list (fun (ident, _, mval) ->
          dot ^^ Pp_cabs.pp_cabs_identifier ident ^^ equals
          ^^^ pp_mem_value mval
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
    | Prov_some alloc_id -> N.to_string alloc_id
    | Prov_double (alloc_id1, alloc_id2) ->
      "(" ^ N.to_string alloc_id1 ^ ", " ^ N.to_string alloc_id2 ^ ")"
    | Prov_device -> "dev"

  (* TODO: DEBUG *)
  let print_bytemap str =
    if !Debug_ocaml.debug_level > 4 then begin
      Printf.fprintf stderr "BEGIN BYTEMAP ==> %s\n" str;
      get >>= fun st ->
      IntMap.iter (fun addr (meta, c_opt) ->
        Printf.fprintf stderr "@%s ==> %s: %s\n"
          (N.to_string addr)
          (match meta with Mpointer p -> string_of_provenance p | Mother -> "-")
          (match c_opt with None -> "UNSPEC" | Some c ->
              string_of_int (int_of_char c))
      ) st.bytemap;
      prerr_endline "END";
    return ()
    end else
      return ()

  let get_allocation alloc_id : allocation memM =
    get >>= fun st ->
    match IntMap.find_opt alloc_id st.allocations with
    | Some ret -> return ret
    | None -> fail (MerrOutsideLifetime
                      ("Twin.get_allocation, alloc_id="
                       ^ N.to_string alloc_id))

  let get_provenance addr =
    get >>= fun st ->
    let filter alloc_id alloc =
      N.less_equal alloc.base addr
      && N.less_equal addr (N.add alloc.base alloc.size)
    in
    let filtered_allocs = IntMap.filter filter st.allocations in
    match IntMap.bindings filtered_allocs with
    | [] -> return Prov_none
    | [(i1, _)] -> return (Prov_some i1)
    | [(i1, _); (i2, _)] -> return (Prov_double (i1, i2))
    | _ -> failwith "get_provenance prov error"

  let is_within_bound alloc_id lvalue_ty addr =
    get_allocation alloc_id >>= fun alloc ->
    return (N.less_equal alloc.base addr
            && N.less_equal (N.add addr (N.of_int (sizeof lvalue_ty)))
                            (N.add alloc.base alloc.size))

  let is_within_device ty addr =
    return begin
      List.exists (fun (min, max) ->
          N.less_equal min addr
          && N.less_equal (N.add addr (N.of_int (sizeof ty))) max
        ) device_ranges
    end

  (* INTERNAL: fetch_bytes *)
  let fetch_bytes base_addr n_bytes =
    get >>= fun st ->
    let addrs = List.init n_bytes (fun z -> N.add base_addr (N.of_int z)) in
    return begin
      List.map (fun addr ->
        match IntMap.find_opt addr st.bytemap with
          | Some b -> b
          | None -> (Mother, None)
      ) addrs
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
        if is_signed && N.(equal (succ zero)
                          (extract_num (of_int (int_of_char first)) 7 1)) then
          N.of_int (-1)
        else
          N.zero in
      let rec aux acc = function
        | [] -> acc
        | c::cs' ->
          aux N.(bitwise_xor (of_int (int_of_char c)) (shift_left acc 8)) cs'
      in
      aux init cs

  let combine_meta = function
    | [] -> failwith "combine_meta ==> empty"
    | m::xs ->
      if List.for_all (fun z -> z = m) xs then m else Mpointer Prov_none

  let rec combine_bytes ty (bs : (meta * char option) list) =
    let extract_unspec xs =
      List.fold_left (fun acc_opt c_opt ->
          match acc_opt, c_opt with
          | None, _ -> None
          | _, None -> None
          | (Some acc, Some c) -> Some (c :: acc)
        ) (Some []) (List.rev xs)
    in
    match ty with
    | Void0
    | Array0 (_, None)
    | Function0 _ ->
      assert false
    | Basic0 (Integer ity) ->
      let (bs1, bs2) = L.split_at (sizeof ty) bs in
      let bs1' = List.map snd bs1 in
      let mv = match extract_unspec bs1' with
        | Some cs ->
          MVinteger (ity, int64_of_bytes (AilTypesAux.is_signed_ity ity) cs)
        | None ->
          MVunspecified ty
      in
      return (mv, bs2)
    | Basic0 (Floating fty) ->
        let (bs1, bs2) = L.split_at (sizeof ty) bs in
        let bs1' = List.map snd bs1 in
        let mv = match extract_unspec bs1' with
          | Some cs ->
            let n = N.to_int64 (int64_of_bytes true cs) in
            MVfloating (fty, Int64.float_of_bits n)
          | None ->
            MVunspecified ty
        in
        return (mv, bs2)
    | Array0 (elem_ty, Some n) ->
        let rec aux n acc cs =
          if n < 0 then
            return (MVarray acc, cs)
          else
            combine_bytes elem_ty cs >>= fun (mval, cs') ->
            aux (n-1) (mval :: acc) cs'
        in
        aux (N.to_int n) [] bs
    | Pointer0 (_, ref_ty) ->
        let (bs1, bs2) = L.split_at (sizeof ty) bs in
        let (metas, bs1') = List.split bs1 in
        let meta = combine_meta metas in
        begin match extract_unspec bs1' with
          | Some cs ->
            let n = int64_of_bytes false cs in
            let pvb = if N.equal n N.zero then PVnull ref_ty else PVconcrete n in
            begin match meta with
              | Mpointer prov ->
                return (MVpointer (ref_ty, PV (prov, pvb)), bs2)
              | Mother ->
                get_provenance n >>= fun prov ->
                return (MVpointer (ref_ty, PV (prov, pvb)), bs2)
            end
          | None ->
            let cty = Core_ctype.Pointer0 (AilTypes.no_qualifiers, ref_ty) in
            return (MVunspecified cty, bs2)
        end
    | Atomic0 atom_ty ->
      combine_bytes atom_ty bs
    | Struct0 tag_sym ->
      let (bs1, bs2) = L.split_at (sizeof ty) bs in
      let f (acc_xs, prev_offset, acc_bs) (memb_ident, memb_ty, memb_offset)=
        let pad = memb_offset - prev_offset in
        combine_bytes memb_ty (L.drop pad acc_bs) >>= fun (mval, acc_bs') ->
        return ((memb_ident, memb_ty, mval)::acc_xs, prev_offset+sizeof memb_ty, acc_bs')
      in
      foldlM f ([], 0, bs1) (fst (offsetsof tag_sym)) >>= fun (rev_xs, _, bs') ->
      return (MVstruct (tag_sym, List.rev rev_xs), bs2)
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
  | MVunspecified ty -> ty
  | MVinteger (ity, _) -> Basic0 (AilTypes.Integer ity)
  | MVfloating (fty, _) -> Basic0 (AilTypes.Floating fty)
  | MVpointer (ref_ty, _) -> Pointer0 (AilTypes.no_qualifiers, ref_ty)
  | MVarray [] -> assert false
  | MVarray ((mval::_) as mvals) ->
    Array0 (typeof mval, Some (N.of_int (List.length mvals)))
  | MVstruct (tag_sym, _) -> Struct0 tag_sym
  | MVunion (tag_sym, _, _) -> Union0 tag_sym

(* INTERNAL explode_bytes *)
let rec explode_bytes mval : (meta * char option) list =
  match mval with
  | MVunspecified ty ->
    List.init (sizeof ty) (fun _ -> (Mother, None))
  | MVinteger (ity, n) ->
    List.map (fun z -> (Mother, z)) begin
      bytes_of_int64 (AilTypesAux.is_signed_ity ity)
        (sizeof (Basic0 (Integer ity))) n
    end
  | MVfloating (fty, fval) ->
    List.map (fun z -> (Mother, z)) begin
      bytes_of_int64 true (sizeof (Basic0 (Floating fty)))
        (N.of_int64 (Int64.bits_of_float fval))
    end
  | MVpointer (_, PV (prov, ptrval_)) ->
    let ptr_size =
      match Impl.sizeof_pointer with
      | None -> failwith "the Twin model requires a complete implementation"
      | Some z -> z
    in begin match ptrval_ with
      | PVnull _ -> List.init ptr_size (fun _ -> (Mother, Some '\000'))
      | PVfunction _ -> failwith "TODO: explode_bytes, PVfunction"
      | PVconcrete addr ->
        List.map (fun z -> (Mpointer prov, z)) begin
          bytes_of_int64 false ptr_size addr
        end
    end
  | MVarray mvals -> L.concat (List.map explode_bytes mvals)
  | MVstruct (tag_sym, xs) ->
    let (offs, last_off) = offsetsof tag_sym in
    let final_pad = sizeof (Core_ctype.Struct0 tag_sym) - last_off in
    snd begin
      (* TODO: rewrite now that offsetsof returns the paddings *)
      List.fold_left2 (fun (last_off, acc) (ident, ty, off) (_, _, mval) ->
        let pad = off - last_off in
        ( off + sizeof ty
        , acc @
          List.init pad (fun _ -> (Mother, None)) @
          explode_bytes mval )
      ) (0, []) offs xs
    end @
    List.init final_pad (fun _ -> (Mother, None))
  | MVunion (tag_sym, memb_ident, mval) ->
    let size = sizeof (Core_ctype.Union0 tag_sym) in
    let bs = explode_bytes mval in
    bs @ List.init (size - List.length bs) (fun _ -> (Mother, None))

  (* INTERNAL allocate *)
  let allocate align size ty init_opt : pointer_value memM =
    Debug_ocaml.warn [] (fun () ->
      "MAX ALLOCATION SIZE: " ^ N.to_string max_address
    );
    get >>= fun st ->
    let alloc_id      = st.next_alloc_id in
    let next_alloc_id = N.succ alloc_id in
    let delta addr =
      let m = N.modulus addr align in
      if N.equal m N.zero then N.zero else N.sub align m
    in
    let addr = N.add st.next_address (delta st.next_address) in
    let twin_addr = N.add st.next_twin_address (delta st.next_twin_address) in
    let add_alloc twin_alloc_flag_flag addr =
      let (is_readonly, bytemap) =
        match init_opt with
        | None -> (false, st.bytemap)
        | Some mval ->
          let bs =
            List.mapi (fun i b -> (N.add addr (N.of_int i), b))
              (explode_bytes mval)
          in
          (true, List.fold_left (fun acc (addr, b) -> IntMap.add addr b acc)
            st.bytemap bs)
      in
      put { next_alloc_id= next_alloc_id;
            allocations= IntMap.add alloc_id { base= addr;
                                               size= size;
                                               ty= ty;
                                               is_readonly= is_readonly}
                st.allocations;
            next_address= N.add addr size;
            next_twin_address= N.add twin_addr size;
            twin_alloc_flag= twin_alloc_flag_flag;
            bytemap= bytemap;
          } >>= fun () ->
      return (PV (Prov_some alloc_id, PVconcrete addr))
    in
    if st.twin_alloc_flag then
      Eff.msum "twin allocation"
        [ ("twin", add_alloc true twin_addr);
          ("original", add_alloc false addr) ]
    else
      add_alloc false addr

  let allocate_static _ _ (align) ty init_opt : pointer_value memM =
    let size = N.of_int (sizeof ty) in
    allocate align size (Some ty) init_opt

  let allocate_dynamic _ _ (align) (size) =
    allocate align size None None

  let realloc _ _ _ =
    failwith "twin: realloc"

  let kill loc is_dyn p : unit memM =
    let do_kill id =
      Debug_ocaml.print_debug 1 [] (fun () ->
        "KILLING alloc_id= " ^ N.to_string id 
      );
      update (fun st -> {st with allocations= IntMap.remove id st.allocations})
    in
    match p with
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
      get_allocation alloc_id >>= fun alloc ->
      if N.equal addr alloc.base then
        do_kill alloc_id
      else
        fail (MerrOther "attempted to kill with an invalid pointer")
    | PV (Prov_double (alloc_id1, alloc_id2), PVconcrete addr) ->
      get_allocation alloc_id1 >>= fun alloc1 ->
      get_allocation alloc_id2 >>= fun alloc2 ->
      if N.equal addr alloc1.base then
        do_kill alloc_id1
      else if N.equal addr alloc2.base then
        do_kill alloc_id2
      else
        fail (MerrOther "attempted to kill with an invalid pointer")

  let load loc ty (PV (prov, ptrval_)) =
    let do_load addr =
      get >>= fun st ->
      fetch_bytes addr (sizeof ty) >>= fun bs ->
      combine_bytes ty bs >>= fun (mval, bs') ->
      match bs' with
        | [] -> return (Footprint, mval)
        | _ -> fail (MerrWIP "load, bs' <> []")
    in
    match (prov, ptrval_) with
    | (_, PVnull _) ->
      fail (MerrAccess (loc, LoadAccess, NullPtr))
    | (_, PVfunction _) ->
      fail (MerrAccess (loc, LoadAccess, FunctionPtr))
    | (Prov_none, _) ->
      fail (MerrAccess (loc, LoadAccess, OutOfBoundPtr))
    | (Prov_device, PVconcrete addr) ->
      begin is_within_device ty addr >>= function
        | true -> do_load addr
        | false -> fail (MerrAccess (loc, LoadAccess, OutOfBoundPtr))
      end
    | (Prov_some alloc_id, PVconcrete addr) ->
      begin is_within_bound alloc_id ty addr >>= function
        | true -> do_load addr
        | false -> fail (MerrAccess (loc, LoadAccess, OutOfBoundPtr))
      end
    | (Prov_double (alloc_id1, alloc_id2), PVconcrete addr) ->
       begin is_within_bound alloc_id1 ty addr >>= function
         | true -> do_load addr
         | false ->
           begin is_within_bound alloc_id2 ty addr >>= function
             | true -> do_load addr
             | false -> fail (MerrAccess (loc, LoadAccess, OutOfBoundPtr))
           end
       end

  let store loc ty is_locking (PV (prov, ptrval_)) mval =
    Debug_ocaml.print_debug 3 [] (fun () ->
      "ENTERING STORE: ty=" ^
      String_core_ctype.string_of_ctype ty ^ "@" ^
      Pp_utils.to_plain_string (pp_pointer_value (PV (prov, ptrval_))) ^
      ", mval= " ^ Pp_utils.to_plain_string (pp_mem_value mval)
    );
    if not (ctype_equal(Core_ctype.unatomic ty)(Core_ctype.unatomic(typeof mval)))
    then begin
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
          (N.add addr (N.of_int i), b)
        ) (explode_bytes mval) in
        update begin fun st ->
          { st with bytemap=
            List.fold_left (fun acc (addr, b) ->
              IntMap.add addr b acc
            ) st.bytemap bs }
        end >>
        print_bytemap ("AFTER STORE => " ^ Location_ocaml.location_to_string loc)
        >>= fun () ->
        return Footprint
      in
      let check_and_do_store alloc_id addr =
        get_allocation alloc_id >>= fun alloc ->
        if alloc.is_readonly then
          fail (MerrWriteOnReadOnly loc)
        else
          do_store addr >>= fun fp ->
          if is_locking then
            Eff.update (fun st ->
              { st with allocations=
                  IntMap.update alloc_id (function
                    | Some alloc -> Some { alloc with is_readonly= true }
                    | None       -> None
                  ) st.allocations }
            ) >>= fun () ->
            return fp
          else
            return fp
      in
      match (prov, ptrval_) with
      | (_, PVnull _) ->
        fail (MerrAccess (loc, StoreAccess, NullPtr))
      | (_, PVfunction _) ->
        fail (MerrAccess (loc, StoreAccess, FunctionPtr))
      | (Prov_none, _) ->
        fail (MerrAccess (loc, StoreAccess, OutOfBoundPtr))
      | (Prov_device, PVconcrete addr) ->
        begin is_within_device ty addr >>= function
          | true -> do_store addr
          | false -> fail (MerrAccess (loc, StoreAccess, OutOfBoundPtr))
        end
      | (Prov_some alloc_id, PVconcrete addr) ->
        begin is_within_bound alloc_id ty addr >>= function
          | true -> check_and_do_store alloc_id addr
          | false -> fail (MerrAccess (loc, StoreAccess, OutOfBoundPtr))
        end
      | (Prov_double (alloc_id1, alloc_id2), PVconcrete addr) ->
        begin is_within_bound alloc_id1 ty addr >>= function
          | true -> check_and_do_store alloc_id1 addr
          | false ->
          begin is_within_bound alloc_id2 ty addr >>= function
            | true -> check_and_do_store alloc_id2 addr
            | false -> fail (MerrAccess (loc, StoreAccess, OutOfBoundPtr))
          end
        end

  let null_ptrval ty =
    PV (Prov_none, PVnull ty)

  let fun_ptrval sym =
    PV (Prov_none, PVfunction sym)

  let concrete_ptrval _ _ = failwith "twin: concrete_ptrval"
  let case_ptrval _ _ _ _ = failwith "twin: case_ptrval"

  (* TODO: not sure if I need to consider double provenance here *)
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
          if prov1 = prov2 then
            return (N.equal addr1 addr2)
          else
            Eff.msum "pointer equality"
              [ ("using provenance", return false)
              ; ("ignoring provenance", return (N.equal addr1 addr2)) ]

  let ne_ptrval ptrval1 ptrval2 =
    eq_ptrval ptrval1 ptrval2 >>= fun b ->
    return (not b)

  let lt_ptrval (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
    | (PVconcrete addr1, PVconcrete addr2) -> return (N.compare addr1 addr2 == -1)
    | _ -> fail (MerrWIP "lt_ptrval")

  let gt_ptrval (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
    | (PVconcrete addr1, PVconcrete addr2) -> return (N.compare addr1 addr2 == 1)
    | _ -> fail (MerrWIP "gt_ptrval")

  let le_ptrval (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
    | (PVconcrete addr1, PVconcrete addr2) ->
      let cmp = N.compare addr1 addr2 in
      return (cmp = -1 || cmp = 0)
    | _ ->
      fail (MerrWIP "le_ptrval")

  let ge_ptrval (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
    | (PVconcrete addr1, PVconcrete addr2) ->
      let cmp = N.compare addr1 addr2 in
      return (cmp = 1 || cmp = 0)
    | _ ->
      fail (MerrWIP "ge_ptrval")

  let diff_ptrval diff_ty ptrval1 ptrval2 =
    match ptrval1, ptrval2 with
    | PV (Prov_some alloc_id1, (PVconcrete addr1)),
      PV (Prov_some alloc_id2, (PVconcrete addr2))
      when N.equal alloc_id1 alloc_id2 ->
      get_allocation alloc_id1 >>= fun alloc ->
      (* NOTE: this is not like "is_within_bound" because it allows
       * one-past pointers *)
      if   N.less_equal alloc.base addr1
         && N.less_equal addr1 (N.add alloc.base alloc.size)
         && N.less_equal alloc.base addr2
         && N.less_equal addr2 (N.add alloc.base alloc.size) then
        (* NOTE: the result of subtraction of two pointer values
         * is an integer value with empty provenance, irrespective of
         * the operand provenances *)
        (* TODO: check that this is correct for arrays of arrays ... *)
        (* TODO: if not, sync with symbolic defacto *)
        let diff_ty' = match diff_ty with
          | Core_ctype.Array0 (elem_ty, _) -> elem_ty
          | _ -> diff_ty
        in
        return ((N.div (N.sub addr1 addr2) (N.of_int (sizeof diff_ty'))))
      else
        fail MerrPtrdiff
    | _ ->
      fail MerrPtrdiff

  let validForDeref_ptrval ref_ty = function
    | PV (_, PVnull _)
    | PV (_, PVfunction _) ->
      return false
    | PV (Prov_device, PVconcrete _) ->
      return true
    | PV (Prov_some _, PVconcrete _) ->
      return true
    | PV (Prov_double _, PVconcrete _) ->
      return true
    | PV (Prov_none, _) ->
      return false

  let isWellAligned_ptrval ref_ty ptrval =
    (* TODO: catch builtin function types *)
    match Core_ctype.unatomic ref_ty with
    | Void0
    | Function0 _ ->
      fail (MerrOther "called isWellAligned_ptrval on void or a function type")
    | _ ->
      begin match ptrval with
        | PV (_, PVnull _) ->
          return true
        | PV (_, PVfunction _) ->
          fail (MerrOther "called isWellAligned_ptrval on function pointer")
        | PV (_, PVconcrete addr) ->
          return (N.(equal (modulus addr (of_int (alignof ref_ty))) zero))
      end

  let ptrcast_ival _ ref_ty (n) =
    if not (N.equal n N.zero) then
      (* STD \<section>6.3.2.3#5 *)
      Debug_ocaml.warn [] (fun () ->
        "implementation defined cast from integer to pointer"
      );
    if List.exists (fun (min, max) ->
        N.less_equal min n && N.less_equal n max) device_ranges
    then
      return (PV (Prov_device, PVconcrete n))
    else if N.equal n N.zero then
      return (PV (Prov_none, PVnull ref_ty))
    else
      get_provenance n >>= fun prov ->
      return (PV (prov, PVconcrete n))

  let offsetof_ival tag_sym memb_ident =
    let (xs, _) = offsetsof tag_sym in
    let pred (ident, _, _) = cabs_ident_equal ident memb_ident in
    match List.find_opt pred xs with
    | Some (_, _, offset) ->
      (N.of_int offset)
    | None ->
      failwith "Twin.offsetof_ival: invalid memb_ident"

  let array_shift_ptrval (PV (prov, ptrval_)) ty (ival) =
    let offset = (N.(mul (of_int (sizeof ty)) ival)) in
    PV (prov, match ptrval_ with
    | PVnull _ ->
      (* TODO: this seems to be undefined in ISO C *)
      (* NOTE: in C++, if offset = 0, this is defined and returns a PVnull *)
      failwith "TODO(shift a null pointer should be undefined behaviour)"
    | PVfunction _ ->
      failwith "Twin.array_shift_ptrval, PVfunction"
    | PVconcrete addr ->
      PVconcrete (N.add addr offset))

  let member_shift_ptrval (PV (prov, ptrval_)) tag_sym memb_ident =
    let offset = offsetof_ival tag_sym memb_ident in
    PV (prov, match ptrval_ with
    | PVnull _ -> PVconcrete offset
    | PVfunction _ -> failwith "Twin.member_shift_ptrval, PVfunction"
    | PVconcrete addr -> PVconcrete (N.add addr offset))
  
  let eff_array_shift_ptrval ptrval ty ival =
    failwith "TODO(twin): eff_array_shift_ptrval"

  
  let concurRead_ival ity sym = failwith "TODO: concurRead_ival"

  let integer_ival n = n

  let max_ival ity =
    let open Nat_big_num in
    match Impl.sizeof_ity ity with
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
          unsigned_max
        | Size_t
        | Unsigned _ ->
          unsigned_max
        | Ptrdiff_t
        | Signed _ ->
          signed_max
        | Enum _ ->
          (* TODO: hack, assuming like int *)
          sub (pow_int (of_int 2) (8*4-1)) (of_int 1)
        | IBuiltin _ ->
          failwith "TODO: max_ival: IBuiltin"
      end
    | None ->
      failwith "the Twin model requires a complete implementation MAX"

  let min_ival ity =
    let open N in
    match ity with
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
        failwith "the Twin model requires a complete implementation MIN"
      end
    | Enum _ ->
      (* TODO: hack, assuming like int *)
      negate (pow_int (of_int 2) (8*4-1))
    | IBuiltin _ ->
      failwith "TODO: min_ival: Builtin"

  let intcast_ptrval _ ity (PV (prov, ptrval_)) =
    match ptrval_ with
    | PVnull _ ->
      return (N.zero)
    | PVfunction _ ->
      failwith "TODO: intcast_ptrval PVfunction"
    | PVconcrete addr ->
      let ity_max = max_ival ity in
      let ity_min = min_ival ity in
      if N.(less addr ity_min || less ity_max addr) then
        fail MerrIntFromPtr
      else
          return (addr)

  let op_ival iop =
    match iop with
    | IntAdd -> N.add
    | IntSub -> N.sub
    | IntMul -> N.mul
    | IntDiv -> N.integerDiv_t
    | IntRem_t -> N.integerRem_t
    | IntRem_f -> N.integerRem_f
    | IntExp ->
      (* TODO: fail properly when y is too big? *)
      fun x y -> N.pow_int x (N.to_int y)

  let sizeof_ival ty =
    N.of_int (sizeof ty)

  let alignof_ival ty =
    N.of_int (alignof ty)

  let bitwise_complement_ival _ n =
    N.(sub (negate n) (of_int 1))

  let bitwise_and_ival _ n1 n2 =
    N.bitwise_and n1 n2

  let bitwise_or_ival _ n1 n2 =
    N.bitwise_or n1 n2

  let bitwise_xor_ival _ n1 n2 =
    N.bitwise_xor n1 n2

  let case_integer_value (n) f_conc _ =
    f_conc n

  let is_specified_ival ival =
    true

  let zero_fval =
    0.0

  let one_fval =
    1.0

  let str_fval str =
    float_of_string str

  let case_fval fval _ fconc =
    fconc fval

  let op_fval fop fval1 fval2 =
    match fop with
    | FloatAdd -> fval1 +. fval2
    | FloatSub -> fval1 -. fval2
    | FloatMul -> fval1 *. fval2
    | FloatDiv -> fval1 /. fval2

  let eq_fval fval1 fval2 =
    fval1 = fval2

  let lt_fval fval1 fval2 =
    fval1 < fval2

  let le_fval fval1 fval2 =
    fval1 <= fval2

  let fvfromint n =
    Int64.float_of_bits (N.to_int64 n)

  let ivfromfloat ity fval =
    (N.of_int64 (Int64.bits_of_float fval))

  let eq_ival _ n1 n2 =
    Some (N.equal n1 n2)

  let lt_ival _ n1 n2 =
    Some (N.compare n1 n2 = -1)

  let le_ival _ n1 n2 =
    let cmp = N.compare n1 n2 in
    Some (cmp = -1 || cmp = 0)

  let eval_integer_value (n) =
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

  let case_mem_value mval f_unspec f_concur f_ival f_fval f_ptr
      f_array f_struct f_union =
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
  
  let memcpy ptrval1 ptrval2 (size_n) =
    let loc = Location_ocaml.other "memcpy" in
    let unsigned_char_ty =
      Core_ctype.Basic0 (AilTypes.(Integer (Unsigned Ichar)))
    in
    let rec aux i =
      if N.less i size_n then
        load loc unsigned_char_ty
          (array_shift_ptrval ptrval2 unsigned_char_ty (i))
        >>= fun (_, mval) ->
        store loc unsigned_char_ty false
          (array_shift_ptrval ptrval1 unsigned_char_ty (i)) mval
        >>= fun _ ->
        aux (N.succ i)
      else
        return ptrval1
    in
    aux N.zero

  let memcmp ptrval1 ptrval2 (size_n) =
    let unsigned_char_ty =
      Core_ctype.Basic0 (AilTypes.(Integer (Unsigned Ichar)))
    in
    let rec get_bytes ptrval acc = function
      | 0 ->
        return (List.rev acc)
      | size ->
        load Location_ocaml.unknown unsigned_char_ty ptrval >>= function
        | (_, MVinteger (_, (byte_n))) ->
          let ptr' =
            array_shift_ptrval ptrval unsigned_char_ty ((N.(succ zero)))
          in
          get_bytes ptr' (byte_n :: acc) (size-1)
        | _ ->
          assert false
    in
    get_bytes ptrval1 [] (N.to_int size_n) >>= fun bytes1 ->
    get_bytes ptrval2 [] (N.to_int size_n) >>= fun bytes2 ->
    return ((List.fold_left (fun acc (n1, n2) ->
        if N.equal acc N.zero then N.of_int (N.compare n1 n2) else acc
      ) N.zero (List.combine bytes1 bytes2)))


  (* JSON serialisation *)

  let serialise_prov = function
    | Prov_some n -> Json.of_bigint n
    | Prov_double (n, m) -> `List [Json.of_bigint n; Json.of_bigint m]
    | Prov_none -> `Null
    | Prov_device -> `String "Device"

  let serialise_map f m =
    let serialise_entry (k, v) = (N.to_string k, f v)
    in `Assoc (List.map serialise_entry (IntMap.bindings m))

  let serialise_allocation alloc =
    let serialise_ctype ty = `String (String_core_ctype.string_of_ctype ty) in
    `Assoc [
      ("base", Json.of_bigint alloc.base);
      ("type", Json.of_option serialise_ctype alloc.ty);
      ("size", Json.of_bigint alloc.size);
    ]

  let serialise_byte (m, c_opt) =
    let serialise_char c = `Int (Char.code c) in
    `Assoc[
      ("prov", match m with Mpointer p -> serialise_prov p
                          | Mother -> `String "other");
      ("value", Json.of_option serialise_char c_opt)
    ]

  let serialise_mem_state st =
    `Assoc [
      ("kind",          `String "Twin");
      ("allocations",   serialise_map serialise_allocation st.allocations);
      ("bytemap",       serialise_map serialise_byte st.bytemap)
    ]

end

include Twin
