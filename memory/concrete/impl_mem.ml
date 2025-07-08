open Ctype

(*open Ocaml_implementation*)
open Memory_model
open Mem_common

module N = struct
  include Nat_big_num
  let of_float = Z.of_float
end

module L = struct
  include List
  include Lem_list
end

let ident_equal x y =
       Symbol.instance_Basic_classes_Eq_Symbol_identifier_dict.isEqual_method x y

let ctype_mem_compatible ty1 ty2 =
  let rec unqualify_and_unatomic (Ctype (_, ty)) =
    match ty with
      | Void
      | Basic _
      | Struct _
      | Union _ ->
          ty
      | Byte ->
          (* treat bytes as unsigned chars for typing *)
          Basic (Integer (Unsigned Ichar))
      | Function ((_, ret_ty), xs, b) ->
          Function (
            (no_qualifiers, Ctype ([], unqualify_and_unatomic ret_ty)),
            List.map (fun (_, ty, _) -> (no_qualifiers, Ctype ([], unqualify_and_unatomic ty), false)) xs,
            b
          )
      | FunctionNoParams (_, ret_ty) ->
          FunctionNoParams (no_qualifiers, Ctype ([], unqualify_and_unatomic ret_ty))
      | Array (elem_ty, n_opt) ->
          Array (Ctype ([], unqualify_and_unatomic elem_ty), n_opt)
      | Pointer (_, ref_ty) ->
          Pointer (no_qualifiers, Ctype ([], unqualify_and_unatomic ref_ty))
      | Atomic atom_ty ->
          unqualify_and_unatomic atom_ty
          (* Atomic (Ctype ([], unqualify atom_ty)) *) in
  Ctype.ctypeEqual (Ctype ([], unqualify_and_unatomic ty1)) (Ctype ([], unqualify_and_unatomic ty2))

module Eff : sig
  type ('a, 'err, 'cs, 'st) eff =
    ('a, string, 'err, 'cs, 'st) Nondeterminism.ndM
  val return: 'a -> ('a, 'err, 'cs, 'st) eff
  val (>>=): ('a, 'err, 'cs, 'st) eff -> ('a -> ('b, 'err, 'cs, 'st) eff) -> ('b, 'err, 'cs, 'st) eff
  val read: ('st -> 'a) -> ('a, 'err, 'cs, 'st) eff
  val update: ('st -> 'st) -> (unit, 'err, 'cs, 'st) eff
  val modify: ('st -> 'a * 'st) -> ('a, 'err, 'cs, 'st) eff
  val get: ('st, 'err, 'cs, 'st) eff
  val put: 'st -> (unit, 'err, 'cs, 'st) eff
(*  val fail: 'err -> ('a, 'err, 'cs, 'st) eff *)
  val mapM: ('a -> ('b, 'err, 'cs, 'st) eff) -> 'a list -> ('b list, 'err, 'cs, 'st) eff
  val msum: string -> (string * ('a, 'err, 'cs, 'st) eff) list -> ('a, 'err, 'cs, 'st) eff
end = struct
  type ('a, 'err, 'cs, 'st) eff =
    ('a, string, 'err, 'cs, 'st) Nondeterminism.ndM
  
  let return = Nondeterminism.nd_return
  let (>>=) = Nondeterminism.nd_bind
  
  let read = Nondeterminism.nd_read
  let update = Nondeterminism.nd_update
  let modify f = 
    Nondeterminism.nd_get >>= fun st ->
    let (ret, st') = f st in
    Nondeterminism.nd_put st' >>= fun () ->
    return ret
  
  let get = Nondeterminism.nd_get
  let put = Nondeterminism.nd_put
(*  let fail err = Nondeterminism.kill (Other err) *)
  let mapM _ _ = failwith "TODO: Concrete.Eff.mapM"
  
  let msum str xs =
    Nondeterminism.(
      msum Mem_common.instance_Nondeterminism_Constraints_Mem_common_mem_constraint_dict () str xs
    )
end




module IntMap = Map.Make(struct
  type t = Nat_big_num.num
  let compare = Nat_big_num.compare
end)


(* TODO: memoise this, it's stupid to recompute this every time... *)
(* NOTE: returns ([(memb_ident, type, offset)], last_offset) *)
let rec offsetsof ?(ignore_flexible=false) tagDefs tag_sym =
  let open N in
  match Pmap.find tag_sym tagDefs with
    | _, StructDef (membrs_, flexible_opt) ->
        (* NOTE: the offset of a flexible array member is just like
           that of any other member *)
        let membrs = match flexible_opt with
          | None ->
              membrs_
          | Some (FlexibleArrayMember (attrs, ident, qs, ty)) ->
              if ignore_flexible then
                membrs_
              else
                membrs_ @ [(ident, (attrs, None, qs, ty))] in
        let (xs, maxoffset) =
          List.fold_left (fun (xs, last_offset) (membr, (_, align_opt, _, ty)) ->
            let size = sizeof ~tagDefs ty in
            let align =
              match align_opt with
                | None ->
                    of_int (alignof ~tagDefs ty)
                | Some (AlignInteger al_n) ->
                    al_n
                | Some (AlignType al_ty) ->
                  of_int (alignof ~tagDefs al_ty) in
            let x = modulus last_offset align in
            let pad = if equal x zero then zero else sub align x in
            ((membr, ty, add last_offset pad) :: xs, add (add last_offset pad) size)
          ) ([], zero) membrs in
        (List.rev xs, maxoffset)
    | _, UnionDef membrs ->
        (List.map (fun (ident, (_, _, _, ty)) -> (ident, ty, zero)) membrs, zero)

and sizeof ?(tagDefs= Tags.tagDefs ()) (Ctype (_, ty) as cty) : N.num =
  let open N in
  match ty with
    | Void | Array (_, None) | Function _ | FunctionNoParams _ ->
        assert false
    | Basic (Integer ity) ->
        begin match (Ocaml_implementation.get ()).sizeof_ity ity with
          | Some n ->
              of_int n
          | None ->
              failwith ("the concrete memory model requires a complete implementation sizeof INTEGER => " ^ String_core_ctype.string_of_ctype cty)
        end
    | Basic (Floating fty) ->
        begin match (Ocaml_implementation.get ()).sizeof_fty fty with
          | Some n ->
              of_int n
          | None ->
              failwith "the concrete memory model requires a complete implementation sizeof FLOAT"
        end
    | Array (elem_ty, Some n) ->
        (* TODO: what if too big? *)
        mul n (sizeof ~tagDefs elem_ty)
    | Pointer _ ->
        begin match (Ocaml_implementation.get ()).sizeof_pointer with
          | Some n ->
              of_int n
          | None ->
              failwith "the concrete memory model requires a complete implementation sizeof POINTER"
        end
    | Atomic atom_ty ->
        sizeof ~tagDefs atom_ty
    | Struct tag_sym ->
        (* NOTE: the potential flexible array member indirectly take part in the size
           by potentially introducing trailling padding bytes if its presence increases
           the alignment requirement. This is done by the call the to alignof here.
           But other than for these padding bytes, it is not counted in the size
           (hence the `ignore_flexible` in the call to offsetof) *)
        let (_, max_offset) = offsetsof ~ignore_flexible:true tagDefs tag_sym in
        let align = of_int (alignof ~tagDefs cty) in
        let x = modulus max_offset align in
        if equal x zero then max_offset else N.add max_offset (N.sub align x)
    | Union tag_sym ->
        begin match Pmap.find tag_sym (Tags.tagDefs ()) with
          | _, StructDef _ ->
              assert false
          | _, UnionDef membrs ->
              let (max_size, max_align) =
                List.fold_left (fun (acc_size, acc_align) (_, (_, align_opt, _, ty)) ->
                  let align =
                    match align_opt with
                      | None ->
                          of_int (alignof ~tagDefs ty)
                      | Some (AlignInteger al_n) ->
                          al_n
                      | Some (AlignType al_ty) ->
                        of_int (alignof ~tagDefs al_ty) in
                  (max acc_size (sizeof ~tagDefs ty), max acc_align align)
                ) (zero, zero) membrs in
              (* NOTE: adding padding at the end to satisfy the alignment constraints *)
              let x = modulus max_size max_align in
              if equal x zero then max_size else add max_size (sub max_align x)
        end
    | Byte ->
      of_int 1

and alignof ?(tagDefs= Tags.tagDefs ()) (Ctype (_, ty) as cty) =
  match ty with
    | Void ->
        assert false
    | Basic (Integer ity) ->
        begin match (Ocaml_implementation.get ()).alignof_ity ity with
          | Some n ->
              n
          | None ->
              failwith ("the concrete memory model requires a complete implementation alignof INTEGER => " ^ String_core_ctype.string_of_ctype cty)
        end
    | Basic (Floating fty) ->
        begin match (Ocaml_implementation.get ()).alignof_fty fty with
          | Some n ->
              n
          | None ->
              failwith "the concrete memory model requires a complete implementation alignof FLOATING"
        end
    | Array (elem_ty, _) ->
        alignof ~tagDefs elem_ty
    | Function _
    | FunctionNoParams _ ->
        assert false
    | Pointer _ ->
        begin match (Ocaml_implementation.get ()).alignof_pointer with
          | Some n ->
              n
          | None ->
              failwith "the concrete memory model requires a complete implementation alignof POINTER"
        end
    | Atomic atom_ty ->
        alignof ~tagDefs atom_ty
    | Struct tag_sym ->
        begin match Pmap.find tag_sym tagDefs with
          | _, UnionDef _ ->
              assert false
          | _, StructDef (membrs, flexible_opt)  ->
              (* NOTE: we take into account the potential flexible array member by tweaking
                 the accumulator init of the fold. *)
              let init = match flexible_opt with
                | None ->
                    0
                | Some (FlexibleArrayMember (_, _, _, elem_ty)) ->
                    alignof ~tagDefs (Ctype ([], Array (elem_ty, None))) in
              (* NOTE: Structs (and unions) alignment is that of the maximum alignment
                 of any of their components. *)
              List.fold_left (fun acc (_, (_, align_opt, _, ty)) ->
                let memb_align =
                  match align_opt with
                    | None ->
                        alignof ~tagDefs ty
                    | Some (AlignInteger al_n) ->
                        N.to_int al_n
                    | Some (AlignType al_ty) ->
                      alignof ~tagDefs al_ty in
                max memb_align acc
              ) init membrs
        end
    | Union tag_sym ->
        begin match Pmap.find tag_sym (Tags.tagDefs ()) with
          | _, StructDef _ ->
              assert false
          | _, UnionDef membrs ->
              (* NOTE: Structs (and unions) alignment is that of the maximum alignment
                 of any of their components. *)
              List.fold_left (fun acc (_, (_, align_opt, _, ty)) ->
                let memb_align =
                  match align_opt with
                    | None ->
                        alignof ~tagDefs ty
                    | Some (AlignInteger al_n) ->
                        N.to_int al_n
                    | Some (AlignType al_ty) ->
                      alignof ~tagDefs al_ty in
                max memb_align acc
              ) 0 membrs
        end
    | Byte ->
      1


module Concrete : Memory = struct
  let name = "concrete"
  
  (* INTERNAL: only for PNVI-ae-udi (this is iota) *)
  type symbolic_storage_instance_id = N.num
  
  (* INTERNAL: storage_instance_id *)
  type storage_instance_id = N.num
  
  (* INTERNAL: provenance *)
  type provenance =
    | Prov_none
    | Prov_some of storage_instance_id
    | Prov_symbolic of symbolic_storage_instance_id (* only for PNVI-ae-udi *)
    | Prov_device

  (* Note: using Z instead of int64 because we need to be able to have
     unsigned 64bits values *)
  type pointer_value_base =
    | PVnull of ctype
    | PVfunction of Symbol.sym
    | PVconcrete of Symbol.identifier option(* set if pointing to member of a union *) * Nat_big_num.num
  
  type pointer_value =
    | PV of provenance * pointer_value_base
  
  type integer_value =
    | IV of provenance * Nat_big_num.num
  
  type floating_value =
    (* TODO: hack hack hack ==> OCaml's float are 64bits *)
    float
  
  type mem_value =
    | MVunspecified of ctype
    | MVinteger of integerType * integer_value
    | MVfloating of floatingType * floating_value
    | MVpointer of ctype * pointer_value
    | MVarray of mem_value list
    | MVstruct of Symbol.sym (*struct/union tag*) * (Symbol.identifier (*member*) * ctype * mem_value) list
    | MVunion of Symbol.sym (*struct/union tag*) * Symbol.identifier (*member*) * mem_value

  
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
      Cerb_debug.print_debug 1 [] (fun () -> "HELLO: Concrete.with_constraints");
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
  
  let combine_prov prov1 prov2 =
    match (prov1, prov2) with
      | (Prov_none, Prov_none) ->
          Prov_none
      | (Prov_none, Prov_some id) ->
          Prov_some id
      | (Prov_none, Prov_device) ->
          Prov_device
      | (Prov_some id, Prov_none) ->
          Prov_some id
      | (Prov_some id1, Prov_some id2) ->
          if id1 = id2 then
            Prov_some id1
          else
            Prov_none
      | (Prov_some _, Prov_device) ->
          Prov_device
      | (Prov_device, Prov_none) ->
          Prov_device
      | (Prov_device, Prov_some _) ->
          Prov_device
      | (Prov_device, Prov_device) ->
          Prov_device
      
      (* PNVI-ae-udi *)
      (* TODO: this is improvised, need to check with P *)
      | (Prov_symbolic _, _)
      | (_, Prov_symbolic _) ->
          failwith "Concrete.combine_prov: found a Prov_symbolic"  

  
  (* INTERNAL: address *)
  type address = N.num
  
  type readonly_status =
    | IsWritable
    | IsReadOnly of Mem_common.readonly_kind
  (* INTERNAL: allocation *)
  type allocation = {
    base: address;
    size: N.num; (*TODO: this is probably unnecessary once we have the type *)
    ty: ctype option; (* None when dynamically allocated *)
    is_readonly: readonly_status;
    taint: [ `Unexposed | `Exposed ]; (* NOTE: PNVI-ae, PNVI-ae-udi *)
    (* NON-semantics fields *)
    prefix: Symbol.prefix;
  }
  
  (* INTERNAL: Abstract bytes *)
  module AbsByte = struct
    type t = {
      prov: provenance;
      copy_offset: int option;
      value: char option;
    }
    
    let v prov ?(copy_offset = None) value =
      { prov; copy_offset; value }

    let to_json json_of_prov b =
      `Assoc [("prov", json_of_prov b. prov);
              ("offset", Cerb_json.of_option Cerb_json.of_int b.copy_offset);
              ("value", Cerb_json.of_option Cerb_json.of_char b.value);]
    
    (* Given a (non-empty) list of bytes combine their provenance if their are
       compatible. Returns the empty provenance otherwise *)
    let split_bytes = function
      | [] ->
          failwith "Concrete.AbsByte.split_bytes: called on an empty list"
      | (b::bs) as bl ->
          let (_prov, rev_values, offset_status) =
            List.fold_left (fun (prov_acc, val_acc, offset_acc) b ->
              let prov_acc' = match prov_acc, b.prov with
                | `VALID p1, p2 when p1 = p2 -> prov_acc
                | _, _ -> `INVALID
              in
              let offset_acc' = match offset_acc, b.copy_offset with
                | `PtrBytes n1, Some n2 when n1 = n2 ->
                    `PtrBytes (n1+1)
                | _ ->
                    `OtherBytes in
              (prov_acc', b.value :: val_acc, offset_acc')
              ) (`VALID b.prov, [], `PtrBytes 0) bl in
          let values = List.rev rev_values in
          match _prov, offset_status with
          | `VALID z, `PtrBytes _ -> (z, `ValidPtrProv, values)
          | `VALID z, _ -> (z, `NotValidPtrProv, values)
          | `INVALID, _ -> (Prov_none, `NotValidPtrProv, values)
    
    let pvi_split_bytes bs =
      let prov, rev_bs =
        List.fold_left (fun (prov_acc, rev_bs_acc) b ->
          (combine_prov b.prov prov_acc, b.value :: rev_bs_acc)
        ) (Prov_none, []) bs in
      prov, List.rev rev_bs
    
    (* PNVI-ae-udi *)
    let provs_of_bytes bs =
      let xs = List.fold_left (fun acc b ->
        match b.prov with
          | Prov_none ->
              acc
          | Prov_some alloc_id ->
              alloc_id :: acc
          | Prov_symbolic iota -> (* of symbolic_storage_instance_id (* only for PNVI-ae-udi *) *)
              acc (* TODO(iota) *)
          | Prov_device ->
              acc
      ) [] bs in
      match xs with
        | [] ->
            `NoTaint
        | _ ->
            `NewTaint xs
  end
  
  type mem_state = {
    next_alloc_id: storage_instance_id;
    next_iota: symbolic_storage_instance_id;
    last_address: address;
    allocations: allocation IntMap.t;
    (* this is only for PNVI-ae-udi *)
    iota_map: [ `Single of storage_instance_id | `Double of storage_instance_id * storage_instance_id ] IntMap.t;
    funptrmap: (Digest.t * string) IntMap.t;
    varargs: (int * (ctype * pointer_value) list) IntMap.t;
    next_varargs_id: N.num;
    bytemap: AbsByte.t IntMap.t;

    last_used_union_members: Symbol.identifier IntMap.t;
    
    dead_allocations: storage_instance_id list;
    dynamic_addrs: address list;
    last_used: storage_instance_id option;

    requested: (address * N.num) list; (* the addresses (and object sizes) that were allocated with cerb::with_address() *)
  }
  
  let initial_mem_state = {
    next_alloc_id= Nat_big_num.zero;
    next_iota= N.zero;
    allocations= IntMap.empty;
    iota_map= IntMap.empty;
    last_address= N.of_int 0xFFFFFFFFFFFF; (* TODO: this is a random impl-def choice *)
    funptrmap = IntMap.empty;
    varargs = IntMap.empty;
    next_varargs_id = N.zero;
    bytemap= IntMap.empty;

    last_used_union_members= IntMap.empty;
    
    dead_allocations= [];
    dynamic_addrs= [];
    last_used= None;
    requested= [];
  }
  
  (* TODO *)
  type footprint =
      (* base address, size *)
    | FP of [`W | `R] * address * N.num
  
  let overlapping (FP (k1, b1, sz1)) (FP (k2, b2, sz2)) =
    match k1, k2 with
      | `R, `R ->
          false
      | _ ->
          not (N.(less_equal (add b1 sz1) b2) || N.(less_equal (add b2 sz2) b1))
  
  type 'a memM = ('a, mem_error, integer_value mem_constraint, mem_state) Eff.eff
  
  let return = Eff.return
  let bind = Eff.(>>=)
  
  (* TODO: hackish *)
  let fail ?(loc=Cerb_location.other "Concrete") err =
    let open Nondeterminism in
    match undefinedFromMem_error err with
      | Some ub ->
          kill (Undef0 (loc, [ub]))
      | None ->
          kill (Other err)

  
  
  let string_of_provenance = function
    | Prov_none ->
        "@empty"
    | Prov_some alloc_id ->
        "@" ^ N.to_string alloc_id
    | Prov_symbolic iota ->
        "@iota(" ^ N.to_string iota ^ ")"
    | Prov_device ->
        "@device"
  
  (* pretty printing *)
  open PPrint
  open Cerb_pp_prelude
  let pp_pointer_value ?(is_verbose=false) (PV (prov, ptrval_))=
    match ptrval_ with
      | PVnull ty ->
          !^ "NULL" ^^ P.parens (Pp_core_ctype.pp_ctype ty)
      | PVfunction sym ->
          !^ "Cfunction" ^^ P.parens (!^ (Pp_symbol.to_string_pretty sym))
          (* !^ ("<funptr:" ^ Symbol.instance_Show_Show_Symbol_sym_dict.show_method sym ^ ">") *)
      | PVconcrete (_, n) ->
          (* TODO: remove this idiotic hack when Lem's nat_big_num library expose "format" *)
          P.parens (!^ (string_of_provenance prov) ^^ P.comma ^^^ !^ ("0x" ^ Z.format "%x" (Z.of_string (Nat_big_num.to_string n))))
  
  let pp_floating_value_for_coq (f:floating_value) = !^ (string_of_float f)
  
  let pp_integer_value (IV (prov, n)) =
    if !Cerb_debug.debug_level >= 3 then
      !^ ("<" ^ string_of_provenance prov ^ ">:" ^ Nat_big_num.to_string n)
    else
      !^ (Nat_big_num.to_string n)
  
  let pp_integer_value_for_core = pp_integer_value
  
(* internal *)
  let pp_address_for_coq n = !^(N.to_string n)

  (* TODO: this is a temporary hack printing VIP memory values in Coq. *)
  let pp_integer_value_for_coq (IV (prov, n)) = 
    !^"(Mem.IVint" ^^^ (pp_address_for_coq n) ^^ !^")"
    
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
          comma_list (fun (ident, _, mval) ->
            dot ^^ Pp_symbol.pp_identifier ident ^^ equals ^^^ pp_mem_value mval
          ) xs
        )
    | MVunion (tag_sym, membr_ident, mval) ->
        parens (!^ "union" ^^^ !^ (Pp_symbol.to_string_pretty tag_sym)) ^^ braces (
          dot ^^ Pp_symbol.pp_identifier membr_ident ^^ equals ^^^
          pp_mem_value mval
        )
  
  let pp_mem_value_for_coq _ _ _ _ _ v = pp_mem_value v
  
  (* TODO: this is stupid, we need to allow the outside world to specify
     what memory ranges are in device memory *)
  let device_ranges : (address * address) list =
    (* TODO: these are some hardcoded ranges to match the Charon tests... *)
    (* NOTE: these two ranges only have 4 bytes (e.g. one int) *)
    [ (N.of_int64 0x40000000L, N.of_int64 0x40000004L)
    ; (N.of_int64 0xABCL, N.of_int64 0XAC0L) ]
  
  
  let is_PNVI () =
(*    match Switches.(has_switch_pred (function SW_no_integer_provenance _ -> true | _ -> false)) with *)
    match Switches.(has_switch_pred (function SW_PNVI _ -> true | _ -> false)) with
      | None ->
          false
      | Some _ ->
          true
  
  (* NOTE: since we are fusing PVI and PVNI together any creation of an integer_value should
     be done through this function to unsure we always use Prov_none in PVNI *)
  let mk_ival prov n =
    if is_PNVI () then
      IV (Prov_none, n)
    else
      (* We are in the mode where integer values have a provenance *)
      IV (prov, n)
  
  (* TODO: DEBUG *)
  let print_bytemap str =
    if !Cerb_debug.debug_level >= 3 then begin
      Printf.fprintf stderr "BEGIN BYTEMAP ==> %s\n" str;
      get >>= fun st ->
      IntMap.iter AbsByte.(fun addr b ->
        Printf.fprintf stderr "@%s ==> %s: %s%s\n"
          (N.to_string addr)
          (string_of_provenance b.prov)
          (match b.value with None -> "UNSPEC" | Some c -> string_of_int (int_of_char c))
          (match b.copy_offset with None -> "" | Some n -> " [" ^ string_of_int n ^ "]")
      ) st.bytemap;
      prerr_endline "END";
    return ()
    end else
      return ()
  
  let is_dynamic addr : bool memM =
    get >>= fun st ->
    return (List.mem addr st.dynamic_addrs)
  
  let is_dead alloc_id : bool memM =
    get >>= fun st ->
    return (List.mem alloc_id st.dead_allocations)
  
  let get_allocation ~loc alloc_id : allocation memM =
    get >>= fun st ->
    match IntMap.find_opt alloc_id st.allocations with
      | Some ret ->
          return ret
      | None ->
          fail ~loc (MerrOutsideLifetime ("Concrete.get_allocation, alloc_id=" ^ N.to_string alloc_id))
  
  let is_within_bound ~loc alloc_id lvalue_ty addr =
    get_allocation ~loc alloc_id >>= fun alloc ->
    return (N.less_equal alloc.base addr && N.less_equal (N.add addr (sizeof lvalue_ty)) (N.add alloc.base alloc.size))
  
  let is_within_device ty addr =
    return begin
      List.exists (fun (min, max) ->
        N.less_equal min addr && N.less_equal (N.add addr (sizeof ty)) max
      ) device_ranges
    end
  
  (* NOTE: this will have to change when moving to a subobject semantics *)
  let is_atomic_member_access ~loc alloc_id lvalue_ty addr =
    get_allocation ~loc alloc_id >>= fun alloc ->
    match alloc.ty with
      | Some ty when AilTypesAux.is_atomic ty ->
          if    addr = alloc.base && N.equal (sizeof lvalue_ty) alloc.size
             && Ctype.ctypeEqual lvalue_ty ty then
            (* the types equality check is to deal with the case where the
               first member is accessed and their are no padding bytes ... *)
            return false
          else
            let () = Printf.fprintf stderr "addr: %s <--> alloc.base: %s\n"
              (N.to_string addr) (N.to_string alloc.base) in
            let () = Printf.fprintf stderr "|lvalue_ty|: %s <--> |alloc|: %s\n"
              (N.to_string (sizeof lvalue_ty)) (N.to_string alloc.size) in
            return true
      | _ ->
          return false
  
  (* INTERNAL: fetch_bytes *)
  let fetch_bytes bytemap base_addr n_bytes : AbsByte.t list =
    List.map (fun addr ->
      match IntMap.find_opt addr bytemap with
        | Some b ->
            b
        | None ->
            AbsByte.v Prov_none None
    ) (List.init n_bytes (fun z ->
           (* NOTE: the reversal in the offset is to model
              little-endianness *)
(*           let offset = n_bytes - 1 - z in *)
(*KKK*)
         let offset = z in
         Nat_big_num.(add base_addr (of_int offset))
       ))

  
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
  
  let int_of_bytes is_signed bs =
    (* NOTE: the reverse is from little-endianness *)
    match List.rev bs with
      | [] ->
          assert false
      | cs when L.length cs > 16 ->
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
  
  (* TODO: maybe move somewhere else *)
  let find_overlaping st addr : [ `NoAlloc
                                | `SingleAlloc of storage_instance_id
                                | `DoubleAlloc of storage_instance_id * storage_instance_id ] =
    let (require_exposed, allow_one_past) =
      match Switches.(has_switch_pred (function SW_PNVI _ -> true | _ -> false)) with
        | Some (Switches.SW_PNVI variant) ->
            begin match variant with
              | `PLAIN ->
                  (false, false)
              | `AE ->
                  (true, false)
              | `AE_UDI ->
                  (true, true)
            end
        | Some _ ->
            assert false
        | None ->
            (false, false) in
    IntMap.fold (fun alloc_id alloc acc ->
      let new_opt =
        if    not (List.mem alloc_id st.dead_allocations)
           && N.less_equal alloc.base addr && N.less addr (N.add alloc.base alloc.size) then
          (* PNVI-ae, PNVI-ae-udi *)
          if require_exposed && alloc.taint <> `Exposed then
            None
          else
            Some alloc_id
        else if allow_one_past then
          (* PNVI-ae-udi *)
          if    N.equal addr (N.add alloc.base alloc.size)
             && not (require_exposed && alloc.taint <> `Exposed) then
            Some alloc_id
          else
            None
        else
          None in
      match acc, new_opt with
        | _, None ->
            acc
        | `NoAlloc, Some alloc_id ->
            `SingleAlloc alloc_id
        | `SingleAlloc alloc_id1, Some alloc_id2 ->
            `DoubleAlloc (alloc_id1, alloc_id2)
        | `DoubleAlloc _, Some _ ->
            (* TODO: I guess there is an invariant that the new_alloc
               is either of the `DoubleAlloc *)
            acc
(*
            if    not (List.mem alloc_id st.dead_allocations)
               && N.less_equal alloc.base addr && N.less addr (N.add alloc.base alloc.size) then
              (* PNVI-ae, PNVI-ae-udi *)
              if require_exposed && alloc.taint <> `Exposed then
                `NoAlloc
              else
                `SingleAlloc alloc_id
            else if allow_one_past then
              (* PNVI-ae-udi *)
              if N.equal addr (N.add alloc.base alloc.size) then
                match
                  IntMap.fold (fun alloc_id' alloc' acc' ->
                    match acc' with
                      | Some _ ->
                          acc'
                      | None ->
                          if addr = alloc'.base then
                            Some alloc_id'
                          else
                            None
                  ) st.allocations None
                with
                  | None ->
                      `SingleAlloc alloc_id
                  | Some alloc_id' ->
                      `DoubleAlloc (alloc_id, alloc_id')
              else
                `NoAlloc
            else
              `NoAlloc
*)
    ) st.allocations `NoAlloc
  
  (* PNVI-ae *)
  let expose_allocation alloc_id =
    update begin fun st ->
      {st with allocations=
       IntMap.update alloc_id (function
         | Some alloc ->
             Some {alloc with taint= `Exposed}
         | None ->
             None) st.allocations }
    end
  (* PNVI-ae *)
  let expose_allocations = function
    | `NoTaint ->
        return ()
    | `NewTaint xs ->
        update begin fun st ->
          {st with allocations=
           List.fold_left (fun acc alloc_id ->
             IntMap.update alloc_id (function
               | Some alloc ->
                   Some {alloc with taint= `Exposed}
               | None ->
                   None) acc
           ) st.allocations xs }
        end
  
  (* PNVI-ae-udi *)
  let add_iota alloc_ids =
    get >>= fun st ->
    let iota = st.next_iota in
    put {st with next_iota= N.succ st.next_iota;
                 iota_map= IntMap.add iota (`Double alloc_ids) st.iota_map } >>= fun () ->
    return iota
  
  (* PNVI-ae-udi *)
  let lookup_iota iota =
    get >>= fun st ->
    return (IntMap.find iota st.iota_map)
  
  (* PNVI-ae-udi *)
  let resolve_iota precond iota =
    lookup_iota iota >>= begin function
      | `Single alloc_id ->
          begin precond alloc_id >>= function
            | `OK ->
                return alloc_id
            | `FAIL (loc, err) ->
                fail ~loc err
          end
      | `Double (alloc_id1, alloc_id2) ->
          begin precond alloc_id1 >>= function
            | `OK ->
                return alloc_id1
            | `FAIL _ ->
                begin precond alloc_id2 >>= function
                  | `OK ->
                      return alloc_id2
                  | `FAIL (loc, err) ->
                      fail ~loc err
                end
          end
    end >>= fun alloc_id ->
    update begin fun st ->
      {st with iota_map= IntMap.add iota (`Single alloc_id) st.iota_map }
    end >>= fun () ->
    return alloc_id
  
  
  (* INTERNAL abst: ctype -> AbsByte.t list -> [`NoTaint | `NewTaint of storage_instance_id list] * mem_value * AbsByte.t list *)
  (* ASSUMES: has_size ty /\ |bs| >= sizeof ty*)
  (* property that should hold:
       forall ty bs bs' mval.
         has_size ty -> |bs| >= sizeof ty -> abst ty bs = (mval, bs') ->
         |bs'| + sizeof ty  = |bs| /\ typeof mval = ty *)
  let rec abst ?(is_zap=false) find_overlaping ~(addr : address) unionmap funptrmap (Ctype (_, ty) as cty) (bs : AbsByte.t list) : [`NoTaint | `NewTaint of storage_instance_id list] * mem_value * AbsByte.t list =
    let self ?(offset=0) = abst find_overlaping ~addr:(N.add addr (N.of_int offset)) unionmap funptrmap in
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
    
    if N.less (N.of_int (List.length bs)) (sizeof cty) then
      failwith "abst, |bs| < sizeof(ty)";
    
    let merge_taint x y =
      match x, y with
        | `NoTaint, `NoTaint ->
            `NoTaint
        | `NoTaint, `NewTaint xs
        | `NewTaint xs, `NoTaint ->
            `NewTaint xs
        | `NewTaint xs, `NewTaint ys ->
            `NewTaint (xs @ ys) in
    
    match ty with
      | Void
      | Array (_, None)
      | Function _
      | FunctionNoParams _ ->
          (* ty must have a known size *)
          assert false
      | Basic (Integer ity) ->
          let (bs1, bs2) = L.split_at (N.to_int (sizeof cty)) bs in
          let (prov, bs1') = AbsByte.pvi_split_bytes bs1 in
            (* PNVI-ae-udi *)
          ( AbsByte.provs_of_bytes bs1
          , begin match extract_unspec bs1' with
              | Some cs ->
                  MVinteger ( ity
                            , mk_ival prov (int_of_bytes (AilTypesAux.is_signed_ity ity) cs))
              | None ->
                  MVunspecified cty
            end , bs2)
      | Byte ->
          (* should be handled similarly to integers *)
          let (bs1, bs2) = L.split_at 1 bs in
          let (prov, bs1') = AbsByte.pvi_split_bytes bs1 in
            (* PNVI-ae-udi *)
          ( AbsByte.provs_of_bytes bs1
          , begin match extract_unspec bs1' with
              | Some cs ->
                  (* C++ has std::byte typedef'd to unsigned char, hence false *)
                  MVinteger ( Char , mk_ival prov (int_of_bytes false cs))
              | None ->
                  MVunspecified cty
            end , bs2)
      | Basic (Floating fty) ->
          let (bs1, bs2) = L.split_at (N.to_int (sizeof cty)) bs in
          (* we don't care about provenances for floats *)
          let (_, _, bs1') = AbsByte.split_bytes bs1 in
          ( `NoTaint
          , begin match extract_unspec bs1' with
              | Some cs ->
                  MVfloating ( fty
                             , Int64.float_of_bits (N.to_int64 (int_of_bytes true cs)) )
              | None ->
                  MVunspecified cty
            end, bs2)
      | Array (elem_ty, Some n) ->
          let rec aux n (taint_acc, mval_acc) cs =
            if n <= 0 then
              (taint_acc, MVarray (List.rev mval_acc), cs)
            else
              let (taint, mval, cs') = self elem_ty cs in
              aux (n-1) (merge_taint taint taint_acc, mval :: mval_acc) cs'
          in
          aux (Nat_big_num.to_int n) (`NoTaint, []) bs
      | Pointer (_, ref_ty) ->
          let (bs1, bs2) = L.split_at (N.to_int (sizeof cty)) bs in
          Cerb_debug.print_debug 1 [] (fun () -> "TODO: Concrete, assuming pointer repr is unsigned??");
          let (prov, prov_status, bs1') = AbsByte.split_bytes bs1 in
          ( `NoTaint (* PNVI-ae-udi *)
          , begin match extract_unspec bs1' with
              | Some cs ->
                  let n = int_of_bytes false cs in
                  begin match ref_ty with
                    | Ctype (_, Function _) ->
                        if N.equal n N.zero then
                          (* TODO: check *)
                          MVpointer (ref_ty, PV (Prov_none, PVnull ref_ty))
                        else
                          (* FIXME: This is wrong. A function pointer with the same id in different files might exist. *)
                          begin match IntMap.find_opt n funptrmap with
                            | Some (file_dig, name) ->
                                MVpointer (ref_ty, PV(prov, PVfunction (Symbol.Symbol (file_dig, N.to_int n, SD_Id name))))
                            | None ->
                                failwith ("unknown function pointer: " ^ N.to_string n)
                          end
                    | _ ->
                        if N.equal n N.zero then
                          (* TODO: check *)
                          MVpointer (ref_ty, PV (Prov_none, PVnull ref_ty))
                        else
                          let prov =
                            if is_PNVI () then
(*
                              let () =
                                print_endline "HELLO ==> PNVI abst (ptr)";
                                print_endline "BEGIN";
                                List.iter (fun bt ->
                                  let open AbsByte in
                                  Printf.printf "%s: [%s] - %s\n"
                                    (string_of_provenance bt.prov)
                                    (match bt.copy_offset with Some n -> string_of_int n | None -> "_")
                                    (match bt.value with Some c ->  Char.escaped c | None -> "unspec")
                                ) bs1;
                              print_endline "END" in
*)
                              match prov_status with
                                | `NotValidPtrProv ->
                                    (* KKK print_endline "NotValidPtrProv"; *)
                                    begin match find_overlaping n with
                                      | `NoAlloc ->
                                          Prov_none
                                      | `SingleAlloc alloc_id ->
                                          Prov_some alloc_id
                                      | `DoubleAlloc (alloc_id1, alloc_id2) ->
                                          (* FIXME/HACK(VICTOR): This is wrong, but when serialising the memory in the UI, I get this failwith. *)
                                          Prov_some alloc_id1
                                          (* failwith "TODO(iota): abst => make a iota?" *)
                                    end
                                | `ValidPtrProv ->
                                    (* KKK print_endline ("ValidPtrProv ==> " ^ string_of_provenance prov); *)
                                    prov
                            else
                              prov in
                          MVpointer (ref_ty, PV (prov, PVconcrete (None, n)))
                  end
              | None ->
                  MVunspecified (Ctype ([], Pointer (no_qualifiers, ref_ty)))
            end, bs2)
      | Atomic atom_ty ->
          Cerb_debug.print_debug 1 [] (fun () -> "TODO: Concrete, is it ok to have the repr of atomic types be the same as their non-atomic version??");
          self atom_ty bs
      | Struct tag_sym ->
          (* TODO: the N.to_int on the sizeof() will raise Overflow on huge structs *)
          let (bs1, bs2) = L.split_at (N.to_int (sizeof cty)) bs in
          let (taint, rev_xs, _, bs') = List.fold_left (fun (taint_acc, acc_xs, previous_offset, acc_bs) (memb_ident, memb_ty, memb_offset) ->
            (* TODO: the N.to_int will raise Overflow if the member is huge *)
            let pad = N.to_int (N.sub memb_offset previous_offset) in
            let (taint, mval, acc_bs') = self ~offset:pad memb_ty (L.drop pad acc_bs) in
            (merge_taint taint taint_acc, (memb_ident, memb_ty, mval)::acc_xs, N.add memb_offset (sizeof memb_ty), acc_bs')
          ) (`NoTaint, [], N.zero, bs1) (fst (offsetsof ~ignore_flexible:true (Tags.tagDefs ()) tag_sym)) in
          (* TODO: check that bs' = last padding of the struct *)
          (taint, MVstruct (tag_sym, List.rev rev_xs), bs2)
      | Union tag_sym ->
          let (bs1, bs2) = L.split_at (N.to_int (sizeof cty)) bs in
          if is_zap then
            (* TODO: hack to prevent pointer zap from crashing if a union is in the memory *)
            ( `NoTaint, MVunspecified cty, bs2)
          else (match Pmap.find tag_sym (Tags.tagDefs ()) with
            | _, UnionDef ((first_membr_def :: _) as membrs) ->
                let (membr_ident, (_, _, _, membr_ty)) =
                  match IntMap.find_opt addr unionmap with
                    | None ->
                        first_membr_def
                    | Some membr ->
                        match List.find_opt (fun z -> Symbol.instance_Basic_classes_Eq_Symbol_identifier_dict.isEqual_method (fst z) membr) membrs with
                          | None ->
                              assert false
                          | Some membr_def ->
                              membr_def in
                let (taint, mval, _ ) = self membr_ty bs1 in
                (taint, MVunion (tag_sym, membr_ident, mval), bs2)
            | _ ->
                assert false)

  (* INTERNAL bytes_of_int *)
  let bytes_of_int is_signed size i : (char option) list =
    let nbits = 8 * size in
    let (min, max) =
      if is_signed then
        ( N.negate (N.pow_int (N.of_int 2) (nbits-1))
        , N.sub (N.pow_int (N.of_int 2) (nbits-1)) N.(succ zero) )
      else
        ( N.zero
        , N.sub (N.pow_int (N.of_int 2) nbits) N.(succ zero) ) in
    if not (min <= i && i <= max) || nbits > 128 then begin
      Printf.printf "failed: bytes_of_int(%s), i= %s, nbits= %d, [%s ... %s]\n"
        (if is_signed then "signed" else "unsigned")
        (N.to_string i) nbits (N.to_string min) (N.to_string max);
      assert false
    end else
      List.init size (fun n ->
        Some (char_of_int (N.to_int (N.extract_num i (8*n) 8)))
      )
  
  let rec typeof mval =
    Ctype ([], match mval with
      | MVunspecified (Ctype (_, ty)) ->
          ty
      | MVinteger (ity, _) ->
          Basic (Integer ity)
      | MVfloating (fty, _) ->
          Basic (Floating fty)
      | MVpointer (ref_ty, _) ->
          Pointer (no_qualifiers, ref_ty)
      | MVarray [] ->
          (* ill-formed value *)
          assert false
      | MVarray ((mval::_) as mvals) ->
          (* TODO: checking all the elements would be stupidly slow, but this
             feels wrong *)
          Array (typeof mval, Some (N.of_int (List.length mvals)))
      | MVstruct (tag_sym, _) ->
          Struct tag_sym
      | MVunion (tag_sym, _, _) ->
          Union tag_sym
      )
  
  (* INTERNAL repr *)
  let rec repr funptrmap mval : ((Digest.t * string) IntMap.t * AbsByte.t list) =
    let ret bs = (funptrmap, bs) in
    match mval with
      | MVunspecified ty ->
          (* TODO: the N.to_int on the sizeof() will raise Overflow on huge structs/unions *)
          ret @@ List.init (N.to_int (sizeof ty)) (fun _ -> AbsByte.v Prov_none None)
      | MVinteger (ity, IV (prov, n)) ->
          ret @@List.map (AbsByte.v prov) begin
            bytes_of_int
              (AilTypesAux.is_signed_ity ity)
              (N.to_int (sizeof (Ctype ([], Basic (Integer ity))))) n
          end
      | MVfloating (fty, fval) ->
          ret @@ List.map (AbsByte.v Prov_none) begin
            bytes_of_int
              true (* TODO: check that *)
              (N.to_int (sizeof (Ctype ([], Basic (Floating fty))))) (N.of_int64 (Int64.bits_of_float fval))
          end
      | MVpointer (_, PV (prov, ptrval_)) ->
          Cerb_debug.print_debug 1 [] (fun () -> "NOTE: we fix the sizeof pointers to 8 bytes");
          let ptr_size = match (Ocaml_implementation.get ()).sizeof_pointer with
            | None ->
                failwith "the concrete memory model requires a complete implementation"
            | Some z ->
                z in
          begin match ptrval_ with
            | PVnull _ ->
                Cerb_debug.print_debug 1 [] (fun () -> "NOTE: we fix the representation of all NULL pointers to be 0x0");
                ret @@ List.init ptr_size (fun _ -> AbsByte.v Prov_none (Some '\000'))
            | PVfunction (Symbol.Symbol (file_dig, n, opt_name)) ->
                (* TODO: *)
                (begin match opt_name with
                  | SD_Id name -> IntMap.add (N.of_int n) (file_dig, name) funptrmap
                  | SD_unnamed_tag _
                  | SD_CN_Id _
                  | SD_ObjectAddress _
                  | SD_Return
                  | SD_FunArg _ 
                  | SD_FunArgValue _
                  (* | SD_Pointee _ -> funptrmap *)
                  (* | SD_PredOutput _ -> funptrmap *)
                  | SD_None -> funptrmap
                end, List.map (AbsByte.v prov) begin
                  bytes_of_int
                      false
                      ptr_size (N.of_int n)
                  end)
            | PVconcrete (_, addr) ->
                ret @@ List.mapi (fun i -> AbsByte.v prov ~copy_offset:(Some i)) begin
                  bytes_of_int
                    false (* we model address as unsigned *)
                    ptr_size addr
                end
          end
      | MVarray mvals ->
          let (funptrmap, bs_s) =
            List.fold_left begin fun (funptrmap, bs) mval ->
              let (funptrmap, bs') = repr funptrmap mval in
              (funptrmap, bs' :: bs)
            end (funptrmap, []) mvals in
          (* TODO: use a fold? *)
          (funptrmap, L.concat @@ List.rev bs_s)
      | MVstruct (tag_sym, xs) ->
          let padding_byte _ = AbsByte.v Prov_none None in
          let (offs, last_off) = offsetsof ~ignore_flexible:true (Tags.tagDefs ()) tag_sym in
          (* NOTE: this N.to_int is fine because we can't have huge paddings *)
          let final_pad = N.(to_int (sub (sizeof (Ctype ([], Struct tag_sym))) last_off)) in
          (* TODO: rewrite now that offsetsof returns the paddings *)
          let (funptrmap, _, bs) = List.fold_left2 begin fun (funptrmap, last_off, acc) (ident, ty, off) (_, _, mval) ->
              (* NOTE: this N.to_int is fine because we can't have huge paddings *)
              let pad = N.to_int (N.sub off last_off) in
              let (funptrmap, bs) = repr funptrmap mval in
              (funptrmap, N.add off (sizeof ty), acc @ List.init pad padding_byte @ bs)
            end (funptrmap, N.zero, []) offs xs
          in
          (funptrmap, bs @ List.init final_pad padding_byte)
      | MVunion (tag_sym, memb_ident, mval) ->
          (* TODO: the N.to_int on the sizeof() will raise Overflow on huge structs/unions *)
          let size = N.to_int (sizeof (Ctype ([], Union tag_sym))) in
          let (funptrmap', bs) = repr funptrmap mval in
          (funptrmap', bs @ List.init (size - List.length bs) (fun _ -> AbsByte.v Prov_none None))
  
  
  (* BEGIN DEBUG *)
  let dot_of_mem_state st =
    let get_value alloc =
      let bs = fetch_bytes st.bytemap alloc.base (N.to_int alloc.size) in
      match alloc.ty with
        | Some ty ->
            let (_, mval, _) = abst (find_overlaping st) ~addr:alloc.base st.last_used_union_members st.funptrmap ty bs in
            mval
        | None ->
            failwith "Concrete.dot_of_mem_state: alloc.ty = None"
    in
    let xs = IntMap.fold (fun alloc_id alloc acc ->
      Printf.sprintf "alloc%s [shape=\"record\", label=\"{ addr: %s | sz: %s | %s }\"];"
        (N.to_string alloc_id)
        (N.to_string alloc.base)
        (N.to_string alloc.size)
        (Pp_utils.to_plain_string (pp_mem_value (get_value alloc))) :: acc
    ) st.allocations [] in
    prerr_endline "digraph G{";
    List.iter prerr_endline xs;
    prerr_endline "}"
  (* END DEBUG *)
  
  
  (* TODO: this module should be made parametric in this function (i.e. the allocator should be impl-def) *)
  let allocator (size: N.num) (align: N.num) : (storage_instance_id * address) memM =
    get >>= fun st ->
    let alloc_id = st.next_alloc_id in
    begin
      let open N in
      let z = sub st.last_address size in
      let (q,m) = quomod z align in
      let z' = sub z (if less q zero then negate m else m) in
      if less_equal z' zero then
        fail (MerrOther "Concrete.allocator: failed (out of memory)")
      else
        return z'
    end >>= fun addr ->
    put { st with
      next_alloc_id= Nat_big_num.succ alloc_id;
      last_used= Some alloc_id;
      last_address= addr
    } >>= fun () ->
    return (alloc_id, addr)
  
  let allocator_with_address (addr: N.num) (size: N.num) (align: N.num) : (storage_instance_id * address) memM =
    let open N in
    if equal (N.modulus addr align ) zero then
      (* TODO: need to check non overlapping +
              need to update the normal allocator to avoid requested footprints. *)
      (* for things to work, we need the cerb pipeline to collect all requested footprints 
         by the translation unit, and tell the memory model about them BEFORE THE BEGINNING of execution.
         Otherwise it will possible for the normal allocator to use a requested footprint before a create() with
         the requested footprint is actually executed, which will make the create() fail and the user cry...
         NOTE: ===> but then when linking multiple translation units we must make sure their set of requested footprints do not overlap...
      *)
      get >>= fun st ->
      let alloc_id = st.next_alloc_id in    
      put { st with
        next_alloc_id= Nat_big_num.succ alloc_id;
        last_used= Some alloc_id;
      } >>= fun () ->
      return (alloc_id, addr)
    else
      failwith "allocator_with_address ==> requested adddress has wrong alignment"
  
  let allocate_object tid pref (*is_zero_init*) (IV (_, align)) ty req_addr_opt init_opt : pointer_value memM =
(*    print_bytemap "ENTERING ALLOC_STATIC" >>= fun () -> *)
    let size = sizeof ty in
    begin match req_addr_opt with
      | None ->
          allocator size align
      | Some addr ->
            failwith "TODO: cerb::with_address() is yet implemented"
           (* allocator_with_address addr size align *)
    end >>= fun (alloc_id, addr) ->
    Cerb_debug.print_debug 10(*KKK*) [] (fun () ->
      "STATIC ALLOC - pref: " ^ String_symbol.string_of_prefix pref ^
      " --> alloc_id= " ^ N.to_string alloc_id ^
      ", size= " ^ N.to_string size ^
      ", addr= " ^ N.to_string addr
    );
    begin match init_opt with
      | None ->
          let alloc = {prefix= pref; base= addr; size= size; ty= Some ty; is_readonly= IsWritable; taint= `Unexposed} in
          update (fun st ->
            { st with allocations= IntMap.add alloc_id alloc st.allocations;
                      bytemap=
                        if Switches.(has_switch SW_zero_initialised) then
                          let bs = List.init (Z.to_int size) (fun i ->
                            (Nat_big_num.add addr (Nat_big_num.of_int i), AbsByte.v Prov_none (Some '\000'))
                          ) in
                          List.fold_left (fun acc (addr, b) ->
                            IntMap.add addr b acc
                          ) st.bytemap bs
                        else
                          let (_, pre_bs) = repr st.funptrmap (MVunspecified ty) in
                          let bs = List.mapi (fun i b -> (Nat_big_num.add addr (Nat_big_num.of_int i), b)) pre_bs in              
                          List.fold_left (fun acc (addr, b) ->
                            IntMap.add addr b acc
                          ) st.bytemap bs; }
          )
      | Some mval ->
          let readonly_status =
            match pref with
              | Symbol.PrefStringLiteral _ ->
                  IsReadOnly ReadonlyStringLiteral
              | Symbol.PrefTemporaryLifetime _ ->
                  IsReadOnly ReadonlyTemporaryLifetime
              | _ ->
                  IsReadOnly ReadonlyConstQualified in
          let alloc = {prefix= pref; base= addr; size= size; ty= Some ty; is_readonly= readonly_status; taint= `Unexposed} in
          (* TODO: factorise this with do_store inside Concrete.store *)
          update (fun st ->
            let (funptrmap, pre_bs) = repr st.funptrmap mval in
            let bs = List.mapi (fun i b -> (Nat_big_num.add addr (Nat_big_num.of_int i), b)) pre_bs in
            { st with
                allocations= IntMap.add alloc_id alloc st.allocations;
                bytemap=
                  List.fold_left (fun acc (addr, b) ->
                    IntMap.add addr b acc
                  ) st.bytemap bs;
                funptrmap= funptrmap; }
          )
    end >>= fun () ->
    return (PV (Prov_some alloc_id, PVconcrete (None, addr)))
  
  let update_prefix (pref, mval) =
    match mval with
    | MVpointer (_, PV (Prov_some alloc_id, _)) ->
        let upd_alloc = function
          | Some alloc ->
              Some { alloc with prefix = pref }
          | None ->
              Cerb_debug.warn [] (fun () -> "update_prefix: allocation does not exist");
              None
        in
        update (fun st -> { st with allocations= IntMap.update alloc_id upd_alloc st.allocations })
    | _ ->
        Cerb_debug.warn [] (fun () -> "update_prefix: wrong arguments");
        return ()
  
  let prefix_of_pointer (PV (prov, pv)) : string option memM =
    let open String_symbol in
    let rec aux addr alloc = function
      | None
      | Some (Ctype (_, Void))
      | Some (Ctype (_, Function _))
      | Some (Ctype (_, FunctionNoParams _)) ->
          None
      | Some (Ctype (_, Basic _))
      | Some (Ctype (_, Union _))
      | Some (Ctype (_, Pointer _))
      | Some (Ctype (_, Byte)) ->
          let offset = N.sub addr alloc.base in
          Some (string_of_prefix alloc.prefix ^ " + " ^ N.to_string offset)
      | Some (Ctype (_, Struct tag_sym)) -> (* TODO: nested structs *)
          let offset = N.sub addr alloc.base in
          let (offs, _) = offsetsof (Tags.tagDefs ()) tag_sym in
          let rec find = function
            | [] ->
              None
            | (Symbol.Identifier (_, memb), _, off) :: offs ->
              if N.equal offset off then
                Some (string_of_prefix alloc.prefix ^ "." ^ memb)
              else
                find offs
          in find offs
      | Some (Ctype (_, Array (ty, _))) ->
          let offset = N.sub addr alloc.base in
          if N.less offset alloc.size then
            let n = N.div offset (sizeof ty) in
            Some (string_of_prefix alloc.prefix ^ "[" ^ N.to_string n ^ "]")
          else
            None
      | Some (Ctype (_, Atomic ty)) ->
          aux addr alloc @@ Some ty
    in
    match prov with
    | Prov_some alloc_id ->
      get_allocation ~loc:(Cerb_location.other "concrete") alloc_id >>= fun alloc ->
      begin match pv with
        | PVconcrete (_, addr) ->
          if addr = alloc.base then
            return @@ Some (string_of_prefix alloc.prefix)
          else
            return @@ aux addr alloc alloc.ty
        | PVnull ty ->
          if Some ty = alloc.ty then
            return @@ Some (string_of_prefix alloc.prefix)
          else
            return None
        | _ ->
          return None
      end
    | _ ->
      return None

  let allocate_region tid pref (IV (_, align_n)) (IV (_, size_n)) =
    allocator size_n align_n >>= fun (alloc_id, addr) ->
    Cerb_debug.print_debug 1 [] (fun () ->
      "DYNAMIC ALLOC - pref: " ^ String_symbol.string_of_prefix pref ^ (* pref will always be Core *)
      " --> alloc_id= " ^ N.to_string alloc_id ^
      ", size= " ^ N.to_string size_n ^
      ", addr= " ^ N.to_string addr
    );
    (* TODO: why aren't we using the argument pref? *)
    let alloc = {prefix= Symbol.PrefMalloc; base= addr; size= size_n; ty= None; is_readonly= IsWritable; taint= `Unexposed} in
    update (fun st ->
      { st with
          allocations= IntMap.add alloc_id alloc st.allocations;
          dynamic_addrs= addr :: st.dynamic_addrs }
    ) >>= fun () ->
    return (PV (Prov_some alloc_id, PVconcrete (None, addr)))
  
  (* zap (make unspecified) any pointer in the memory with provenance matching a
     given allocation id *)
  let zap_pointers alloc_id =
    modify (fun st ->
      let bytemap' = IntMap.fold (fun _ alloc acc ->
        let bs = fetch_bytes st.bytemap alloc.base (N.to_int alloc.size) in
        match alloc.ty with
          | None ->
              (* TODO: zapping doesn't work yet for dynamically allocated pointers *)
              acc
          | Some ty ->
              begin match abst ~is_zap:true (find_overlaping st) ~addr:alloc.base st.last_used_union_members st.funptrmap ty bs with
                | (_, MVpointer (ref_ty, (PV (Prov_some ptr_alloc_id, _))), []) when alloc_id = ptr_alloc_id ->
                    let bs' = List.init (N.to_int alloc.size) (fun i ->
                      (Nat_big_num.add alloc.base (Nat_big_num.of_int i), AbsByte.v Prov_none None)
                    ) in
                    List.fold_left (fun acc (addr, b) ->
                      IntMap.add addr b acc
                    ) acc bs'
                | _ ->
                    (* TODO: check *)
                    acc
              end
      ) st.allocations st.bytemap in
    ((), { st with bytemap= bytemap' })
    )
  
  let kill loc is_dyn : pointer_value -> unit memM = function
    | PV (_, PVnull _) ->
        if Switches.(has_switch SW_forbid_nullptr_free) then
          fail ~loc MerrFreeNullPtr
        else
          return ()
    | PV (_, PVfunction _) ->
          fail ~loc (MerrOther "attempted to kill with a function pointer")
    | PV (Prov_none, PVconcrete _) ->
          fail ~loc (MerrOther "attempted to kill with a pointer lacking a provenance")
    | PV (Prov_device, PVconcrete _) ->
        (* TODO: should that be an error ?? *)
        return ()
    
    (* PNVI-ae-udi *)
    | PV (Prov_symbolic iota, PVconcrete (_, addr)) ->
        let precondition z =
          is_dead z >>= function
            | true ->
                return (`FAIL (loc, MerrUndefinedFree Free_dead_allocation))
            | false ->
                get_allocation ~loc z >>= fun alloc ->
                if N.equal addr alloc.base then
                  return `OK
                else
                  return (`FAIL (loc, MerrUndefinedFree Free_out_of_bound)) in
        begin if is_dyn then
          (* this kill is dynamic one (i.e. free() or friends) *)
          is_dynamic addr >>= begin function
            | false ->
                fail ~loc (MerrUndefinedFree Free_non_matching)
            | true ->
                return ()
          end
        else
          return ()
        end >>= fun () ->
        resolve_iota precondition iota >>= fun alloc_id ->
        (* TODO: this is duplicated code from the Prov_some case (I'm keeping
           PNVI-ae-udi stuff separated to avoid polluting the
           vanilla PNVI code) *)
        update begin fun st ->
          {st with dead_allocations= alloc_id :: st.dead_allocations;
                   last_used= Some alloc_id;
                   allocations= IntMap.remove alloc_id st.allocations}
        end >>= fun () ->
        if Switches.(has_switch SW_zap_dead_pointers) then
          zap_pointers alloc_id
        else
          return ()
    
    | PV (Prov_some alloc_id, PVconcrete (_, addr)) ->
        begin if is_dyn then
          (* this kill is dynamic one (i.e. free() or friends) *)
          is_dynamic addr >>= begin function
            | false ->
                fail ~loc (MerrUndefinedFree Free_non_matching)
            | true ->
                return ()
          end
        else
          return ()
        end >>= fun () ->
        is_dead alloc_id >>= begin function
          | true ->
              if is_dyn then
                fail ~loc (MerrUndefinedFree Free_dead_allocation)
              else
                failwith "Concrete: FREE was called on a dead allocation"
          | false ->
              get_allocation ~loc alloc_id >>= fun alloc ->
              if N.equal addr alloc.base then begin
                Cerb_debug.print_debug 1 [] (fun () ->
                  "KILLING alloc_id= " ^ N.to_string alloc_id
                );
                update begin fun st ->
                  {st with dead_allocations= alloc_id :: st.dead_allocations;
                           last_used= Some alloc_id;
                           allocations= IntMap.remove alloc_id st.allocations}
                end >>= fun () ->
                if Switches.(has_switch SW_zap_dead_pointers) then
                  zap_pointers alloc_id
                else
                  return ()
              end else
                fail ~loc (MerrUndefinedFree Free_out_of_bound)
        end
  
  let load loc ty (PV (prov, ptrval_)) =
    Cerb_debug.print_debug 10(*KKK*) [] (fun () ->
      "ENTERING LOAD: " ^ Cerb_location.location_to_string loc
    );
    let do_load alloc_id_opt addr =
      get >>= fun st ->
      (* TODO: the N.to_int will fail on huge objects *)
      let bs = fetch_bytes st.bytemap addr (N.to_int (sizeof ty)) in
      let (taint, mval, bs') = abst (find_overlaping st) ~addr st.last_used_union_members st.funptrmap ty bs in
      (* PNVI-ae-udi *)
      begin if Switches.(has_switch (SW_PNVI `AE) || has_switch (SW_PNVI `AE_UDI)) then
        expose_allocations taint
      else
        return ()
      end >>= fun () ->
      update (fun st -> { st with last_used= alloc_id_opt }) >>= fun () ->
      let fp = FP (`R, addr, (sizeof ty)) in
      begin match bs' with
        | [] ->
            Cerb_debug.print_debug 10(*KKK*) [] (fun () ->
              "EXITING LOAD: ty=" ^ String_core_ctype.string_of_ctype ty ^
              ", @" ^ Pp_utils.to_plain_string (pp_pointer_value (PV (prov, ptrval_))) ^
              " ==> mval= " ^ Pp_utils.to_plain_string (pp_mem_value mval)
             );
            (* trap representation for _Bool *)
            (* TODO: might be nicer to have that part of the Ocaml_implementation interface
               (even so we probably will only ever use it for _Bool) *)
            begin if AilTypesAux.is_Bool ty then
              let is_trap n =
                not N.(equal n zero || equal n (succ zero)) in
              match mval with
                | MVunspecified _ ->
                    fail ~loc (MerrTrapRepresentation LoadAccess)
                | MVinteger (_, (IV (_, n))) when is_trap n ->
                    fail ~loc (MerrTrapRepresentation LoadAccess)
                | _ ->
                    return ()
            else
              return ()
            end >>= fun () ->

            if Switches.(has_switch SW_strict_reads) then
              match mval with
                | MVunspecified _ ->
                    fail ~loc MerrReadUninit
                | _ ->
                    return (fp, mval)
            else
              return (fp, mval)
        | _ ->
            fail ~loc (MerrWIP "load, bs' <> []")
      end in
    match (prov, ptrval_) with
      | (_, PVnull _) ->
          fail ~loc (MerrAccess (LoadAccess, NullPtr))
      | (_, PVfunction _) ->
          fail ~loc (MerrAccess (LoadAccess, FunctionPtr))
      | (Prov_none, _) ->
          fail ~loc (MerrAccess (LoadAccess, OutOfBoundPtr))
      | (Prov_device, PVconcrete (_, addr)) ->
          begin is_within_device ty addr >>= function
            | false ->
                fail ~loc (MerrAccess (LoadAccess, OutOfBoundPtr))
            | true ->
                do_load None addr
          end
      
      (* PNVI-ae-udi *)
      | (Prov_symbolic iota, PVconcrete (_, addr)) ->
        (* TODO: this is duplicated code from the Prov_some case (I'm keeping
           PNVI-ae-udi stuff separated to avoid polluting the
           vanilla PNVI code) *)
          let precondition z =
            is_dead z >>= begin function
              | true ->
                  return (`FAIL (loc, MerrAccess (LoadAccess, DeadPtr)))
              | false ->
                  begin is_within_bound ~loc z ty addr >>= function
                    | false ->
                        return (`FAIL (loc, MerrAccess (LoadAccess, OutOfBoundPtr)))
                    | true ->
                        begin is_atomic_member_access ~loc z ty addr >>= function
                          | true ->
                              return (`FAIL (loc, MerrAccess (LoadAccess, AtomicMemberof)))
                          | false ->
                              return `OK
                        end
                  end
            end in
          resolve_iota precondition iota >>= fun alloc_id ->
          do_load (Some alloc_id) addr
      
      | (Prov_some alloc_id, PVconcrete (_, addr)) ->
          is_dead alloc_id >>= begin function
            | true ->
                fail ~loc (MerrAccess (LoadAccess, DeadPtr))
            | false ->
                return ()
          end >>= fun () ->
          begin is_within_bound ~loc alloc_id ty addr >>= function
            | false ->
                Cerb_debug.print_debug 1 [] (fun () ->
                  "LOAD out of bound, alloc_id=" ^ N.to_string alloc_id
                );
                fail ~loc (MerrAccess (LoadAccess, OutOfBoundPtr))
            | true ->
                begin is_atomic_member_access ~loc alloc_id ty addr >>= function
                  | true ->
                      fail ~loc (MerrAccess (LoadAccess, AtomicMemberof))
                  | false ->
                      do_load (Some alloc_id) addr
                end
          end
  
  
  let store loc ty is_locking (PV (prov, ptrval_)) mval =
    Cerb_debug.print_debug 10(*KKK*) [] (fun () ->
      "ENTERING STORE: ty=" ^ String_core_ctype.string_of_ctype ty ^
      " -> @" ^ Pp_utils.to_plain_string (pp_pointer_value (PV (prov, ptrval_))) ^
      ", mval= " ^ Pp_utils.to_plain_string (pp_mem_value mval)
    );
    if not (ctype_mem_compatible ty (typeof mval)) then begin
      Printf.printf "STORE ty          ==> %s\n"
        (String_core_ctype.string_of_ctype ty);
      Printf.printf "STORE typeof mval ==> %s\n"
        (String_core_ctype.string_of_ctype (typeof mval));
      Printf.printf "STORE ==> %s\n" (Cerb_location.location_to_string loc);
      Printf.printf "STORE mval ==> %s\n"
        (Pp_utils.to_plain_string (pp_mem_value mval));
      fail ~loc (MerrOther "store with an ill-typed memory value")
    end else
      let do_store alloc_id_opt addr =
        update begin fun st ->
          let (funptrmap, pre_bs) = repr st.funptrmap mval in
          let bs = List.mapi (fun i b -> (Nat_big_num.add addr (Nat_big_num.of_int i), b)) pre_bs in
          { st with last_used= alloc_id_opt;
                    bytemap=
                      List.fold_left (fun acc (addr, b) ->
                      IntMap.add addr b acc
                    ) st.bytemap bs;
                    funptrmap= funptrmap; }
        end >>= fun () ->
        begin match ptrval_ with
          | PVconcrete (Some membr, _) ->
              Eff.update (fun st ->
                { st with last_used_union_members= IntMap.add addr membr st.last_used_union_members }
              )
          | _ ->
              return ()
        end >>= fun () ->
        print_bytemap ("AFTER STORE => " ^ Cerb_location.location_to_string loc) >>= fun () ->
        return (FP (`W, addr, (sizeof ty))) in
      let select_ro_kind = function
        | Symbol.PrefTemporaryLifetime _ ->
            ReadonlyTemporaryLifetime
        | Symbol.PrefStringLiteral _ ->
            ReadonlyStringLiteral
        | _ ->
            ReadonlyConstQualified in
      match (prov, ptrval_) with
        | (_, PVnull _) ->
            fail ~loc (MerrAccess (StoreAccess, NullPtr))
        | (_, PVfunction _) ->
            fail ~loc (MerrAccess (StoreAccess, FunctionPtr))
        | (Prov_none, _) ->
            fail ~loc (MerrAccess (StoreAccess, OutOfBoundPtr))
        | (Prov_device, PVconcrete (_, addr)) ->
            begin is_within_device ty addr >>= function
              | false ->
                  fail ~loc (MerrAccess (StoreAccess, OutOfBoundPtr))
              | true ->
                  do_store None addr
            end
        
      (* PNVI-ae-udi *)
      | (Prov_symbolic iota, PVconcrete (_, addr)) ->
        (* TODO: this is duplicated code from the Prov_some case (I'm keeping
           PNVI-ae-udi stuff separated to avoid polluting the
           vanilla PNVI code) *)
          let precondition z =
            is_within_bound ~loc z ty addr >>= function
              | false ->
                  return (`FAIL (loc, MerrAccess (StoreAccess, OutOfBoundPtr)))
              | true ->
                  get_allocation ~loc z >>= fun alloc ->
                  match alloc.is_readonly with
                    | IsReadOnly ro_kind ->
                        return (`FAIL (loc, MerrWriteOnReadOnly ro_kind))
                    | IsWritable ->
                      begin is_atomic_member_access ~loc z ty addr >>= function
                        | true ->
                            return (`FAIL (loc, MerrAccess (LoadAccess, AtomicMemberof)))
                        | false ->
                            return `OK
                      end in
          resolve_iota precondition iota >>= fun alloc_id ->
          do_store (Some alloc_id) addr >>= fun fp ->
          begin if is_locking then
            Eff.update (fun st ->
              { st with allocations=
                  IntMap.update alloc_id (function
                    | Some alloc -> Some { alloc with is_readonly= IsReadOnly (select_ro_kind alloc.prefix) }
                    | None       -> None
                  ) st.allocations }
            )
          else
            return ()
          end >>= fun () ->
          return fp
        
        | (Prov_some alloc_id, PVconcrete (_, addr)) ->
            begin is_within_bound alloc_id ~loc ty addr >>= function
              | false ->
                  fail ~loc (MerrAccess (StoreAccess, OutOfBoundPtr))
              | true ->
                  get_allocation ~loc alloc_id >>= fun alloc ->
                  match alloc.is_readonly with
                    | IsReadOnly ro_kind ->
                        fail ~loc (MerrWriteOnReadOnly ro_kind)
                    | IsWritable ->
                        begin is_atomic_member_access ~loc alloc_id ty addr >>= function
                          | true ->
                              fail ~loc (MerrAccess (LoadAccess, AtomicMemberof))
                          | false ->
                              do_store (Some alloc_id) addr >>= fun fp ->
                              if is_locking then
                                Eff.update (fun st ->
                                  { st with allocations=
                                      IntMap.update alloc_id (function
                                        | Some alloc -> Some { alloc with is_readonly= IsReadOnly (select_ro_kind alloc.prefix) }
                                        | None       -> None
                                      ) st.allocations }
                                ) >>= fun () ->
                                return fp
                              else
                                return fp
                        end
            end

(*
  (* TODO: DEBUG: *)
  >>= fun ret ->
  get >>= fun st ->
  dot_of_mem_state st;
  return ret
*)
  
  let null_ptrval ty =
    PV (Prov_none, PVnull ty)
  
  let fun_ptrval sym =
    PV (Prov_none, PVfunction sym)

  let concrete_ptrval i addr =
    PV (Prov_some i, PVconcrete (None, addr))

  let case_ptrval pv fnull ffun fconc =
    match pv with
    | PV (_, PVnull ty) -> fnull ty
    | PV (_, PVfunction f) -> ffun (Some f)
    | PV (Prov_none, PVconcrete (_, addr)) -> fconc None addr
    | PV (Prov_some i, PVconcrete (_, addr)) -> fconc (Some i) addr
    | _ -> failwith "case_ptrval"

  let case_funsym_opt st (PV (_, ptrval)) =
    match ptrval with
    | PVfunction sym -> Some sym
    | PVconcrete (_, addr) ->
      (* FIXME: This is wrong. A function pointer with the same id in different files might exist. *)
      begin match IntMap.find_opt addr st.funptrmap with
        | Some (file_dig, name) ->
            Some (Symbol.Symbol (file_dig, N.to_int addr, SD_Id name))
        | None ->
            None
      end
    | _ -> None
    
  
  let eq_ptrval loc (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
      | (PVnull _, PVnull _) ->
          return true
      | (PVnull _, _)
      | (_, PVnull _) ->
          return false
      | (PVfunction sym1, PVfunction sym2) ->
          return (Symbol.instance_Basic_classes_Eq_Symbol_sym_dict.Lem_pervasives.isEqual_method sym1 sym2)
      | (PVfunction (Symbol.Symbol (_, _, SD_Id funname)), PVconcrete (_, addr))
      | (PVconcrete (_, addr), PVfunction (Symbol.Symbol (_, _, SD_Id funname))) ->
          get >>= fun st ->
          begin match IntMap.find_opt addr st.funptrmap with
            | Some (_, funname') ->
                return (funname = funname')
            | None ->
                return false
          end
      | (PVfunction _, _)
      | (_, PVfunction _) ->
          return false
      | (PVconcrete (_, addr1), PVconcrete (_, addr2)) ->
          if Switches.(has_switch SW_strict_pointer_equality) then
            return (Nat_big_num.equal addr1 addr2)
          else begin match (prov1, prov2) with
            | (Prov_none, Prov_none) ->
                return true
            | (Prov_some alloc_id1, Prov_some alloc_id2) ->
                return (N.equal alloc_id1 alloc_id2)
            | (Prov_device, Prov_device) ->
                return true
            | (Prov_symbolic iota1, Prov_symbolic iota2) ->
                (* PNVI-ae-udi *)
                lookup_iota iota1 >>= fun ids1 ->
                lookup_iota iota2 >>= fun ids2 ->
                begin match (ids1, ids2) with
                  | (`Single alloc_id1, `Single alloc_id2) ->
                      return (N.equal alloc_id1 alloc_id2)
                  | _ ->
                      return false
                end
            | _ ->
                return false
          end >>= begin function
            | true ->
                return (Nat_big_num.equal addr1 addr2)
            | false ->
                Eff.msum "pointer equality"
                  [ ("using provenance", return false)
                  ; ("ignoring provenance", return (Nat_big_num.equal addr1 addr2)) ]
          end
  
  let ne_ptrval loc ptrval1 ptrval2 =
    eq_ptrval loc ptrval1 ptrval2 >>= fun b ->
    return (not b)
  
  let lt_ptrval loc (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
      | (PVconcrete (_, addr1), PVconcrete (_, addr2)) ->
          if Switches.(has_switch SW_strict_pointer_relationals) then
            match prov1, prov2 with
              | Prov_some alloc1, Prov_some alloc2 when N.equal alloc1 alloc2 ->
                  return (Nat_big_num.compare addr1 addr2 == -1)
              | _ ->
                  (* TODO: one past case *)
                  fail ~loc MerrPtrComparison
          else
            return (Nat_big_num.compare addr1 addr2 == -1)
      | (PVnull _, _)
      | (_, PVnull _) ->
          fail ~loc (MerrWIP "lt_ptrval ==> one null pointer")
      | _ ->
          fail ~loc (MerrWIP "lt_ptrval")
  
  let gt_ptrval loc (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
      | (PVconcrete (_, addr1), PVconcrete (_, addr2)) ->
          if Switches.(has_switch SW_strict_pointer_relationals) then
            match prov1, prov2 with
              | Prov_some alloc1, Prov_some alloc2 when alloc1 = alloc2 ->
                  return (Nat_big_num.compare addr1 addr2 == 1)
              | _ ->
                  (* TODO: one past case *)
                  fail ~loc MerrPtrComparison
          else
            return (Nat_big_num.compare addr1 addr2 == 1)
      | _ ->
          fail ~loc (MerrWIP "gt_ptrval")
  
  let le_ptrval loc (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
      | (PVconcrete (_, addr1), PVconcrete (_, addr2)) ->
          if Switches.(has_switch SW_strict_pointer_relationals) then
            match prov1, prov2 with
              | Prov_some alloc1, Prov_some alloc2 when alloc1 = alloc2 ->
                  let cmp = Nat_big_num.compare addr1 addr2 in
                  return (cmp = -1 || cmp = 0)
              | _ ->
                  (* TODO: one past case *)
                  fail ~loc MerrPtrComparison
          else
            let cmp = Nat_big_num.compare addr1 addr2 in
            return (cmp = -1 || cmp = 0)
      | _ ->
          fail ~loc (MerrWIP "le_ptrval")
  
  let ge_ptrval loc (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
      | (PVconcrete (_, addr1), PVconcrete (_, addr2)) ->
          if Switches.(has_switch SW_strict_pointer_relationals) then
            match prov1, prov2 with
              | Prov_some alloc1, Prov_some alloc2 when alloc1 = alloc2 ->
                  let cmp = Nat_big_num.compare addr1 addr2 in
                  return (cmp = 1 || cmp = 0)
              | _ ->
                  (* TODO: one past case *)
                  fail ~loc MerrPtrComparison
          else
            let cmp = Nat_big_num.compare addr1 addr2 in
            return (cmp = 1 || cmp = 0)
      | _ ->
          fail ~loc (MerrWIP "ge_ptrval")
  
  
  let diff_ptrval loc diff_ty ptrval1 ptrval2 =
    let precond alloc addr1 addr2 =
         N.less_equal alloc.base addr1
      && N.less_equal addr1 (N.add alloc.base alloc.size)
      && N.less_equal alloc.base addr2
      && N.less_equal addr2 (N.add alloc.base alloc.size) in
    
    let valid_postcond addr1 addr2 =
      let diff_ty' = match diff_ty with
        | Ctype (_, Array (elem_ty, _)) ->
            elem_ty
        | _ ->
            diff_ty in
      return (IV (Prov_none, N.div (N.sub addr1 addr2) (sizeof diff_ty'))) in
    let error_postcond =
      fail ~loc MerrPtrdiff in
    if Switches.(has_switch (SW_pointer_arith `PERMISSIVE)) then
      match ptrval1, ptrval2 with
        | PV (_, PVconcrete (_, addr1)), PV (_, PVconcrete (_, addr2)) ->
            valid_postcond addr1 addr2
        | _ ->
            error_postcond
    else match ptrval1, ptrval2 with
      | PV (Prov_some alloc_id1, PVconcrete (_, addr1)), PV (Prov_some alloc_id2, PVconcrete (_, addr2)) ->
          if N.equal alloc_id1 alloc_id2 then
            get_allocation ~loc alloc_id1 >>= fun alloc ->
            if precond alloc addr1 addr2 then
              valid_postcond addr1 addr2
            else
              error_postcond
          else
            error_postcond
      
      (* PNVI-ae-udi *)
      | PV (Prov_symbolic iota, PVconcrete (_, addr1)), PV (Prov_some alloc_id', PVconcrete (_, addr2))
      | PV (Prov_some alloc_id', PVconcrete (_, addr1)), PV (Prov_symbolic iota, PVconcrete (_, addr2)) ->
          (* if A(iota) = {i1, i2} then
               alloc_id' = (i1 or i2) AND precond valid AND iota collapses
             else
               UB *)
          lookup_iota iota >>= begin function
            | `Single alloc_id ->
                if N.equal alloc_id alloc_id' then
                  get_allocation ~loc alloc_id >>= fun alloc ->
                  if precond alloc addr1 addr2 then
                    valid_postcond addr1 addr2
                  else
                    error_postcond
                else
                  error_postcond
            | `Double (alloc_id1, alloc_id2) ->
                if N.equal alloc_id1 alloc_id' || N.equal alloc_id2 alloc_id' then
                  get_allocation ~loc alloc_id' >>= fun alloc ->
                  if precond alloc addr1 addr2 then
                    update begin fun st ->
                      {st with iota_map= IntMap.add iota (`Single alloc_id') st.iota_map }
                    end >>= fun () ->
                    valid_postcond addr1 addr2
                  else
                    error_postcond
                else
                  error_postcond
          end
      
      (* PNVI-ae-udi *)
      | PV (Prov_symbolic iota1, PVconcrete (_, addr1)), PV (Prov_symbolic iota2, PVconcrete (_, addr2)) ->
          (* IF A(iota1) INTER A(iota2) = { i } AND precond valid THEN collapse iota1 and iota2 to i *)
          (* IF A(iota1) INTER A(iota2) = { i1, i2 } AND (precond valid for i1 AND i2) THEN NO collapse *)
          lookup_iota iota1 >>= fun ids1 ->
          lookup_iota iota2 >>= fun ids2 ->
          let inter_ids =
            match ids1, ids2 with
              | `Single x, `Single y ->
                  if N.equal x y then
                    `Single x
                  else
                    `None
              | `Single x, `Double (y, z)
              | `Double (y, z), `Single x ->
                  if N.equal x y || N.equal x z then
                    `Single x
                  else
                    `None
              | `Double (x1, x2), `Double (y1, y2) ->
                  if N.equal x1 y1 then
                    if N.equal x2 y2 then
                      `Double (x1, x2)
                    else
                      `Single x1
                  else if N.equal x2 y2 then
                    `Single x2
                  else
                    `None in
          begin match inter_ids with
            | `None ->
                error_postcond
            | `Single alloc_id' ->
                update begin fun st ->
                  {st with iota_map= IntMap.add iota1 (`Single alloc_id')
                                       (IntMap.add iota2 (`Single alloc_id') st.iota_map) }
                end >>= fun () ->
                valid_postcond addr1 addr2
            | `Double (alloc_id1, alloc_id2) ->
                if N.equal addr1 addr2 then
                  valid_postcond addr1 addr2 (* zero *)
                else
                  fail ~loc (MerrOther "in `diff_ptrval` invariant of PNVI-ae-udi failed: ambiguous iotas with addr1 <> addr2")
          end
      | _ ->
          error_postcond
  
  let isWellAligned_ptrval ref_ty ptrval =
    (* TODO: catch builtin function types *)
    match unatomic_ ref_ty with
      | Void
      | Function _ ->
          fail (MerrOther "called isWellAligned_ptrval on void or a function type")
      | _ ->
          begin match ptrval with
            | PV (_, PVnull _) ->
                return true
            | PV (_, PVfunction _) ->
                fail (MerrOther "called isWellAligned_ptrval on function pointer")
            | PV (_, PVconcrete (_, addr)) ->
(*
                Printf.printf "addr: %s\n" (Nat_big_num.to_string addr);
                Printf.printf "align: %d\n" (alignof ref_ty);
*)
                return (N.(equal (modulus addr (of_int (alignof ref_ty))) zero))
          end
  
  (* Following §6.5.3.3, footnote 102) *)
  let validForDeref_ptrval ref_ty ptrval =
(*
    begin
      Printf.printf "validForDeref: ref_ty= %s, ptrval= %s\n"
        (String_core_ctype.string_of_ctype ref_ty)
        (Pp_utils.to_plain_string (pp_pointer_value ptrval))
    end;
*)
    let do_test alloc_id =
      is_dead alloc_id >>= function
        | true ->
            return false
        | false ->
            isWellAligned_ptrval ref_ty ptrval in
    match ptrval with
      | PV (_, PVnull _)
      | PV (_, PVfunction _) ->
          return false
      | PV (Prov_device, PVconcrete _) as ptrval ->
          isWellAligned_ptrval ref_ty ptrval
      
      (* PNVI-ae-udi *)
      | PV (Prov_symbolic iota, PVconcrete (_, addr)) ->
          lookup_iota iota >>= begin function
            | `Single alloc_id ->
                do_test alloc_id
            | `Double (alloc_id1, alloc_id2) ->
                do_test alloc_id1 >>= begin function
                  | false ->
                      do_test alloc_id2
                  | true ->
                      return true
                end
          end
      | PV (Prov_some alloc_id, PVconcrete _) ->
          do_test alloc_id
      | PV (Prov_none, _) ->
          return false

  
  let ptrfromint loc _ ref_ty (IV (prov, n)) =
    if not (N.equal n N.zero) then
      (* STD §6.3.2.3#5 *)
      Cerb_debug.warn [] (fun () ->
        "implementation defined cast from integer to pointer"
      );
    let n =
      let (min, max) = match (Ocaml_implementation.get ()).sizeof_pointer with
        | Some sz ->
            let open Nat_big_num in
            (of_int 0, sub (pow_int (of_int 2) (8*sz)) (of_int 1))
        | None ->
            failwith "the concrete memory model requires a complete implementation sizeof POINTER" in
      (* wrapI *)
      let dlt = N.succ (N.sub max min) in
      let r = N.integerRem_f n dlt in
      if N.less_equal r max then
        r
      else
        N.sub r dlt in
    if is_PNVI () then
      (* TODO: device memory? *)
      if N.equal n N.zero then
        return (PV (Prov_none, PVnull ref_ty))
      else
        get >>= fun st ->
        begin match find_overlaping st n with
          | `NoAlloc ->
              return Prov_none
          | `SingleAlloc alloc_id ->
              return (Prov_some alloc_id)
          | `DoubleAlloc alloc_ids ->
              add_iota alloc_ids >>= fun iota ->
              return (Prov_symbolic iota)
        end >>= fun prov ->
        return (PV (prov, PVconcrete (None, n)))
    else
      match prov with
        | Prov_none ->
            (* TODO: check (in particular is that ok to only allow device pointers when there is no provenance? *)
            if List.exists (fun (min, max) -> N.less_equal min n && N.less_equal n max) device_ranges then
              return (PV (Prov_device, PVconcrete (None, n)))
            else if N.equal n N.zero then
              return (PV (Prov_none, PVnull ref_ty))
            else
              return (PV (Prov_none, PVconcrete (None, n)))
        | _ ->
            return (PV (prov, PVconcrete (None, n)))
  
  let derive_cap _ _ _ _ : integer_value =
    assert false (* CHERI only *)
  
  let cap_assign_value _ _ _ : integer_value =
    assert false (* CHERI only *)
  
  let ptr_t_int_value _ =
    assert false (* CHERI only *)
  
  let null_cap _ : integer_value =
    assert false (* CHERI only *)

  let get_intrinsic_type_spec _ =
    assert false (* CHERI only *)

  let call_intrinsic _ _ _ =
    assert false (* CHERI only *)

  let offsetof_ival tagDefs tag_sym memb_ident =
    let (xs, _) = offsetsof tagDefs tag_sym in
    let pred (ident, _, _) =
      ident_equal ident memb_ident in
    match List.find_opt pred xs with
      | Some (_, _, offset) ->
          IV (Prov_none, offset)
      | None ->
          failwith "Concrete.offsetof_ival: invalid memb_ident"
  
  let array_shift_ptrval (PV (prov, ptrval_)) ty (IV (_, ival)) =
    (* As a GNU extension ty may be void, in which case the pointer arithmetic
       is performed at the byte granularity *)
    let sz = if AilTypesAux.is_void ty then Z.one else sizeof ty in
    let offset = (Nat_big_num.(mul sz ival)) in
    match prov with
      (* PNVI-ae-udi *)
      | Prov_symbolic iota ->
          failwith "Concrete.array_shift_ptrval found a Prov_symbolic"
      | _ ->
          PV (prov, match ptrval_ with
          | PVnull _ ->
              (* TODO: this seems to be undefined in ISO C *)
              (* NOTE: in C++, if offset = 0, this is defined and returns a PVnull *)
              failwith ("TODO(pure shift a null pointer should be undefined behaviour), offset:" ^ Nat_big_num.to_string offset)
          | PVfunction _ ->
              failwith "Concrete.array_shift_ptrval, PVfunction"
          | PVconcrete (membr_opt, addr) ->
              PVconcrete (membr_opt, N.add addr offset))
  
  let member_shift_ptrval (PV (prov, ptrval_)) tag_sym memb_ident =
    let IV (_, offset) = offsetof_ival (Tags.tagDefs ()) tag_sym memb_ident in
    let membr_opt =
      match Pmap.lookup tag_sym (Tags.tagDefs ()) with
        | Some (_, UnionDef _) ->
            Some memb_ident
        | _ ->
            None in
    PV (prov, match ptrval_ with
      | PVnull ty ->
          (* TODO: unsure, this might just be undefined (gcc-torture assumes the
             following behaviour though) *)
          if N.equal N.zero offset then
            PVnull ty
          else
            PVconcrete (membr_opt, offset)
      | PVfunction _ ->
          failwith "Concrete.member_shift_ptrval, PVfunction"
      | PVconcrete (_, addr) ->
          PVconcrete (membr_opt, N.add addr offset))
  
  let eff_array_shift_ptrval loc ptrval ty (IV (_, ival)) =
    (* KKK print_endline ("HELLO eff_array_shift_ptrval ==> " ^ Pp_utils.to_plain_string (pp_pointer_value ptrval)); *)
    let offset = (Nat_big_num.(mul (sizeof ty) ival)) in
    match ptrval with
      | PV (_, PVnull _) ->
          (* TODO: this seems to be undefined in ISO C *)
          (* NOTE: in C++, if offset = 0, this is defined and returns a PVnull *)
          (* failwith ("TODO(eff shift a null pointer should be undefined behaviour), offset:" ^ Nat_big_num.to_string offset) *)
          fail ~loc MerrArrayShift
      | PV (_, PVfunction _) ->
          failwith "Concrete.eff_array_shift_ptrval, PVfunction"
      
      (* PNVI-ae-udi *)
      | PV (Prov_symbolic iota as prov, PVconcrete (_, addr)) ->
          (* KKK print_endline ("HELLO iota ==> " ^ Pp_utils.to_plain_string (pp_pointer_value ptrval)); *)
          (* TODO: this is duplicated code from the Prov_some case (I'm keeping
             PNVI-ae-udi stuff separated to avoid polluting the
             vanilla PNVI code) *)
          let shifted_addr = N.add addr offset in
          let precond z =
            (* TODO: is it correct to use the "ty" as the lvalue_ty? *)
            if    Switches.(has_switch (SW_pointer_arith `STRICT))
               || (is_PNVI () && not (Switches.(has_switch (SW_pointer_arith `PERMISSIVE)))) then
              get_allocation ~loc z >>= fun alloc ->
              if    N.less_equal alloc.base shifted_addr
                 && N.less_equal (N.add shifted_addr (sizeof ty))
                                 (N.add (N.add alloc.base alloc.size) (sizeof ty)) then
                return true
              else
                return false
            else
              return true in
          lookup_iota iota >>= begin function
            | `Double (alloc_id1, alloc_id2) ->
                if not (N.equal ival N.zero) then
                  (* TODO: this is yucky *)
                  precond alloc_id1 >>= begin function
                    | true ->
                        precond alloc_id2 >>= begin function
                          | true ->
                              if Switches.(has_switch (SW_pointer_arith `PERMISSIVE)) then
                                return `NoCollapse
                              else begin
                                Printf.printf "id1= %s, id2= %s ==> addr= %s\n"
                                  (N.to_string alloc_id1) (N.to_string alloc_id2)
                                  (N.to_string shifted_addr);
                                fail ~loc (MerrOther "(PNVI-ae-uid) ambiguous non-zero array shift")
                              end
                          | false ->
                              return (`Collapse alloc_id1)
                        end
                    | false ->
                        precond alloc_id2 >>= begin function
                          | true ->
                              return (`Collapse alloc_id2)
                          | false ->
                              fail ~loc MerrArrayShift
                        end
                  end >>= begin function
                    | `Collapse alloc_id ->
                        update begin fun st ->
                          {st with iota_map= IntMap.add iota (`Single alloc_id) st.iota_map }
                        end
                    | `NoCollapse ->
                        return ()
                  end >>= fun () ->
                  return (PV (prov, PVconcrete (None, shifted_addr)))
                else
                  (* TODO: this is yucky *)
                  precond alloc_id1 >>= begin function
                    | true ->
                        return ()
                    | false ->
                        precond alloc_id2 >>= begin function
                          | true ->
                              return ()
                          | false ->
                              fail ~loc MerrArrayShift
                        end
                  end >>= fun () ->
                  return (PV (prov, PVconcrete (None, shifted_addr)))
            | `Single alloc_id ->
                precond alloc_id >>= begin function
                  | true ->
                      return (PV (prov, PVconcrete (None, shifted_addr)))
                  | false ->
                      fail ~loc MerrArrayShift
                end
          end
      
      | PV (Prov_some alloc_id, PVconcrete (_, addr)) ->
          (* TODO: is it correct to use the "ty" as the lvalue_ty? *)
          let shifted_addr = N.add addr offset in
          if    Switches.(has_switch (SW_pointer_arith `STRICT))
             || (is_PNVI () && not (Switches.(has_switch (SW_pointer_arith `PERMISSIVE)))) then
            get_allocation ~loc alloc_id >>= fun alloc ->
            if    N.less_equal alloc.base shifted_addr
               && N.less_equal (N.add shifted_addr (sizeof ty))
                               (N.add (N.add alloc.base alloc.size) (sizeof ty)) then
              return (PV (Prov_some alloc_id, PVconcrete (None, shifted_addr)))
            else
              fail ~loc MerrArrayShift
          else
            return (PV (Prov_some alloc_id, PVconcrete (None, shifted_addr)))
      | PV (Prov_none, PVconcrete (_, addr)) ->
          if    Switches.(has_switch (SW_pointer_arith `STRICT))
             || (is_PNVI () && not (Switches.(has_switch (SW_pointer_arith `PERMISSIVE)))) then
            fail ~loc (MerrOther "out-of-bound pointer arithmetic (Prov_none)")
          else
            return (PV (Prov_none, PVconcrete (None, N.add addr offset)))
      | PV (Prov_device, PVconcrete (_, addr)) ->
          (* TODO: check *)
          return (PV (Prov_device, PVconcrete (None, N.add addr offset)))

let eff_member_shift_ptrval _ tag_sym membr_ident ptrval =
  return (member_shift_ptrval tag_sym membr_ident ptrval)

  let concurRead_ival ity sym =
    failwith "TODO: concurRead_ival"
  
  let integer_ival n =
    IV (Prov_none, n)
  
  let max_ival ity =
    let open Nat_big_num in
    let ity = match ity with
      | Enum nm -> (Ocaml_implementation.get ()).typeof_enum nm
      | _ -> ity
    in
    IV (Prov_none, begin match (Ocaml_implementation.get ()).sizeof_ity ity with
      | Some n ->
          let signed_max =
            sub (pow_int (of_int 2) (8*n-1)) (of_int 1) in
          let unsigned_max =
            sub (pow_int (of_int 2) (8*n)) (of_int 1) in
          begin match ity with
            | Char ->
                if (Ocaml_implementation.get ()).is_signed_ity Char then
                  signed_max
                else
                  unsigned_max
            | Bool ->
                (* TODO: not sure about this (maybe it should be 1 and not 255? *)
                unsigned_max
            | Size_t
            | Wchar_t (* TODO: it is implementation defined if unsigned *)
            | Unsigned _ ->
                unsigned_max
            | Ptrdiff_t
            | Wint_t (* TODO *)
            | Signed _ ->
                signed_max
            | Ptraddr_t ->
                unsigned_max
            | Enum _ ->
                assert false (* handled above *)
          end
      | None ->
          failwith "the concrete memory model requires a complete implementation MAX"
    end)
  
  let min_ival ity =
    let open Nat_big_num in
    let ity = match ity with
      | Enum nm -> (Ocaml_implementation.get ()).typeof_enum nm
      | _ -> ity
    in
    IV (Prov_none, begin match ity with
      | Char ->
          if (Ocaml_implementation.get ()).is_signed_ity Char then
            negate (pow_int (of_int 2) (8-1))
          else
            zero
      | Bool
      | Size_t
      | Wchar_t (* TODO: it is implementation defined if unsigned *)
      | Wint_t
      | Unsigned _ ->
          (* all of these are unsigned *)
          zero
      | Ptrdiff_t
      | Signed _ ->
          (* and all of these are signed *)
          begin match (Ocaml_implementation.get ()).sizeof_ity ity with
            | Some n ->
                negate (pow_int (of_int 2) (8*n-1))
            | None ->
                failwith "the concrete memory model requires a complete implementation MIN"
          end
      | Ptraddr_t -> zero
      | Enum _ ->
          assert false (* handled above *)
    end)
  
  (* TODO: conversion? *)
  let intfromptr loc _ ity (PV (prov, ptrval_)) =
    match ptrval_ with
      | PVnull _ ->
          return (mk_ival prov Nat_big_num.zero)
      | PVfunction (Symbol.Symbol (_, n, _)) ->
          return (mk_ival prov (Nat_big_num.of_int n))
      | PVconcrete (_, addr) ->
          begin if Switches.(has_switch (SW_PNVI `AE) || has_switch (SW_PNVI `AE_UDI)) then
            (* PNVI-ae, PNVI-ae-udi *)
            match prov with
              | Prov_some alloc_id ->
                  expose_allocation alloc_id
              | _ ->
                  return ()
          else
            return ()
          end >>= fun () ->
          let IV (_, ity_max) = max_ival ity in
          let IV (_, ity_min) = min_ival ity in
          if N.(less addr ity_min || less ity_max addr) then
            fail ~loc MerrIntFromPtr
          else
            return (mk_ival prov addr)


  let op_ival iop (IV (prov1, n1)) (IV (prov2, n2)) =
    (* NOTE: for PNVI we assume that prov1 = prov2 = Prov_none *)
    match iop with
      | IntAdd ->
          IV (combine_prov prov1 prov2, Nat_big_num.add n1 n2)
      | IntSub ->
          let prov' = match prov1, prov2 with
            | Prov_some _, Prov_some _
            | Prov_none, _ ->
                Prov_none
            | _ ->
                prov1 in
          IV (prov', Nat_big_num.sub n1 n2)
      | IntMul ->
          IV (combine_prov prov1 prov2, Nat_big_num.mul n1 n2)
      | IntDiv ->
          IV (combine_prov prov1 prov2, Nat_big_num.(if equal n2 zero then zero else integerDiv_t n1 n2))
      | IntRem_t ->
          IV (combine_prov prov1 prov2, Nat_big_num.integerRem_t n1 n2)
      | IntRem_f ->
          IV (combine_prov prov1 prov2, Nat_big_num.integerRem_f n1 n2)
      | IntExp ->
          (* NOTE: this operation doesn't exists in C, but is used in the elaboration of the
             shift operators. And for these we want the provenance of the left operand to be
             the one that is forwarded *)
          (* TODO: fail properly when y is too big? *)
          IV (Prov_none, Nat_big_num.pow_int n1 (Nat_big_num.to_int n2))
  
  let sizeof_ival ty =
    IV (Prov_none, sizeof ty)
  let alignof_ival ty =
    IV (Prov_none, Nat_big_num.of_int (alignof ty))
  
  let bitwise_complement_ival _ (IV (prov, n)) =
    (* NOTE: for PNVI we assume that prov = Prov_none *)
    (* TODO *)
    (* prerr_endline "Concrete.bitwise_complement ==> HACK"; *)
    IV (prov, Nat_big_num.(sub (negate n) (of_int 1)))

  let bitwise_and_ival _ (IV (prov1, n1)) (IV (prov2, n2)) =
    (* NOTE: for PNVI we assume that prov1 = prov2 = Prov_none *)
    IV (combine_prov prov1 prov2, Nat_big_num.bitwise_and n1 n2)
  let bitwise_or_ival _ (IV (prov1, n1)) (IV (prov2, n2)) =
    (* NOTE: for PNVI we assume that prov1 = prov2 = Prov_none *)
    IV (combine_prov prov1 prov2, Nat_big_num.bitwise_or n1 n2)
  let bitwise_xor_ival _ (IV (prov1, n1)) (IV (prov2, n2)) =
    (* NOTE: for PNVI we assume that prov1 = prov2 = Prov_none *)
    IV (combine_prov prov1 prov2, Nat_big_num.bitwise_xor n1 n2)
  
  let case_integer_value (IV (_, n)) f_concrete _ =
    f_concrete n
  
  let is_specified_ival ival =
    true
  
  let zero_fval =
    0.0
  let one_fval =
    1.0
  let str_fval str =
    float_of_string str
  
  let case_fval fval _ fconcrete =
    fconcrete fval
  
  let op_fval fop fval1 fval2 =
    match fop with
      | FloatAdd ->
          fval1 +. fval2
      | FloatSub ->
          fval1 -. fval2
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
    (* NOTE: if n is too big, the float will be truncated *)
    float_of_string (N.to_string n)
  
  let ivfromfloat _ fval =
    IV (Prov_none, N.of_float fval)
  
  let eq_ival (IV (_, n1)) (IV (_, n2)) =
    Some (Nat_big_num.equal n1 n2)
  let lt_ival (IV (_, n1)) (IV (_, n2)) =
    Some (Nat_big_num.compare n1 n2 = -1)
  let le_ival (IV (_, n1)) (IV (_, n2)) =
    let cmp = Nat_big_num.compare n1 n2 in
    Some (cmp = -1 || cmp = 0)
  
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
  
  


  let pp_pretty_pointer_value = pp_pointer_value ~is_verbose:false
  
  (*
  TODO: Hack we are printing the concrete's pointer_value_base as VIP pointer_value.

Concrete: type pointer_value_base =
    | PVnull of ctype
    | PVfunction of Symbol.sym
    | PVconcrete of Symbol.identifier option(* set if pointing to member of a union *) * Nat_big_num.num


VIP:type pointer_value =
  | PVnull
  | PVloc of location
  | PVfunptr of Symbol.sym

  *)
  let pp_pointer_value_for_coq pp_symbol (PV (_,pvb)) = 
    match pvb with
    | PVnull _ -> !^"Mem.PVnull"
    | PVconcrete (_, addr) -> !^"(Mem.PVloc" 
        ^^^ !^"(" 
        ^^^ !^"Mem.Prov_empty"  (* TODO: provenance place holder *)
        ^^^ !^", " 
        ^^^ pp_address_for_coq addr 
        ^^^ !^")" 
        ^^^ !^")"
    | PVfunction sym -> !^"(Mem.PVfunptr" ^^^ pp_symbol sym ^^ !^")"

   let pp_pretty_integer_value ?basis ~use_upper = pp_integer_value
  let pp_pretty_mem_value ?basis ~use_upper = pp_mem_value
  
  (* TODO check *)
  let memcpy loc ptrval1 ptrval2 (IV (_, size_n)) =
    (* TODO: if ptrval1 and ptrval2 overlap ==> UB *)
    (* TODO: copy ptrval2 into ptrval1 *)
    let rec aux i =
      if Nat_big_num.less i size_n then
        load loc Ctype.unsigned_char (array_shift_ptrval ptrval2 Ctype.unsigned_char (IV (Prov_none, i))) >>= fun (_, mval) ->
        store loc Ctype.unsigned_char false (array_shift_ptrval ptrval1 Ctype.unsigned_char (IV (Prov_none, i))) mval >>= fun _ ->
        aux (Nat_big_num.succ i)
      else
        return ptrval1 in
    aux Nat_big_num.zero
  
  
  (* TODO: validate more, but looks good *)
  let memcmp ptrval1 ptrval2 (IV (_, size_n)) =
    let rec get_bytes ptrval acc = function
      | 0 ->
          return (List.rev acc)
      | size ->
          load Cerb_location.unknown Ctype.unsigned_char ptrval >>= function
            | (_, MVinteger (_, (IV (byte_prov, byte_n)))) ->
                let ptr' = array_shift_ptrval ptrval Ctype.unsigned_char (IV (Prov_none, Nat_big_num.(succ zero))) in
                get_bytes ptr' (byte_n :: acc) (size-1)
            | _ ->
                assert false in
     get_bytes ptrval1 [] (Nat_big_num.to_int size_n) >>= fun bytes1 ->
     get_bytes ptrval2 [] (Nat_big_num.to_int size_n) >>= fun bytes2 ->
     
     let open Nat_big_num in
     return (IV (Prov_none, List.fold_left (fun acc (n1, n2) ->
                   if equal acc zero then of_int (Nat_big_num.compare n1 n2) else acc
                 ) zero (List.combine bytes1 bytes2)))

  let realloc loc tid align ptr size : pointer_value memM =
    match ptr with
    | PV (Prov_none, PVnull _) ->
      allocate_region tid (Symbol.PrefOther "realloc") align size
    | PV (Prov_none, _) ->
      fail ~loc (MerrWIP "realloc no provenance")
    | PV (Prov_some alloc_id, PVconcrete (_, addr)) ->
      is_dynamic addr >>= begin function
        | false ->
            fail ~loc (MerrUndefinedRealloc Free_non_matching)
        | true ->
           is_dead alloc_id >>= (function
            | true ->
                fail ~loc (MerrUndefinedRealloc Free_dead_allocation)
            | false ->
                get_allocation ~loc:(Cerb_location.other "Concrete.realloc") alloc_id >>= fun alloc ->
                if alloc.base = addr then
                  allocate_region tid (Symbol.PrefOther "realloc") align size >>= fun new_ptr ->
                  let size_to_copy =
                    let IV (_, size_n) = size in
                    IV (Prov_none, Nat_big_num.min alloc.size size_n) in
                  memcpy loc new_ptr ptr size_to_copy >>= fun _ ->
                  kill (Cerb_location.other "realloc") true ptr >>= fun () ->
                  return new_ptr
                else
                  fail ~loc (MerrWIP "realloc: invalid pointer"))
      end
    | PV _ ->
        fail ~loc (MerrWIP "realloc: invalid pointer")

  let va_start args =
    get >>= fun st ->
    let id = st.next_varargs_id in
    update (fun st -> { st with varargs = IntMap.add id (0, args) st.varargs;
                                next_varargs_id = N.succ st.next_varargs_id;
                      } ) >>= fun _ ->
    return (IV (Prov_none, id))

  let va_copy va =
    match va with
    | IV (Prov_none, id) ->
      get >>= fun st ->
      begin match IntMap.find_opt id st.varargs with
        | Some args ->
          let id = st.next_varargs_id in
          update (fun st -> { st with varargs = IntMap.add id args st.varargs;
                                      next_varargs_id = N.succ st.next_varargs_id;
                            } ) >>= fun _ ->
          return (IV (Prov_none, id))
        | None ->
            fail (MerrWIP "va_copy: not initiliased")
      end
    | _ ->
      fail (MerrWIP "va_copy: invalid va_list")

  let va_arg va ty =
    match va with
    | IV (Prov_none, id) ->
      get >>= fun st ->
      begin match IntMap.find_opt id st.varargs with
        | Some (i, args) ->
          begin match List.nth_opt args i with
            | Some (_, ptr) -> (* TODO: check type is compatible *)
              update (fun st -> { st with varargs = IntMap.add id (i+1, args) st.varargs })
              >>= fun _ ->
              return ptr
            | None ->
              fail (MerrWIP "va_arg: invalid number of arguments")
          end
        | None ->
            fail (MerrWIP "va_arg: not initiliased")
      end
    | _ ->
      fail (MerrWIP "va_arg: invalid va_list")

  let va_end va =
    match va with
    | IV (Prov_none, id) ->
      get >>= fun st ->
      begin match IntMap.find_opt id st.varargs with
        | Some _ ->
          update (fun st -> { st with varargs = IntMap.remove id st.varargs })
        | None ->
            fail (MerrWIP "va_end: not initiliased")
      end
    | _ ->
      fail (MerrWIP "va_end: invalid va_list")

  let va_list va_idx =
    get >>= fun st ->
    begin match IntMap.find_opt va_idx st.varargs with
      | Some (n, args) ->
          assert (n = 0); (* not sure what happens with n <> 0 *)
          return args
      | None ->
          fail (MerrWIP "va_list")
    end

  let copy_alloc_id ival ptrval =
    (* cast_ptrval_to_ival(uintptr_t,𝑝1),cast_ival_to_ptrval(void,𝑥) *)
    (* the first ctype is the original referenced type, the integerType is the target integer type *)
    intfromptr (Cerb_location.other "copy_alloc_id") Ctype.void Ctype.(Unsigned Intptr_t) ptrval >>= fun _ ->
    ptrfromint (Cerb_location.other "copy_alloc_id") Ctype.(Unsigned Intptr_t) Ctype.void ival

  (* Bytes are always typedef'd to unsigned chars, and I'm assuming unsigned
     chars are always 8 bits. This function flips the interpretation of the
     leading bit if it is 1. *)
  let bytefromint loc (IV (_, intval) as ival) =
    assert (N.(less_equal (of_int 0) intval && less_equal intval (of_int 255)));
    ival

  let intfrombyte _loc (IV (_, intval) as ival) =
    assert (N.(less_equal (of_int 0) intval && less_equal intval (of_int 255)));
    ival

  (* JSON serialisation: Memory layout for UI *)

  type ui_value =
    { kind: [ `Unspec | `Basic | `Char | `Pointer | `Unspecptr
            | `Funptr | `Intptr | `Padding ];
      size: int; (* number of square on the left size of the row *)
      path: string list; (* tag list *)
      value: string;
      prov: provenance;
      bytes: AbsByte.t list option;
      typ: ctype option;
    }

  type ui_alloc =
    { id: int;
      base: string;
      prefix: Symbol.prefix;
      dyn: bool; (* dynamic memory *)
      typ: ctype;
      size: int;
      values: ui_value list;
      exposed: bool;
    }

  let rec mk_ui_values st bs ty mval : ui_value list =
    let mk_ui_values = mk_ui_values st in
    let mk_scalar kind v p bs_opt =
      (* TODO: the N.to_int on the sizeof() will raise Overflow on huge objects *)
      [{ kind; size = N.to_int (sizeof ty); path = []; value = v;
         prov = p; typ = Some ty; bytes = bs_opt }] in
    let mk_pad n v =
      { kind = `Padding; size = n; typ = None; path = []; value = v;
        prov = Prov_none; bytes = None } in
    let add_path p r = { r with path = p :: r.path } in
    match mval with
    | MVunspecified (Ctype (_, Pointer _)) ->
      mk_scalar `Unspecptr "unspecified" Prov_none (Some bs)
    | MVunspecified _ ->
      mk_scalar `Unspec "unspecified" Prov_none (Some bs)
    | MVinteger (cty, IV(prov, n)) ->
      begin match cty with
        | Char | Signed Ichar | Unsigned Ichar ->
          mk_scalar `Char (N.to_string n) prov None
        | Ptrdiff_t | Signed Intptr_t | Unsigned Intptr_t ->
          mk_scalar `Intptr (N.to_string n) prov None
        | _ ->
          mk_scalar `Basic (N.to_string n) prov None
      end
    | MVfloating (_, f) ->
      mk_scalar `Basic (string_of_float f) Prov_none None
    | MVpointer (_, PV(prov, pv)) ->
      begin match pv with
        | PVnull _ ->
          mk_scalar `Pointer "NULL" Prov_none None
        | PVconcrete (_, n) ->
          mk_scalar `Pointer (N.to_string n) prov (Some bs)
        | PVfunction sym ->
          mk_scalar `Funptr (Pp_symbol.to_string_pretty sym) Prov_none None
      end
    | MVarray mvals ->
      begin match ty with
        | Ctype (_, Array (elem_ty, _)) ->
          (* TODO: the N.to_int on the sizeof() will raise Overflow on huge structs/unions *)
          let size = N.to_int (sizeof elem_ty) in
          let (rev_rows, _, _) = List.fold_left begin fun (acc, i, acc_bs) mval ->
              let row = List.map (add_path (string_of_int i)) @@ mk_ui_values acc_bs elem_ty mval in
              (row::acc, i+1, L.drop size acc_bs)
            end ([], 0, bs) mvals
          in List.concat @@ (List.rev rev_rows)
        | _ ->
          failwith "mk_ui_values: array type is wrong"
      end
    | MVstruct (tag_sym, _) ->
      let open N in
      (* NOTE: we recombine the bytes to get paddings *)
      (* TODO: the N.to_int on the sizeof() will raise Overflow on huge structs *)
      let (bs1, bs2) = L.split_at (N.to_int (sizeof ty)) bs in
          let (rev_rowss, _, bs') = List.fold_left begin
          fun (acc_rowss, previous_offset, acc_bs) (Symbol.Identifier (_, memb), memb_ty, memb_offset) ->
            let pad = to_int (sub memb_offset previous_offset) in
            let acc_bs' = L.drop pad acc_bs in
            let (_, mval, acc_bs'') = abst (find_overlaping st) ~addr:N.zero(*TODO!!!!*) st.last_used_union_members st.funptrmap memb_ty acc_bs' in
            let rows = mk_ui_values acc_bs' memb_ty mval in
            let rows' = List.map (add_path memb) rows in
            (* TODO: set padding value here *)
            let rows'' = if pad = 0 then rows' else mk_pad pad "" :: rows' in
            (rows''::acc_rowss, N.add memb_offset (sizeof memb_ty), acc_bs'')
        end ([], N.zero, bs1) (fst (offsetsof (Tags.tagDefs ()) tag_sym))
      in List.concat (List.rev rev_rowss)
    | MVunion (tag_sym, Symbol.Identifier (_, memb), mval) ->
      List.map (add_path memb) (mk_ui_values bs ty mval) (* FIXME: THE TYPE IS WRONG *)

  let mk_ui_alloc st id alloc : ui_alloc =
    let ty = match alloc.ty with Some ty -> ty | None -> Ctype ([], Array (Ctype ([], Basic (Integer Char)), Some alloc.size)) in
    let size = N.to_int alloc.size in
    let bs = fetch_bytes st.bytemap alloc.base size in
    let (_, mval, _) = abst (find_overlaping st) ~addr:alloc.base st.last_used_union_members st.funptrmap ty bs in
    { id = id;
      base = N.to_string alloc.base;
      prefix = alloc.prefix;
      dyn = List.mem alloc.base st.dynamic_addrs;
      typ = ty;
      size = size;
      values = mk_ui_values st bs ty mval;
      exposed = (alloc.taint = `Exposed);
    }

  let serialise_prefix = function
    | Symbol.PrefOther s ->
      (* TODO: this should not be possible anymore *)
      `Assoc [("kind", `String "other"); ("name", `String s)]
    | Symbol.PrefMalloc ->
      `Assoc [("kind", `String "malloc");
              ("scope", `Null);
              ("name", `String "malloc'd");
              ("loc", `Null)]
    | Symbol.PrefStringLiteral (loc, _) ->
      `Assoc [("kind", `String "string literal");
              ("scope", `Null);
              ("name", `String "literal");
              ("loc", Cerb_location.to_json loc)]
    | Symbol.PrefTemporaryLifetime (loc, _) ->
      `Assoc [("kind", `String "rvalue temporary");
              ("scope", `Null);
              ("name", `String "temporary");
              ("loc", Cerb_location.to_json loc)]
    | Symbol.PrefCompoundLiteral (loc, _) ->
      `Assoc [("kind", `String "compound literal");
              ("scope", `Null);
              ("name", `String "literal");
              ("loc", Cerb_location.to_json loc)]
    | Symbol.PrefFunArg (loc, _, n) ->
      `Assoc [("kind", `String "arg");
              ("scope", `Null);
              ("name", `String ("arg" ^ string_of_int n));
              ("loc", Cerb_location.to_json loc)]
    | Symbol.PrefSource (_, []) ->
      failwith "serialise_prefix: PrefSource with an empty list"
    | Symbol.PrefSource (loc, [name]) ->
        `Assoc [("kind", `String "source");
                ("name", `String (Pp_symbol.to_string_pretty name));
                ("scope", `Null);
                ("loc", Cerb_location.to_json loc);]
    | Symbol.PrefSource (loc, [scope; name]) ->
        `Assoc [("kind", `String "source");
                ("name", `String (Pp_symbol.to_string_pretty name));
                ("scope", `String (Pp_symbol.to_string_pretty scope));
                ("loc", Cerb_location.to_json loc);]
    | Symbol.PrefSource (_, _) ->
      failwith "serialise_prefix: PrefSource with more than one scope"

  let serialise_prov st = function
    | Prov_some n ->
      `Assoc [("kind", `String "prov");
              ("value", `Int (N.to_int n))]
    | Prov_symbolic i ->
      `Assoc [("kind", `String "iota");
              ("value", `Int (N.to_int i));
              ("iota", match IntMap.find_opt i st.iota_map with
                | None ->
                  `Null (* it should be impossible *)
                | Some (`Single n) ->
                  `List [`Int (N.to_int n)]
                | Some (`Double (n1, n2)) ->
                  `List [`Int (N.to_int n1);
                         `Int (N.to_int n2)])]
    | _ ->
      `Assoc [("kind", `String "empty")]

  let serialise_map f m : Cerb_json.json =
    let serialise_entry (k, v) = (N.to_string k, f (N.to_int k) v)
    in `Assoc (List.map serialise_entry (IntMap.bindings m))

  let serialise_ui_values st (v:ui_value) : Cerb_json.json =
    let string_of_kind = function
      | `Unspec -> "unspecified"
      | `Basic -> "basic"
      | `Pointer -> "pointer"
      | `Funptr -> "funptr"
      | `Intptr -> "intptr"
      | `Unspecptr -> "unspecptr"
      | `Char -> "char"
      | `Padding -> "padding"
    in
    `Assoc [("kind"), `String (string_of_kind v.kind);
            ("size", `Int v.size);
            ("path", `List (List.map Cerb_json.of_string v.path));
            ("value", `String v.value);
            ("prov", serialise_prov st v.prov);
            ("type", Cerb_json.of_option (fun ty -> `String (String_core_ctype.string_of_ctype ty)) v.typ);
            ("bytes", Cerb_json.of_option (fun bs -> `List (List.map (AbsByte.to_json (serialise_prov st)) bs)) v.bytes); ]

  let serialise_ui_alloc st (a:ui_alloc) : Cerb_json.json =
    `Assoc [("id", `Int a.id);
            ("base", `String a.base);
            ("prefix", serialise_prefix a.prefix);
            ("dyn", `Bool a.dyn);
            ("type", `String (String_core_ctype.string_of_ctype a.typ));
            ("size", `Int a.size);
            ("values", `List (List.map (serialise_ui_values st) a.values));
            ("exposed", `Bool a.exposed);
           ]

  let serialise_mem_state dig (st: mem_state) : Cerb_json.json =
    let allocs = IntMap.filter (fun _ (alloc : allocation) ->
        match alloc.prefix with
        | Symbol.PrefSource (_, syms) -> List.exists (fun (Symbol.Symbol (hash, _, _)) -> hash = dig) syms
        | Symbol.PrefStringLiteral (_, hash) -> hash = dig
        | Symbol.PrefCompoundLiteral (_, hash) -> hash = dig
        | Symbol.PrefFunArg (_, hash, _) -> hash = dig
        | Symbol.PrefMalloc -> true
        | _ -> false
      ) st.allocations in
    `Assoc [("map", serialise_map (fun id alloc -> serialise_ui_alloc st @@ mk_ui_alloc st id alloc) allocs);
            ("last_used", Cerb_json.of_option (fun v -> `Int (N.to_int v)) st.last_used);]


end

include Concrete

let string_of_integer_value ival =
  Pp_utils.to_plain_string (pp_integer_value ival)

let string_of_mem_value mval =
  Pp_utils.to_plain_string begin
    (* TODO: factorise *)
    let saved = !Cerb_colour.do_colour in
    Cerb_colour.do_colour := false;
    let ret = pp_mem_value mval in
    Cerb_colour.do_colour := saved;
    ret
  end
