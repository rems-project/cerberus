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
    ('a, string, 'err, 'cs, 'st) Nondeterminism.ndM
  val return: 'a -> ('a, 'err, 'cs, 'st) eff
  val (>>=): ('a, 'err, 'cs, 'st) eff -> ('a -> ('b, 'err, 'cs, 'st) eff) -> ('b, 'err, 'cs, 'st) eff
(*  val (>>): ('a, 'err, 'cs, 'st) eff -> ('b, 'err, 'cs, 'st) eff -> ('b, 'err, 'cs, 'st) eff *)
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
  | Basic0 (Integer ity) as ty ->
      begin match Impl.sizeof_ity ity with
        | Some n ->
            n
        | None ->
            failwith ("the concrete memory model requires a complete implementation sizeof INTEGER => " ^ String_core_ctype.string_of_ctype ty)
      end
  | Basic0 (Floating fty) ->
      begin match Impl.sizeof_fty fty with
        | Some n ->
            n
        | None ->
            failwith "the concrete memory model requires a complete implementation sizeof FLOAT"
      end
  | Array0 (elem_ty, Some n) ->
      (* TODO: what if too big? *)
      Nat_big_num.to_int n * sizeof elem_ty
  | Pointer0 _ ->
      begin match Impl.sizeof_pointer with
        | Some n ->
            n
        | None ->
            failwith "the concrete memory model requires a complete implementation sizeof POINTER"
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
            (* NOTE: adding padding at the end to satisfy the alignment constraints *)
            let x = max_size mod max_align in
            if x = 0 then max_size else max_size + (max_align - x)
      end
  | Builtin0 str ->
     failwith ("TODO: sizeof Builtin ==> " ^ str)

and alignof = function
  | Void0 ->
      assert false
  | Basic0 (Integer ity) as ty ->
      begin match Impl.alignof_ity ity with
        | Some n ->
            n
        | None ->
            failwith ("the concrete memory model requires a complete implementation alignof INTEGER => " ^ String_core_ctype.string_of_ctype ty)
      end
  | Basic0 (Floating fty) ->
      begin match Impl.alignof_fty fty with
        | Some n ->
            n
        | None ->
            failwith "the concrete memory model requires a complete implementation alignof FLOATING"
      end
  | Array0 (elem_ty, _) ->
      alignof elem_ty
  | Function0 _ ->
      assert false
  | Pointer0 _ ->
      begin match Impl.alignof_pointer with
        | Some n ->
            n
        | None ->
            failwith "the concrete memory model requires a complete implementation alignof POINTER"
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
     failwith ("TODO: alignof Builtin ==> " ^ str)


module Concrete : Memory = struct
  let name = "I am the concrete memory model"

  type provenance =
    | Prov_none
    | Prov_some of Nat_big_num.num
    | Prov_device
    | Prov_wildcard
  
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
    | MVstruct of Symbol.sym (*struct/union tag*) * (Cabs.cabs_identifier (*member*) * Core_ctype.ctype0 * mem_value) list
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
    prefix: Symbol.prefix;
    base: address;
    size: N.num; (*TODO: this is probably unnecessary once we have the type *)
    ty: Core_ctype.ctype0 option; (* None when dynamically allocated *)
    is_readonly: bool;
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

    let to_json b =
      `Assoc [("prov", match b.prov with Prov_some n -> `Int (N.to_int n) | _ -> `Null);
              ("offset", Json.of_option Json.of_int b.copy_offset);
              ("value", Json.of_option Json.of_char b.value);]
    
    (* Given a (non-empty) list of bytes combine their provenance if their are
       compatible. Returns the empty provenance otherwise *)
    let split_bytes = function
      | [] ->
          failwith "Concrete.AbsByte.split_bytes: called on an empty list"
      | bs ->
          let (_prov, rev_values, offset_status) =
            List.fold_left (fun (prov_acc, val_acc, offset_acc) b ->
              let prov_acc' = match prov_acc, b.prov with
                | `VALID (Prov_some alloc_id1), Prov_some alloc_id2 when alloc_id1 <> alloc_id2 ->
                    `INVALID
                | `VALID Prov_none, (Prov_some _ as new_prov) ->
                    `VALID new_prov
                | prev_acc, _ ->
                    prev_acc in
              let offset_acc' = match offset_acc, b.copy_offset with
                | `PtrBytes n1, Some n2 when n1 = n2 ->
                    `PtrBytes (n1+1)
                | _ ->
                    `OtherBytes in
              (prov_acc', b.value :: val_acc, offset_acc')
            ) (`VALID Prov_none, [], `PtrBytes 0) bs in
          ( (match _prov with `INVALID -> Prov_none | `VALID z -> z)
          , (match offset_status with `OtherBytes -> `NotValidPtrProv | _ -> `ValidPtrProv)
          , List.rev rev_values )
  end
  
  type mem_state = {
    next_alloc_id: allocation_id;
    allocations: allocation IntMap.t;
    next_address: address;
    funptrmap: (Digest.t * string) IntMap.t;
    varargs: (int * (Core_ctype.ctype0 * pointer_value) list) IntMap.t;
    next_varargs_id: N.num;
    bytemap: AbsByte.t IntMap.t;
    
    dead_allocations: allocation_id list;
    dynamic_addrs: address list;
    last_used: allocation_id option;
  }
  
  let initial_mem_state = {
    next_alloc_id= Nat_big_num.zero;
    allocations= IntMap.empty;
    next_address= Nat_big_num.(succ zero);
    funptrmap = IntMap.empty;
    varargs = IntMap.empty;
    next_varargs_id = N.zero;
    bytemap= IntMap.empty;
    
    dead_allocations= [];
    dynamic_addrs= [];
    last_used= None;
  }
  
  type footprint =
    | Footprint
  
  let do_overlap fp1 fp2 =
    failwith "TODO: do_overlap"
  
  type 'a memM = ('a, mem_error, integer_value mem_constraint, mem_state) Eff.eff
  
  let return = Eff.return
  let bind = Eff.(>>=)
  
  (* TODO: hackish *)
  let fail err =
    let loc = match err with
      | MerrAccess (loc, _, _)
      | MerrWriteOnReadOnly loc
      | MerrUndefinedFree (loc, _) ->
          loc
      | MerrOutsideLifetime _
      | MerrInternal _
      | MerrOther _
      | MerrPtrdiff
      | MerrUndefinedRealloc
      | MerrIntFromPtr
      | MerrPtrFromInt
      | MerrPtrComparison
      | MerrWIP _ ->
          Location_ocaml.other "Concrete" in
    let open Nondeterminism in
    match undefinedFromMem_error err with
      | Some ubs ->
          kill (Undef0 (loc, ubs))
      | None ->
          kill (Other err)

  
  
  let string_of_provenance = function
    | Prov_none -> ""
    | Prov_some alloc_id ->
        N.to_string alloc_id
    | Prov_device ->
        "dev"
    | Prov_wildcard ->
        "wildcard"
  
  (* pretty printing *)
  open PPrint
  open Pp_prelude
  let pp_pointer_value (PV (prov, ptrval_))=
    match ptrval_ with
      | PVnull ty ->
          !^ "NULL" ^^ P.parens (Pp_core_ctype.pp_ctype ty)
      | PVfunction sym ->
          !^ "Cfunction" ^^ P.parens (!^ (Pp_symbol.to_string_pretty sym))
          (* !^ ("<funptr:" ^ Symbol.instance_Show_Show_Symbol_sym_dict.show_method sym ^ ">") *)
      | PVconcrete n ->
          (* TODO: remove this idiotic hack when Lem's nat_big_num library expose "format" *)
          P.parens (!^ ("@" ^ string_of_provenance prov) ^^ P.comma ^^^ !^ ("0x" ^ Z.format "%x" (Z.of_string (Nat_big_num.to_string n))))
  
  let pp_integer_value (IV (prov, n)) =
    if !Debug_ocaml.debug_level >= 3 then
      !^ ("<" ^ string_of_provenance prov ^ ">:" ^ Nat_big_num.to_string n)
    else
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
          comma_list (fun (ident, _, mval) ->
            dot ^^ Pp_cabs.pp_cabs_identifier ident ^^ equals ^^^ pp_mem_value mval
          ) xs
        )
    | MVunion (tag_sym, membr_ident, mval) ->
        parens (!^ "union" ^^^ !^ (Pp_symbol.to_string_pretty tag_sym)) ^^ braces (
          dot ^^ Pp_cabs.pp_cabs_identifier membr_ident ^^ equals ^^^
          pp_mem_value mval
        )
  
  
  (* TODO: this is stupid, we need to allow the outside world to specify
     what memory ranges are in device memory *)
  let device_ranges : (address * address) list =
    (* TODO: these are some hardcoded ranges to match the Charon tests... *)
    (* NOTE: these two ranges only have 4 bytes (e.g. one int) *)
    [ (N.of_int64 0x40000000L, N.of_int64 0x40000004L)
    ; (N.of_int64 0xABCL, N.of_int64 0XAC0L) ]
  
  
  (* NOTE: since we are fusing PVI and PVNI together any creation of an integer_value should
     be done through this function to unsure we always use Prov_none in PVNI *)
  let is_PNVI () =
    match Switches.(has_switch_pred (function SW_no_integer_provenance _ -> true | _ -> false)) with
      | None ->
          false
      | Some _ ->
          true
  
  let mk_ival prov n =
    if is_PNVI () then
      IV (Prov_none, n)
    else
      (* We are in the mode where integer values have a provenance *)
      IV (prov, n)
  
  (* TODO: DEBUG *)
  let print_bytemap str =
    if !Debug_ocaml.debug_level >= 3 then begin
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
  
  let get_allocation alloc_id : allocation memM =
    get >>= fun st ->
    match IntMap.find_opt alloc_id st.allocations with
      | Some ret ->
          return ret
      | None ->
          fail (MerrOutsideLifetime ("Concrete.get_allocation, alloc_id=" ^ N.to_string alloc_id))
  
  let is_within_bound alloc_id lvalue_ty addr =
    get_allocation alloc_id >>= fun alloc ->
    return (N.less_equal alloc.base addr && N.less_equal (N.add addr (N.of_int (sizeof lvalue_ty))) (N.add alloc.base alloc.size))
  
  let is_within_device ty addr =
    return begin
      List.exists (fun (min, max) ->
        N.less_equal min addr && N.less_equal (N.add addr (N.of_int (sizeof ty))) max
      ) device_ranges
    end
  
  
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
  let find_overlaping st addr : allocation_id option =
    IntMap.fold (fun alloc_id alloc acc ->
      match acc with
        | Some _ ->
            acc
        | None ->
            if    not (List.mem alloc_id st.dead_allocations)
               && N.less_equal alloc.base addr && N.less addr (N.add alloc.base alloc.size) then
              Some alloc_id
            else
              None
    ) st.allocations None
  
  
  (* INTERNAL combine_bytes: ctype -> AbsByte.t list -> mem_value * AbsByte.t list *)
  (* ASSUMES: has_size ty /\ |bs| >= sizeof ty*)
  (* property that should hold:
       forall ty bs bs' mval.
         has_size ty -> |bs| >= sizeof ty -> combine_bytes ty bs = (mval, bs') ->
         |bs'| + sizeof ty  = |bs| /\ typeof mval = ty *)
  let rec combine_bytes find_overlaping funptrmap ty (bs : AbsByte.t list) : mem_value * AbsByte.t list =
    let self = combine_bytes find_overlaping funptrmap in
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
    
    if List.length bs < sizeof ty then
      failwith "combine_bytes, |bs| < sizeof(ty)";
    
    match ty with
      | Void0
      | Array0 (_, None)
      | Function0 _ ->
          (* ty must have a known size *)
          assert false
      | Basic0 (Integer ity) ->
          let (bs1, bs2) = L.split_at (sizeof ty) bs in
          let (prov, _, bs1') = AbsByte.split_bytes bs1 in
          (begin match extract_unspec bs1' with
            | Some cs ->
                MVinteger ( ity
                          , mk_ival prov (int_of_bytes (AilTypesAux.is_signed_ity ity) cs))
            | None ->
                MVunspecified ty
          end , bs2)
      | Basic0 (Floating fty) ->
          let (bs1, bs2) = L.split_at (sizeof ty) bs in
          (* we don't care about provenances for floats *)
          let (_, _, bs1') = AbsByte.split_bytes bs1 in
          (begin match extract_unspec bs1' with
            | Some cs ->
                MVfloating ( fty
                           , Int64.float_of_bits (N.to_int64 (int_of_bytes true cs)) )
            | None ->
                MVunspecified ty
          end, bs2)
      | Array0 (elem_ty, Some n) ->
          let rec aux n acc cs =
            if n <= 0 then
              (MVarray (List.rev acc), cs)
            else
              let (mval, cs') = self elem_ty cs in
              aux (n-1) (mval :: acc) cs'
          in
          aux (Nat_big_num.to_int n) [] bs
      | Pointer0 (_, ref_ty) ->
          let (bs1, bs2) = L.split_at (sizeof ty) bs in
          Debug_ocaml.print_debug 1 [] (fun () -> "TODO: Concrete, assuming pointer repr is unsigned??");
          let (prov, prov_status, bs1') = AbsByte.split_bytes bs1 in
          (begin match extract_unspec bs1' with
            | Some cs ->
                let n = int_of_bytes false cs in
                begin match ref_ty with
                  | Function0 _ ->
                      if N.equal n N.zero then
                        (* TODO: check *)
                        MVpointer (ref_ty, PV (Prov_none, PVnull ref_ty))
                      else
                        (* FIXME: This is wrong. A function pointer with the same id in different files might exist. *)
                        begin match IntMap.find_opt n funptrmap with
                          | Some (file_dig, name) ->
                              MVpointer (ref_ty, PV(prov, PVfunction (Symbol.Symbol (file_dig, N.to_int n, Some name))))
                          | None -> failwith ("unknown function pointer: " ^ N.to_string n)
                        end
                  | _ ->
                      if N.equal n N.zero then
                        (* TODO: check *)
                        MVpointer (ref_ty, PV (Prov_none, PVnull ref_ty))
                      else
                        let prov =
                          if is_PNVI () then
                            match prov_status with
                              | `NotValidPtrProv ->
                                  begin match find_overlaping n with
                                    | None ->
                                        Prov_none
                                    | Some alloc_id ->
                                        Prov_some alloc_id
                                  end
                              | `ValidPtrProv ->
                                  prov
                          else
                            prov in
                        MVpointer (ref_ty, PV (prov, PVconcrete n))
                end
            | None ->
                MVunspecified (Core_ctype.Pointer0 (AilTypes.no_qualifiers, ref_ty))
          end, bs2)
      | Atomic0 atom_ty ->
          Debug_ocaml.print_debug 1 [] (fun () -> "TODO: Concrete, is it ok to have the repr of atomic types be the same as their non-atomic version??");
          self atom_ty bs
      | Struct0 tag_sym ->
          let (bs1, bs2) = L.split_at (sizeof ty) bs in
          let (rev_xs, _, bs') = List.fold_left (fun (acc_xs, previous_offset, acc_bs) (memb_ident, memb_ty, memb_offset) ->
            let pad = memb_offset - previous_offset in
            let (mval, acc_bs') = self memb_ty (L.drop pad acc_bs) in
            ((memb_ident, memb_ty, mval)::acc_xs, memb_offset + sizeof memb_ty, acc_bs')
          ) ([], 0, bs1) (fst (offsetsof tag_sym)) in
          (* TODO: check that bs' = last padding of the struct *)
          (MVstruct (tag_sym, List.rev rev_xs), bs2)
      | Union0 tag_sym ->
          failwith "TODO: combine_bytes, Union (as value)"
      | Builtin0 str ->
          failwith "TODO: combine_bytes, Builtin"
  
  
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
  let rec explode_bytes funptrmap mval : ((Digest.t * string) IntMap.t * AbsByte.t list) =
    let ret bs = (funptrmap, bs) in
    match mval with
      | MVunspecified ty ->
          ret @@ List.init (sizeof ty) (fun _ -> AbsByte.v Prov_none None)
      | MVinteger (ity, IV (prov, n)) ->
          ret @@List.map (AbsByte.v prov) begin
            bytes_of_int
              (AilTypesAux.is_signed_ity ity)
              (sizeof (Basic0 (Integer ity))) n
          end
      | MVfloating (fty, fval) ->
          ret @@ List.map (AbsByte.v Prov_none) begin
            bytes_of_int
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
                ret @@ List.init ptr_size (fun _ -> AbsByte.v Prov_none (Some '\000'))
            | PVfunction (Symbol.Symbol (file_dig, n, opt_name)) ->
                (* TODO: *)
                (begin match opt_name with
                  | Some name -> IntMap.add (N.of_int n) (file_dig, name) funptrmap
                  | None -> funptrmap
                end, List.map (AbsByte.v prov) begin
                  bytes_of_int
                      false
                      ptr_size (N.of_int n)
                  end)
            | PVconcrete addr ->
                ret @@ List.mapi (fun i -> AbsByte.v prov ~copy_offset:(Some i)) begin
                  bytes_of_int
                    false (* we model address as unsigned *)
                    ptr_size addr
                end
          end
      | MVarray mvals ->
          let (funptrmap, bs_s) =
            List.fold_left begin fun (funptrmap, bs) mval ->
              let (funptrmap, bs') = explode_bytes funptrmap mval in
              (funptrmap, bs' :: bs)
            end (funptrmap, []) mvals in
          (* TODO: use a fold? *)
          (funptrmap, L.concat @@ List.rev bs_s)
      | MVstruct (tag_sym, xs) ->
          let padding_byte _ = AbsByte.v Prov_none None in
          let (offs, last_off) = offsetsof tag_sym in
          let final_pad = sizeof (Core_ctype.Struct0 tag_sym) - last_off in
          (* TODO: rewrite now that offsetsof returns the paddings *)
          let (funptrmap, _, bs) = List.fold_left2 begin fun (funptrmap, last_off, acc) (ident, ty, off) (_, _, mval) ->
              let pad = off - last_off in
              let (funptrmap, bs) = explode_bytes funptrmap mval in
              (funptrmap, off + sizeof ty, acc @ List.init pad padding_byte @ bs)
            end (funptrmap, 0, []) offs xs
          in
          (funptrmap, bs @ List.init final_pad padding_byte)
      | MVunion (tag_sym, memb_ident, mval) ->
          let size = sizeof (Core_ctype.Union0 tag_sym) in
          let (funptrmap', bs) = explode_bytes funptrmap mval in
          (funptrmap', bs @ List.init (size - List.length bs) (fun _ -> AbsByte.v Prov_none None))
  
  
  (* BEGIN DEBUG *)
  let dot_of_mem_state st =
    let get_value alloc =
      let bs = fetch_bytes st.bytemap alloc.base (N.to_int alloc.size) in
      let Some ty = alloc.ty in
      let (mval, bs') = combine_bytes (find_overlaping st) st.funptrmap ty bs in
      mval
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
(*
  let dot_of_mem_state st =
  type allocation = {
    base: address;
    size: N.num; (*TODO: this is probably unnecessary once we have the type *)
    ty: Core_ctype.ctype0 option; (* None when dynamically allocated *)
    is_readonly: bool;
  }
  
  type mem_state = {
    next_alloc_id: allocation_id;
    allocations: allocation IntMap.t;
    next_address: address;
    bytemap: (provenance * char option) IntMap.t;
  }
*)
  (* END DEBUG *)
  
  let allocate_static tid pref (IV (_, align)) ty init_opt : pointer_value memM =
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
      
      match init_opt with
        | None ->
            ( PV (Prov_some alloc_id, PVconcrete addr)
            , { st with
                  next_alloc_id= Nat_big_num.succ st.next_alloc_id;
                  allocations= IntMap.add alloc_id {prefix= pref; base= addr; size= size; ty= Some ty; is_readonly= false} st.allocations;
                  last_used= Some st.next_alloc_id;
                  next_address= Nat_big_num.add addr size } )
        | Some mval ->
            (* TODO: factorise this with do_store inside Concrete.store *)
            let (funptrmap, pre_bs) = explode_bytes st.funptrmap mval in
            let bs = List.mapi (fun i b -> (Nat_big_num.add addr (Nat_big_num.of_int i), b)) pre_bs in
            ( PV (Prov_some alloc_id, PVconcrete addr)
            , { st with
                  next_alloc_id= Nat_big_num.succ st.next_alloc_id;
                  allocations= IntMap.add alloc_id {prefix= pref; base= addr; size= size; ty= Some ty; is_readonly= true} st.allocations;
                  next_address= Nat_big_num.add addr size;
                  last_used= Some st.next_alloc_id;
                  bytemap=
                    List.fold_left (fun acc (addr, b) ->
                      IntMap.add addr b acc
                    ) st.bytemap bs;
                  funptrmap= funptrmap;
              } )
    end
  

  let allocate_dynamic tid pref (IV (_, align_n)) (IV (_, size_n)) =
    modify (fun st ->
      let alloc_id = st.next_alloc_id in
      let addr = Nat_big_num.(add st.next_address (sub align_n (modulus st.next_address align_n))) in
      Debug_ocaml.print_debug 1 [] (fun () ->
        "DYNAMIC ALLOC - pref: " ^ String_symbol.string_of_prefix pref ^
        " --> alloc_id= " ^ N.to_string alloc_id ^
        ", size= " ^ N.to_string size_n ^
        ", addr= " ^ N.to_string addr
      );
      ( PV (Prov_some st.next_alloc_id, PVconcrete addr)
      , { st with
            next_alloc_id= Nat_big_num.succ st.next_alloc_id;
            allocations= IntMap.add alloc_id {prefix= pref; base= addr; size= size_n; ty= None; is_readonly= false} st.allocations;
            next_address= Nat_big_num.add addr size_n;
            last_used= Some st.next_alloc_id;
            dynamic_addrs= addr :: st.dynamic_addrs })
    )
  
  (* zap (make unspecified) any pointer in the memory with provenance matching a
     given allocation id *)
  let zap_pointers alloc_id =
    modify (fun st ->
      let bytemap' = IntMap.fold (fun alloc_id alloc acc ->
        let bs = fetch_bytes st.bytemap alloc.base (N.to_int alloc.size) in
        match alloc.ty with
          | None ->
              (* TODO: zapping doesn't work yet for dynamically allocated pointers *)
              acc
          | Some ty ->
              begin match combine_bytes (find_overlaping st) st.funptrmap ty bs with
                | (MVpointer (ref_ty, (PV (Prov_some alloc_id', _))), []) when alloc_id = alloc_id' ->
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
          fail (MerrOther "attempted to kill with a null pointer")
        else
          return ()
    | PV (_, PVfunction _) ->
          fail (MerrOther "attempted to kill with a function pointer")
    | PV (Prov_none, PVconcrete _) ->
          fail (MerrOther "attempted to kill with a pointer lacking a provenance")
    | PV (Prov_device, PVconcrete _) ->
        (* TODO: should that be an error ?? *)
        return ()
    | PV (Prov_some alloc_id, PVconcrete addr) ->
        begin if is_dyn then
          (* this kill is dynamic one (i.e. free() or friends) *)
          is_dynamic addr >>= begin function
            | false ->
                fail (MerrUndefinedFree (loc, Free_static_allocation))
            | true ->
                return ()
          end
        else
          return ()
        end >>= fun () ->
        is_dead alloc_id >>= begin function
          | true ->
              if is_dyn then
                fail (MerrUndefinedFree (loc, Free_dead_allocation))
              else
                failwith "Concrete: FREE was called on a dead allocation"
          | false ->
              get_allocation alloc_id >>= fun alloc ->
              if N.equal addr alloc.base then begin
                Debug_ocaml.print_debug 1 [] (fun () ->
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
                fail (MerrUndefinedFree (loc, Free_out_of_bound))
        end
    | PV (Prov_wildcard, _) ->
        failwith "TODO: Concrete.kill ==> Prov_wildcard"
  
  let load loc ty (PV (prov, ptrval_)) =
(*    print_bytemap "ENTERING LOAD" >>= fun () -> *)
    let do_load alloc_id_opt addr =
      get >>= fun st ->
      let bs = fetch_bytes st.bytemap addr (sizeof ty) in
      let (mval, bs') = combine_bytes (find_overlaping st) st.funptrmap ty bs in
      update (fun st -> { st with last_used= alloc_id_opt }) >>= fun () ->
      begin match bs' with
        | [] ->
            if Switches.(has_switch SW_strict_reads) then
              match mval with
                | MVunspecified _ ->
                    fail (MerrOther "load from uninitialised memory")
                | _ ->
                    return (Footprint, mval)
            else
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
                do_load None addr
          end
      | (Prov_some alloc_id, PVconcrete addr) ->
          is_dead alloc_id >>= begin function
            | true ->
                fail (MerrAccess (loc, LoadAccess, DeadPtr))
            | false ->
                return ()
          end >>= fun () ->
          begin is_within_bound alloc_id ty addr >>= function
            | false ->
                Debug_ocaml.print_debug 1 [] (fun () ->
                  "LOAD out of bound, alloc_id=" ^ N.to_string alloc_id
                );
                fail (MerrAccess (loc, LoadAccess, OutOfBoundPtr))
            | true ->
                do_load (Some alloc_id) addr
          end
      | (Prov_wildcard, _) ->
          failwith "TODO: Concrete.load ==> Prov_wildcard"
  
  
  let store loc ty is_locking (PV (prov, ptrval_)) mval =
    Debug_ocaml.print_debug 3 [] (fun () ->
      "ENTERING STORE: ty=" ^ String_core_ctype.string_of_ctype ty ^
      " -> @" ^ Pp_utils.to_plain_string (pp_pointer_value (PV (prov, ptrval_))) ^
      ", mval= " ^ Pp_utils.to_plain_string (pp_mem_value mval)
    );
    if not (ctype_equal (Core_ctype.unatomic ty) (Core_ctype.unatomic (typeof mval))) then begin
      Printf.printf "STORE ty          ==> %s\n"
        (String_core_ctype.string_of_ctype ty);
      Printf.printf "STORE typeof mval ==> %s\n"
        (String_core_ctype.string_of_ctype (typeof mval));
      Printf.printf "STORE ==> %s\n" (Location_ocaml.location_to_string loc);
      Printf.printf "STORE mval ==> %s\n"
        (Pp_utils.to_plain_string (pp_mem_value mval));
      fail (MerrOther "store with an ill-typed memory value")
    end else
      let do_store alloc_id_opt addr =
        update begin fun st ->
          let (funptrmap, pre_bs) = explode_bytes st.funptrmap mval in
          let bs = List.mapi (fun i b -> (Nat_big_num.add addr (Nat_big_num.of_int i), b)) pre_bs in
          { st with last_used= alloc_id_opt;
                    bytemap=
                      List.fold_left (fun acc (addr, b) ->
                      IntMap.add addr b acc
                    ) st.bytemap bs;
                    funptrmap= funptrmap; }
        end >>= fun () ->
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
                  do_store None addr
            end
        | (Prov_some alloc_id, PVconcrete addr) ->
            begin is_within_bound alloc_id ty addr >>= function
              | false ->
                  fail (MerrAccess (loc, StoreAccess, OutOfBoundPtr))
              | true ->
                  get_allocation alloc_id >>= fun alloc ->
                  if alloc.is_readonly then
                    fail (MerrWriteOnReadOnly loc)
                  else
                    do_store (Some alloc_id) addr >>= fun fp ->
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
            end
        | (Prov_wildcard, _) ->
            failwith "TODO: Concrete.store ==> Prov_wildcard"

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
    PV (Prov_some i, PVconcrete addr)

  let case_ptrval pv fnull ffun fconc _ =
    match pv with
    | PV (_, PVnull ty) -> fnull ty
    | PV (_, PVfunction f) -> ffun f
    | PV (Prov_none, PVconcrete addr) -> fconc None addr
    | PV (Prov_some i, PVconcrete addr) -> fconc (Some i) addr
    | _ -> failwith "case_ptrval"

  
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
            return (Nat_big_num.equal addr1 addr2)
          else
            Eff.msum "pointer equality"
              [ ("using provenance", return false)
              ; ("ignoring provenance", return (Nat_big_num.equal addr1 addr2)) ]
  
  let ne_ptrval ptrval1 ptrval2 =
    eq_ptrval ptrval1 ptrval2 >>= fun b ->
    return (not b)
  
  let lt_ptrval (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
      | (PVconcrete addr1, PVconcrete addr2) ->
          if Switches.(has_switch SW_strict_pointer_relationals) then
            match prov1, prov2 with
              | Prov_some alloc1, Prov_some alloc2 when alloc1 = alloc2 ->
                  return (Nat_big_num.compare addr1 addr2 == -1)
              | _ ->
                  (* TODO: one past case *)
                  fail MerrPtrComparison
          else
            return (Nat_big_num.compare addr1 addr2 == -1)
      | (PVnull _, _)
      | (_, PVnull _) ->
          fail (MerrWIP "lt_ptrval ==> one null pointer")
      | _ ->
          fail (MerrWIP "lt_ptrval")
  
  let gt_ptrval (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
      | (PVconcrete addr1, PVconcrete addr2) ->
          if Switches.(has_switch SW_strict_pointer_relationals) then
            match prov1, prov2 with
              | Prov_some alloc1, Prov_some alloc2 when alloc1 = alloc2 ->
                  return (Nat_big_num.compare addr1 addr2 == 1)
              | _ ->
                  (* TODO: one past case *)
                  fail MerrPtrComparison
          else
            return (Nat_big_num.compare addr1 addr2 == 1)
      | _ ->
          fail (MerrWIP "gt_ptrval")
  
  let le_ptrval (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
      | (PVconcrete addr1, PVconcrete addr2) ->
          if Switches.(has_switch SW_strict_pointer_relationals) then
            match prov1, prov2 with
              | Prov_some alloc1, Prov_some alloc2 when alloc1 = alloc2 ->
                  let cmp = Nat_big_num.compare addr1 addr2 in
                  return (cmp = -1 || cmp = 0)
              | _ ->
                  (* TODO: one past case *)
                  fail MerrPtrComparison
          else
            let cmp = Nat_big_num.compare addr1 addr2 in
            return (cmp = -1 || cmp = 0)
      | _ ->
          fail (MerrWIP "le_ptrval")
  
  let ge_ptrval (PV (prov1, ptrval_1)) (PV (prov2, ptrval_2)) =
    match (ptrval_1, ptrval_2) with
      | (PVconcrete addr1, PVconcrete addr2) ->
          if Switches.(has_switch SW_strict_pointer_relationals) then
            match prov1, prov2 with
              | Prov_some alloc1, Prov_some alloc2 when alloc1 = alloc2 ->
                  let cmp = Nat_big_num.compare addr1 addr2 in
                  return (cmp = 1 || cmp = 0)
              | _ ->
                  (* TODO: one past case *)
                  fail MerrPtrComparison
          else
            let cmp = Nat_big_num.compare addr1 addr2 in
            return (cmp = 1 || cmp = 0)
      | _ ->
          fail (MerrWIP "ge_ptrval")
  
  
  let diff_ptrval diff_ty ptrval1 ptrval2 =
    (* TODO: check that this is correct for arrays of arrays ... *)
    (* TODO: if not, sync with symbolic defacto *)
    let diff_ty' = match diff_ty with
      | Core_ctype.Array0 (elem_ty, _) ->
          elem_ty
      | _ ->
          diff_ty in
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
(*
      | PV (Prov_some alloc_id1, (PVconcrete addr1)), PV (Prov_some alloc_id2, (PVconcrete addr2)) ->
          if N.equal alloc_id1 alloc_id2 then
            get_allocation alloc_id1 >>= fun alloc ->
            (* NOTE: this is not like "is_within_bound" because it allows one-past pointers *)
            if    N.less_equal alloc.base addr1
               && N.less_equal addr1 (N.add alloc.base alloc.size)
               && N.less_equal alloc.base addr2
               && N.less_equal addr2 (N.add alloc.base alloc.size) then
              (* NOTE: the result of subtraction of two pointer values is an integer value with
                 empty provenance, irrespective of the operand provenances *)
              return (IV (Prov_none, N.div (N.sub addr1 addr2) (N.of_int (sizeof diff_ty'))))
            else
              fail MerrPtrdiff
          else
            get_allocation alloc_id1 >>= fun alloc1 ->
            get_allocation alloc_id2 >>= fun alloc2 ->
              if    N.equal addr1 (N.add alloc2.base alloc2.size)
                 || N.equal addr2 (N.add alloc1.base alloc1.size) then
                return (IV (Prov_none, N.div (N.sub addr1 addr2) (N.of_int (sizeof diff_ty'))))
              else
                fail MerrPtrdiff
*)
      | _ ->
          fail MerrPtrdiff
  
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
(*
                Printf.printf "addr: %s\n" (Nat_big_num.to_string addr);
                Printf.printf "align: %d\n" (alignof ref_ty);
*)
                return (N.(equal (modulus addr (of_int (alignof ref_ty))) zero))
          end
  
  (* Following §6.5.3.3, footnote 102) *)
  let validForDeref_ptrval ref_ty = function
    | PV (_, PVnull _)
    | PV (_, PVfunction _) ->
        return false
    | PV (Prov_device, PVconcrete _) as ptrval ->
        isWellAligned_ptrval ref_ty ptrval
    | PV (Prov_some alloc_id, PVconcrete _) as ptrval ->
        is_dead alloc_id >>= begin function
          | true ->
              return false
          | false ->
              isWellAligned_ptrval ref_ty ptrval
(*
              get_allocation alloc_id >>= fun alloc ->
              begin match alloc.ty with
                | Some ty ->
                    isWellAligned_ptrval ty ptrval
                | None ->
                    return true
              end
*)
        end
    | PV (Prov_none, _) ->
        return false
    | PV (Prov_wildcard, _) ->
        failwith "TODO: Concrete.validForDeref ==> Prov_wildcard"

  
  let ptrcast_ival _ ref_ty (IV (prov, n)) =
    if not (N.equal n N.zero) then
      (* STD §6.3.2.3#5 *)
      Debug_ocaml.warn [] (fun () ->
        "implementation defined cast from integer to pointer"
      );
    let sw_opt =
      Switches.(has_switch_pred (function SW_no_integer_provenance _ -> true | _ -> false)) in
    
    let n =
      let (min, max) = match Impl.sizeof_pointer with
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
    match sw_opt with
      | Some (Switches.SW_no_integer_provenance variant) ->
          (* TODO: device memory? *)
          if N.equal n N.zero then
            return (PV (Prov_none, PVnull ref_ty))
          else
            get >>= fun st ->
            (match find_overlaping st n with
              | None ->
                  if variant = 0 then
                    return Prov_none
                  else if variant = 1 then
                    fail MerrPtrFromInt
                  else
                    (* TODO: assuming variant = 4 *)
                    return Prov_wildcard
              | Some alloc_id ->
                  return (Prov_some alloc_id)) >>= fun prov ->
            return (PV (prov, PVconcrete n))
      | Some _ ->
          assert false
      | None ->
          begin match prov with
            | Prov_none ->
                (* TODO: check (in particular is that ok to only allow device pointers when there is no provenance? *)
                if List.exists (fun (min, max) -> N.less_equal min n && N.less_equal n max) device_ranges then
                  return (PV (Prov_device, PVconcrete n))
                else if N.equal n N.zero then
                  return (PV (Prov_none, PVnull ref_ty))
                else
                  return (PV (Prov_none, PVconcrete n))
            | _ ->
                return (PV (prov, PVconcrete n))
          end
  
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
          (* TODO: this seems to be undefined in ISO C *)
          (* NOTE: in C++, if offset = 0, this is defined and returns a PVnull *)
          failwith "TODO(shift a null pointer should be undefined behaviour)"
      | PVfunction _ ->
          failwith "Concrete.array_shift_ptrval, PVfunction"
      | PVconcrete addr ->
          PVconcrete (N.add addr offset))
  
  let member_shift_ptrval (PV (prov, ptrval_)) tag_sym memb_ident =
    let IV (_, offset) = offsetof_ival tag_sym memb_ident in
    PV (prov, match ptrval_ with
      | PVnull ty ->
          (* TODO: unsure, this might just be undefined (gcc-torture assumes the
             following behaviour though) *)
          if N.equal N.zero offset then
            PVnull ty
          else
            PVconcrete offset
      | PVfunction _ ->
          failwith "Concrete.member_shift_ptrval, PVfunction"
      | PVconcrete addr ->
          PVconcrete (N.add addr offset))
  
  let eff_array_shift_ptrval ptrval ty (IV (_, ival)) =
    let offset = (Nat_big_num.(mul (of_int (sizeof ty)) ival)) in
    match ptrval with
      | PV (_, PVnull _) ->
          (* TODO: this seems to be undefined in ISO C *)
          (* NOTE: in C++, if offset = 0, this is defined and returns a PVnull *)
          failwith "TODO(shift a null pointer should be undefined behaviour)"
      | PV (_, PVfunction _) ->
          failwith "Concrete.eff_array_shift_ptrval, PVfunction"
      | PV (Prov_some alloc_id, PVconcrete addr) ->
          (* TODO: is it correct to use the "ty" as the lvalue_ty? *)
          let addr' = N.add addr offset in
          if Switches.(has_switch SW_strict_pointer_arith) then
            get_allocation alloc_id >>= fun alloc ->
(*            Printf.printf "addr: %s, (base: %s,  base+size: %s, |ty|: %s" (N.to_string addr); *)
            if    N.less_equal alloc.base addr'
               && N.less_equal (N.add addr' (N.of_int (sizeof ty)))
                               (N.add (N.add alloc.base alloc.size) (N.of_int (sizeof ty))) then
              return (PV (Prov_some alloc_id, PVconcrete addr'))
            else
              fail (MerrOther "out-of-bound pointer arithmetic")
          else
            return (PV (Prov_some alloc_id, PVconcrete addr'))
      | PV (prov, PVconcrete addr) ->
          (* TODO: check *)
          return (PV (prov, PVconcrete (N.add addr offset)))
  
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
                (* TODO: hack, assuming like int *)
                sub (pow_int (of_int 2) (8*4-1)) (of_int 1)
            | IBuiltin _ ->
                failwith "TODO: max_ival: IBuiltin"
          end
      | None ->
          failwith "the concrete memory model requires a complete implementation MAX"
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
                failwith "the concrete memory model requires a complete implementation MIN"
          end
      | Enum _ ->
          (* TODO: hack, assuming like int *)
          negate (pow_int (of_int 2) (8*4-1))
      | IBuiltin _ -> 
          failwith "TODO: min_ival: Builtin"
    end)
  
  (* TODO: conversion? *)
  let intcast_ptrval _ ity (PV (prov, ptrval_)) =
    match ptrval_ with
      | PVnull _ ->
          return (mk_ival prov Nat_big_num.zero)
      | PVfunction (Symbol.Symbol (_, n, _)) ->
          return (mk_ival prov (Nat_big_num.of_int n))
      | PVconcrete addr ->
          let IV (_, ity_max) = max_ival ity in
          let IV (_, ity_min) = min_ival ity in
          if N.(less addr ity_min || less ity_max addr) then
            fail MerrIntFromPtr
          else
            return (mk_ival prov addr)

let combine_prov prov1 prov2 =
  match (prov1, prov2) with
    | (Prov_none, Prov_none) ->
        Prov_none
    | (Prov_none, Prov_some id) ->
        Prov_some id
    | (Prov_none, Prov_wildcard) ->
        Prov_wildcard
    | (Prov_none, Prov_device) ->
        Prov_device
    | (Prov_some id, Prov_none) ->
        Prov_some id
    | (Prov_some id1, Prov_some id2) ->
        if id1 = id2 then
          Prov_some id1
        else
          Prov_none
    | (Prov_some _, Prov_wildcard) ->
        Prov_wildcard
    | (Prov_some _, Prov_device) ->
        Prov_device
    | (Prov_device, Prov_none) ->
        Prov_device
    | (Prov_device, Prov_some _) ->
        Prov_device
    | (Prov_device, Prov_device) ->
        Prov_device
    | (Prov_device, Prov_wildcard) ->
        Prov_wildcard
    | (Prov_wildcard, _) ->
        Prov_wildcard


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
          IV (combine_prov prov1 prov2, Nat_big_num.integerDiv_t n1 n2)
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
    IV (Prov_none, Nat_big_num.of_int (sizeof ty))
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
  
  let ivfromfloat ity fval =
    (* TODO: hack maybe the elaboration should do that?? *)
    match ity with
      | Bool ->
          IV (Prov_none, if fval = 0.0 then N.zero else N.(succ zero))
      | _ ->
          let Some nbytes = Impl.sizeof_ity ity in
          let nbits = 8 * nbytes in
          let is_signed = AilTypesAux.is_signed_ity ity in
          let (min, max) =
            if is_signed then
              ( N.negate (N.pow_int (N.of_int 2) (nbits-1))
              , N.sub (N.pow_int (N.of_int 2) (nbits-1)) N.(succ zero) )
            else
              ( N.zero
              , N.sub (N.pow_int (N.of_int 2) nbits) N.(succ zero) ) in
          let wrapI n =
            let dlt = N.succ (N.sub max min) in
            let r = N.integerRem_f n dlt in
            if N.less_equal r max then
              r
            else
              N.sub r dlt in
          IV (Prov_none, (wrapI (N.of_int64 (Int64.of_float fval))))
  
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
  
  (* TODO check *)
  let memcpy ptrval1 ptrval2 (IV (_, size_n)) =
    let loc = Location_ocaml.other "memcpy" in
    let unsigned_char_ty = Core_ctype.Basic0 (AilTypes.(Integer (Unsigned Ichar))) in
    (* TODO: if ptrval1 and ptrval2 overlap ==> UB *)
    (* TODO: copy ptrval2 into ptrval1 *)
    let rec aux i =
      if Nat_big_num.less i size_n then
        load loc unsigned_char_ty (array_shift_ptrval ptrval2 unsigned_char_ty (IV (Prov_none, i))) >>= fun (_, mval) ->
        store loc unsigned_char_ty false (array_shift_ptrval ptrval1 unsigned_char_ty (IV (Prov_none, i))) mval >>= fun _ ->
        aux (Nat_big_num.succ i)
      else
        return ptrval1 in
    aux Nat_big_num.zero
  
  
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

  let realloc tid align ptr size : pointer_value memM =
    match ptr with
    | PV (Prov_none, PVnull _) ->
      allocate_dynamic tid (Symbol.PrefOther "realloc") align size
    | PV (Prov_none, _) ->
      fail (MerrWIP "realloc no provenance")
    | PV (Prov_some alloc_id, PVconcrete addr) ->
      is_dynamic addr >>= begin function
        | false ->
            fail (MerrUndefinedRealloc)
        | true ->
            get_allocation alloc_id >>= fun alloc ->
            if alloc.base = addr then
              allocate_dynamic tid (Symbol.PrefOther "realloc") align size >>= fun new_ptr ->
              memcpy new_ptr ptr (IV (Prov_none, alloc.size)) >>= fun _ ->
              kill (Location_ocaml.other "realloc") true ptr >>= fun () ->
              return new_ptr
            else
              fail (MerrWIP "realloc: invalid pointer")
      end
    | PV _ ->
      fail (MerrWIP "realloc: invalid pointer")

  let va_start args =
    get >>= fun st ->
    let id = st.next_varargs_id in
    update (fun st -> { st with varargs = IntMap.add id (0, args) st.varargs;
                                next_varargs_id = N.succ st.next_varargs_id;
                      } ) >>= fun _ ->
    return (IV (Prov_none, id))

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

  (* JSON serialisation: Memory layout for UI *)

  type ui_value =
    { size: int; (* number of square on the left size of the row *)
      path: string list; (* tag list *)
      value: string;
      prov: int option;
      bytes: AbsByte.t list option;
      typ: Core_ctype.ctype0 option;
    }

  type ui_alloc =
    { id: int;
      base: int;
      prefix: Symbol.prefix;
      dyn: bool; (* dynamic memory *)
      typ: Core_ctype.ctype0;
      size: int;
      values: ui_value list;
    }

  let rec mk_ui_values st bs ty mval : ui_value list =
    let mk_ui_values = mk_ui_values st in
    let mk_scalar v p bs_opt =
      [{ size = sizeof ty; path = []; value = v;
         prov = p; typ = Some ty; bytes = bs_opt }] in
    let mk_pad n v =
      { size = n; typ = None; path = []; value = v;
        prov = None; bytes = None } in
    let add_path p r = { r with path = p :: r.path } in
    match mval with
    | MVunspecified _ ->
      mk_scalar "unspecified" None None
    | MVinteger (_, IV(prov, n)) ->
      let p = match prov with Prov_some n -> Some (N.to_int n) | _ -> None in
      mk_scalar (N.to_string n) p None
    | MVfloating (_, f) ->
      mk_scalar (string_of_float f) None None
    | MVpointer (_, PV(prov, pv)) ->
      begin match pv with
        | PVnull _ ->
          mk_scalar "NULL" None None
        | PVconcrete n ->
          let p = match prov with Prov_some n -> Some (N.to_int n) | _ -> None in
          mk_scalar (N.to_string n) p (Some bs)
        | PVfunction sym ->
          mk_scalar (Pp_symbol.to_string_pretty sym) None None
      end
    | MVarray mvals ->
      begin match ty with
        | Array0 (elem_ty, _) ->
          let size = sizeof elem_ty in
          let (rev_rows, _, _) = List.fold_left begin fun (acc, i, acc_bs) mval ->
              let row = List.map (add_path (string_of_int i)) @@ mk_ui_values acc_bs elem_ty mval in
              (row::acc, i+1, L.drop size acc_bs)
            end ([], 0, bs) mvals
          in List.concat @@ (List.rev rev_rows)
        | _ ->
          failwith "mk_ui_values: array type is wrong"
      end
    | MVstruct (tag_sym, _) ->
      (* NOTE: we recombine the bytes to get paddings *)
      let (bs1, bs2) = L.split_at (sizeof ty) bs in
          let (rev_rowss, _, bs') = List.fold_left begin
          fun (acc_rowss, previous_offset, acc_bs) (Cabs.CabsIdentifier (_, memb), memb_ty, memb_offset) ->
            let pad = memb_offset - previous_offset in
            let acc_bs' = L.drop pad acc_bs in
            let (mval, acc_bs'') = combine_bytes (find_overlaping st) st.funptrmap memb_ty acc_bs' in
            let rows = mk_ui_values acc_bs' memb_ty mval in
            let rows' = List.map (add_path memb) rows in
            (* TODO: set padding value here *)
            let rows'' = if pad = 0 then rows' else mk_pad pad "" :: rows' in
            (rows''::acc_rowss, memb_offset + sizeof memb_ty, acc_bs'')
        end ([], 0, bs1) (fst (offsetsof tag_sym))
      in List.concat (List.rev rev_rowss)
    | MVunion (tag_sym, Cabs.CabsIdentifier (_, memb), mval) ->
      List.map (add_path memb) (mk_ui_values bs ty mval) (* FIXME: THE TYPE IS WRONG *)

  let mk_ui_alloc st id alloc : ui_alloc =
    let ty = match alloc.ty with Some ty -> ty | None -> Array0 (Basic0 (Integer Char), Some alloc.size) in
    let size = N.to_int alloc.size in
    let bs = fetch_bytes st.bytemap alloc.base size in
    let (mval, _) = combine_bytes (find_overlaping st) st.funptrmap ty bs in
    { id = id;
      base = N.to_int alloc.base;
      prefix = alloc.prefix;
      dyn = List.mem alloc.base st.dynamic_addrs;
      typ = ty;
      size = size;
      values = mk_ui_values st bs ty mval;
    }

  let serialise_prefix = function
    | Symbol.PrefOther s ->
      `Assoc [("kind", `String "other"); ("name", `String s)]
    | Symbol.PrefSource (_, []) ->
      failwith "serialise_prefix: PrefSource with an empty list"
    | Symbol.PrefSource (loc, [name]) ->
        `Assoc [("kind", `String "source");
                ("name", `String (Pp_symbol.to_string_pretty name));
                ("scope", `Null);
                ("loc", Location_ocaml.to_json loc);]
    | Symbol.PrefSource (loc, [scope; name]) ->
        `Assoc [("kind", `String "source");
                ("name", `String (Pp_symbol.to_string_pretty name));
                ("scope", `String (Pp_symbol.to_string_pretty scope));
                ("loc", Location_ocaml.to_json loc);]
    | Symbol.PrefSource (_, _) ->
      failwith "serialise_prefix: PrefSource with more than one scope"

  let serialise_map f m : Json.json =
    let serialise_entry (k, v) = (N.to_string k, f (N.to_int k) v)
    in `Assoc (List.map serialise_entry (IntMap.bindings m))

  let serialise_ui_values (v:ui_value) : Json.json =
    `Assoc [("size", `Int v.size);
            ("path", `List (List.map Json.of_string v.path));
            ("value", `String v.value);
            ("prov", Json.of_option Json.of_int v.prov);
            ("type", Json.of_option (fun ty -> `String (String_core_ctype.string_of_ctype ty)) v.typ);
            ("bytes", Json.of_option (fun bs -> `List (List.map AbsByte.to_json bs)) v.bytes); ]

  let serialise_ui_alloc (a:ui_alloc) : Json.json =
    `Assoc [("id", `Int a.id);
            ("base", `Int a.base);
            ("prefix", serialise_prefix a.prefix);
            ("dyn", `Bool a.dyn);
            ("type", `String (String_core_ctype.string_of_ctype a.typ));
            ("size", `Int a.size);
            ("values", `List (List.map serialise_ui_values a.values));
           ]

  let serialise_mem_state dig (st: mem_state) : Json.json =
    let allocs = IntMap.filter (fun _ (alloc : allocation) ->
        match alloc.prefix with
        | Symbol.PrefSource (_, syms) -> List.exists (fun (Symbol.Symbol (hash, _, _)) -> hash = dig) syms
        | _ -> false
      ) st.allocations in
    `Assoc [("map", serialise_map (fun id alloc -> serialise_ui_alloc @@ mk_ui_alloc st id alloc) allocs);
            ("last_used", Json.of_option (fun v -> `Int (N.to_int v)) st.last_used);]

end

include Concrete
