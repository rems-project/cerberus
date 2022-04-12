module Z = struct
  include Nat_big_num
  let format = Z.format
  let equal_num = equal
end

open Capability
open Sail_morello
open Sail_lib

module Morello_permission : Cap_permission = struct
  type t =
    {
      global: bool;
      executive: bool ;

      permits_load: bool;
      permits_store: bool;
      permits_execute: bool ;
      permits_load_cap: bool;
      permits_store_cap: bool;
      permits_store_local_cap: bool;
      permits_seal: bool;
      permits_unseal: bool;
      permits_system_access: bool;

      permits_ccall: bool; (* called "permoit_branch_sealer_pair" in Morello *)

      permit_compartment_id: bool; (* Morello-spefic? *)
      permit_mutable_load : bool; (* Morello-spefic? *)

      (* User[N] *)
      user_perms: bool list;
    }  [@@deriving eq,show]

  let user_perms_len = 4

  (* Input list contains permissions in the order listed in Morello
     spec, from "User" to "Local" with additional "global" and
     "exectuve" in the begining *)
  let of_list b =
    let np = List.length b in
    if np <> (user_perms_len + 14) then
      (Debug_ocaml.warn [] (fun () -> "Morello.P.of_list: invalid lengths permissions: " ^ (Stdlib.string_of_int np));
      None)
    else
      Some
        {
          permits_load            = List.nth b 17 ;
          permits_store           = List.nth b 16 ;
          permits_execute         = List.nth b 15 ;
          permits_load_cap        = List.nth b 14 ;
          permits_store_cap       = List.nth b 13 ;
          permits_store_local_cap = List.nth b 12 ;
          permits_seal            = List.nth b 11 ;
          permits_unseal          = List.nth b 10 ;
          permits_system_access   = List.nth b 9  ;
          permits_ccall           = List.nth b 8  ;
          permit_compartment_id   = List.nth b 7  ;
          permit_mutable_load     = List.nth b 6  ;

          user_perms = take user_perms_len (drop 2 b) ;

          executive              = List.nth b 1;
          global                 = List.nth b 0;
        }

  (* inverse of [of_list] *)
  let to_list p =
    [
      p.global;
      p.executive
    ]
    @ p.user_perms (* Do we need List.rev here? *)
    @ [
        p.permit_mutable_load;
        p.permit_compartment_id;
        p.permits_ccall;
        p.permits_system_access;
        p.permits_unseal;
        p.permits_seal;
        p.permits_store_local_cap;
        p.permits_store_cap;
        p.permits_load_cap;
        p.permits_execute;
        p.permits_store;
        p.permits_load;
      ]

  let perm_is_global          p = p.global
  let perm_is_executive       p = p.executive
  let perm_is_execute         p = p.permits_execute
  let perm_is_ccall           p = p.permits_ccall
  let perm_is_load            p = p.permits_load
  let perm_is_load_cap        p = p.permits_load_cap
  let perm_is_seal            p = p.permits_seal
  let perm_is_store           p = p.permits_store
  let perm_is_store_cap       p = p.permits_store_cap
  let perm_is_store_local_cap p = p.permits_store_local_cap
  let perm_is_system_access   p = p.permits_system_access
  let perm_is_unseal          p = p.permits_unseal

  let get_user_perms          p = p.user_perms

  let perm_clear_global          p = {p with global                  = false}
  let perm_clear_executive       p = {p with executive               = false}
  let perm_clear_execute         p = {p with permits_execute         = false}
  let perm_clear_ccall           p = {p with permits_ccall           = false}
  let perm_clear_load            p = {p with permits_load            = false}
  let perm_clear_load_cap        p = {p with permits_load_cap        = false}
  let perm_clear_seal            p = {p with permits_seal            = false}
  let perm_clear_store           p = {p with permits_store           = false}
  let perm_clear_store_cap       p = {p with permits_store_cap       = false}
  let perm_clear_store_local_cap p = {p with permits_store_local_cap = false}
  let perm_clear_system_access   p = {p with permits_system_access   = false}
  let perm_clear_unseal          p = {p with permits_unseal          = false}
  let perm_and_user_perms p up =
    {p with user_perms = List.map2 (&&) p.user_perms up}

  let perm_p0 =
    {
      global = false ;
      executive = false ;
      permits_load = false ;
      permits_store = false ;
      permits_execute = false ;
      permits_load_cap = false ;
      permits_store_cap = false ;
      permits_store_local_cap = false ;
      permits_seal = false ;
      permits_unseal = false ;
      permits_system_access = false ;
      permits_ccall = false ;
      permit_compartment_id = false ;
      permit_mutable_load = false ;
      user_perms = List.init user_perms_len (fun _ -> false)
    }

  let perm_alloc =
    { perm_p0 with
      permits_load = true ;
      permits_store = true ;
      permits_load_cap = true ;
      permits_store_cap = true ;
      permits_store_local_cap = true ; (* not sure *)
    }

  (** Returns permission a string in "simplified format".

      Example: "rwRW"

      See also:
      https://github.com/CTSRD-CHERI/cheri-c-programming/wiki/Displaying-Capabilities#simplified-forma
   *)
  let to_string (c:t) =
    let s f l = if f then l else "" in
    s c.permits_load "l"
    ^ s c.permits_store "w"
    ^ s c.permits_execute "x"
    ^ s c.permits_load_cap "R"
    ^ s c.permits_store_cap "W"
    ^ s c.executive "E"

end

module Morello_capability: Capability
       with type vaddr = Z.num
       with type vaddr_interval = Z.num*Z.num
  =
  struct
    module P = Morello_permission

    (** always unsigned! *)
    type vaddr = Z.num
                   [@@deriving eq,show]

    (**  15 bits actually. *)
    type otype = Z.num
                   [@@deriving eq,show]

    let min_vaddr  = Z.of_int 0
    let max_vaddr  = let open Z in sub (pow_int (of_int 2) 64) (of_int 1)
    let sizeof_vaddr = 8 (* 64-bit *)


    let vaddr_in_range a =
      (Z.greater_equal a min_vaddr) && (Z.less_equal a max_vaddr)

    let sizeof_cap = 16 (* 128 bit *)

    type vaddr_interval = vaddr * vaddr
                                    [@@deriving eq,show]

    type cap_seal_t =
      | Cap_Unsealed
      | Cap_SEntry (* "RB" in Morello *)
      | Cap_Indirect_SEntry (* "LB" in Morello *)
      (* | Cap_Indirect_SEntry_Pair *) (* "LBP" in Morello. TODO see why unused *)
      | Cap_Sealed of otype
                        [@@deriving eq,show]

    type t =
      {
        valid: bool;
        value: vaddr;
        obj_type: otype;
        bounds: vaddr_interval;
        flags: bool list;
        perms: P.t;
      }  [@@deriving eq,show]

    let cap_SEAL_TYPE_UNSEALED:otype = Z.of_int 0
    let cap_SEAL_TYPE_RB:otype       = Z.of_int 1 (* register-based branch *)
    let cap_SEAL_TYPE_LPB:otype      = Z.of_int 2 (* load pair and branch *)
    let cap_SEAL_TYPE_LB:otype       = Z.of_int 3 (* load and branch *)

    let cap_flags_len = 8

    let cap_is_valid c = c.valid

    let cap_get_obj_type c = c.obj_type

    let cap_get_value c = c.value

    let cap_get_bounds c = c.bounds

    let cap_get_seal c =
      let x = c.obj_type in
      if Z.equal x cap_SEAL_TYPE_UNSEALED then Cap_Unsealed
      else (if Z.equal x cap_SEAL_TYPE_RB then Cap_SEntry
            else (if Z.equal x cap_SEAL_TYPE_LPB then Cap_Indirect_SEntry
                  else (if Z.equal x cap_SEAL_TYPE_LB then Cap_Indirect_SEntry
                        else Cap_Sealed x)))

    let get_flags c = c.flags

    let get_perms c = c.perms

    let flags_from_value_bits (x:bit list): bool list =
      let x = zero_extend (x, Z.of_int 64) in
      let flags' = drop (64-8) x in
      List.map bool_of_bit flags'

    let flags_from_value (v:vaddr): bool list =
      let bits = to_bits' (64, v) in
      assert(List.length bits = 64);
      flags_from_value_bits bits

    (* Capability for newly allocated region *)
    let alloc_cap a size =
      {
        valid = true ;
        value = a ;
        obj_type = cap_SEAL_TYPE_UNSEALED ;
        bounds = (a, Z.add a size) ;
        flags = flags_from_value a ;
        perms = P.perm_alloc ;
      }

    let alloc_fun a =
      {
        valid = true ;
        value = a ;
        obj_type = cap_SEAL_TYPE_RB ; (* TODO(CHERI): check this *)
        bounds = (a, Z.succ (Z.succ a)) ; (* for all functions to have unique addresses we
                                             presently allocate 1-byte region for each *)
        flags = flags_from_value a;
        perms = P.perm_alloc ;
      }

    (* private function to decode bit list *)
    let decode_bits bits =
      if List.length bits <> 129 then
        (Debug_ocaml.warn [] (fun () -> "Morello.decode: wrong number of cap bits");
        None)
      else
        let value' = zCapGetValue bits in
        let value = uint value' in
        let (base', limit', isExponentValid) = zCapGetBounds bits in
        if not isExponentValid then
          (Debug_ocaml.warn [] (fun () -> "Morello.decode: invalid exponent");
          None)
        else
          let flags = flags_from_value_bits value' in
          let perms' = zCapGetPermissions bits  in
          let perms_data = List.map bool_of_bit perms' in
          match P.of_list perms_data with
          | None ->
             (Debug_ocaml.warn [] (fun () -> "Morello.decode: could not decode permissions");
              None)
          | Some perms ->
             let otype = uint (zCapGetObjectType bits) in
             Some {
                 valid = zCapIsTagSet bits;
                 value = value;
                 obj_type = otype;
                 bounds = (uint base', uint limit');
                 flags = flags ;
                 perms = perms ;
               }

    let decode (bytes:char list) (tag:bool) =
      let bit_list_of_char c =
        get_slice_int' (8, (Z.of_int (int_of_char c)), 0) in
      (* TODO(CHERI): check if bytes' and bits' decoding order is correct *)
      let bits = List.concat (List.map bit_list_of_char bytes) in
      decode_bits ([bit_of_bool tag] @ bits)

    let bytes_of_bits (b:bit list) : char list =
      assert((List.length b) mod 8 == 0);
      (* TODO(CHERI): check if bytes' and bits' encoding order is correct *)
      let bs = break 8 b in
      let zs = List.map uint bs in
      let is = List.map Z.to_int zs in
      List.map char_of_int is

    (* There is no such function in Sail, so we define it here *)
    let zCapSetPermissins ((zc__arg, zp) : (bit list * bit list)) : bit list =
      sail_call (fun r ->
          let zc = ref (zc__arg : bit list) in
          begin
            zc := (update_subrange (!zc, zCAP_PERMS_HI_BIT, zCAP_PERMS_LO_BIT, zp));
            r.return !zc
          end)

    let encode_to_bits exact c =
      (* start with NULL capabiluty *)
      let bits = zCapNull () in

      (* Set initial tag value. It may change later! *)
      let bits = zCapSetTag (bits,[bit_of_bool (cap_is_valid c)]) in

      (* otype *)
      let bits = zCapSetObjectType (bits, to_bits' (64, cap_get_obj_type c)) in

      (* bounds *)
      let (base',limit') = cap_get_bounds c in
      let len' = Z.sub limit' base' in
      let base = to_bits' (64, base') and len = to_bits' (65, len') in
      (* temporary set the value to base *)
      let bits = zCapSetValue (bits, base) in
      (* derive new capabilty with len-sized bounds *)
      let bits = zCapSetBounds (bits, len, exact) in

      (* actual value *)
      let bits = zCapSetValue (bits, to_bits' (64, cap_get_value c)) in

      (* flags *)
      let flags = get_flags c |> List.map bit_of_bool in
      assert (List.length flags == 8) ;
      let flags = zero_extend (flags, (Z.of_int 64)) in
      assert (List.length flags == 64) ;
      let bits = zCapSetFlags (bits, flags) in

      (* permissions *)
      let perms = get_perms c |> P.to_list |>  List.map bit_of_bool in
      assert (List.length perms == 18) ;
      let bits = zCapSetPermissins (bits, perms) in
      bits

    let encode exact c =
      let bits = encode_to_bits exact c in
      (* Convert to bytes *)
      assert (List.length bits == 129) ;
      let bytes = bytes_of_bits (drop 1 bits) in
      assert (List.length bytes == 16) ;
      (* extract the final tag *)
      let tag = zCapIsTagSet bits in
      (bytes, tag)

    let cap_vaddr_representable c a =
      vaddr_in_range a &&
      (let cap_bits = encode_to_bits true c in
      zCapIsRepresentable (cap_bits, (to_bits' (64, a))))

    let cap_bounds_representable_exactly c (base',limit') =
      (* encode with tag set *)
      let bits = encode_to_bits true c in
      let len' = Z.sub limit' base' in
      let base = to_bits' (64, base') and len = to_bits' (65, len') in
      (* set the value to base *)
      let bits = zCapSetValue (bits, base) in
      (* derive new capabilty with len-sized bounds *)
      let bits = zCapSetBounds (bits, len, true) in
      (* if tag is still set, bounds are representable exactly *)
      zCapIsTagSet bits

    let cap_invalidate c = {c with valid = false }

    (* Modifying the Capability Value (vaddress of object type)

       Related instructions:
       - SCVALUE in Morello
       - CPYTYPE in Morello
     *)
    let cap_set_value c cv =
      if cap_vaddr_representable c cv then
        {c with
          value = cv;
          flags = flags_from_value cv
        }
      else
        cap_invalidate c

    (* Reducing the Capability Bounds (with rounding)

       Related instructions:
       - SCBNDS (immediate) in Morello?
     *)
    let cap_narrow_bounds c (a0,a1) =
      assert(vaddr_in_range a0) ;
      assert(vaddr_in_range a1) ;
      (* TODO(CHERI) *)
      c

    (* Reducing the Capability Bounds (exact)

       Related instructions:
       - SCBNDSE (immediate) in Morello?
     *)
    let cap_narrow_bounds_exact c (a0,a1) =
      assert(vaddr_in_range a0) ;
      assert(vaddr_in_range a1) ;
      (* TODO(CHERI) *)
      c

    (* Reducing the Capability Permissions

       Related instructions:
       - CLRPERM in Morello
     *)
    let cap_narrow_perms c p = c (* TODO *)

    (* Sealing operations *)

    (* Regular sealing (with object type)

       Related instructions:
       - SEAL (capabilitiy) in Morello
     *)
    let cap_seal c k =
      cap_set_value c (cap_get_value k)

    (* Seal Entry
       - SEAL (immediatete) in Morello
     *)
    let cap_seal_entry c = c (* TODO *)

    (* Seal Indirect Entry
       - SEAL (immediatete) in Morello
     *)
    let cap_seal_indirect_entry c = c (* TODO *)

    (* Seal Entry Pair
       - SEAL (immediatete) in Morello
     *)
    let cap_seal_indirect_entry_pair c = c (* TODO *)

    (* Modifying the Capability Flags
       - BICFLGS in Morello
       - EORFLGS in Morello
       - ORRFLGS in Morello
       - SCFLGS in Morello
     *)
    let cap_set_flags c f =
      (* TODO(CHERI): also modify value *)
      {c with flags = f }

    (* --- Controlled non-monotonic manipulation --  *)

    (* Unsealing a capability using an unsealing operation.
       - UNSEAL in Morello
     *)
    let cap_unseal c k = (* TODO: check if allowed *)
      {c with obj_type = cap_SEAL_TYPE_UNSEALED}

    (* exact equality. compares capability metadata as well as value *)
    let eq = (=)

    (* compare value only ignoring metadata *)
    let value_compare x y = compare x.value y.value

    (* Helper function to check if capability is sealed (with any kind of seal) *)
    let is_sealed c =
      match cap_get_seal c with
      | Cap_Unsealed -> false
      | _ -> true

    (* Helper function to check if sealed entry capability *)
    let is_sentry c =
      match cap_get_seal c with
      | Cap_Sealed _ -> true
      | _ -> false

    (** Returns capability as a string in "simplified format". This
        function is used from "printf" when "%#p" format is specified.

        Example: "0xfffffff7ff8c [rwRW,0xfffffff7ff88-0xfffffff7ff90]"

        TODO(CHERI) "In addition, for null-derived capabilities
        (capabilities where the tag and upper attribute word are all
        zero), only the address is displayed (the Basic Format)."

        See also:
        https://github.com/CTSRD-CHERI/cheri-c-programming/wiki/Displaying-Capabilities#simplified-forma
     *)
    let to_string (c:t) =
      let vstring x = "0x" ^ (Z.format "%x" x) in
      let (b0,b1) = c.bounds in

      let flags =
        let attrs =
          let a f s l = if f then s::l else l in
          a (not c.valid) "invald"
          @@ a (is_sentry c) "sentry"
          @@ a (is_sealed c) "sealed" []
        in
        if List.length attrs = 0 then ""
        else " (" ^ String.concat "," attrs ^ ")"
      in

      Printf.sprintf "%s [%s,%s-%s]%s"
        (vstring c.value)
        (P.to_string c.perms)
        (vstring b0)
        (vstring b1)
        flags

    let cap_c0 () =
      match decode_bits (zCapNull ()) with
      | Some c -> c
      | None ->
         failwith "Could not construct NULL capability (C0)!"

  end
