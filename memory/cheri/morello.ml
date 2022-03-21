module Z = struct
  include Nat_big_num
  let format = Z.format
end

open Capability

module Morello_permission : Cap_permission = struct
  type t =
    {
      global: bool;
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
    }

  let user_perms_len = 4

  let perm_is_global          p = p.global
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
    {
      global = false ;
      permits_load = true ;
      permits_store = true ;
      permits_execute = false ;
      permits_load_cap = true ;
      permits_store_cap = true ;
      permits_store_local_cap = true ; (* not sure *)
      permits_seal = false ;
      permits_unseal = false ;
      permits_system_access = false ;
      permits_ccall = false ;
      permit_compartment_id = false ;
      permit_mutable_load = false ;
      user_perms = List.init user_perms_len (fun _ -> false)
    }

  (** Returns permission a string in "simplified format".

      Example: "rwRW"

      See also:
      https://github.com/CTSRD-CHERI/cheri-c-programming/wiki/Displaying-Capabilities#simplified-forma
   *)
  let to_string (c:t) = ""


end

module Morello_capability: Capability
       with type vaddr = Z.num
       with type vaddr_interval = Z.num*Z.num
  =
  struct
    module P = Morello_permission
    type vaddr = Z.num
    type otype = Z.num (*  15 bits actually. *)

    let min_vaddr  = Nat_big_num.of_int 0
    let max_vaddr  = let open Nat_big_num in sub (pow_int (of_int 2) 64) (of_int 1)
    let sizeof_vaddr = 8 (* 64-bit *)

    let sizeof_cap = 16 (* 128 bit *)

    type vaddr_interval = vaddr * vaddr

    type cap_seal_t =
      | Cap_Unsealed
      | Cap_SEntry (* "RB" in Morello *)
      | Cap_Indirect_SEntry (* "LB" in Morello *)
      (* | Cap_Indirect_SEntry_Pair *) (* "LBP" in Morello. TODO see why unused *)
      | Cap_Sealed of otype

    type t =
      {
        valid: bool;
        value: vaddr;
        obj_type: otype;
        bounds: vaddr_interval;
        flags: bool list;
        perms: P.t;
        is_execuvite : bool; (* Morello-spefic? *)
      }

    let cap_SEAL_TYPE_UNSEALED:otype = Z.of_int 0
    let cap_SEAL_TYPE_RB:otype       = Z.of_int 1 (* register-based branch *)
    let cap_SEAL_TYPE_LPB:otype      = Z.of_int 2 (* load pair and branch *)
    let cap_SEAL_TYPE_LB:otype       = Z.of_int 3 (* load and branch *)

    let cap_flags_len = 8

    let cap_is_valid c = c.valid (* TODO: maybe more checks *)

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

    (* Capability for newly allocated region *)
    let alloc_cap a size =
      {
        valid = true ;
        value = a ;
        obj_type = cap_SEAL_TYPE_UNSEALED ;
        bounds = (a, Z.add a size) ;
        flags = List.init cap_flags_len (fun _ -> false) ;
        perms = P.perm_alloc ;
        is_execuvite = false
      }

    let cap_vaddr_representable c a = true (* TODO *)

    let cap_bounds_representable_exactly c (a0,a1) = true (* TODO *)

    let cap_invalidate c = {c with valid = false }

    (* Modifying the Capability Value (vaddress of object type)

       Related instructions:
       - SCVALUE in Morello
       - CPYTYPE in Morello
     *)
    let cap_set_value c cv =
      let c = {c with value = cv} in
      if cap_vaddr_representable c cv then
        (* TODO: additional checks for "if any bounds bits are taken
           from the value, ensure the top address bit doesn't
           change". See `CapSetValue` in morello spec *)
        c
      else
        cap_invalidate c

    (* Reducing the Capability Bounds (with rounding)

       Related instructions:
       - SCBNDS (immediate) in Morello?
     *)
    let cap_narrow_bounds c (a0,c1) = c

    (* Reducing the Capability Bounds (exact)

       Related instructions:
       - SCBNDSE (immediate) in Morello?
     *)
    let cap_narrow_bounds_exact c (a0,c1) = c

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
    let cap_set_flags c f = {c with flags = f }

    (* --- Controlled non-monotonic manipulation --  *)

    (* Unsealing a capability using an unsealing operation.
       - UNSEAL in Morello
     *)
    let cap_unseal c k = (* TODO: check if allowed *)
      {c with obj_type = cap_SEAL_TYPE_UNSEALED}


    let decode (bytes:char list) (tag:bool) = None (* TODO implement *)

    let encode c = [] (* TODO implement *)

    (* exact equality. compares capability metadata as well as value *)
    let eq = (=)

    (* compare value only ignoring metadata *)
    let value_compare x y = compare x.value y.value

    (** Returns capability as a string in "simplified format". This
        function is used from "printf" when "%#p" format is specified.

        Example: "0xfffffff7ff8c [rwRW,0xfffffff7ff88-0xfffffff7ff90]"

        See also:
        https://github.com/CTSRD-CHERI/cheri-c-programming/wiki/Displaying-Capabilities#simplified-forma
     *)
    let to_string (c:t) =
      let vstring x = "0x" ^ (Z.format "%x" x) in
      let (b0,b1) = c.bounds in
      (* TODO(CHERI): print flags *)
      Printf.sprintf "%s [%s,%s-%s]"
        (vstring c.value)
        (P.to_string c.perms)
        (vstring b0)
        (* TODO(CHERI): check if this is correct. wiki says "top:
           Upper bound of capability plus 1." But also we need to
           consider the fact that our bounds are inclusive *)
        (vstring (Nat_big_num.succ b1))

    (* In morello the null capabilitiy is defined as encoding of all
       zeroes. Related pseudocode definition: CapNull *)
    let cap_c0 =
      match decode (List.init sizeof_cap (Fun.const 'a')) false with
      | Some c -> c
      | None ->
         (* TODO(CHERI): temporary workaround until decode is implemented *)
         {
           valid = false;
           value = Z.of_int 0;
           obj_type = cap_SEAL_TYPE_UNSEALED;
           bounds = (Z.of_int 0, Z.of_int 0);
           flags = List.init cap_flags_len (fun _ -> false) ;
           perms = P.perm_p0 ;
           is_execuvite = false
         }
           (* failwith "Could not construct NULL capability (C0)" *)

  end
