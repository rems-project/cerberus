module N = Nat_big_num

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
end

module Morello_capability: Capability =
  struct
    module P = Morello_permission
    type vaddr = N.num
    type otype = N.num (*  15 bits actually. *)

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

        (* "Union" type of two values *)
        value: vaddr;
        obj_type: otype;

        bounds: vaddr_interval;
        flags: bool list;
        perms: P.t;
        is_execuvite : bool; (* Morello-spefic? *)
      }

    let cap_SEAL_TYPE_UNSEALED:otype = N.of_int 0
    let cap_SEAL_TYPE_RB:otype       = N.of_int 1 (* register-based branch *)
    let cap_SEAL_TYPE_LPB:otype      = N.of_int 2 (* load pair and branch *)
    let cap_SEAL_TYPE_LB:otype       = N.of_int 3 (* load and branch *)

    let cap_flags_len = 8

    let cap_is_valid c = c.valid (* TODO: maybe more checks *)

    let cap_get_obj_type c = c.obj_type

    let cap_get_value c = c.value

    let cap_get_bounds c = c.bounds

    let cap_get_seal c =
      let x = c.obj_type in
      if N.equal x cap_SEAL_TYPE_UNSEALED then Cap_Unsealed
      else (if N.equal x cap_SEAL_TYPE_RB then Cap_SEntry
            else (if N.equal x cap_SEAL_TYPE_LPB then Cap_Indirect_SEntry
                  else (if N.equal x cap_SEAL_TYPE_LB then Cap_Indirect_SEntry
                        else Cap_Sealed x)))

    let get_flags c = c.flags

    let get_perms c = c.perms

    let cap_c0 =  {
        valid = false;
        value = N.of_int 0;
        obj_type = cap_SEAL_TYPE_UNSEALED;
        bounds = (N.of_int 0, N.of_int 0);
        flags = List.init cap_flags_len (fun _ -> false) ;
        perms = P.perm_p0 ;
        is_execuvite = false ;
      }

    let cap_vaddr_representable c a = true (* TODO *)

    let cap_bounds_representable_exactly c (a0,a1) = true (* TODO *)

    let cap_invalidate c = {c with valid = false }

    (* Modifying the Capability Value (vaddress of object type)

       Related instructions:
       - SCVALUE in Morello
       - CPYTYPE in Morello
     *)
    let cap_set_value c cv = c (* TODO *)

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

    let to_string (c:t) =
      ("0x" ^ Z.format "%x" (Z.of_string (N.to_string c.value)))
        (* TODO: print more fields, including permissions *)

  end
