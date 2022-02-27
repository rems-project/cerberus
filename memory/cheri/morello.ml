open Capability

let morello_user_perms_len = 4

type morello_perm =
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


module Morello_permission : Cap_permission = struct
  type t = morello_perm
  let user_perms_len = morello_user_perms_len

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
  let perm_and_user_perms p np = p (* TODO *)

end

