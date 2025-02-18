type cerb_switch =
  (* `PERMISSIVE allows out-of-bound pointer values. This the default behaviour
     for PNVI, whereas `STRICT (making out-of-bound pointer values creations
     UB, as in ISO) is the default for all variant of PNVI *)
  | SW_pointer_arith of [ `PERMISSIVE | `STRICT ]
  
    (* makes reading from uinitialised memory, Undefined *)
  | SW_strict_reads
  
    (* makes it an error to free a NULL pointer (stricter than ISO) *)
  | SW_forbid_nullptr_free
  | SW_zap_dead_pointers
  
    (* make the equality operators strictly base on the numerical value of pointers *)
  | SW_strict_pointer_equality
  
    (* make the relational operators UB when relating distinct objects (ISO) *)
  | SW_strict_pointer_relationals
  
  | SW_PNVI of [ `PLAIN | `AE | `AE_UDI ]
  | SW_CHERI
  
    (* the elaboration places the allocation/initialisation/deallocation of
       non-variadic functions inside the body of the Core procedures
       (instead of at that caller side) *)
  | SW_inner_arg_temps

    (* allow (with %p) formatted printing of non-void pointers (relaxing ISO) *)
  | SW_permissive_printf

    (* make it so every object allocation is zero initialised *)
  | SW_zero_initialised

  (* pointer revocation *)
  | SW_revocation of [ `INSTANT | `CORNUCOPIA]

  (* parsing of magic comments (e.g. "/*@ magic() @*/" as statements *)
  | SW_at_magic_comments

  (* set magic comment syntax to "/*$ ... $*/" *)
  | SW_magic_comment_char_dollar

  (* type aliases (e.g. size_t) are normalised during the elaboration to Core.
     As a result the generated Core has fixed their implementation. *)
  | SW_elaboration_normalises_types

let internal_ref =
  ref []


let get_switches () =
  !internal_ref

let has_switch sw =
  List.mem sw !internal_ref


let has_switch_pred pred =
  List.find_opt pred !internal_ref


let set strs =
  let read_switch = function
    | "strict_pointer_arith" ->
        Some (SW_pointer_arith `STRICT)
    | "permissive_pointer_arith" ->
        Some (SW_pointer_arith `PERMISSIVE)
    | "strict_reads" ->
        Some SW_strict_reads
    | "forbid_nullptr_free" ->
        Some SW_forbid_nullptr_free
    | "zap_dead_pointers" ->
        Some SW_zap_dead_pointers
    | "strict_pointer_equality" ->
        Some SW_strict_pointer_equality
    | "strict_pointer_relationals" ->
        Some SW_strict_pointer_relationals
    | "PNVI" ->
        Some (SW_PNVI `PLAIN)
    | "PNVI_ae" ->
        Some (SW_PNVI `AE)
    | "PNVI_ae_udi" ->
        Some (SW_PNVI `AE_UDI)
    | "inner_arg_temps" ->
        Some SW_inner_arg_temps
    | "permissive_printf" ->
        Some SW_permissive_printf
    | "zero_initialised" ->
        Some SW_zero_initialised
    | "CHERI" ->
        Some SW_CHERI
    | "revoke_dead_pointers" ->
        Some (SW_revocation `INSTANT)
    | "cornucopia" ->
        Some (SW_revocation `CORNUCOPIA)
    | "at_magic_comments" ->
        Some SW_at_magic_comments
    | "magic_comment_char_dollar" ->
        Some (SW_magic_comment_char_dollar)
    | "elaboration_normalises_types" ->
        Some SW_elaboration_normalises_types
    | _ ->
        None in
  let pred x = function
    | SW_pointer_arith _ ->
        begin match x with
          | SW_pointer_arith _ -> true
          | _ -> false
        end
    | SW_PNVI _ ->
        begin match x with
          | SW_PNVI _ -> true
          | _ -> false
        end
    | SW_revocation _ ->
        begin match x with
          | SW_revocation _ -> true
          | _ -> false
        end
    | SW_strict_reads
    | SW_forbid_nullptr_free
    | SW_zap_dead_pointers
    | SW_strict_pointer_equality
    | SW_strict_pointer_relationals
    | SW_CHERI
    | SW_inner_arg_temps
    | SW_permissive_printf
    | SW_zero_initialised
    | SW_at_magic_comments
    | SW_magic_comment_char_dollar
    | SW_elaboration_normalises_types as y ->
        x = y in
  List.iter (fun str ->
    match read_switch str with
      | Some sw ->
          if None = has_switch_pred (pred sw) then
            internal_ref := sw :: !internal_ref
          else
            prerr_endline ("switch '" ^ String.escaped str ^ "' would override a previous switch --> ignoring.")
      | None ->
          prerr_endline ("failed to parse switch '" ^ String.escaped str ^ "' --> ignoring.")
  ) strs

let set_iso_switches () =
  internal_ref := [
      SW_pointer_arith `STRICT
    ; SW_strict_reads
    ; SW_zap_dead_pointers
    ; SW_strict_pointer_equality
    ; SW_strict_pointer_relationals
    ; SW_PNVI `AE_UDI ]

let is_CHERI () =
  List.exists (function SW_CHERI -> true | _ -> false) !internal_ref

let is_PNVI () =
  List.exists (function SW_PNVI _ -> true | _ -> false) !internal_ref

let has_strict_pointer_arith () =
  has_switch (SW_pointer_arith `STRICT)
