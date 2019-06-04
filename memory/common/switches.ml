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



let are_incompatible = function
  | (SW_PNVI x, SW_PNVI y) ->
      x <> y
  | _ ->
      false



(*
UB when reading uninitialised memory
 *)

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
    | _ ->
        None in
  List.iter (fun str ->
    match read_switch str with
      | Some sw ->
          if not (has_switch sw) then
            internal_ref := sw :: !internal_ref
      | None ->
          prerr_endline ("failed to parse switch `" ^ String.escaped str ^ "' --> ignoring.")
  ) strs


let is_PNVI () =
  List.exists (function SW_PNVI _ -> true | _ -> false) !internal_ref

let has_strict_pointer_arith () =
  has_switch (SW_pointer_arith `STRICT)
