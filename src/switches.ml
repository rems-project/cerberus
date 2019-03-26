type cerb_switch =
    (* makes the creation of out-of-bound pointer values, Undefined (ISO) *)
  | SW_strict_pointer_arith
    (* makes reading from uinitialised memory, Undefined (ISO) *)
  | SW_strict_reads
    (* makes it an error to free a NULL pointer (stricter than ISO) *)
  | SW_forbid_nullptr_free
  | SW_zap_dead_pointers
  
    (* make the relational operators UB when relating distinct objects (ISO) *)
  | SW_strict_pointer_relationals
  
    (* n=0 => basic proposal, other versions supported for now: n= 1, 4 *)
(*  | SW_no_integer_provenance of int *)
  
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
        Some SW_strict_pointer_arith
    | "strict_reads" ->
        Some SW_strict_reads
    | "forbid_nullptr_free" ->
        Some SW_forbid_nullptr_free
    | "zap_dead_pointers" ->
        Some SW_zap_dead_pointers
    | "strict_pointer_relationals" ->
        Some SW_strict_pointer_relationals

(*
    | "no_integer_provenance" ->
        Some (SW_no_integer_provenance 0)
    | "no_integer_provenance_v1" ->
        Some (SW_no_integer_provenance 1)
    | "no_integer_provenance_v4" ->
        Some (SW_no_integer_provenance 4)
*)
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
