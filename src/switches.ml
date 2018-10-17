type cerb_switch =
    (* makes the creation of out-of-bound pointer values, Undefined (ISO) *)
  | SW_strict_pointer_arith
    (* makes reading from uinitialised memory, Undefined (ISO) *)
  | SW_strict_reads
    (* makes it an error to free a NULL pointer (stricter than ISO) *)
  | SW_forbid_nullptr_free
  | SW_zap_dead_pointers
  
    (* n=0 => basic proposal, other versions supported for now: n= 1, 4 *)
  | SW_no_integer_provenance of int


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
    | "no_integer_provenance" ->
        Some (SW_no_integer_provenance 0)
    | "no_integer_provenance_v1" ->
        Some (SW_no_integer_provenance 1)
    | "no_integer_provenance_v4" ->
        Some (SW_no_integer_provenance 4)
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
