type cerb_switch =
    (* makes the creation of out-of-bound pointer values, Undefined *)
  | SW_strict_pointer_arith
    (* makes reading from uinitialised memory, Undefined *)
  | SW_strict_reads



let internal_ref =
  ref []


let get_switches () =
  !internal_ref

let has_switch sw =
  List.mem sw !internal_ref





let set strs =
  let read_switch = function
    | "strict_pointer_arith" ->
        Some SW_strict_pointer_arith
    | "strict_reads" ->
        Some SW_strict_reads
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
