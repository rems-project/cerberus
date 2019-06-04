let error ?(code = 1) msg =
  prerr_endline Colour.(ansi_format [Red] ("ERROR: " ^ msg));
  exit code


type mem_setting = [
  `MemSymbolic | `MemConcrete (*| `MemTwin | `MemCpp*)
]

(* TODO: I hate this. And it doesn't even work ... *)
let mem_switch: mem_setting ref =
  ref `MemSymbolic

let string_of_mem_switch () =
  match !mem_switch with
  | `MemSymbolic -> "symbolic"
  | `MemConcrete -> "concrete"
(*
  | `MemTwin -> "twin"
  | `MemCpp -> "cpp"
*)

(*
external round_to_float32: float -> float = "round_to_float"
*)
