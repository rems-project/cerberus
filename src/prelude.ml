let error ?(code = 1) msg =
  prerr_endline Colour.(ansi_format [Red] ("ERROR: " ^ msg));
  exit code


type mem_setting =
  [ `MemDefacto | `MemConcrete ]

(* TODO: I hate this. And it doesn't even work ... *)
let mem_switch: mem_setting ref =
(*  ref `MemDefacto *)
  ref `MemConcrete
