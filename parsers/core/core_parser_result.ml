(* ... *)
type result =
  | Rfile of Core.sym * (Global.zero Core.fun_map)
  | Rstd  of Global.zero Core.fun_map
  | Rimpl of Global.zero Core.impl
