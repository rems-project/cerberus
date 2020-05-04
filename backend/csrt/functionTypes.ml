open PPrint
open Pp_tools

type t = {arguments: Types.t; return: Types.t}

let subst sym sym' ft = 
  { arguments = Types.subst sym sym' ft.arguments;
    return = Types.subst sym sym' ft.return }

let pp ft = flow (break 1) [Types.pp ft.arguments;arrow;Types.pp ft.return]


let make arguments return = {arguments; return}
