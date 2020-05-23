open PPrint
open Pp_tools

type t = {arguments: Types.t; return: Types.t}

let subst_var subst ft = 
  { arguments = Types.subst_var subst ft.arguments;
    return = Types.subst_var subst ft.return }

let subst_vars = Tools.make_substs subst_var

let pp ft = flow (break 1) [Types.pp ft.arguments;arrow;Types.pp ft.return]


let make arguments return = {arguments; return}
