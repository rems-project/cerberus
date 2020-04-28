open Pp_tools

type t = F of {arguments: Types.t; return: Types.t}

let subst sym sym' (F t) = 
  F { arguments = Types.subst sym sym' t.arguments;
      return = Types.subst sym sym' t.return }

let pp (F t) = Types.pp t.arguments ^^^ arrow ^^^ Types.pp t.return


let make arguments return = F {arguments; return}
