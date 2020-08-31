open Pp
module SymSet = Set.Make(Sym)


module NoReturn : ArgumentTypes.RSig = struct
  type t = Bot
  let subst_var _subst Bot = Bot
  let free_vars Bot = SymSet.empty
  let instantiate_struct_member _subst Bot = Bot
  let pp Bot = if !unicode then !^"\u{22A5}" else !^"bot"
end

include ArgumentTypes.Make(NoReturn)
