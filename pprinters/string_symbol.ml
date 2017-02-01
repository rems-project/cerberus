open Symbol
open Pp_symbol

let string_of_prefix pref =
  Pp_utils.to_plain_string (pp_prefix pref)
