let ($) f x = f x
let (-|) f g x = f (g x)
let (>?>) x b f g = if b then f x else g x


(* Requires ocaml at least 4.00.0 *)
(* let (>|>) x f = f x *)
external (|>) : 'a -> ('a -> 'b) -> 'b = "%revapply"



(* use this to print a fatal error message *)
let error str =
  prerr_endline $ Colour.ansi_format [Colour.Red] ("ERROR: " ^ str);
  exit 1


let debug_print str =
  if !Boot_ocaml.debug_level > 0 then
    print_endline str
