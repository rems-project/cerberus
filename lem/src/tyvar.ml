open Format

type t = Ulib.Text.t

let compare r1 r2 = 
  if r1 == r2 then
    0 
  else 
    Ulib.Text.compare r1 r2

let pp ppf s =
  fprintf ppf "'%s" (Ulib.Text.to_string s)

let nth i =
  if i < 26 then
    Ulib.Text.of_char (Char.chr (i+97))
  else
    Ulib.Text.of_latin1 ("a" ^ string_of_int (i-26))

let from_rope s =
  s

let (^) = Ulib.Text.(^^^)

let to_rope s = s
