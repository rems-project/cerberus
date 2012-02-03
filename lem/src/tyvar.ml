open Format

type t = BatRope.t

let compare r1 r2 = 
  if r1 == r2 then
    0 
  else 
    BatRope.compare r1 r2

let pp ppf s =
  fprintf ppf "'%s" (BatRope.to_string s)

let nth i =
  if i < 26 then
    BatRope.of_char (Char.chr (i+97))
  else
    BatRope.of_latin1 ("a" ^ string_of_int (i-26))

let from_rope s =
  s

let (^) = BatRope.(^^^)

let to_rope s = s
