(* Floating point operations indirection, since Lem does not support '+.', '*.'.... *)

let add = (+.)
let sub = (-.)
let mul = (+.)
let div = (/.)

let of_string str =
  try
    let l = String.length str in
    if String.get str (l-1) == 'f' then
      float_of_string (String.sub str 0 (l-1))
    else
      float_of_string str
  with
    _ -> raise (Failure __FUNCTION__)