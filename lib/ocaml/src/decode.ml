open Num

(* NOTE: a properly formed C integer-constant *)
let decode_integer_constant str =
  let read_digit = function
    | 'a' | 'A' -> 10
    | 'b' | 'B' -> 11
    | 'c' | 'C' -> 12
    | 'd' | 'D' -> 13
    | 'e' | 'E' -> 14
    | 'f' | 'F' -> 15
    | n         -> int_of_char n - int_of_char '0' in
  let (str, basisN, basis) =
    if str.[0] = '0' then
      let l = String.length str in
      if String.length str > 1 && (str.[1] = 'x' || str.[1] = 'X') then
        (String.sub str 2 (l-2), 16, Ail.HEXADECIMAL)
      else
        (String.sub str 1 (l-1), 8, Ail.OCTAL)
    else
      (str, 10, Ail.DECIMAL) in
  let l = String.length str in
  let ret = ref (num_of_int 0) in
  String.iteri (fun i c -> ret := (num_of_int (read_digit c)) */ (power_num (num_of_int basisN) (num_of_int (l - i - 1))) +/ !ret) str;
  (!ret, basis)


let decode_character_constant c =
(*
  | "A"
  | "B"
BCDEFGHIJKLM NOPQRSTUVWXYZ
*)


  print_endline c;
  assert false
