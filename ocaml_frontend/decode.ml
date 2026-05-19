module Z = struct
  include Z
  let integerRem_f = Big_int_Z.mod_big_int
end

(* NOTE: a properly formed C integer-constant *)
(* TODO: this explodes if the string is empty *)
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
      if String.length str > 1 then
        begin match str.[1] with
          | 'x' | 'X' ->
            (String.sub str 2 (l-2), 16, AilSyntax.Hexadecimal)
          | 'b' | 'B' ->
            (String.sub str 2 (l-2), 2, AilSyntax.Binary)
          | _ ->
            (String.sub str 1 (l-1), 8, AilSyntax.Octal)
        end
      else
        (String.sub str 1 (l-1), 8, AilSyntax.Octal)
    else
      (str, 10, AilSyntax.Decimal) in
  let l = String.length str in
  let ret = ref Z.zero in
  String.iteri (fun i c ->
    ret := Z.add (Z.mul (Z.of_int (read_digit c)) (Z.pow (Z.of_int basisN) ((l - i - 1)))) !ret) str;
  (basis, !ret)




(* TODO: making the implementation choice of using ASCII for now *)
let decode_character_constant_aux = function
  (* NOTE: first there are the "basic source and basic execution sets" (see §5.2.1#2) *)
  (* uppercases letters *)
  | "A" -> Z.of_int 65
  | "B" -> Z.of_int 66
  | "C" -> Z.of_int 67
  | "D" -> Z.of_int 68
  | "E" -> Z.of_int 69
  | "F" -> Z.of_int 70
  | "G" -> Z.of_int 71
  | "H" -> Z.of_int 72
  | "I" -> Z.of_int 73
  | "J" -> Z.of_int 74
  | "K" -> Z.of_int 75
  | "L" -> Z.of_int 76
  | "M" -> Z.of_int 77
  | "N" -> Z.of_int 78
  | "O" -> Z.of_int 79
  | "P" -> Z.of_int 80
  | "Q" -> Z.of_int 81
  | "R" -> Z.of_int 82
  | "S" -> Z.of_int 83
  | "T" -> Z.of_int 84
  | "U" -> Z.of_int 85
  | "V" -> Z.of_int 86
  | "W" -> Z.of_int 87
  | "X" -> Z.of_int 88
  | "Y" -> Z.of_int 89
  | "Z" -> Z.of_int 90
  
  (* lowercase letters *)
  | "a" -> Z.of_int 97
  | "b" -> Z.of_int 98
  | "c" -> Z.of_int 99
  | "d" -> Z.of_int 100
  | "e" -> Z.of_int 101
  | "f" -> Z.of_int 102
  | "g" -> Z.of_int 103
  | "h" -> Z.of_int 104
  | "i" -> Z.of_int 105
  | "j" -> Z.of_int 106
  | "k" -> Z.of_int 107
  | "l" -> Z.of_int 108
  | "m" -> Z.of_int 109
  | "n" -> Z.of_int 110
  | "o" -> Z.of_int 111
  | "p" -> Z.of_int 112
  | "q" -> Z.of_int 113
  | "r" -> Z.of_int 114
  | "s" -> Z.of_int 115
  | "t" -> Z.of_int 116
  | "u" -> Z.of_int 117
  | "v" -> Z.of_int 118
  | "w" -> Z.of_int 119
  | "x" -> Z.of_int 120
  | "y" -> Z.of_int 121
  | "z" -> Z.of_int 122
  
  (* digits *)
  | "0" -> Z.of_int 48
  | "1" -> Z.of_int 49
  | "2" -> Z.of_int 50
  | "3" -> Z.of_int 51
  | "4" -> Z.of_int 52
  | "5" -> Z.of_int 53
  | "6" -> Z.of_int 54
  | "7" -> Z.of_int 55
  | "8" -> Z.of_int 56
  | "9" -> Z.of_int 57
  
  (* graphic characters *)
  | "!"    -> Z.of_int 33
  | "\"" | "\\\""   -> Z.of_int 34 (* TODO: check *)
  | "#"    -> Z.of_int 35
  | "%"    -> Z.of_int 37
  | "&"    -> Z.of_int 38
  | "'" | "\\'"   -> Z.of_int 39 (* TODO: check *)
  | "("    -> Z.of_int 40
  | ")"    -> Z.of_int 41
  | "*"    -> Z.of_int 42
  | "+"    -> Z.of_int 43
  | ","    -> Z.of_int 44
  | "-"    -> Z.of_int 45
  | "."    -> Z.of_int 46
  | "/"    -> Z.of_int 47
  | ":"    -> Z.of_int 58
  | ";"    -> Z.of_int 59
  | "<"    -> Z.of_int 60
  | "="    -> Z.of_int 61
  | ">"    -> Z.of_int 62
  | "?"    -> Z.of_int 63
  | "["    -> Z.of_int 91
  | "\\\\" -> Z.of_int 92
  | "]"    -> Z.of_int 93
  | "^"    -> Z.of_int 94
  | "_"    -> Z.of_int 95
  | "{"    -> Z.of_int 123
  | "|"    -> Z.of_int 124
  | "}"    -> Z.of_int 125
  | "~"    -> Z.of_int 126
  
  | " "    -> Z.of_int 32
  | "\t"   -> Z.of_int 9
  
  (* §5.2.2#2 *)
  | "\\a"   -> Z.of_int 7
  | "\\b"   -> Z.of_int 8
  | "\\f"   -> Z.of_int 12
  | "\\n"   -> Z.of_int 10
  | "\\r"   -> Z.of_int 13
  | "\\t"   -> Z.of_int 9
  | "\\v"   -> Z.of_int 11

  (* NOTE: here are the (graphical) extended characters from ASCII *)
  | "$"     -> Z.of_int 36
  | "@"     -> Z.of_int 64
  | "`"     -> Z.of_int 96
  
  | str ->
      if String.length str = 0 then
        failwith "decode_character_constant: empty constant"
      else
        if String.get str 0 = '\\' then
          if String.length str = 1 then
            failwith "decode_character_constant, invalid constant: '\\'"
          else
            if String.get str 1 = 'x' then
              if String.length str = 2 then
                failwith "decode_character_constant, invalid constant: '\\x'"
              else
                (* Hexadecimal escape sequence *)
                (* see STD §6.4.4.4#9 *)
                let str = String.sub str 2 (String.length str - 2) in
                let b = ref true in
                String.iter (fun c ->
                  let n = Char.code c in
                  if not (48 <= n && n <= 57 || 65 <= n && n <= 70 || 97 <= n && n <= 102) then
                    b := false
                ) str;
                if !b then
                  snd (decode_integer_constant ("0x" ^ str))
                else
                  failwith ("decode_character_constant, started like an hexa constant, but failed: " ^ str)
            else
                let str = String.sub str 1 (String.length str - 1) in
                let b = ref true in
                String.iter (fun c ->
                  let n = Char.code c in
                  if not (48 <= n && n <= 56) then
                    b := false
                ) str;
                if !b then
                  snd (decode_integer_constant ("0" ^ str))
                else
                  failwith ("decode_character_constant, started like an octal constant, but failed: " ^ str)
        else
          failwith ("decode_character_constant: invalid char constant ==> " ^ str)

let decode_character_constant str =
  let open Ocaml_implementation in
  let open Z in
  let impl = get () in
  (* let Some sz = impl.sizeof_ity Ctype.Char in *)
  let (min, max) =
    if impl.is_signed_ity Ctype.Char then
      (neg (pow (of_int 2) Stdlib.(8-1)), sub (pow (of_int 2) Stdlib.(8-1)) (of_int 1))
    else
      (zero, sub (pow (of_int 2) (8)) (of_int 1)) in
  let wrapI n =
    let dlt = succ (sub max min) in
    let r = integerRem_f n dlt in
    if leq r max then
      r
    else
      sub r dlt in
  wrapI (decode_character_constant_aux str)

let escaped_char c =
  Char.escaped c

let encode_character_constant n =
  (* TODO: fixing the encoding to ASCII for now *)
  Char.chr (Z.to_int n land 0xff)

(* formats a float for a given precision (used by formatted.lem) *)
let format_string_of_float prec f =
  (* TODO: maybe best to reimplement this ourselves at some point
     insted of using OCaml's printf *)
  let fmt = Scanf.format_from_string ("%." ^ string_of_int prec ^ "f") "%f" in
  Printf.sprintf fmt f