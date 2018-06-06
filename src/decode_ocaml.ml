
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
      if String.length str > 1 && (str.[1] = 'x' || str.[1] = 'X') then
        (String.sub str 2 (l-2), 16, AilSyntax.Hexadecimal)
      else
        (String.sub str 1 (l-1), 8, AilSyntax.Octal)
    else
      (str, 10, AilSyntax.Decimal) in
  let l = String.length str in
  let ret = ref (Nat_big_num.of_int 0) in
  String.iteri (fun i c ->
    ret := Nat_big_num.add (Nat_big_num.mul (Nat_big_num.of_int (read_digit c)) (Nat_big_num.pow_int_positive basisN ((l - i - 1)))) !ret) str;
  (basis, !ret)




(* TODO: making the implementation choice of using ASCII for now *)
let decode_character_constant = function
  (* NOTE: first there are the "basic source and basic execution sets" (see §5.2.1#2) *)
  (* uppercases letters *)
  | "A" -> Nat_big_num.of_int 65
  | "B" -> Nat_big_num.of_int 66
  | "C" -> Nat_big_num.of_int 67
  | "D" -> Nat_big_num.of_int 68
  | "E" -> Nat_big_num.of_int 69
  | "F" -> Nat_big_num.of_int 70
  | "G" -> Nat_big_num.of_int 71
  | "H" -> Nat_big_num.of_int 72
  | "I" -> Nat_big_num.of_int 73
  | "J" -> Nat_big_num.of_int 74
  | "K" -> Nat_big_num.of_int 75
  | "L" -> Nat_big_num.of_int 76
  | "M" -> Nat_big_num.of_int 77
  | "N" -> Nat_big_num.of_int 78
  | "O" -> Nat_big_num.of_int 79
  | "P" -> Nat_big_num.of_int 80
  | "Q" -> Nat_big_num.of_int 81
  | "R" -> Nat_big_num.of_int 82
  | "S" -> Nat_big_num.of_int 83
  | "T" -> Nat_big_num.of_int 84
  | "U" -> Nat_big_num.of_int 85
  | "V" -> Nat_big_num.of_int 86
  | "W" -> Nat_big_num.of_int 87
  | "X" -> Nat_big_num.of_int 88
  | "Y" -> Nat_big_num.of_int 89
  | "Z" -> Nat_big_num.of_int 90
  
  (* lowercase letters *)
  | "a" -> Nat_big_num.of_int 97
  | "b" -> Nat_big_num.of_int 98
  | "c" -> Nat_big_num.of_int 99
  | "d" -> Nat_big_num.of_int 100
  | "e" -> Nat_big_num.of_int 101
  | "f" -> Nat_big_num.of_int 102
  | "g" -> Nat_big_num.of_int 103
  | "h" -> Nat_big_num.of_int 104
  | "i" -> Nat_big_num.of_int 105
  | "j" -> Nat_big_num.of_int 106
  | "k" -> Nat_big_num.of_int 107
  | "l" -> Nat_big_num.of_int 108
  | "m" -> Nat_big_num.of_int 109
  | "n" -> Nat_big_num.of_int 110
  | "o" -> Nat_big_num.of_int 111
  | "p" -> Nat_big_num.of_int 112
  | "q" -> Nat_big_num.of_int 113
  | "r" -> Nat_big_num.of_int 114
  | "s" -> Nat_big_num.of_int 115
  | "t" -> Nat_big_num.of_int 116
  | "u" -> Nat_big_num.of_int 117
  | "v" -> Nat_big_num.of_int 118
  | "w" -> Nat_big_num.of_int 119
  | "x" -> Nat_big_num.of_int 120
  | "y" -> Nat_big_num.of_int 121
  | "z" -> Nat_big_num.of_int 122
  
  (* digits *)
  | "0" -> Nat_big_num.of_int 48
  | "1" -> Nat_big_num.of_int 49
  | "2" -> Nat_big_num.of_int 50
  | "3" -> Nat_big_num.of_int 51
  | "4" -> Nat_big_num.of_int 52
  | "5" -> Nat_big_num.of_int 53
  | "6" -> Nat_big_num.of_int 54
  | "7" -> Nat_big_num.of_int 55
  | "8" -> Nat_big_num.of_int 56
  | "9" -> Nat_big_num.of_int 57
  
  (* graphic characters *)
  | "!"    -> Nat_big_num.of_int 33
  | "\"" | "\\\""   -> Nat_big_num.of_int 34 (* TODO: check *)
  | "#"    -> Nat_big_num.of_int 35
  | "%"    -> Nat_big_num.of_int 37
  | "&"    -> Nat_big_num.of_int 38
  | "'" | "\\'"   -> Nat_big_num.of_int 39 (* TODO: check *)
  | "("    -> Nat_big_num.of_int 40
  | ")"    -> Nat_big_num.of_int 41
  | "*"    -> Nat_big_num.of_int 42
  | "+"    -> Nat_big_num.of_int 43
  | ","    -> Nat_big_num.of_int 44
  | "-"    -> Nat_big_num.of_int 45
  | "."    -> Nat_big_num.of_int 46
  | "/"    -> Nat_big_num.of_int 47
  | ":"    -> Nat_big_num.of_int 58
  | ";"    -> Nat_big_num.of_int 59
  | "<"    -> Nat_big_num.of_int 60
  | "="    -> Nat_big_num.of_int 61
  | ">"    -> Nat_big_num.of_int 62
  | "?"    -> Nat_big_num.of_int 63
  | "["    -> Nat_big_num.of_int 91
  | "\\\\" -> Nat_big_num.of_int 92
  | "]"    -> Nat_big_num.of_int 93
  | "^"    -> Nat_big_num.of_int 94
  | "_"    -> Nat_big_num.of_int 95
  | "{"    -> Nat_big_num.of_int 123
  | "|"    -> Nat_big_num.of_int 124
  | "}"    -> Nat_big_num.of_int 125
  | "~"    -> Nat_big_num.of_int 126
  
  | " "    -> Nat_big_num.of_int 32
  
  (* §5.2.2#2 *)
  | "\\a"   -> Nat_big_num.of_int 7
  | "\\b"   -> Nat_big_num.of_int 8
  | "\\f"   -> Nat_big_num.of_int 12
  | "\\n"   -> Nat_big_num.of_int 10
  | "\\r"   -> Nat_big_num.of_int 13
  | "\\t"   -> Nat_big_num.of_int 9
  | "\\v"   -> Nat_big_num.of_int 11

  (* NOTE: here are the (graphical) extended characters from ASCII *)
  | "$"     -> Nat_big_num.of_int 36
  | "@"     -> Nat_big_num.of_int 64
  | "`"     -> Nat_big_num.of_int 96
  
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
          failwith "decode_character_constant: invalid char constant"


let encode_character_constant n =
  (* TODO: fixing the encoding to ASCII for now *)
(*  Printf.printf "ENCODING %s\n" (Nat_big_num.to_string n); *)
  Char.chr (Nat_big_num.to_int n)
