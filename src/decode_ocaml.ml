
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
        (String.sub str 2 (l-2), 16, () (* Ail.HEXADECIMAL *))
      else
        (String.sub str 1 (l-1), 8, () (* Ail.OCTAL *))
    else
      (str, 10, () (* Ail.DECIMAL *)) in
  let l = String.length str in
  let ret = ref (Big_int.big_int_of_int 0) in
  String.iteri (fun i c ->
    ret := Big_int.add_big_int (Big_int.mult_big_int (Big_int.big_int_of_int (read_digit c)) (Big_int.power_int_positive_int basisN ((l - i - 1)))) !ret) str;
  (* (!ret, basis) *)
  !ret




(* TODO: making the implementation choice of using ASCII for now *)
let decode_character_constant = function
  (* uppercases letters *)
  | "A" -> Big_int.big_int_of_int 65
  | "B" -> Big_int.big_int_of_int 66
  | "C" -> Big_int.big_int_of_int 67
  | "D" -> Big_int.big_int_of_int 68
  | "E" -> Big_int.big_int_of_int 69
  | "F" -> Big_int.big_int_of_int 70
  | "G" -> Big_int.big_int_of_int 71
  | "H" -> Big_int.big_int_of_int 72
  | "I" -> Big_int.big_int_of_int 73
  | "J" -> Big_int.big_int_of_int 74
  | "K" -> Big_int.big_int_of_int 75
  | "L" -> Big_int.big_int_of_int 76
  | "M" -> Big_int.big_int_of_int 77
  | "N" -> Big_int.big_int_of_int 78
  | "O" -> Big_int.big_int_of_int 79
  | "P" -> Big_int.big_int_of_int 80
  | "Q" -> Big_int.big_int_of_int 81
  | "R" -> Big_int.big_int_of_int 82
  | "S" -> Big_int.big_int_of_int 83
  | "T" -> Big_int.big_int_of_int 84
  | "U" -> Big_int.big_int_of_int 85
  | "V" -> Big_int.big_int_of_int 86
  | "W" -> Big_int.big_int_of_int 87
  | "X" -> Big_int.big_int_of_int 88
  | "Y" -> Big_int.big_int_of_int 89
  | "Z" -> Big_int.big_int_of_int 90
  
  (* lowercase letters *)
  | "a" -> Big_int.big_int_of_int 97
  | "b" -> Big_int.big_int_of_int 98
  | "c" -> Big_int.big_int_of_int 99
  | "d" -> Big_int.big_int_of_int 100
  | "e" -> Big_int.big_int_of_int 101
  | "f" -> Big_int.big_int_of_int 102
  | "g" -> Big_int.big_int_of_int 103
  | "h" -> Big_int.big_int_of_int 104
  | "i" -> Big_int.big_int_of_int 105
  | "j" -> Big_int.big_int_of_int 106
  | "k" -> Big_int.big_int_of_int 107
  | "l" -> Big_int.big_int_of_int 108
  | "m" -> Big_int.big_int_of_int 109
  | "n" -> Big_int.big_int_of_int 110
  | "o" -> Big_int.big_int_of_int 111
  | "p" -> Big_int.big_int_of_int 112
  | "q" -> Big_int.big_int_of_int 113
  | "r" -> Big_int.big_int_of_int 114
  | "s" -> Big_int.big_int_of_int 115
  | "t" -> Big_int.big_int_of_int 116
  | "u" -> Big_int.big_int_of_int 117
  | "v" -> Big_int.big_int_of_int 118
  | "w" -> Big_int.big_int_of_int 119
  | "x" -> Big_int.big_int_of_int 120
  | "y" -> Big_int.big_int_of_int 121
  | "z" -> Big_int.big_int_of_int 122
  
  (* digits *)
  | "0" -> Big_int.big_int_of_int 48
  | "1" -> Big_int.big_int_of_int 49
  | "2" -> Big_int.big_int_of_int 50
  | "3" -> Big_int.big_int_of_int 51
  | "4" -> Big_int.big_int_of_int 52
  | "5" -> Big_int.big_int_of_int 53
  | "6" -> Big_int.big_int_of_int 54
  | "7" -> Big_int.big_int_of_int 55
  | "8" -> Big_int.big_int_of_int 56
  | "9" -> Big_int.big_int_of_int 57
  
  (* graphic characters *)
  | "!"    -> Big_int.big_int_of_int 33
  | "\\\"" -> Big_int.big_int_of_int 34
  | "#"    -> Big_int.big_int_of_int 35
  | "%"    -> Big_int.big_int_of_int 37
  | "&"    -> Big_int.big_int_of_int 38
  | "'"    -> Big_int.big_int_of_int 39
  | "("    -> Big_int.big_int_of_int 40
  | ")"    -> Big_int.big_int_of_int 41
  | "*"    -> Big_int.big_int_of_int 42
  | "+"    -> Big_int.big_int_of_int 43
  | ","    -> Big_int.big_int_of_int 44
  | "-"    -> Big_int.big_int_of_int 45
  | "."    -> Big_int.big_int_of_int 46
  | "/"    -> Big_int.big_int_of_int 47
  | ":"    -> Big_int.big_int_of_int 58
  | ";"    -> Big_int.big_int_of_int 59
  | "<"    -> Big_int.big_int_of_int 60
  | "="    -> Big_int.big_int_of_int 61
  | ">"    -> Big_int.big_int_of_int 62
  | "?"    -> Big_int.big_int_of_int 63
  | "["    -> Big_int.big_int_of_int 91
  | "\\\\" -> Big_int.big_int_of_int 92
  | "]"    -> Big_int.big_int_of_int 93
  | "^"    -> Big_int.big_int_of_int 94
  | "_"    -> Big_int.big_int_of_int 95
  | "{"    -> Big_int.big_int_of_int 123
  | "|"    -> Big_int.big_int_of_int 124
  | "}"    -> Big_int.big_int_of_int 125
  | "~"    -> Big_int.big_int_of_int 126
