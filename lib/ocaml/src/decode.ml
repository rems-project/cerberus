open Num

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
        (String.sub str 2 (l-2), 16, Ail.HEXADECIMAL)
      else
        (String.sub str 1 (l-1), 8, Ail.OCTAL)
    else
      (str, 10, Ail.DECIMAL) in
  let l = String.length str in
  let ret = ref (num_of_int 0) in
  String.iteri (fun i c -> ret := (num_of_int (read_digit c)) */ (power_num (num_of_int basisN) (num_of_int (l - i - 1))) +/ !ret) str;
  (!ret, basis)




(* TODO: making the implementation choice of using ASCII for now *)
let decode_character_constant = function
  (* uppercases letters *)
  | "A" -> num_of_int 65
  | "B" -> num_of_int 66
  | "C" -> num_of_int 67
  | "D" -> num_of_int 68
  | "E" -> num_of_int 69
  | "F" -> num_of_int 70
  | "G" -> num_of_int 71
  | "H" -> num_of_int 72
  | "I" -> num_of_int 73
  | "J" -> num_of_int 74
  | "K" -> num_of_int 75
  | "L" -> num_of_int 76
  | "M" -> num_of_int 77
  | "N" -> num_of_int 78
  | "O" -> num_of_int 79
  | "P" -> num_of_int 80
  | "Q" -> num_of_int 81
  | "R" -> num_of_int 82
  | "S" -> num_of_int 83
  | "T" -> num_of_int 84
  | "U" -> num_of_int 85
  | "V" -> num_of_int 86
  | "W" -> num_of_int 87
  | "X" -> num_of_int 88
  | "Y" -> num_of_int 89
  | "Z" -> num_of_int 90
  
  (* lowercase letters *)
  | "a" -> num_of_int 97
  | "b" -> num_of_int 98
  | "c" -> num_of_int 99
  | "d" -> num_of_int 100
  | "e" -> num_of_int 101
  | "f" -> num_of_int 102
  | "g" -> num_of_int 103
  | "h" -> num_of_int 104
  | "i" -> num_of_int 105
  | "j" -> num_of_int 106
  | "k" -> num_of_int 107
  | "l" -> num_of_int 108
  | "m" -> num_of_int 109
  | "n" -> num_of_int 110
  | "o" -> num_of_int 111
  | "p" -> num_of_int 112
  | "q" -> num_of_int 113
  | "r" -> num_of_int 114
  | "s" -> num_of_int 115
  | "t" -> num_of_int 116
  | "u" -> num_of_int 117
  | "v" -> num_of_int 118
  | "w" -> num_of_int 119
  | "x" -> num_of_int 120
  | "y" -> num_of_int 121
  | "z" -> num_of_int 122
  
  (* digits *)
  | "0" -> num_of_int 48
  | "1" -> num_of_int 49
  | "2" -> num_of_int 50
  | "3" -> num_of_int 51
  | "4" -> num_of_int 52
  | "5" -> num_of_int 53
  | "6" -> num_of_int 54
  | "7" -> num_of_int 55
  | "8" -> num_of_int 56
  | "9" -> num_of_int 57
  
  (* graphic characters *)
  | "!"    -> num_of_int 33
  | "\\\"" -> num_of_int 34
  | "#"    -> num_of_int 35
  | "%"    -> num_of_int 37
  | "&"    -> num_of_int 38
  | "'"    -> num_of_int 39
  | "("    -> num_of_int 40
  | ")"    -> num_of_int 41
  | "*"    -> num_of_int 42
  | "+"    -> num_of_int 43
  | ","    -> num_of_int 44
  | "-"    -> num_of_int 45
  | "."    -> num_of_int 46
  | "/"    -> num_of_int 47
  | ":"    -> num_of_int 58
  | ";"    -> num_of_int 59
  | "<"    -> num_of_int 60
  | "="    -> num_of_int 61
  | ">"    -> num_of_int 62
  | "?"    -> num_of_int 63
  | "["    -> num_of_int 91
  | "\\\\" -> num_of_int 92
  | "]"    -> num_of_int 93
  | "^"    -> num_of_int 94
  | "_"    -> num_of_int 95
  | "{"    -> num_of_int 123
  | "|"    -> num_of_int 124
  | "}"    -> num_of_int 125
  | "~"    -> num_of_int 126
