module P = PPrint

let (!^)  = P.(!^)
let (^^)  = P.(^^)
let (^/^) = P.(^/^)

let (^^^) x y = x ^^ P.space ^^ y
let comma_list f = P.separate_map (P.comma ^^ P.space) f
let semi_list f  = P.separate_map (P.semi ^^ P.space) f
