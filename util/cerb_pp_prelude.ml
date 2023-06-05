module P = PPrint

let (!^)  = P.(!^)
let (^^)  = P.(^^)
let (^/^) = P.(^/^)
let (^//^) = P.(^//^)

let (^^^) x y =
(* TODO, was:        x ^^ P.space ^^ y *)
  if P.requirement y = 0 then
    x
  else
    x ^^ P.space ^^ y


(*let comma_list f = P.separate_map (P.comma ^^ P.space) f *)
let comma_list f xs = P.flow (P.comma ^^ P.break 1) (List.map f xs)
(*let semi_list f  = P.separate_map (P.semi ^^ P.space) f*)
let semi_list f xs  = P.flow (P.semi ^^ P.break 1) (List.map f xs)


let with_grouped_arg d1 d2 =
  P.ifflat (d1 ^^ P.parens d2)
    (d1 ^^ P.parens (P.nest 2 (P.hardline ^^ d2) ^^ P.hardline))

let with_grouped_args ?(sep=P.comma) d1 ds =
  P.ifflat (d1 ^^ P.parens (P.separate (sep ^^ P.space) ds))
    (d1 ^^ P.parens (P.separate_map P.comma (fun z -> P.nest 2 (P.hardline ^^ z) ^^ P.hardline) ds))