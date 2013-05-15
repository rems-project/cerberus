open Global
open Sb

module P = PPrint

let (!^ ) = P.(!^)
let (^^)  = P.(^^)

let (^^^) x y = x ^^ P.space ^^ y


let pp n sb =
  !^ ("digraph G" ^ string_of_int n) ^^ P.braces
    (P.separate_map (P.semi ^^ P.break 1) (fun (i, a) ->
      !^ (string_of_int i) ^^^ P.brackets (!^ "label=" ^^^ (P.dquotes $ !^ (string_of_int i) ^^ P.colon ^^^ !^ (Pp_run.string_of_trace_action a))))
       (Pmap.bindings sb.actions) ^^ P.break 1 ^^
       
       P.separate_map (P.semi ^^ P.break 1) (fun (i, i') ->
         !^ (string_of_int i) ^^^ !^ "->" ^^^ !^ (string_of_int i'))
       sb.edges)
