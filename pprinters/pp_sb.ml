open Global
open Sb

module P = PPrint

let (!^ ) = P.(!^)
let (^^)  = P.(^^)

let (^^^) x y = x ^^ P.space ^^ y




let string_of_trace_action tact =
  let f o =
    "[\\text{" ^ (Boot.to_plain_string $ PPrint.separate_map PPrint.dot
                   (fun x -> PPrint.string (Pp_run.string_of_sym x)) (fst o)) ^ "}]" in
  match tact with
    | Core_run.Tcreate (ty, o) ->
        f o ^ " \\Leftarrow {\\color{red}\\mathbf{C}_\\text{" ^ (Boot.to_plain_string $ Pp_core.pp_ctype ty) ^ "}}"
    | Core_run.Talloc (n, o) ->
        f o ^ " \\Leftarrow {\\color{red}\\mathbf{A}_\\text{" ^ Num.string_of_num n ^ "}}"
    | Core_run.Tkill o ->
        "{\\color{red}\\mathbf{K}} " ^ f o
    | Core_run.Tstore (ty, o, n, mo) ->
        "{\\color{red}\\mathbf{S}_\\text{" ^ (Boot.to_plain_string $ Pp_core.pp_ctype ty) ^ "}} " ^ f o ^
          " := " ^ Pp_run.string_of_mem_value n ^ 
          ", " ^ (Boot.to_plain_string $ Pp_core.pp_memory_order mo)
    | Core_run.Tload (ty, o, v, mo) ->
        "{\\color{red}\\mathbf{L}_\\text{" ^ (Boot.to_plain_string $ Pp_core.pp_ctype ty) ^ "}} " ^
          f o ^ " = " ^ Pp_run.string_of_mem_value v ^ 
          ", " ^ (Boot.to_plain_string $ Pp_core.pp_memory_order mo)


let pp n sb =
  !^ ("digraph G" ^ string_of_int n) ^^ P.braces
    (P.separate_map (P.semi ^^ P.break 1) (fun (i, a) ->
      !^ (string_of_int i) ^^^ P.brackets (!^ "label=" ^^^ (P.dquotes $ !^ (string_of_int i) ^^ P.colon ^^^ !^ (string_of_trace_action a))))
       (Pmap.bindings sb.actions) ^^ P.break 1 ^^
       
       P.separate_map (P.semi ^^ P.break 1) (fun (i, i') ->
         !^ (string_of_int i) ^^^ !^ "->" ^^^ !^ (string_of_int i'))
       sb.edges)
