open Global
open Sb

module P = PPrint

let (!^ ) = P.(!^)
let (^^)  = P.(^^)

let (^^^) x y = x ^^ P.space ^^ y





let escape_underscores str =
  let occurences = ref 0 in
  String.iter (fun c ->
    if c == '_' then occurences := !occurences + 1
  ) str;
  let str' = String.create (String.length str + !occurences) in
  let shift = ref 0 in
  String.iteri (fun i c ->
    if c == '_' then (
      String.set str' (i + !shift) '\\';
      shift := !shift + 1;
    );
    String.set str' (i + !shift) c;
  ) str;
  str'



let string_of_trace_action tact =
  let f o =
    "[\\text{" ^ String.concat "." (List.map Pp_run.string_of_sym $ fst o) ^ "}]" in
  
  let pp_ctype ty        = escape_underscores $ Boot.to_plain_string (Pp_core.pp_ctype ty) in
  let pp_memory_order mo = escape_underscores $ Boot.to_plain_string (Pp_core.pp_memory_order mo) in
  
  match tact with
    | Core_run.Tcreate (ty, o, tid) ->
        f o ^ " \\Leftarrow {\\color{red}\\mathbf{C}_\\text{" ^ pp_ctype ty ^ "}}" ^
          " on thread " ^ (Pp_run.string_of_thread_id tid)
    | Core_run.Talloc (n, o, tid) ->
        f o ^ " \\Leftarrow {\\color{red}\\mathbf{A}_\\text{" ^ Num.string_of_num n ^ "}}" ^
          " on thread " ^ (Pp_run.string_of_thread_id tid)
    | Core_run.Tkill (o, tid) ->
        "{\\color{red}\\mathbf{K}} " ^ f o ^
          " on thread " ^ (Pp_run.string_of_thread_id tid)
    | Core_run.Tstore (ty, o, n, mo, tid) ->
        "{\\color{red}\\mathbf{S}_\\text{" ^ pp_ctype ty ^ 
          ", " ^ pp_memory_order mo ^ "}} " ^ f o ^
          " := " ^ Pp_run.string_of_mem_value n ^
          " on thread " ^ (Pp_run.string_of_thread_id tid)
    | Core_run.Tload (ty, o, v, mo, tid) ->
        "{\\color{red}\\mathbf{L}_\\text{" ^ pp_ctype ty ^ 
          ", " ^ pp_memory_order mo ^ "}} " ^
          f o ^ " = " ^ Pp_run.string_of_mem_value v ^
          " on thread " ^ (Pp_run.string_of_thread_id tid)





let pp n g =
  let f rel col =
    P.separate_map (P.semi ^^ P.break 1) (fun (i, i') ->
      !^ (string_of_int i) ^^^ !^ "->" ^^^ !^ (string_of_int i') ^^^
        P.brackets (!^ "color" ^^ P.equals ^^ P.dquotes !^ col)) rel in
  
  !^ ("digraph G" ^ string_of_int n) ^^ P.braces
    (P.separate_map (P.semi ^^ P.break 1) (fun (i, a) ->
      !^ (string_of_int i) ^^^ P.brackets (!^ "label=" ^^^ (P.dquotes $ !^ (string_of_int i) ^^ P.colon ^^^ !^ (string_of_trace_action a))))
       (Pmap.bindings g.actions) ^^ P.break 1 ^^
       
       f g.sb "black" ^^ P.break 1 ^^
       f g.asw "DeepPink4" ^^ P.break 1 ^^
       f g.rf "red" ^^ P.break 1 ^^
       f g.mo "blue" ^^ P.break 1 ^^
       f g.sc "orange" ^^ P.break 1 ^^
       f g.hb "ForestGreen"
)
