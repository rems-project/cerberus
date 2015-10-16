open Global
open Sb

module P = PPrint

let ($) f x = f x
let (-|) f g x = f (g x)


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
  
  let pp_ctype ty        = escape_underscores $ Boot_pprint.to_plain_string (Pp_core.pp_ctype ty) in
  let pp_memory_order mo = escape_underscores $ Boot_pprint.to_plain_string (Pp_core.pp_memory_order mo) in
  
  match tact with
    | Core_run_effect.Tcreate (ty, o, tid) ->
        f o ^ " \\Leftarrow {\\color{red}\\mathbf{C}_\\text{" ^ pp_ctype ty ^ "}}"
    | Core_run_effect.Talloc (n, o, tid) ->
        f o ^ " \\Leftarrow {\\color{red}\\mathbf{A}_\\text{" ^ Nat_big_num.to_string n ^ "}}"
    | Core_run_effect.Tkill (o, tid) ->
        "{\\color{red}\\mathbf{K}} " ^ f o
    | Core_run_effect.Tstore (ty, o, n, mo, tid) ->
        "{\\color{red}\\mathbf{S}_\\text{" ^ pp_ctype ty ^
          ", " ^ pp_memory_order mo ^ "}} " ^ f o ^
          " := " ^ Pp_run.string_of_mem_value n
    | Core_run_effect.Tload (ty, o, v, mo, tid) ->
        "{\\color{red}\\mathbf{L}_\\text{" ^ pp_ctype ty ^
          ", " ^ pp_memory_order mo ^ "}} " ^
          f o ^ " = " ^ Pp_run.string_of_mem_value v
    | Core_run_effect.Trmw (ty ,o, e, d, mo, tid) ->
        "{\\color{red}\\mathbf{RMW}_\\text{" ^ pp_ctype ty ^
          ", " ^ pp_memory_order mo ^ "}} " ^
          f o ^ " = " ^ Pp_run.string_of_mem_value e ^
          " \\Rightarrow " ^
          f o ^ " := " ^ Pp_run.string_of_mem_value d





let pp n g =
  let threads =
    List.fold_left (fun acc (aid, act) ->
      let tid = Core_run_effect.tid_of act in
      Pmap.add tid ((aid, act) :: if Pmap.mem tid acc then Pmap.find tid acc else []) acc
    ) (Pmap.empty Pervasives.compare) $ Pmap.bindings_list g.actions in
  
  let pp_relation rel col =
    P.separate_map (P.semi ^^ P.break 1) (fun (i, i') ->
      !^ (Nat_big_num.to_string i) ^^^ !^ "->" ^^^ !^ (Nat_big_num.to_string i') ^^^
        P.brackets (!^ "color" ^^ P.equals ^^ P.dquotes !^ col)) rel ^^ if List.length rel > 0 then P.semi else P.empty in
  
  !^ ("digraph G" ^ string_of_int n) ^^ P.braces
    (P.concat_map (fun (tid, acts) ->
      !^ ("subgraph cluster_" ^ Pp_run.string_of_thread_id tid) ^^ P.braces
        (!^ "label" ^^ P.equals ^^ P.dquotes !^ ("\\mathbf{thread}_{" ^ (Pp_run.string_of_thread_id tid) ^ "}") ^^ P.semi ^^
        !^ "style=filled;color=lightgrey; node [shape=box,style=filled,color=white];" ^^
        P.separate_map P.semi (fun (aid, act) -> 
          !^ (Nat_big_num.to_string aid) ^^ P.brackets (!^ "label=" ^^ (P.dquotes $ !^ (Nat_big_num.to_string aid) ^^ P.colon ^^^ !^ (string_of_trace_action act)))
        ) acts)
     ) (Pmap.bindings_list threads) ^^ P.semi ^^ P.break 1 ^^
     
     pp_relation g.sb1  "black"       ^^ P.break 1 ^^
     pp_relation g.asw1 "DeepPink4"   ^^ P.break 1 ^^
     pp_relation g.rf1  "red"         ^^ P.break 1 ^^
     pp_relation g.mo1  "blue"        ^^ P.break 1 ^^
     pp_relation g.sc1  "orange"      ^^ P.break 1 ^^
     pp_relation g.hb  "ForestGreen"
    )
