(* Extract location marks from a pretty printer Core *)

type t =
  { line: int;
    col:  int;
  }

let mk (l, c) =
  { line= l;
    col=  c;
  }

type range =
  { init:  t;
    final: t;
  }

let mk_line (l0, l) =
  { init=  mk (l0, 0);
    final= mk (l,  0);
  }

let range_cmp l1 l2 =
  if l1.init.line = l2.init.line then
    if l1.final.line = l2.final.line then
      if l1.init.col = l2.init.col then
        l1.final.col - l2.final.col
      else l1.init.col - l2.init.col
    else l1.final.line - l2.final.line
  else l1.init.line - l2.init.line

let sort locs =
  List.sort (fun ls1 ls2 -> range_cmp (fst ls1) (fst ls2)) locs

(* Parse location markers: {-#dd:dd-dd:dd:#-} *)
let parse str =
  try
    match List.map int_of_string (Str.split (Str.regexp "[{}#:-]+") str) with
    | [il; ic; fi; fc] ->
      Some { init=  mk (il-1, ic-1);
             final= mk (fi-1, fc-1);
           }
    | _ -> None
  with _ -> None

let json_of_range l =
  let json_of_point l =
    Json.Map [("line", Json.Int l.line); ("ch", Json.Int l.col)]
  in
  Json.Map [("begin", json_of_point l.init); ("end", json_of_point l.final)]

let json_of locs = Json.Array
  (List.fold_left (
    fun (jss, i) (cloc, coreloc) ->
      let js = Json.Map [
          ("c", json_of_range cloc);
          ("core", json_of_range coreloc);
          ("color", Json.Int i);
        ]
      in (js::jss, i+1)
  ) ([], 1) (sort locs)
  |> fst)

(* Retrieve locations in core *)
let extract core =
  let count_lines str =
    let n = ref 0 in
    String.iter (fun c -> if c == '\n' then n := !n + 1) str; !n
  in
  (* Stack using lists *)
  let push sp x = x::sp
  in
  let pop = function
    | x::sp -> (x, sp)
    | [] -> raise (Failure "popping an empty stack")
  in
  (* chunks - of core source
   * locs   - pair of c location and core location
   * sp     - stack of visited location marks
   * l0     - line of last visited location mark
   * l      - current line
   **)
  try
    let rec loop (chunks, locs) sp l0 l = function
      | [] -> (String.concat "" (List.rev chunks), locs)
      | res::rest -> match res with
        (* if chunk, add to chunks *)
        | Str.Text chunk ->
          loop (chunk::chunks, locs) sp l0 (l+(count_lines chunk)) rest
        (* if location mark then ... *)
        | Str.Delim loc  ->
          (* if end mark then pop last location and save it in locs *)
          if String.compare loc "{-#ELOC#-}" = 0 then
            match pop sp with
            | ((Some c_loc, l0'), sp') ->
              loop (chunks, (c_loc, mk_line (l0, l))::locs) sp' l0' l rest
            | ((None, l0'), sp') ->
              loop (chunks, locs) sp' l0' l rest
          else
            let loc_no_unicode =
              Str.replace_first (Str.regexp_string "§") "" loc
            in loop (chunks, locs) (push sp (parse loc_no_unicode, l0)) l l rest
    in
    let (core', ls) = Str.full_split (Str.regexp "{-#[^#§]*#-}") core
                  |> loop ([], []) [] 0 0
    in (core', json_of ls)
  with
  | Not_found ->
    print_endline "parse_core: Not_found"; (core, json_of [])
  | Invalid_argument err ->
    print_endline ("parse_core: Invalid argument " ^ err); (core, json_of [])
  | Failure err ->
    print_endline ("parse_core: Failure " ^ err); (core, json_of [])
  | _ -> print_endline "parse_core: Fatal"; (core, json_of [])
