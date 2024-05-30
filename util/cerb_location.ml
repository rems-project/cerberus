open Lexing

type cursor =
  | NoCursor
  | PointCursor of Lexing.position
  | RegionCursor of Lexing.position * Lexing.position

type t =
  | Loc_unknown
  | Loc_other of string
  | Loc_point of Lexing.position
    (* start, end, cursor *)
  | Loc_region of Lexing.position * Lexing.position * cursor
  | Loc_regions of (Lexing.position * Lexing.position) list * cursor


let unknown =
  Loc_unknown

let is_unknown_location = function
  | Loc_unknown -> true
  | _ -> false

let other str =
  Loc_other str

let point pos =
  Loc_point pos

let region (b, e) cur =
  Loc_region (b, e, cur)

let regions xs cur =
  match xs with
    | [] ->
        failwith "Cerb_location.region, xs must not be []"
    | _ ->
        (* TODO: need to sort the regions *)
        Loc_regions (xs, cur)

let with_cursor = function
  | Loc_unknown
  | Loc_other _
  | Loc_regions ([], NoCursor) ->
      Loc_unknown
  | Loc_point z
  | Loc_region (_, _, PointCursor z)
  | Loc_region (z, _, NoCursor)
  | Loc_regions (_, PointCursor z)
  | Loc_regions ((z,_)::_, NoCursor) ->
      Loc_point z
  | Loc_region (_, _, RegionCursor (b, e)) 
  | Loc_regions (_, RegionCursor (b, e)) ->
      Loc_region (b, e, NoCursor)


(* [with_cursor_from loc1 loc2] makes a new (region location) with the region from loc1
   and the cursor from loc2 if there is one, otherwise uses the beginning of loc2 as the cursor (if possible) *)
let with_cursor_from loc1 loc2 =
  let cursor = match loc2 with
    | Loc_unknown
    | Loc_other _ ->
        NoCursor
    | Loc_point z ->
        PointCursor z
    | Loc_region (start_p, end_p, NoCursor) ->
        RegionCursor (start_p, end_p)
    | Loc_region (_, _, cur) ->
        cur
    | Loc_regions (_, z) ->
        (* not putting a cursor because it seems arbitrary to use the first region *)
        z in
  match loc1 with
    | Loc_unknown ->
        begin match cursor with
          | NoCursor ->
              Loc_unknown
          | PointCursor pos ->
              Loc_point pos
          | RegionCursor (b, e) ->
            Loc_region (b, e, NoCursor)
        end
    | Loc_other str ->
        Loc_other str
    | Loc_point z ->
        Loc_region (z, z, cursor)
    | Loc_region (begin_loc, end_loc, _) ->
        Loc_region (begin_loc, end_loc, cursor)
    | Loc_regions (regions, _) ->
        Loc_regions (regions, cursor)

let from_main_file = function
  | Loc_unknown
  | Loc_other _
  | Loc_regions ([], _) -> false
  | Loc_point pos
  | Loc_region (pos, _, _)
  | Loc_regions ((pos,_)::_, _) ->
    let ext = Filename.extension pos.pos_fname in
    ext = ".c" || ext = ".core"


let outer_bbox xs =
  let (b0, e0) = match xs with
    | [] ->
        assert false
    | (b,e) :: _ ->
        (b,e) in
  let pos_lt pos1 pos2 =
    (* assuming pos_fname are the same *)
    if pos1.pos_lnum = pos2.pos_lnum then
      pos1.pos_cnum < pos2.pos_cnum
    else
      pos1.pos_lnum < pos2.pos_lnum in
  List.fold_left (fun (bAcc, eAcc) (b, e) ->
    ((if pos_lt b bAcc then b else bAcc), (if pos_lt e eAcc then eAcc else e))
  ) (b0, e0) xs


let bbox_location = function
  | [] ->
      Loc_unknown
  | xs ->
      match begin
        List.fold_left (fun (def_loc, acc) loc ->
          match loc with
            | Loc_unknown ->
                (def_loc, acc)
            | Loc_other _ ->
                (loc, acc)
            | Loc_point pos ->
                (def_loc, (pos, pos) :: acc)
            | Loc_region (pos1, pos2, _) ->
                (* invariant from Loc_region is that pos1 <= pos2 *)
                (def_loc, (pos1, pos2) :: acc)
            | Loc_regions (xs, _) ->
                (def_loc, xs @ acc)
        ) (Loc_unknown, []) xs
      end with
        | (loc, []) ->
            loc
        | (_, xs') ->
            let (b, e) = outer_bbox xs' in
            Loc_region (b, e, NoCursor)


let with_regions_and_cursor locs loc_opt =
  let cursor_opt = match loc_opt with
    | Some (Loc_point z) -> PointCursor z
    | Some (Loc_region (_, _, z))
    | Some (Loc_regions (_, z)) -> z
    | _ -> NoCursor
  in
  let pos_of_region = function
    | Loc_point p -> Some (p, p)
    | Loc_region (p1, p2, _) -> Some (p1, p2)
    | _ -> None
  in
  let rec the acc = function
    | Some x::xs -> the (x::acc) xs
    | [] -> Some acc
    | None::_ -> None
  in
  match the [] (List.map pos_of_region locs) with
  | Some regs -> Loc_regions (regs, cursor_opt)
  | None -> Loc_unknown


let to_cartesian loc =
  let point_of_pos pos = Lexing.(pos.pos_lnum-1, pos.pos_cnum-pos.pos_bol) in
  match loc with
    | Loc_point p -> Some (point_of_pos p, (0,0))
    | Loc_region (p1, p2, _) -> Some (point_of_pos p1, point_of_pos p2)
    | _ -> None

let location_to_string ?(charon=false) loc =
  let string_of_pos ?(shrink=false) pos =
    if shrink || (charon && from_main_file loc) then
      Printf.sprintf "%d:%d" pos.pos_lnum (1+pos.pos_cnum-pos.pos_bol)
    else
      Printf.sprintf "%s:%d:%d" pos.pos_fname pos.pos_lnum (1+pos.pos_cnum-pos.pos_bol) in
  let shrink z =
    if charon && from_main_file loc then
      ""
    else
      z in
  match loc with
    | Loc_unknown ->
        "unknown location"
    | Loc_other str ->
        "other_location(" ^ str ^ ")"
    | Loc_point pos ->
        string_of_pos pos ^ ":"
    | Loc_region (pos1, pos2, pos_opt) ->
        string_of_pos pos1 ^ "-" ^
        begin if pos1.pos_fname = pos2.pos_fname then
          ""
        else
          shrink pos2.pos_fname
        end ^
        begin if pos1.pos_lnum = pos2.pos_lnum then
          ""
        else
          string_of_int pos2.pos_lnum ^ ":"
        end ^
        string_of_int (1+pos2.pos_cnum-pos2.pos_bol)
        ^ begin match pos_opt with
          | NoCursor -> ""
          | PointCursor pos -> " (cursor: " ^ string_of_pos ~shrink:true pos ^ ")"
          | RegionCursor (b, e) -> " (cursor: " ^ string_of_pos ~shrink:true b ^ " - " ^ string_of_pos ~shrink:true e ^ ")"
        end
    | Loc_regions (xs, _) ->
        let (pos1, pos2) = outer_bbox xs in
        string_of_pos pos1 ^ "-" ^
        begin if pos1.pos_fname = pos2.pos_fname then
          ""
        else
          shrink pos2.pos_fname
        end ^
        begin if pos1.pos_lnum = pos2.pos_lnum then
          ""
        else
          string_of_int pos2.pos_lnum ^ ":"
        end ^
        string_of_int (1+pos2.pos_cnum-pos2.pos_bol)



module P = PPrint
open Cerb_pp_prelude

let print_location loc =
  let print_lex pos =
    !^"RT.position" ^^^ P.dquotes !^(pos.Lexing.pos_fname)
    ^^^ !^(string_of_int pos.Lexing.pos_lnum)
    ^^^ !^(string_of_int pos.Lexing.pos_bol)
    ^^^ !^(string_of_int pos.Lexing.pos_cnum)
  in
  let print_cursor = function
    | NoCursor ->
        !^ "Cerb_location.NoCursor"
    | PointCursor pos ->
        !^ "Cerb_location.PointCursor" ^^^ P.parens (print_lex pos)
    | RegionCursor (b, e) ->
        !^ "Cerb_location.RegionCursor"
        ^^^ P.parens (print_lex b)
        ^^^ P.parens (print_lex e)
  in
  match loc with
    | Loc_unknown ->
        !^"Cerb_location.unknown"
    | Loc_other str ->
        !^ "Cerb_location.other" ^^ P.parens (P.dquotes !^ (String.escaped str))
    | Loc_point pos ->
        !^"Cerb_location.point" ^^^ P.parens (print_lex pos)
    | Loc_region (pos1, pos2, cur) ->
        !^"Cerb_location.region"
        ^^^ P.parens (print_lex pos1)
        ^^^ P.parens (print_lex pos2)
        ^^^ P.parens (print_cursor cur)
  | Loc_regions (xs, cur) ->
      let print_pair pp (x, y) = P.parens (pp x ^^ P.comma ^^^ pp y) in
      let print_list pp xs = P.brackets (P.separate_map (P.semi ^^ P.space) pp xs) in
      !^"Cerb_location.regions"
      ^^^ P.parens (print_list (print_pair print_lex) xs)
      ^^^ P.parens (print_cursor cur)


open Lexing

let to_json loc =
  let of_pos p =
    `Assoc [("line", `Int (p.pos_lnum-1));
            ("ch", `Int (p.pos_cnum-p.pos_bol))] in
  match loc with
    | Loc_unknown ->
        `Null
    | Loc_other _str ->
        `Null (* `String str *)
    | Loc_point p ->
        `Assoc [("begin", of_pos p); ("end", of_pos p)]
    | Loc_region (p1, p2, _) ->
        `Assoc [("begin", of_pos p1); ("end", of_pos p2)]
    | Loc_regions (xs, _) ->
        let (pos1, pos2) = outer_bbox xs in
        `Assoc [("begin", of_pos pos1); ("end", of_pos pos2)]


open Cerb_colour

let pp_location =
  let last_pos = ref Lexing.dummy_pos in
  fun ?(clever = false) loc ->
  let string_of_pos p =
    let open Lexing in
    let ret =
      if !last_pos.pos_fname <> p.pos_fname then
        p.pos_fname ^ ":" ^ string_of_int p.pos_lnum ^ ":" ^ string_of_int (p.pos_cnum - p.pos_bol)
      else if !last_pos.pos_lnum <> p.pos_lnum then
        "line:" ^ string_of_int p.pos_lnum ^ ":" ^ string_of_int (p.pos_cnum - p.pos_bol)
      else
        "col:" ^ string_of_int (p.pos_cnum - p.pos_bol) in
    begin if clever then last_pos := p end;
    ret in
  let aux_region start_p end_p cur =
    let mk_cursor_str () =
      match cur with
        | NoCursor -> ""
        | PointCursor cursor_p -> " " ^ string_of_pos cursor_p
        | RegionCursor (b, e) -> " " ^ string_of_pos b ^ " - " ^ string_of_pos e in
    if !last_pos.pos_fname = start_p.pos_fname &&
       start_p.pos_fname = end_p.pos_fname &&
       start_p.pos_lnum = end_p.pos_lnum
    then
      let start_p_str = string_of_pos start_p in
      P.angles (
        !^ (ansi_format ~err:true [Yellow] (start_p_str ^ " - " ^ string_of_int (end_p.pos_cnum - end_p.pos_bol)))
      ) ^^ !^ (ansi_format ~err:true [Yellow] (mk_cursor_str ()))
    else
      let start_p_str = string_of_pos start_p in
      let end_p_str   = string_of_pos end_p in
      P.angles (
        !^ (ansi_format ~err:true [Yellow] start_p_str) ^^ P.comma ^^^
        !^ (ansi_format ~err:true [Yellow] end_p_str)
      ) ^^ !^ (ansi_format ~err:true [Yellow] (mk_cursor_str ())) in
  match loc with
    | Loc_unknown ->
        P.angles !^ (ansi_format ~err:true [Yellow] "unknown location")
    | Loc_other str ->
        P.angles !^ (ansi_format ~err:true [Yellow] ("other location (" ^ str ^ ")"))
    | Loc_point pos ->
        let pos_str = string_of_pos pos in
        P.angles !^ (ansi_format ~err:true [Yellow] pos_str)
    | Loc_region (start_p, end_p, cur) ->
        aux_region start_p end_p cur
    | Loc_regions (xs, cur) ->
        let (start_p, end_p) = outer_bbox xs in
        aux_region start_p end_p cur


let string_of_pos pos =
  ansi_format ~err:true [Bold] (
    Printf.sprintf "%s:%d:%d:" pos.pos_fname pos.pos_lnum (1 + pos.pos_cnum - pos.pos_bol)
  )

let get_line n ic =
  seek_in ic 0;
  let rec aux = function
    | 1 -> input_line ic
    | n -> let _ = input_line ic in
           aux (n-1) in
  aux n



let string_at_line fname lnum cpos =
  try
    if Sys.file_exists fname then
      let ic = open_in fname in
      let sub l start n =
        if start + n < String.length l then String.sub l start n
        else Printf.sprintf "(?error: Cerb_location.string_at_line with %S, %i-%i)"
               l start n
      in
      let l =
        let l_ = get_line lnum ic in
        match Cerb_util.terminal_size () with
          | None ->
              (None, l_)
          | Some (_, term_col) ->
              if cpos >= term_col then begin
                (* The cursor position is beyond the width of the terminal *)
                let mid = term_col / 2 in
                let start  = max 0 (cpos - mid) in
                let n = String.length l_ - start in
                ( Some (cpos - start + 5)
                , if n + 5 <= term_col then
                    "  ..." ^ sub l_ start n
                  else
                  try 
                    "  ..." ^ String.sub l_ start (term_col - 5 - 3) ^ "..." 
                  with _ -> ("OOPS: " ^ l_))
              end else if String.length l_ > term_col then
                (* The cursor is within the terminal width, but the line needs
                   to be truncated *)
                (None, sub l_ 0 (term_col - 3) ^ "...")
              else
                (None, l_) in
      close_in ic;
      Some l
    else
      None
  with
    End_of_file ->
      (* TODO *)
      None


let head_pos_of_location = function
  | Loc_unknown ->
      ( "unknown location "
      , "" )
  | Loc_other str ->
      ( "other location (" ^ str ^ ") "
      , "" )
  | Loc_point pos ->
      ( string_of_pos pos
      , let cpos = pos.pos_cnum - pos.pos_bol in
        match string_at_line pos.pos_fname pos.pos_lnum cpos with
          | Some (cpos'_opt, l) ->
              let cpos = match cpos'_opt with
                | Some cpos' -> cpos'
                | None       -> cpos in
              l ^ "\n" ^
              ansi_format ~err:true [Bold; Green] (String.init (cpos + 1) (fun n -> if n < cpos then ' ' else '^'))
          | None ->
              "" )
  | Loc_region (start_p, end_p, cursor) ->
      ( string_of_pos start_p
      , let cpos1 = start_p.pos_cnum - start_p.pos_bol in
        match string_at_line start_p.pos_fname start_p.pos_lnum cpos1 with
          | Some (_, l) ->
              let cpos2 =
                if start_p.pos_lnum = end_p.pos_lnum then
                  end_p.pos_cnum - end_p.pos_bol
                else
                  String.length l in
              let cursor_n = match cursor with
                | PointCursor cursor_p
                | RegionCursor (cursor_p, _) ->
                    cursor_p.pos_cnum - cursor_p.pos_bol 
                | NoCursor ->
                    cpos1 in
              l ^ "\n" ^
              ansi_format ~err:true [Bold; Green] (
                String.init ((max cursor_n cpos2) + 1)
                  (fun n -> if n = cursor_n then '^' else if n >= cpos1 && n < cpos2 then '~' else if n < String.length l && l.[n] = '\t' then '\t' else ' ')
              )
          | None ->
              "" )
  | Loc_regions (xs, cursor) ->
      let pos = match cursor with
        | NoCursor -> fst (List.hd xs)
        | PointCursor p
        | RegionCursor (p, _) -> p
      in
      ( string_of_pos pos
      , let cursor_p = pos.pos_cnum - pos.pos_bol in
        match string_at_line pos.pos_fname pos.pos_lnum cursor_p with
        | Some (_, l) ->
          let ps = List.map (fun (s, e) -> (s.pos_cnum - s.pos_bol, e.pos_cnum - e.pos_bol)) xs in
          l ^ "\n" ^ ansi_format ~err:true [Bold; Green]
            (String.init (String.length l)
               (fun n -> if n = cursor_p then '^'
                         else if List.exists (fun (p1, p2) -> n >= p1 && n < p2) ps then '~'
                         else ' ')
            )
        | None -> "" )



let simple_location = 
  let string_of_pos pos =
    Printf.sprintf "%d:%d" pos.pos_lnum (1 + pos.pos_cnum - pos.pos_bol)
  in
  function
  | Loc_unknown -> 
     "<unknown location>"
  | Loc_other str ->
     "<other location: " ^ str ^ ">"
  | Loc_point pos -> 
     string_of_pos pos
  | Loc_region (start_p, end_p, _) ->
     Printf.sprintf "<%s--%s>" (string_of_pos start_p) (string_of_pos end_p)
  | Loc_regions (xs, _) ->
     let (start_p, end_p) = List.hd xs in
     Printf.sprintf "<%s--%s>" (string_of_pos start_p) (string_of_pos end_p)

let get_filename = function
  | Loc_unknown
  | Loc_regions ([], _) ->
      None
  | Loc_other _ ->
      Some "<internal>"
  | Loc_point pos 
  | Loc_region (pos, _, _)
  | Loc_regions ((pos, _) :: _, _) ->
      Some pos.pos_fname

let is_unknown = function
  | Loc_unknown -> true 
  | _ -> false

let is_other = function
  | Loc_other str -> Some str
  | _ -> None

let is_library_location loc =
  let excluded =
    let tbl = Hashtbl.create 3 in
    Hashtbl.add tbl (Cerb_runtime.in_runtime "libc/include") ();
    Hashtbl.add tbl (Cerb_runtime.in_runtime "libcore") ();
    Hashtbl.add tbl (Cerb_runtime.in_runtime "libcore/impls") ();
    tbl in
  match get_filename loc with
    | Some path ->
        Hashtbl.mem excluded (Filename.dirname path)
    | None ->
        false



(* following simple_location *)
let line_numbers = function
  | Loc_unknown -> None
  | Loc_other _ -> None
  | Loc_point p -> Some (p.pos_lnum, p.pos_lnum)
  | Loc_region (p1, p2, _) -> Some (p1.pos_lnum, p2.pos_lnum)
  | Loc_regions ((p1,p2) :: _, _) -> Some (p1.pos_lnum, p2.pos_lnum)
  | Loc_regions ([], _) -> None
