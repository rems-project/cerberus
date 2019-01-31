open Lexing

type t =
  | Loc_unknown
  | Loc_other of string
  | Loc_point of Lexing.position
    (* start, end, cursor *)
  | Loc_region of Lexing.position * Lexing.position * Lexing.position option
  | Loc_regions of (Lexing.position * Lexing.position) list * Lexing.position option

let unknown =
  Loc_unknown

let other str =
  Loc_other str

let point pos =
  Loc_point pos

let region (b, e) cursor_opt =
  Loc_region (b, e, cursor_opt)

let regions xs cursor_opt =
  match xs with
    | [] ->
        failwith "Location_ocaml.region, xs must not be []"
    | _ ->
        (* TODO: need to sort the regions *)
        Loc_regions (xs, cursor_opt)

let with_cursor = function
  | Loc_unknown
  | Loc_other _
  | Loc_regions ([], None) ->
    Loc_unknown
  | Loc_point z
  | Loc_region (_, _, Some z)
  | Loc_region (z, _, None)
  | Loc_regions (_, Some z)
  | Loc_regions ((z,_)::_, None) ->
    Loc_point z


(* [with_cursor_from loc1 loc2] makes a new (region location) with the region from loc1 and the cursor (if any) from loc2 *)
let with_cursor_from loc1 loc2 =
  let cursor_opt = match loc2 with
    | Loc_unknown
    | Loc_other _ ->
        None
    | Loc_point z ->
        Some z
    | Loc_region (_, _, z)
    | Loc_regions (_, z) ->
        z in
  match loc1 with
    | Loc_unknown ->
        (match cursor_opt with Some loc -> Loc_point loc | _ -> Loc_unknown)
    | Loc_other str ->
        Loc_other str
    | Loc_point z ->
        Loc_region (z, z, cursor_opt)
    | Loc_region (begin_loc, end_loc, _) ->
        Loc_region (begin_loc, end_loc, cursor_opt)
    | Loc_regions (regions, _) ->
        Loc_regions (regions, cursor_opt)

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

(*let bbox_of loc =  *)

let bbox_location xs =
  let (b, e) = outer_bbox begin
    List.fold_left (fun acc loc ->
      match loc with
        | Loc_unknown
        | Loc_other _ ->
            acc
        | Loc_point pos ->
            (pos, pos) :: acc
        | Loc_region (pos1, pos2, _) ->
            (* invariant from Loc_region is that pos1 <= pos2 *)
            (pos1, pos2) :: acc
        | Loc_regions (xs, _) ->
            xs @ acc
    ) [] xs
  end in
  Loc_region (b, e, None)


let with_regions_and_cursor locs loc_opt =
  let cursor_opt = match loc_opt with
    | Some (Loc_point z) -> Some z
    | Some (Loc_region (_, _, z))
    | Some (Loc_regions (_, z)) -> z
    | _ -> None
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
  let string_of_pos pos =
    if charon && from_main_file loc then
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
    | Loc_region (pos1, pos2, _) ->
        string_of_pos pos1 ^ "-" ^
        begin if pos1.pos_fname = pos2.pos_fname then
          ""
        else
          shrink pos2.pos_fname
        end ^
        begin if pos1.pos_lnum = pos2.pos_lnum then
          ""
        else
          string_of_int pos2.pos_lnum
        end ^
        string_of_int (1+pos2.pos_cnum-pos2.pos_bol)
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
          string_of_int pos2.pos_lnum
        end ^
        string_of_int (1+pos2.pos_cnum-pos2.pos_bol)



module P = PPrint
open Pp_prelude

let print_location loc =
  let print_lex pos =
    !^"A.position" ^^^ P.dquotes !^(pos.Lexing.pos_fname)
    ^^^ !^(string_of_int pos.Lexing.pos_lnum)
    ^^^ !^(string_of_int pos.Lexing.pos_bol)
    ^^^ !^(string_of_int pos.Lexing.pos_cnum)
  in
  let print_option pp = Util.Option.case
      (fun e -> !^"Some" ^^^ P.parens (pp e))
      (fun _ -> !^"None") in
  match loc with
    | Loc_unknown ->
        !^"Location_ocaml.unknown"
    | Loc_other str ->
        !^ "Location_ocaml.other" ^^ P.parens (P.dquotes !^ (String.escaped str))
    | Loc_point pos ->
        !^"Location_ocaml.point" ^^^ P.parens (print_lex pos)
    | Loc_region (pos1, pos2, opos3) ->
        !^"Location_ocaml.region"
        ^^^ P.parens (print_lex pos1)
        ^^^ P.parens (print_lex pos2)
        ^^^ P.parens (print_option print_lex opos3)
  | Loc_regions (xs, opos) ->
      let print_pair pp (x, y) = P.parens (pp x ^^ P.comma ^^^ pp y) in
      let print_list pp xs = P.brackets (P.separate_map (P.semi ^^ P.space) pp xs) in
      !^"Location_ocaml.regions"
      ^^^ P.parens (print_list (print_pair print_lex) xs)
      ^^^ P.parens (print_option print_lex opos)


open Lexing

let to_json loc =
  let of_pos p =
    `Assoc [("line", `Int (p.pos_lnum-1));
            ("ch", `Int (p.pos_cnum-p.pos_bol))] in
  match loc with
    | Loc_unknown ->
        `Null
    | Loc_other str ->
        `Null (* `String str *)
    | Loc_point p ->
        `Assoc [("begin", of_pos p); ("end", of_pos p)]
    | Loc_region (p1, p2, _) ->
        `Assoc [("begin", of_pos p1); ("end", of_pos p2)]
    | Loc_regions (xs, _) ->
        let (pos1, pos2) = outer_bbox xs in
        `Assoc [("begin", of_pos pos1); ("end", of_pos pos2)]


open Colour

let pp_location =
  let last_pos = ref Lexing.dummy_pos in
  fun loc ->
  let string_of_pos p =
    let open Lexing in
    let ret =
      if !last_pos.pos_fname <> p.pos_fname then
        p.pos_fname ^ ":" ^ string_of_int p.pos_lnum ^ ":" ^ string_of_int (p.pos_cnum - p.pos_bol)
      else if !last_pos.pos_lnum <> p.pos_lnum then
        "line:" ^ string_of_int p.pos_lnum ^ ":" ^ string_of_int (p.pos_cnum - p.pos_bol)
      else
        "col:" ^ string_of_int (p.pos_cnum - p.pos_bol) in
    last_pos := p;
    ret in
  let aux_region start_p end_p cursor_p_opt =
    let start_p_str = string_of_pos start_p in
    let end_p_str   = string_of_pos start_p in
    let cursor_p_str =
      match cursor_p_opt with
        | None -> ""
        | Some cursor_p -> " " ^ string_of_pos cursor_p in
    P.angles (
      !^ (ansi_format [Yellow] start_p_str) ^^ P.comma ^^^
      !^ (ansi_format [Yellow] end_p_str)
    ) ^^
    P.optional (fun _ -> !^ (ansi_format [Yellow] cursor_p_str)) cursor_p_opt in
  match loc with
    | Loc_unknown ->
        P.angles !^ (ansi_format [Yellow] "unknown location")
    | Loc_other str ->
        P.angles !^ (ansi_format [Yellow] ("other location (" ^ str ^ ")"))
    | Loc_point pos ->
        let pos_str = string_of_pos pos in
        P.angles !^ (ansi_format [Yellow] pos_str)
    | Loc_region (start_p, end_p, cursor_p_opt) ->
        aux_region start_p end_p cursor_p_opt
    | Loc_regions (xs, cursor_p_opt) ->
        let (start_p, end_p) = outer_bbox xs in
        aux_region start_p end_p cursor_p_opt


let string_of_pos pos =
  ansi_format [Bold] (
    Printf.sprintf "%s:%d:%d:" pos.pos_fname pos.pos_lnum (1 + pos.pos_cnum - pos.pos_bol)
  )

let get_line n ic =
  seek_in ic 0;
  let rec aux = function
    | 1 -> input_line ic
    | n -> let _ = input_line ic in
           aux (n-1) in
  aux n


external terminal_size: unit -> (int * int) option = "terminal_size"

let string_at_line fname lnum cpos =
  try
    if Sys.file_exists fname then
      let ic = open_in fname in
      let l =
        let l_ = get_line lnum ic in
        match terminal_size () with
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
                    "  ..." ^ String.sub l_ start n
                  else
                  "  ..." ^ String.sub l_ start (term_col - 5 - 3) ^ "..." )
              end else if String.length l_ > term_col then
                (* The cursor is within the terminal width, but the line needs
                   to be truncated *)
                (None, String.sub l_ 0 (term_col - 3) ^ "...")
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
              ansi_format [Bold; Green] (String.init (cpos + 1) (fun n -> if n < cpos then ' ' else '^'))
          | None ->
              "" )
  | Loc_region (start_p, end_p, cursor_p_opt) ->
      ( string_of_pos start_p
      , let cpos1 = start_p.pos_cnum - start_p.pos_bol in
        match string_at_line start_p.pos_fname start_p.pos_lnum cpos1 with
          | Some (_, l) ->
              let cpos2 =
                if start_p.pos_lnum = end_p.pos_lnum then
                  end_p.pos_cnum - end_p.pos_bol
                else
                  String.length l in
              let cursor = match cursor_p_opt with
                | Some cursor_p ->
                    cursor_p.pos_cnum - cursor_p.pos_bol 
                | None ->
                    cpos1 in
              l ^ "\n" ^
              ansi_format [Bold; Green] (
                String.init ((max cursor cpos2) + 1)
                  (fun n -> if n = cursor then '^' else if n >= cpos1 && n < cpos2 then '~' else ' ')
              )
          | None ->
              "" )
  | Loc_regions (xs, cursor_p_opt) ->
      let pos = match cursor_p_opt with
        | None -> fst (List.hd xs)
        | Some p -> p
      in
      ( string_of_pos pos
      , let cursor_p = pos.pos_cnum - pos.pos_bol in
        match string_at_line pos.pos_fname pos.pos_lnum cursor_p with
        | Some (_, l) ->
          let ps = List.map (fun (s, e) -> (s.pos_cnum - s.pos_bol, e.pos_cnum - e.pos_bol)) xs in
          l ^ "\n" ^ ansi_format [Bold; Green]
            (String.init (String.length l)
               (fun n -> if n = cursor_p then '^'
                         else if List.exists (fun (p1, p2) -> n >= p1 && n < p2) ps then '~'
                         else ' ')
            )
        | None -> "" )

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
