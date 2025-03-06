
(* The lexing position is the real location in the file parsed.
In particular, this is likely a file that was produced by the pre-processor.
The `source_file` and `source_line` refer to the locations in the original
source, if one is available, otherwise they should match what's in `file`.
*)
type t = {
  file: Lexing.position; (* position in the pre-processed file *)
  source_file: string;   (* file containing the original source *)
  source_line: int;      (* line number in the original file *)
}

let dummy = { file = Lexing.dummy_pos; source_file = ""; source_line = 0 }

let from_lexing p =
  { file = p; source_file = p.pos_fname; source_line = p.pos_lnum; }

let line pos = pos.source_line
let file pos = pos.source_file


(* Column for this position, 1 based *)
let column pos =
  let f = pos.file in
  Lexing.(1 + f.pos_cnum - f.pos_bol)

let to_file_lexing p = p.file

let change_cnum pos n =
  { pos with file = { pos.file with pos_cnum = pos.file.pos_cnum + n } }

let set_source (f,n) pos = { pos with source_file = f; source_line = n }


module LineMap = struct
  module Map = Map.Make(Int)

  type t = {
    file:   string;               (* pre-processed file *)
    lines:  (string * int) Map.t 
    (* The map associates lines in the pre-processed file with
       declarations about the original source (file, line number).
       We keep a whole map, rather than just the last locations,
       to support parsing in mulitple passes.  For example, we first parse
       CN magic comments as just a literal, and then we parse them fully
       in a secondary pass. *)


  }

  let empty file = { file = file; lines = Map.empty }

  let add k v mp = { mp with lines = Map.add k v mp.lines }

  let lookup k mp =
    match Map.find_last_opt (fun l -> l < k) mp.lines with
    | None           -> (mp.file, k)
    | Some (l,(f,n)) -> (f, n + (k - l - 1))

  let dump mp =
    Printf.printf "+--- %s\n" mp.file;
    Map.iter (fun k (f,n) ->
      Printf.printf "| %d: %s:%d\n" k f n
    ) mp.lines;
    Printf.printf "+--------------------\n"
end
