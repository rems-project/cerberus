module L = Lexing

type t = {
  s : L.position;
  e : L.position
}

let make s e =
  let (=>) b1 b2 = if b1 then b2 else true in
  assert (s.L.pos_fname = e.L.pos_fname);
  assert (s.L.pos_lnum <= e.L.pos_lnum);
  assert ((s.L.pos_lnum = e.L.pos_lnum) => (s.L.pos_bol <= e.L.pos_bol));
  assert (s.L.pos_cnum <= e.L.pos_cnum);
  {s; e}

let from_lexbuf {L.lex_start_p = s; L.lex_curr_p = e; _} = {s; e}

let name {s; _} = s.L.pos_fname
let first_line {s; _} = s.L.pos_lnum
let last_line {e; _} = e.L.pos_lnum
let first_line_offset {s; _} = s.L.pos_lnum
let last_line_offset {e; _} = e.L.pos_lnum
let first_char {s; _} = s.L.pos_cnum
let last_char {e; _} = e.L.pos_cnum

let lines_to_string p =
  let f = first_line p in
  let l = last_line p in
  if f = l then
    "line " ^ BatInt.to_string f
  else
    "lines " ^ BatInt.to_string f ^ "-" ^ BatInt.to_string l
