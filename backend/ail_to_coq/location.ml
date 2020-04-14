open Extra

type t = int

type loc_data =
  { loc_file  : string
  ; loc_line1 : int
  ; loc_col1  : int
  ; loc_line2 : int
  ; loc_col2  : int }

let htbl = Hashtbl.create 97
let counter = ref (-1)

let none : unit -> t = fun _ ->
  incr counter; !counter

let make : string -> int -> int -> int -> int -> t = fun f l1 c1 l2 c2 ->
  let data =
    { loc_file = f
    ; loc_line1 = l1+1 ; loc_col1 = c1
    ; loc_line2 = l2+1 ; loc_col2 = c2 }
  in
  let key = incr counter; !counter in
  Hashtbl.add htbl key data; key

let get : t -> loc_data option = fun key ->
  try Some(Hashtbl.find htbl key) with Not_found -> None

let pp_data : loc_data pp = fun ff data ->
  let (l1, c1) = (data.loc_line1, data.loc_col1) in
  let (l2, c2) = (data.loc_line2, data.loc_col2) in
  Format.fprintf ff "%s %i:%i" data.loc_file l1 c1;
  if l1 = l2 && c1 <> c2 then Format.fprintf ff "-%i" c2;
  if l1 <> l2 then Format.fprintf ff "-%i:%i" l2 c2

let pp : t pp = fun ff key ->
  match get key with
  | Some(d) -> pp_data ff d
  | None    -> Format.fprintf ff "unknown"

type 'a located = { elt : 'a ; loc : t }
