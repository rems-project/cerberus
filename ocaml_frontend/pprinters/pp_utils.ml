let to_plain_string d =
  let buf = Buffer.create 50 in
  PPrint.ToBuffer.compact buf d;
  let str = Buffer.contents buf in
  Buffer.clear buf;
  str

let to_plain_pretty_string ?(rfrac=1.0) ?(width=150) d =
  let buf = Buffer.create 50 in
  PPrint.ToBuffer.pretty rfrac width buf d;
  let str = Buffer.contents buf in
  Buffer.clear buf;
  str

let map_with_last f_all f_last xs =
  let rec aux acc = function
    | [] ->
        acc
    | [x] ->
        f_last x :: acc
    | x::xs ->
        aux (f_all x :: acc) xs
  in
  List.rev (aux [] xs)
