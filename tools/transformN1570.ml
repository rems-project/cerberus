open Soup
let () =
  let soup =
    read_file "n1570_2.html" |> parse
  in
  let key k =
    let n = String.get k 0 in
    if n > '0' && n <= '9' then
      "§" ^ (Str.global_replace (Str.regexp "p") "#" k)
    else k
  in
  let entry n =
    match attribute "name" n with
    | Some k -> (key k, `String (trimmed_texts n |> String.concat "\n"))
    | None -> failwith "no key"
  in
  (soup $$ "body a[name]")
  |> Soup.to_list
  |> List.map entry
  |> fun ss -> `Assoc ss
  |> Yojson.pretty_to_channel stdout
