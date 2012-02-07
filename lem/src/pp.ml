open Format

let pp_str ppf s =
  fprintf ppf "%s" s

let rec lst sep f ppf = function
  | [] -> ()
  | [x] ->
      fprintf ppf "%a"
        f x
  | (h::t) -> 
      f ppf h;
      fprintf ppf sep;
      lst sep f ppf t

let opt f ppf = function
  | None ->
      fprintf ppf "None"
  | Some(x) ->
      fprintf ppf "Some(%a)"
        f x

let pp_to_string pp =
  let b = Buffer.create 16 in
  let f = formatter_of_buffer b in
    pp f;
    pp_print_flush f ();
    Buffer.contents b
