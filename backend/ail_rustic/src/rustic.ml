open AilSyntax

let plop (Symbol.Identifier (_, s)) = s

let plop2 = function
| [] -> ""
| _ :: _ as l -> "(" ^ String.concat ", " l ^ ")"


let foo3 attrs =
  String.concat ", " (List.map (fun a -> plop a.Annot.attr_id ^ plop2 a.Annot.attr_args) attrs)

let foo2 (Symbol.Symbol (_, _, Some id), (_, Annot.Attrs attrs, _, _)) =
  print_string (id ^ ": " ^ foo3 attrs ^ "\n")

let foo fs =
  List.iter foo2 fs

let rec map_option_aux f acc = function
  | [] -> List.rev acc
  | x :: xs ->
    (match f x with
     | None -> map_option_aux f acc xs
     | Some y -> map_option_aux f (y :: acc) xs)

let map_option f xs = map_option_aux f [] xs

module Ail_identifier = struct
  type t = AilSyntax.ail_identifier
  let compare (x : t) y = Symbol.symbol_compare
end

module Ail_identifier_map = Map.Make(Ail_identifier)

let add_left id x m =
  match Ail_identifier_map.find_opt id m with
  | None -> Ail_identifier_map.add id (Some x, None)
  | Some (_, y) -> Ail_identifier_map.add id (Some x, y)

let add_left id y m =
  match Ail_identifier_map.find_opt id m with
  | None -> Ail_identifier_map.add id (None, Some y)
  | Some (x, _) -> Ail_identifier_map.add id (x, Some y)

let collect_functions s =
  let ds = map_option (function (id, (_, Decl_function (a, b, c, d, e, f))) -> Some (id, (a, b, c, d, e, f)) | (_, (_, Decl_object _)) -> None) s.declarations in
  let fs = s.function_definitions in
  let m = Ail_identifier_map.empty in
  let m = List.fold_left (fun m (id, d) -> add_left id d m) m ds in
  let m = List.fold_left (fun m (id, f) -> add_right id f m) m fs in
  m

let run_rustic ail_file =
  match ail_file with
  | (id, s) ->
    let x = collect_functions s in
    foo fs;
    ()