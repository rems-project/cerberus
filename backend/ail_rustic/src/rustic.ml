let rec map_option_aux f acc = function
  | [] -> List.rev acc
  | x :: xs ->
    (match f x with
     | None -> map_option_aux f acc xs
     | Some y -> map_option_aux f (y :: acc) xs)

let map_option f xs = map_option_aux f [] xs


open AilSyntax

let string_of_identifier (Symbol.Identifier (_, s)) = s

let plop2 = function
| [] -> ""
| _ :: _ as l -> "(" ^ String.concat ", " l ^ ")"

let string_of_attr attr =
  string_of_identifier attr.Annot.attr_id ^ plop2 attr.Annot.attr_args

let string_of_attrs attrs =
  String.concat ", " (List.map string_of_attr attrs)

let string_of_sym (Symbol.Symbol (_, _, Some id)) = id

let string_of_fun_wo_args sym ((_, Annot.Attrs attrs, _, _)) =
  string_of_sym sym ^ ": " ^ string_of_attrs attrs

let string_of_ty = function
| Ctype.Ctype _ -> "?"

let string_of_annots annots =
  let annots =
    map_option
      (let open Annot in function
      | Astd x -> None
      | Aloc loc -> None
      | Auid _ -> None
      | Abmc _ -> None
      | Aattrs (Attrs attrs) -> Some attrs)
      annots in
  let annots = List.concat annots in
  String.concat " " (List.map string_of_attr annots)

let rec string_of_ctype = let open Ctype in function
| Ctype (annots, cty_) ->
  string_of_annots annots ^ string_of_ctype_ cty_
and string_of_ctype_ = function
| Void -> "void"
| Basic x -> "int" (* TODO: lies *)
| Array (cty, sz) -> "array(" ^ string_of_ctype cty ^ ")"
| Function _ -> "function"
| Pointer (qls, cty) -> string_of_ctype cty ^ "*"
| Atomic cty -> "atomic(" ^ string_of_ctype cty ^ ")"
| Struct name -> string_of_sym name
| Union name -> string_of_sym name

let string_of_arg (ty, id) =
  match ty with
  | (_, cty, _) ->
    string_of_sym id ^ " : " ^ string_of_ctype cty

let string_of_args args =
  String.concat "," (List.map string_of_arg args)

let string_of_fun_w_args sym (retty, argsty) ((_, Annot.Attrs attrs, args, _)) =
  let args = List.combine argsty args in
  string_of_sym sym ^ ":" ^ (match attrs with | [] -> "" | _::_ -> " " ^ string_of_attrs attrs) ^ " (" ^ string_of_args args ^ ")"

let string_of_fun = function
| (x, (Some ty, Some bod)) -> string_of_fun_w_args x ty bod
| (x, (_, Some bod)) -> string_of_fun_wo_args x bod
| (_, (None, None)) -> assert false (* ? *)
| (x, _)-> string_of_sym x ^ " no body"

let print_funs fs =
  List.iter (fun f -> print_string (string_of_fun f ^ "\n")) fs

module Ail_identifier = struct
  type t = AilSyntax.ail_identifier
  let compare (x : t) y = Symbol.symbol_compare x y
end

module Ail_identifier_map = Map.Make(Ail_identifier)

let add_left id x m =
  match Ail_identifier_map.find_opt id m with
  | None -> Ail_identifier_map.add id (Some x, None) m
  | Some (_, y) -> Ail_identifier_map.add id (Some x, y) m

let add_right id y m =
  match Ail_identifier_map.find_opt id m with
  | None -> Ail_identifier_map.add id (None, Some y) m
  | Some (x, _) -> Ail_identifier_map.add id (x, Some y) m

let collect_functions s =
  let ds = map_option (function (id, (_, Decl_function (a, b, c, d, e, f))) -> Some (id, (b, c)) | (_, (_, Decl_object _)) -> None) s.declarations in
  let fs = s.function_definitions in
  let m = Ail_identifier_map.empty in
  (* this may discard stuff *)
  let m = List.fold_left (fun m (id, d) -> add_left id d m) m ds in
  let m = List.fold_left (fun m (id, f) -> add_right id f m) m fs in
  m

let run_rustic ail_file =
  match ail_file with
  | (id, s) ->
    let fs = collect_functions s in
    print_funs (Ail_identifier_map.bindings fs);
    ()