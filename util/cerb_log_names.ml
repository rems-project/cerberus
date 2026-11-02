let upper = function 'A'..'Z' -> true | _ -> false
let identifier_char = function
  | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' -> true
  | _ -> false

let valid_component s = s <> "" && String.for_all identifier_char s
let module_name s = valid_component s && upper s.[0]
let function_name s = valid_component s && match s.[0] with
  | 'a'..'z' -> true
  | '_' -> String.length s > 1
  | _ -> false

let valid_selector name =
  let rec valid qualified = function
    | [] -> qualified
    | s :: rest when module_name s -> valid true rest
    | [s] -> qualified && function_name s
    | _ -> false in
  valid false (String.split_on_char '.' name)

let canonical raw =
  let raw = match List.find_opt (fun prefix -> String.starts_with ~prefix raw)
      ["Cerb_frontend__"; "Cerb_backend__"; "Dune__exe__"] with
    | None -> raw
    | Some prefix ->
        let start = String.length prefix in
        String.sub raw start (String.length raw - start) in
  let rec take modules = function
    | s :: rest when module_name s -> take (s :: modules) rest
    | s :: _ when modules <> [] && function_name s ->
        String.concat "." (List.rev (s :: modules))
    | _ -> invalid_arg "Cerb_log: expected a qualified function name (use __FUNCTION__)" in
  take [] (String.split_on_char '.' raw)

let selected selectors =
  let names = Hashtbl.create (List.length selectors) in
  List.iter (fun name -> Hashtbl.replace names name ()) selectors;
  fun name ->
    Hashtbl.mem names name ||
    match String.rindex_opt name '.' with
    | Some dot when dot + 1 < String.length name && not (upper name.[dot + 1]) ->
        Hashtbl.mem names (String.sub name 0 dot)
    | _ -> false
