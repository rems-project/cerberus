(* Matching runs only at configuration or first use of a static name. Keep it
   separate from the address-keyed cache, whose hits never inspect text. *)
module Names = Hashtbl.Make (String)

let upper = function 'A'..'Z' -> true | _ -> false
let identifier name =
  name <> "" && String.for_all (function
    | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' -> true | _ -> false) name
let module_name name = identifier name && upper name.[0]
let function_name name =
  identifier name && name <> "_" &&
  (match name.[0] with 'a'..'z' | '_' -> true | _ -> false)

let valid_selector name =
  match List.rev (String.split_on_char '.' name) with
  | last :: qualifiers ->
      List.for_all module_name qualifiers &&
      (module_name last || (qualifiers <> [] && function_name last))
  | [] -> false

let canonical raw =
  let wrappers = ["Cerb_frontend__"; "Cerb_backend__"; "Dune__exe__"] in
  let name = match List.find_opt (fun prefix -> String.starts_with ~prefix raw) wrappers with
    | Some wrapper ->
        String.sub raw (String.length wrapper) (String.length raw - String.length wrapper)
    | None -> raw in
  (* The first function component names the source. Nested functions and
     anonymous closures belong to that outer function. Do not strip digits:
     [function0] and [function] can be different functions. *)
  let rec outer modules = function
    | part :: rest when module_name part -> outer (part :: modules) rest
    | fn :: _ when modules <> [] && function_name fn ->
        String.concat "." (List.rev (fn :: modules))
    | _ -> invalid_arg "Cerb_log_auto: expected a qualified function name (use __FUNCTION__)"
  in
  outer [] (String.split_on_char '.' name)

let selected selectors =
  let names = Names.create (List.length selectors) in
  List.iter (fun name -> Names.replace names name ()) selectors;
  fun name ->
    Names.mem names name ||
    match String.rindex_opt name '.' with
    | Some dot when dot + 1 < String.length name && not (upper name.[dot + 1]) ->
        Names.mem names (String.sub name 0 dot)
    | _ -> false
