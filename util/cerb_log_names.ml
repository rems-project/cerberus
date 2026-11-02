(* Matching runs only at configuration or first use of a static name. Keep it
   separate from the address-keyed cache, whose hits never inspect text. *)
module Names = Hashtbl.Make (String)

let upper = function 'A'..'Z' -> true | _ -> false
let identifier_char = function
  | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '\'' -> true
  | _ -> false

(* Scan the original string, without allocating components or per-call closures.
   Return the exclusive component end, or [-1] for an invalid character. *)
let rec component_end name length i =
  if i = length || name.[i] = '.' then i
  else if identifier_char name.[i] then component_end name length (i + 1)
  else -1

let function_start name start stop =
  match name.[start] with
  | 'a'..'z' -> true
  | '_' -> stop > start + 1
  | _ -> false

let rec selector_from name length start qualified =
  let stop = component_end name length start in
  stop > start &&
  if upper name.[start] then
    stop = length || selector_from name length (stop + 1) true
  else qualified && stop = length && function_start name start stop

let valid_selector name = selector_from name (String.length name) 0 false

let rec prefix_matches raw start prefix length i =
  i = length ||
  (raw.[start + i] = prefix.[i] && prefix_matches raw start prefix length (i + 1))

(* Return the end index on success, or [0] on failure. All matched prefixes are
   nonempty, so the result needs no allocated option or substring. *)
let prefix_end raw length start prefix =
  let prefix_length = String.length prefix in
  if length - start >= prefix_length &&
     prefix_matches raw start prefix prefix_length 0
  then start + prefix_length
  else 0

(* Dispatch before matching, and consume the shared [Cerb_] prefix only once. *)
let wrapper_end raw length =
  if length = 0 then 0 else
  match raw.[0] with
  | 'C' ->
      let start = prefix_end raw length 1 "erb_" in
      if start = 0 || start = length then 0 else
      begin match raw.[start] with
      | 'f' -> prefix_end raw length (start + 1) "rontend__"
      | 'b' -> prefix_end raw length (start + 1) "ackend__"
      | _ -> 0
      end
  | 'D' -> prefix_end raw length 1 "une__exe__"
  | _ -> 0

(* The first function component names the source. Nested functions and anonymous
   closures belong to it; their suffix is not part of the name to validate.
   Preserve digits: [function0] and [function] can be different functions. *)
let rec function_end name length start qualified =
  let stop = component_end name length start in
  if stop <= start then -1
  else if upper name.[start] then
    if stop = length then -1
    else function_end name length (stop + 1) true
  else if qualified && function_start name start stop then stop
  else -1

let canonical raw =
  let length = String.length raw in
  let start = wrapper_end raw length in
  let stop = function_end raw length start false in
  if stop < 0 then
    invalid_arg "Cerb_log: expected a qualified function name (use __FUNCTION__)"
  else if start = 0 && stop = length then raw
  else String.sub raw start (stop - start)

let selected selectors =
  let names = Names.create (List.length selectors) in
  List.iter (fun name -> Names.replace names name ()) selectors;
  fun name ->
    Names.mem names name ||
    match String.rindex_opt name '.' with
    | Some dot when dot + 1 < String.length name && not (upper name.[dot + 1]) ->
        Names.mem names (String.sub name 0 dot)
    | _ -> false
