(* Configure once before starting workers. The policy, selector table and
   source levels remain unchanged until all workers have joined. Only the
   memo table and its writer-protected source registry grow during use. *)
external pointer_hash : string -> int = "cerb_log_pointer_hash" [@@noalloc]
external is_static : string -> bool = "cerb_log_is_static" [@@noalloc]
module Pointer = struct
  type t = string
  let equal = (==)
  let hash = pointer_hash
end
module Names = Hashtbl.Make (String)

type policy = {
  active : bool;
  select : string -> bool;
  pointers : (string, Logs.src option) Saturn.Htbl.t;
  sources : Logs.src Names.t;
  writer : Mutex.t;
}

let fresh active select = {
  active; select;
  pointers = Saturn.Htbl.create ~hashed_type:(module Pointer) ();
  sources = Names.create 32;
  writer = Mutex.create ();
}
let policy = ref (fresh false (fun _ -> false))

let selected_source p name =
  if not (p.select name) then None else
  let src = match Names.find_opt p.sources name with
    | Some src -> src
    | None ->
        let src = Logs.Src.create name in
        Logs.Src.set_level src (Some Logs.Debug);
        Names.add p.sources name src;
        src in
  Some src

let[@inline never] first_use p raw =
  (* Heap strings can move, changing their address hash. They never enter the
     table. Looking one up before this check cannot match a static address;
     validation therefore belongs only on the miss path. *)
  if not (is_static raw) then
    invalid_arg "Cerb_log_auto: expected a static source name (use __FUNCTION__)";
  Mutex.lock p.writer;
  Fun.protect ~finally:(fun () -> Mutex.unlock p.writer) (fun () ->
    (* Another domain may have populated the entry while we waited. Keep
       normalization, source creation and insertion within the same lock so
       aliases and concurrent first calls share a single registered source. *)
    match Saturn.Htbl.find_exn p.pointers raw with
    | decision -> decision
    | exception Not_found ->
        let decision = selected_source p (Cerb_log_names.canonical raw) in
        if not (Saturn.Htbl.try_add p.pointers raw decision) then
          failwith "Cerb_log_auto: duplicate insertion under writer lock";
        decision)

let source p raw =
  (* [find_exn] returns the cached option itself. [find_opt] would allocate an
     additional outer [Some] on each hit. [None] is a cached rejection, while
     [Not_found] means this address has not yet been resolved. *)
  match Saturn.Htbl.find_exn p.pointers raw with
  | decision -> decision
  | exception Not_found -> first_use p raw

let configure ?(discover=false) level selectors =
  List.iter (fun name ->
    if name <> "all" && not (Cerb_log_names.valid_selector name) then
      invalid_arg ("invalid debug selector: " ^ name)) selectors;
  let all = level = Some Logs.Debug || List.mem "all" selectors in
  let active = level <> None && (all || selectors <> []) in
  let select = if not active then (fun _ -> false) else if all then (fun _ -> true)
    else Cerb_log_names.selected selectors in
  (* Listing observes disabled sites too, without enabling their messages. *)
  let p = fresh (active || discover) select in
  List.iter (fun src ->
    let name = Logs.Src.name src in
    Logs.Src.set_level src (if select name then Some Logs.Debug else level);
    Names.replace p.sources name src) (Logs.Src.list ());
  policy := p

let sources () =
  (* Call after workers join. Include negative entries without registering
     Logs sources for them or retaining a second table of their names. *)
  let encountered = Saturn.Htbl.to_seq (!policy).pointers
    |> Seq.map (fun (raw, _) -> Cerb_log_names.canonical raw)
    |> List.of_seq in
  List.sort_uniq String.compare
    (encountered @ List.map Logs.Src.name (Logs.Src.list ()))

let debug_enabled raw =
  let p = !policy in
  p.active && Option.is_some (source p raw)

let debugf raw message =
  let p = !policy in
  if p.active then match source p raw with
    | None -> ()
    | Some src -> Logs.debug ~src message

let debug raw message =
  let p = !policy in
  if p.active then match source p raw with
    | None -> ()
    | Some src -> Logs.debug ~src (fun m -> m "%s" (message ()))

let debug_located raw loc message =
  let p = !policy in
  if p.active then match source p raw with
    | None -> ()
    | Some src -> Cerb_log.debug_located src loc message
