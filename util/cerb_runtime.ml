(** Discover the path to the Cerberus runtime. *)

(** If it is set, [specified_runtime] has highest priority, and it can thus be
    used to override the "detected" runtime path from the CLI for example. *)
let specified_runtime : string option ref = ref None

(** [find_build_runtime ()] attempts to locate the build-time Cerberus runtime
    (inside the Dune [_build] directory) using the PATH. Exception [Not_found]
    is raised in case of failure. *)
let find_build_runtime : unit -> string = fun _ ->
  let path = String.split_on_char ':' (Sys.getenv "PATH") in
  let suffix = "/_build/install/default/bin" in
  let len_suffix = String.length suffix in
  let rec find_prefix path =
    match path with
    | []        -> raise Not_found
    | p :: path ->
    let len = String.length p in
    if len < len_suffix then find_prefix path else
    let p_suffix = String.sub p (len - len_suffix) len_suffix in
    if p_suffix <> suffix then find_prefix path else
    String.sub p 0 (len - len_suffix)
  in
  let runtime_path =
    Filename.concat (find_prefix path)
      "_build/install/default/lib/cerberus/runtime"
  in
  if not (Sys.file_exists runtime_path) then raise Not_found;
  runtime_path

(** [detect_runtime ()] locates the cerberus runtime. Note that if opam is not
    properly initialized then the function may raise [Failure]. *)
let detect_runtime : unit -> string = fun _ ->
  (* First check for specified runtime. *)
  match !specified_runtime with Some(path) -> path | None ->
  (* Then check the CERB_RUNTIME environment variable. *)
  try Sys.getenv "CERB_RUNTIME" with Not_found ->
  (* Then check for build time runtime (in repository). *)
  try find_build_runtime () with Not_found ->
  (* Fall back to installed runtime under the opam switch prefix. *)
  let prefix =
    try Sys.getenv "OPAM_SWITCH_PREFIX"
    with Not_found -> failwith "OPAM_SWITCH_PREFIX not set."
  in
  Filename.concat prefix "lib/cerberus/runtime"

(** [runtime ()] is a memoised version of [detect_runtime ()]. This means that
    if [Failure] is not raised on its first call, it will not be raised later,
    during other calls. *)
let runtime : unit -> string =
  let runtime = Lazy.from_fun detect_runtime in
  fun _ -> Lazy.force runtime

(** [in_runtime path] appends [path] to the Cerberus runtime path (as returned
    by [runtime ()]. Exceptions [Failure] can be raised accordingly. *)
let in_runtime : string -> string = fun path ->
  Filename.concat (runtime ()) path
