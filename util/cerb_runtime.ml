(** Discover the path to the Cerberus runtime. *)

let cerblib_pkgname = "cerberus-lib"

(** If it is set, [specified_runtime] has highest priority, and it can thus be
    used to override the "detected" runtime path from the CLI for example. *)
let specified_runtime : string option ref = ref None

(** [find_build_install_path ()] attempts to locate the build-time install
    directory for Cerberus packages (inside the Dune [_build] directory) using
    the PATH. Exception [Not_found] is raised in case of failure. *)
let [@warning "-32"] find_build_install_path : unit -> string = fun _ ->
  let path = String.split_on_char ':' (Sys.getenv "PATH") in
  let suffix_r = Str.regexp {|^\(.*/_build/install/[a-z][a-z\-]*\)/bin$|} in
  let rec find_prefix path =
    match path with
    | []        -> raise Not_found
    | p :: path ->
        if Str.string_match suffix_r p 0
        then Str.matched_group 1 p
        else find_prefix path
  in
  let install_path = find_prefix path in
  if not Sys.(file_exists install_path && is_directory install_path) then
    raise Not_found;
  install_path

type runtime_loc = {
  source: [ `SPECIFIED | `ENV_VAR | `BUILD_DIR | `OPAM ];
  mk: pkg:string -> string;
}

(** [detect_runtime ()] locates the cerberus runtime. Note that if opam is not
    properly initialized then the function may raise [Failure]. *)
let detect_runtime : unit -> runtime_loc = fun _ ->
  (* First check for specified runtime. *)
  let wrap source prefix =
    { source
    ; mk= fun ~pkg ->
        Filename.(concat (concat prefix "lib") (concat pkg "runtime")) } in
  match !specified_runtime with Some(path) -> wrap `SPECIFIED path | None ->
  (* Then check the CERB_INSTALL_PREFIX environment variable. *)
  try wrap `ENV_VAR (Sys.getenv "CERB_INSTALL_PREFIX") with Not_found ->
  (* Then check for build time runtime (in repository). *)
  (* TODO: temporarily disabling the dune runtime discovery for the CN split
           because it does not work with pinned opam installs *)
  (* try wrap `BUILD_DIR (find_build_install_path ()) with Not_found -> *)
  (* Fall back to installed runtime under the opam switch prefix. *)
  try wrap `OPAM (Sys.getenv "OPAM_SWITCH_PREFIX") with Not_found ->
  failwith "OPAM_SWITCH_PREFIX not set."

(** [runtime ()] is a memoised version of [detect_runtime ()]. This means that
    if [Failure] is not raised on its first call, it will not be raised later,
    during other calls. *)
let runtime : unit -> runtime_loc =
  let runtime = Lazy.from_fun detect_runtime in
  fun _ -> Lazy.force runtime

(** [in_runtime path] appends [path] to the Cerberus runtime path (as returned
    by [runtime ()]. Exceptions [Failure] can be raised accordingly. *)
let in_runtime ?pkg : string -> string = fun path ->
  let runtime =
    (runtime ()).mk ~pkg:(Option.fold ~none:cerblib_pkgname ~some:Fun.id pkg) in
  Filename.concat runtime path
