(** Discover the path to the Cerberus runtime. *)

let cerblib_pkgname = "cerberus-lib"

(** If it is set, [specified_runtime] has highest priority, and it can thus be
    used to override the "detected" runtime path from the CLI for example. *)
let specified_runtime : string option ref = ref None

let (/) = Filename.concat

(** [find_cerblib_sourceroot ()] attempts to locate the build-time source
    directory for Cerberus packages (inside the Dune [_build] directory) using
    the PATH and by looking for [cerberus-lib.opam]. *)
let find_cerblib_sourceroot () =
  let path = String.split_on_char ':' (Sys.getenv "PATH") in
  let suffix_r = Str.regexp {|^\(.*\)/_build/install/[a-z][a-z\-]*/bin$|} in
  let rec find_prefix path =
    match path with
    | []        -> None
    | p :: path ->
        if Str.string_match suffix_r p 0
        then Some (Str.matched_group 1 p)
        else find_prefix path
  in
  Option.bind (find_prefix path) (fun z ->
    if not (Sys.file_exists (z / cerblib_pkgname ^ ".opam")) then
      None
    else
      Some z
  )

type runtime_loc = {
  cerblib_sourceroot_opt: string option;
  mk: pkg:string -> [ `SPECIFIED | `ENV_VAR | `OPAM ] * string;
}

(** [detect_runtime ()] locates the cerberus runtime. Note that if opam is not
    properly initialized then the function may raise [Failure]. *)
let detect_runtime : unit -> runtime_loc = fun _ ->
  (* First check for specified runtime. *)
  let wrap ?(check_sourceroot=false) source prefix =
    { cerblib_sourceroot_opt=
        if check_sourceroot then
          (* Then check for build time runtime (in repository). *)
          find_cerblib_sourceroot ()
        else None
    ; mk= fun ~pkg -> source, prefix / "lib" / pkg / "runtime" } in
  match !specified_runtime with Some(path) -> wrap `SPECIFIED path | None ->
  (* Then check the CERB_INSTALL_PREFIX environment variable. *)
  try wrap `ENV_VAR (Sys.getenv "CERB_INSTALL_PREFIX") with Not_found ->
  (* Fall back to installed runtime under the opam switch prefix. *)
  try wrap ~check_sourceroot:true `OPAM (Sys.getenv "OPAM_SWITCH_PREFIX")
  with Not_found ->
    failwith "OPAM_SWITCH_PREFIX not set."

(** [runtime ()] is a memoised version of [detect_runtime ()]. This means that
    if [Failure] is not raised on its first call, it will not be raised later,
    during other calls. *)
let runtime : unit -> runtime_loc =
  let runtime = Lazy.from_fun detect_runtime in
  fun _ -> Lazy.force runtime

(** [in_runtime pkg path] appends [path] to the Cerberus' package [pkg]
    (["cerberus-lib"] when absent) runtime path (as returned by [runtime ()].
    Exceptions [Failure] can be raised accordingly. *)
let in_runtime ?pkg : string -> string = fun path ->
  let pkg_is_cerblib, pkg = match pkg with
    | None -> true, cerblib_pkgname
    | Some pkg -> String.equal cerblib_pkgname pkg, pkg in
  let runtime = runtime () in
  (match runtime.cerblib_sourceroot_opt with
    | Some sourceroot when pkg_is_cerblib ->
        sourceroot / "runtime"
    | _ ->
        snd (runtime.mk ~pkg)
  ) / path
