let run_cmd cmd =
  let (oc, ic, ec) = Unix.open_process_full cmd (Unix.environment ()) in
  let version =
    try Some (Printf.sprintf "%s" (input_line oc))
    with End_of_file -> None
  in
  match Unix.close_process_full (oc, ic, ec) with
  | Unix.WEXITED(0) -> version
  | _               -> None

let git_version =
  Option.map ((^) "git-") @@ run_cmd "git describe --dirty --always"

let git_version_date =
  Option.bind (run_cmd "git describe --always") (fun hash ->
    run_cmd ("git show --no-patch --format=\"%ci\" " ^ hash))

let or_unknown = Option.value ~default:"unknown"

let git_version = git_version |> or_unknown

let git_version_date = git_version_date |> or_unknown

let version =
  (* Trick to check whether the watermark has been substituted. *)
  if "%%VERSION%%" <> "%%" ^ "VERSION%%" then "%%VERSION%%" else
  (* If not, we fallback to git version. *)
  git_version

let _ =
  let line fmt = Printf.printf (fmt ^^ "\n%!") in
  line "(** Version informations. *)";
  line "";
  line "(** [git_version] gives a git commit version description. *)";
  line "let git_version : string = \"%s\"" git_version;
  line "";
  line "(** [git_version_date] gives a commit version date. *)";
  line "let git_version_date : string = \"%s\"" git_version_date;
  line "";
  line "(** [version] gives a version description. *)";
  line "let version : string = \"%s\"" version
