let git_version =
  let cmd = "git describe --dirty --always" in
  let (oc, ic, ec) = Unix.open_process_full cmd (Unix.environment ()) in
  let version =
    try Printf.sprintf "git-%s" (input_line oc)
    with End_of_file -> "unknown"
  in
  match Unix.close_process_full (oc, ic, ec) with
  | Unix.WEXITED(0) -> version
  | _               -> "unknown"

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
  line "(** [version] gives a version description. *)";
  line "let version : string = \"%s\"" version
