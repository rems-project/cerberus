open AilSyntax

type typed_ail = GenTypes.genTypeCategory AilSyntax.ail_program

(** [section_name fname] builds a reasonable Coq section name from a file. The
    slash, dash and dot characters are replaced by underscores. Note that this
    function will miserably fail on weird file names (e.g., ["A file.c"]). *)
let section_name : string -> string = fun fname ->
  let cleanup name c = String.concat "_" (String.split_on_char c name) in
  List.fold_left cleanup fname ['/'; '-'; '.']

let run : string -> typed_ail -> unit = fun fname (entry_point, sigma) ->
  (* Extract the different parts of the AST. *)
  let decls      = sigma.declarations         in
  (*let obj_defs   = sigma.object_definitions   in*)
  let fun_defs   = sigma.function_definitions in
  (*let assertions = sigma.static_assertions    in*)
  let tag_defs   = sigma.tag_definitions      in
  (*let ext_idmap  = sigma.extern_idmap         in*)

  (* Formatting utilities. *)
  let indent = ref 0 in
  let line fmt =
    let s = String.make (2 * !indent) ' ' in
    Printf.printf ("%s" ^^ fmt ^^ "\n%!") s
  in
  let comment fmt = line ("(* " ^^ fmt ^^ " *)") in
  let skip_line () = Printf.printf "\n%!" in

  (* Short names for common functions. *)
  let sym_to_str = Pp_symbol.to_string_pretty in

  (* Printing some header. *)
  line "From refinedc.lang Require Export notation.";
  line "Set Default Proof Using \"Type\".";
  skip_line ();

  (* Printing generation data and entry point in a comment. *)
  let entry_point =
    match entry_point with
    | None     -> ""
    | Some(id) -> Printf.sprintf ", entry point [%s]" (sym_to_str id)
  in
  comment "Generated from [%s]%s." fname entry_point;

  (* Opening the section. *)
  let sect = section_name fname in
  line "Section %s." sect;
  incr indent;

  (* Declaration of objects (global variable) in the context. *)
  let decl_obj (id, (_, decl)) =
    match decl with
    | Decl_object _ -> line "Context (%s : loc)." (sym_to_str id);
    | _             -> ()
  in
  comment "Global variables.";
  List.iter decl_obj decls;

  (* Declaration of functions in the context. *)
  skip_line ();
  let decl_obj (id, (_, decl)) =
    match decl with
    | Decl_function _ -> line "Context (%s : loc)." (sym_to_str id);
    | _               -> ()
  in
  comment "Functions.";
  List.iter decl_obj decls;

  (* Definition of structs. *)
  let tag_def (id, def) =
    let id = sym_to_str id in
    skip_line ();
    comment "Definition of struct [%s]." id;
    line "Program Definition %s := {|" id;
    incr indent;
    line "sl_members := [";
    incr indent;
    comment "TODO 1"; (* TODO *)
    decr indent;
    line "];";
    decr indent;
    line "|}.";
    line "Next Obligation. do ! constructor; set_solver. Qed."
  in
  List.iter tag_def tag_defs;

  (* Definition of functions. *)
  let fun_def (id, def) =
    let id = sym_to_str id in
    skip_line ();
    comment "Definition of function [%s]." id;
    line "Definition impl_%s : function := {|" id;
    incr indent;
    line "f_args := [";
    incr indent;
    comment "TODO 2"; (* TODO *)
    decr indent;
    line "];";
    line "f_local_vars := [";
    incr indent;
    comment "TODO 3"; (* TODO *)
    decr indent;
    line "];";
    line "f_init := \"init\";";
    line "f_code := [";
    incr indent;
    comment "TODO 4"; (* TODO *)
    decr indent;
    line "];";
    decr indent;
    line "|}."
  in
  List.iter fun_def fun_defs;

  (* Closing the section. *)
  decr indent;
  line "End %s." sect


(* Reference output **********************************************************

Program Definition struct_mpool := {|
  sl_members := [("entry_list", LPtr)];
|}.
Next Obligation. do ! constructor; set_solver. Qed.

Program Definition struct_mpool_entry := {|
  sl_members := [("next", LPtr)];
|}.
Next Obligation. do ! constructor; set_solver. Qed.

Definition mpool_init : function := {|
  f_args := [("p", LPtr)];
  f_local_vars := [];
  f_init := "init";
  f_code := {[ "init" :=
                 (!{LPtr}"p") at{struct_mpool} "entry_list" <-{LPtr} NULL;
                 Return VOID ]}%E;
|}.

Definition mpool_get : function := {|
  f_args := [("p", LPtr)];
  f_local_vars := [("entry", LPtr)];
  f_init := "init";
  f_code := {[ "init" :=
    if: use{LPtr} (!{LPtr} "p" at{struct_mpool} "entry_list") = NULL
    then Return NULL else
    "entry" <-{LPtr} use{LPtr} (!{LPtr} "p" at{struct_mpool} "entry_list");
    (!{LPtr} "p" at{struct_mpool} "entry_list") <-{LPtr} use{LPtr} (!{LPtr} "entry" at{struct_mpool_entry} "next");
    Return (use{LPtr} "entry") ]}%E;
|}.

Definition mpool_put : function := {|
  f_args := [("p", LPtr); ("ptr", LPtr)];
  f_local_vars := [("e", LPtr)];
  f_init := "init";
  f_code := {[ "init" :=
                 "e" <-{LPtr} use{LPtr} "ptr";
                 (!{LPtr} "e" at{struct_mpool_entry} "next") <-{LPtr} use{LPtr} (!{LPtr} "p" at{struct_mpool} "entry_list");
                 (!{LPtr} "p" at{struct_mpool} "entry_list") <-{LPtr} use{LPtr} "e";
                 Return VOID ]}%E;
|}.

Definition main : function := {|
  f_args := [];
  f_local_vars := [("p", layout_of struct_mpool); ("p1", LPtr); ("p2", LPtr)];
  f_init := "init";
  f_code := {[ "init" :=
                 "_" <- mpool_init with [& "p"];
                 "_" <- mpool_put with [& "p"; &e1 ];
                 "_" <- mpool_put with [& "p"; &e2 ];
                 "r1" <- mpool_get with [& "p" ];
                 "p1" <-{LPtr} "r1";
                 if: use{LPtr} "p1" = NULL then Goto "abort" else
                 "r2" <- mpool_get with [& "p" ];
                 "p2" <-{LPtr} "r2";
                 if: use{LPtr} "p2" = NULL then Goto "abort" else
                 Return VOID ]}%E;
|}.
*****************************************************************************)
