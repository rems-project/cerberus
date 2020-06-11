let sad = " " ^ Ansi.start_red ^ "sad" ^ Ansi.reset_colour
let happy = " " ^ Ansi.start_green ^ "happy" ^ Ansi.reset_colour ^ "\n"
let rejected_as_expected = " " ^ Ansi.start_green ^ "rejected as expected" ^ Ansi.reset_colour ^ "\n"
let unexpectedly_accepted = " " ^ Ansi.start_red ^ "unexpectedly accepted" ^ Ansi.reset_colour ^ "\n"

let check_function2 stys ftys id f =
  match Typechecker.check_function stys ftys id f with
  | RC_skip -> " " ^ Ansi.start_yellow ^ "skipped" ^  Ansi.reset_colour ^ "\n"
  | RC_consider RC_typechecks_as_expected -> happy
  | RC_consider (RC_fails_to_typecheck err) -> sad ^ ": " ^ Typechecker.Type_error.string_of err ^ "\n"
  | RC_consider RC_rejected_as_expected -> rejected_as_expected
  | RC_consider RC_unexpectedly_typechecks -> unexpectedly_accepted

let check_function3 stys (ftys : Typechecker.fun_spec_t Rustic_types.String_map.t) id f =
  print_string (id ^ ":");
  flush stdout;
  print_string (check_function2 stys ftys id f)

let run_rustic (id, s) =
  let fs = Typechecker.collect_functions s in
  let stys = Typechecker.collect_structs s in
  let ftys = Typechecker.collect_function_types fs in
  Rustic_types.String_map.iter (check_function3 stys ftys) fs;
  ()