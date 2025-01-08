module Config = TestGenConfig
open Pp

let setup ~output_dir =
  string "#!/bin/bash"
  ^^ twice hardline
  ^^ string "# copied from cn-runtime-single-file.sh"
  ^^ hardline
  ^^ string "RUNTIME_PREFIX=\"$OPAM_SWITCH_PREFIX/lib/cn/runtime\""
  ^^ hardline
  ^^ string "[ -d \"${RUNTIME_PREFIX}\" ]"
  ^^ space
  ^^ twice bar
  ^^ space
  ^^ parens
       (nest
          4
          (hardline
           ^^ string
                "printf \"Could not find CN's runtime directory (looked at: \
                 '${RUNTIME_PREFIX}')\""
           ^^ hardline
           ^^ string "exit 1")
        ^^ hardline)
  ^^ twice hardline
  ^^ string ("TEST_DIR=" ^ Filename.dirname (Filename.concat output_dir "junk"))
  ^^ hardline
  ^^ string "pushd $TEST_DIR > /dev/null"
  ^^ hardline


let attempt cmd success failure =
  separate_map space string [ "if"; cmd; ";"; "then" ]
  ^^ nest 4 (hardline ^^ string ("echo \"" ^ success ^ "\""))
  ^^ hardline
  ^^ string "else"
  ^^ nest
       4
       (hardline ^^ string ("printf \"" ^ failure ^ "\"") ^^ hardline ^^ string "exit 1")
  ^^ hardline
  ^^ string "fi"


let cc_flags () =
  [ "-g"; "\"-I${RUNTIME_PREFIX}/include/\"" ]
  @ (let sanitize, no_sanitize = Config.has_sanitizers () in
     (match sanitize with Some sanitize -> [ "-fsanitize=" ^ sanitize ] | None -> [])
     @
     match no_sanitize with
     | Some no_sanitize -> [ "-fno-sanitize=" ^ no_sanitize ]
     | None -> [])
  @
  if Config.is_coverage () then
    [ "--coverage" ]
  else
    []


let compile ~filename_base =
  string "# Compile"
  ^^ hardline
  ^^ attempt
       (String.concat
          " "
          ([ "cc";
             "-c";
             "-o";
             "\"./" ^ filename_base ^ "_test.o\"";
             "\"./" ^ filename_base ^ "_test.c\""
           ]
           @ cc_flags ()))
       ("Compiled '" ^ filename_base ^ "_test.c'.")
       ("Failed to compile '" ^ filename_base ^ "_test.c' in ${TEST_DIR}.")
  ^^ (if Config.with_static_hack () then
        empty
      else
        twice hardline
        ^^ attempt
             (String.concat
                " "
                ([ "cc";
                   "-c";
                   "-o";
                   "\"./" ^ filename_base ^ "-exec.o\"";
                   "\"./" ^ filename_base ^ "-exec.c\""
                 ]
                 @ cc_flags ()))
             ("Compiled '" ^ filename_base ^ "-exec.c'.")
             ("Failed to compile '" ^ filename_base ^ "-exec.c' in ${TEST_DIR}.")
        ^^ twice hardline
        ^^ attempt
             (String.concat
                " "
                ([ "cc"; "-c"; "-o"; "\"./cn.o\""; "\"./cn.c\"" ] @ cc_flags ()))
             "Compiled 'cn.c'."
             "Failed to compile 'cn.c' in ${TEST_DIR}.")
  ^^ hardline


let link ~filename_base =
  string "# Link"
  ^^ hardline
  ^^ string "echo"
  ^^ twice hardline
  ^^ attempt
       (String.concat
          " "
          ([ "cc";
             "-o";
             "\"./tests.out\"";
             (filename_base
              ^ "_test.o"
              ^
              if Config.with_static_hack () then
                ""
              else
                " " ^ filename_base ^ "-exec.o cn.o");
             "\"${RUNTIME_PREFIX}/libcn.a\""
           ]
           @ cc_flags ()))
       "Linked C *.o files."
       "Failed to link *.o files in ${TEST_DIR}."
  ^^ hardline


let run () =
  let cmd =
    separate_map
      space
      string
      ([ "./tests.out" ]
       @ (Config.has_input_timeout ()
          |> Option.map (fun input_timeout ->
            [ "--input-timeout"; string_of_int input_timeout ])
          |> Option.to_list
          |> List.flatten)
       @ (Config.has_null_in_every ()
          |> Option.map (fun null_in_every ->
            [ "--null-in-every"; string_of_int null_in_every ])
          |> Option.to_list
          |> List.flatten)
       @ (Config.has_seed ()
          |> Option.map (fun seed -> [ "--seed"; seed ])
          |> Option.to_list
          |> List.flatten)
       @ (Config.has_logging_level ()
          |> Option.map (fun level -> [ "--logging-level"; string_of_int level ])
          |> Option.to_list
          |> List.flatten)
       @ (Config.has_progress_level ()
          |> Option.map (fun level -> [ "--progress-level"; string_of_int level ])
          |> Option.to_list
          |> List.flatten)
       @ (if Config.is_interactive () then
            [ "--interactive" ]
          else
            [])
       @ (match Config.is_until_timeout () with
          | Some timeout -> [ "--until-timeout"; string_of_int timeout ]
          | None -> [])
       @ (if Config.is_exit_fast () then
            [ "--exit-fast" ]
          else
            [])
       @ (Config.has_max_stack_depth ()
          |> Option.map (fun max_stack_depth ->
            [ "--max-stack-depth"; string_of_int max_stack_depth ])
          |> Option.to_list
          |> List.flatten)
       @ (Config.has_max_generator_size ()
          |> Option.map (fun max_generator_size ->
            [ "--max-generator-size"; string_of_int max_generator_size ])
          |> Option.to_list
          |> List.flatten)
       @ (if Config.is_sized_null () then
            [ "--sized-null" ]
          else
            [])
       @ (Config.has_allowed_depth_failures ()
          |> Option.map (fun allowed_depth_failures ->
            [ "--allowed-depth-failures"; string_of_int allowed_depth_failures ])
          |> Option.to_list
          |> List.flatten)
       @ (Config.has_allowed_size_split_backtracks ()
          |> Option.map (fun allowed_size_split_backtracks ->
            [ "--allowed-size-split-backtracks";
              string_of_int allowed_size_split_backtracks
            ])
          |> Option.to_list
          |> List.flatten))
  in
  string "# Run"
  ^^ hardline
  ^^ string "echo"
  ^^ twice hardline
  ^^ cmd
  ^^ hardline
  ^^ string "test_exit_code=$? # Save tests exit code for later"
  ^^ hardline


let coverage ~filename_base =
  string "# Coverage"
  ^^ hardline
  ^^ attempt
       ("gcov \"" ^ filename_base ^ "_test.c\"")
       "Recorded coverage via gcov."
       "Failed to record coverage."
  ^^ twice hardline
  ^^ attempt
       "lcov --capture --directory . --output-file coverage.info"
       "Collected coverage via lcov."
       "Failed to collect coverage."
  ^^ twice hardline
  ^^ attempt
       "genhtml --output-directory html \"coverage.info\""
       "Generated HTML report at '${TEST_DIR}/html/'."
       "Failed to generate HTML report."
  ^^ hardline


let generate ~(output_dir : string) ~(filename_base : string) : Pp.document =
  setup ~output_dir
  ^^ hardline
  ^^ compile ~filename_base
  ^^ hardline
  ^^ link ~filename_base
  ^^ hardline
  ^^ run ()
  ^^ hardline
  ^^ (if Config.is_coverage () then
        coverage ~filename_base ^^ hardline
      else
        empty)
  ^^ string "popd > /dev/null"
  ^^ hardline
  ^^ string "exit $test_exit_code"
  ^^ hardline
