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


let compile ~test_file =
  string "# Compile"
  ^^ hardline
  ^^ attempt
       (String.concat
          " "
          ([ "cc";
             "-g";
             "-c";
             "\"-I${RUNTIME_PREFIX}/include/\"";
             "-o";
             "\"./" ^ Filename.chop_extension test_file ^ ".o\"";
             "\"./" ^ test_file ^ "\""
           ]
           @
           if Config.is_coverage () then
             [ "--coverage" ]
           else
             []))
       "Compiled C files."
       "Failed to compile C files in ${TEST_DIR}."
  ^^ hardline


let link ~test_file =
  string "# Link"
  ^^ hardline
  ^^ attempt
       (String.concat
          " "
          ([ "cc";
             "-g";
             "\"-I${RUNTIME_PREFIX}/include\"";
             "-o";
             "\"./tests.out\"";
             Filename.chop_extension test_file ^ ".o";
             "\"${RUNTIME_PREFIX}/libcn.a\""
           ]
           @
           if Config.is_coverage () then
             [ "--coverage" ]
           else
             []))
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
  ^^ cmd
  ^^ hardline
  ^^ string "test_exit_code=$? # Save tests exit code for later"
  ^^ hardline


let coverage ~test_file =
  string "# Coverage"
  ^^ hardline
  ^^ attempt
       ("gcov \"" ^ test_file ^ "\"")
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
       "Generated HTML report at \\\"${TEST_DIR}/html/\\\"."
       "Failed to generate HTML report."
  ^^ hardline


let generate ~(output_dir : string) ~(test_file : string) : Pp.document =
  setup ~output_dir
  ^^ hardline
  ^^ compile ~test_file
  ^^ hardline
  ^^ link ~test_file
  ^^ hardline
  ^^ run ()
  ^^ hardline
  ^^ (if Config.is_coverage () then
        coverage ~test_file ^^ hardline
      else
        empty)
  ^^ string "popd > /dev/null"
  ^^ hardline
  ^^ string "exit $test_exit_code"
  ^^ hardline
