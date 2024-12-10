module CF = Cerb_frontend
module A = CF.AilSyntax
module C = CF.Ctype
module BT = BaseTypes
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module CtA = Cn_internal_to_ail
module Utils = Executable_spec_utils
module ESpecInternal = Executable_spec_internal
module Config = TestGenConfig
module SymSet = Set.Make (Sym)

let debug_log_file : out_channel option ref = ref None

let debug_log (str : string) : unit =
  match !debug_log_file with
  | Some oc ->
    output_string oc str;
    flush oc
  | None -> ()


let debug_stage (stage : string) (str : string) : unit =
  debug_log (stage ^ ":\n");
  debug_log (str ^ "\n\n")


let pp_label ?(width : int = 30) (label : string) : Pp.document =
  let padding = max 2 ((width - (String.length label + 2)) / 2) in
  let open Pp in
  repeat width slash
  ^^ hardline
  ^^ repeat padding slash
  ^^ space
  ^^ string label
  ^^ space
  ^^ repeat padding slash
  ^^ hardline
  ^^ repeat width slash


let compile_unit_tests (insts : Executable_spec_extract.instrumentation list) =
  let open Pp in
  separate_map
    (semi ^^ twice hardline)
    (fun (inst : Executable_spec_extract.instrumentation) ->
      CF.Pp_ail.pp_statement
        A.(
          Utils.mk_stmt
            (AilSexpr
               (Utils.mk_expr
                  (AilEcall
                     ( Utils.mk_expr (AilEident (Sym.fresh_named "CN_UNIT_TEST_CASE")),
                       [ Utils.mk_expr (AilEident inst.fn) ] ))))))
    insts


let compile_generators
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (prog5 : unit Mucore.file)
  (insts : Executable_spec_extract.instrumentation list)
  : PPrint.document
  =
  let ctx = GenCompile.compile prog5.resource_predicates insts in
  debug_stage "Compile" (ctx |> GenDefinitions.pp_context |> Pp.plain ~width:80);
  let ctx = ctx |> GenInline.inline in
  debug_stage "Inline" (ctx |> GenDefinitions.pp_context |> Pp.plain ~width:80);
  let ctx = ctx |> GenNormalize.normalize prog5 in
  debug_stage "Normalize" (ctx |> GenDefinitions.pp_context |> Pp.plain ~width:80);
  let ctx = ctx |> GenDistribute.distribute in
  debug_stage "Distribute" (ctx |> GenDefinitions.pp_context |> Pp.plain ~width:80);
  let ctx = ctx |> GenOptimize.optimize prog5 in
  debug_stage "Optimize" (ctx |> GenDefinitions.pp_context |> Pp.plain ~width:80);
  let ctx = ctx |> GenRuntime.elaborate in
  debug_stage "Elaborated" (ctx |> GenRuntime.pp |> Pp.plain ~width:80);
  ctx |> GenCodeGen.compile sigma


let compile_random_test_case
  (prog5 : unit Mucore.file)
  (args_map : (Sym.t * (Sym.t * C.ctype) list) list)
  (convert_from : Sym.t * C.ctype -> Pp.document)
  (inst : Executable_spec_extract.instrumentation)
  : Pp.document
  =
  let open Pp in
  let args = List.assoc Sym.equal inst.fn args_map in
  let globals =
    let global_syms =
      let args = args |> List.map fst in
      inst.internal
      |> Option.get
      |> AT.get_lat
      |> LAT.free_vars (fun _ -> SymSet.empty)
      |> SymSet.to_seq
      |> List.of_seq
      |> List.filter (fun x ->
        not
          (List.mem (fun x y -> String.equal (Sym.pp_string x) (Sym.pp_string y)) x args))
    in
    List.map
      (fun sym ->
        match List.assoc Sym.equal sym prog5.globs with
        | GlobalDecl sct -> (sym, sct)
        | GlobalDef (sct, _) -> (sym, sct))
      global_syms
  in
  (if List.is_empty globals then
     string "CN_RANDOM_TEST_CASE"
   else (
     let init_name = string "cn_test_" ^^ Sym.pp inst.fn ^^ string "_init" in
     string "void"
     ^^ space
     ^^ init_name
     ^^ parens
          (string "struct"
           ^^ space
           ^^ string (String.concat "_" [ "cn_gen"; Sym.pp_string inst.fn; "record" ])
           ^^ star
           ^^ space
           ^^ string "res")
     ^^ space
     ^^ braces
          (nest
             2
             (hardline
              ^^ separate_map
                   hardline
                   (fun (sym, sct) ->
                     let ty =
                       CF.Pp_ail.pp_ctype
                         ~executable_spec:true
                         ~is_human:false
                         C.no_qualifiers
                         (Sctypes.to_ctype sct)
                     in
                     Sym.pp sym
                     ^^ space
                     ^^ equals
                     ^^ space
                     ^^ star
                     ^^ parens (ty ^^ star)
                     ^^ string "convert_from_cn_pointer"
                     ^^ parens (string "res->cn_gen_" ^^ Sym.pp sym)
                     ^^ semi
                     ^^ hardline
                     ^^ string "cn_assume_ownership"
                     ^^ parens
                          (separate
                             (comma ^^ space)
                             [ ampersand ^^ Sym.pp sym;
                               string "sizeof" ^^ parens ty;
                               string "(char*)" ^^ dquotes init_name
                             ])
                     ^^ semi)
                   globals)
           ^^ hardline)
     ^^ twice hardline
     ^^ string "CN_RANDOM_TEST_CASE_WITH_INIT"))
  ^^ parens
       (separate
          (comma ^^ space)
          [ inst.fn_loc
            |> Cerb_location.get_filename
            |> Option.get
            |> Filename.basename
            |> String.split_on_char '.'
            |> List.hd
            |> string;
            Sym.pp inst.fn;
            int (Config.get_num_samples ());
            separate_map (comma ^^ space) convert_from args
          ])
  ^^ twice hardline


let compile_random_tests
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (prog5 : unit Mucore.file)
  (insts : Executable_spec_extract.instrumentation list)
  : Pp.document
  =
  let declarations : A.sigma_declaration list =
    insts
    |> List.map (fun (inst : Executable_spec_extract.instrumentation) ->
      (inst.fn, List.assoc Sym.equal inst.fn sigma.declarations))
  in
  let args_map : (Sym.t * (Sym.t * C.ctype) list) list =
    List.map
      (fun (inst : Executable_spec_extract.instrumentation) ->
        ( inst.fn,
          let _, _, _, xs, _ = List.assoc Sym.equal inst.fn sigma.function_definitions in
          match List.assoc Sym.equal inst.fn declarations with
          | _, _, Decl_function (_, _, cts, _, _, _) ->
            List.combine xs (List.map (fun (_, ct, _) -> ct) cts)
          | _ ->
            failwith
              (String.concat
                 " "
                 [ "Function declaration not found for";
                   Sym.pp_string inst.fn;
                   "@";
                   __LOC__
                 ]) ))
      insts
  in
  let convert_from ((x, ct) : Sym.t * C.ctype) =
    CF.Pp_ail.pp_expression
      (Utils.mk_expr
         (CtA.wrap_with_convert_from
            A.(
              AilEmemberofptr
                ( Utils.mk_expr (AilEident (Sym.fresh_named "res")),
                  Sym.Identifier (Locations.other __LOC__, "cn_gen_" ^ Sym.pp_string x) ))
            (Memory.bt_of_sct (Sctypes.of_ctype_unsafe (Locations.other __LOC__) ct))))
  in
  let open Pp in
  concat_map (compile_random_test_case prog5 args_map convert_from) insts


let compile_assumes
  ~(without_ownership_checking : bool)
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (prog5 : unit Mucore.file)
  (insts : Executable_spec_extract.instrumentation list)
  : Pp.document
  =
  let declarations, function_definitions =
    List.split
      (List.map
         (fun ctype ->
           Cn_internal_to_ail.generate_assume_ownership_function
             ~without_ownership_checking
             ctype)
         (let module CtypeSet =
            Set.Make (struct
              type t = C.ctype

              let compare a b = compare (Hashtbl.hash a) (Hashtbl.hash b)
            end)
          in
         !CtA.ownership_ctypes |> CtypeSet.of_list |> CtypeSet.to_seq |> List.of_seq)
       @ Cn_internal_to_ail.cn_to_ail_assume_predicates_internal
           prog5.resource_predicates
           sigma.cn_datatypes
           []
           prog5.resource_predicates
       @ ESpecInternal.generate_c_assume_pres_internal insts sigma prog5)
  in
  let open Pp in
  separate_map
    (twice hardline)
    (fun (tag, (_, _, decl)) ->
      CF.Pp_ail.pp_function_prototype ~executable_spec:true tag decl)
    declarations
  ^^ twice hardline
  ^^ CF.Pp_ail.pp_program
       ~executable_spec:true
       ~show_include:true
       (None, { A.empty_sigma with declarations; function_definitions })


let should_be_unit_test
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (inst : Executable_spec_extract.instrumentation)
  =
  let _, _, decl = List.assoc Sym.equal inst.fn sigma.declarations in
  match decl with
  | Decl_function (_, _, args, _, _, _) ->
    List.is_empty args
    && SymSet.is_empty
         (LAT.free_vars (fun _ -> SymSet.empty) (AT.get_lat (Option.get inst.internal)))
  | Decl_object _ -> failwith __LOC__


let compile_tests
  ~(without_ownership_checking : bool)
  (filename_base : string)
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (prog5 : unit Mucore.file)
  (insts : Executable_spec_extract.instrumentation list)
  =
  let unit_tests, random_tests = List.partition (should_be_unit_test sigma) insts in
  let unit_tests_doc = compile_unit_tests unit_tests in
  let random_tests_doc = compile_random_tests sigma prog5 random_tests in
  let open Pp in
  string "#include "
  ^^ dquotes (string (filename_base ^ "_gen.h"))
  ^^ hardline
  ^^ string "#include "
  ^^ dquotes (string (filename_base ^ "-exec.c"))
  ^^ hardline
  ^^ string "#include "
  ^^ dquotes (string "cn.c")
  ^^ twice hardline
  ^^ pp_label "Assume Ownership Functions"
  ^^ twice hardline
  ^^ compile_assumes ~without_ownership_checking sigma prog5 insts
  ^^ pp_label "Unit tests"
  ^^ twice hardline
  ^^ unit_tests_doc
  ^^ twice hardline
  ^^ pp_label "Random tests"
  ^^ twice hardline
  ^^ random_tests_doc
  ^^ pp_label "Main function"
  ^^ twice hardline
  ^^ string "int main"
  ^^ parens (string "int argc, char* argv[]")
  ^^ break 1
  ^^ braces
       (nest
          2
          (hardline
           ^^ concat_map
                (fun decl ->
                  let fn, (loc, _, _) = decl in
                  let suite =
                    loc
                    |> Cerb_location.get_filename
                    |> Option.get
                    |> Filename.basename
                    |> String.split_on_char '.'
                    |> List.hd
                  in
                  string "cn_register_test_case"
                  ^^ parens
                       (separate
                          (comma ^^ space)
                          [ string "(char*)" ^^ dquotes (string suite);
                            string "(char*)" ^^ dquotes (Sym.pp fn);
                            string "&cn_test" ^^ underscore ^^ Sym.pp fn
                          ])
                  ^^ semi
                  ^^ hardline)
                (List.map
                   (fun (inst : Executable_spec_extract.instrumentation) ->
                     (inst.fn, List.assoc Sym.equal inst.fn sigma.declarations))
                   insts)
           ^^ string "return cn_test_main(argc, argv);")
        ^^ hardline)
  ^^ hardline


let compile_script ~(output_dir : string) ~(test_file : string) : Pp.document =
  let open Pp in
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
  ^^ twice hardline
  ^^ string "# Compile"
  ^^ hardline
  ^^ separate_map
       space
       string
       [ "if";
         "cc";
         "-g";
         "-c";
         "\"-I${RUNTIME_PREFIX}/include/\"";
         "-o";
         "\"./" ^ Filename.chop_extension test_file ^ ".o\"";
         "\"./" ^ test_file ^ "\"";
         (if Config.is_coverage () then "--coverage;" else ";");
         "then"
       ]
  ^^ nest 4 (hardline ^^ string "echo \"Compiled C files.\"")
  ^^ hardline
  ^^ string "else"
  ^^ nest
       4
       (hardline
        ^^ string "printf \"Failed to compile C files in ${TEST_DIR}.\""
        ^^ hardline
        ^^ string "exit 1")
  ^^ hardline
  ^^ string "fi"
  ^^ twice hardline
  ^^ string "# Link"
  ^^ hardline
  ^^ separate_map
       space
       string
       [ "if";
         "cc";
         "-g";
         "\"-I${RUNTIME_PREFIX}/include\"";
         "-o";
         "\"./tests.out\"";
         Filename.chop_extension test_file ^ ".o";
         "\"${RUNTIME_PREFIX}/libcn.a\"";
         (if Config.is_coverage () then "--coverage;" else ";");
         "then"
       ]
  ^^ nest 4 (hardline ^^ string "echo \"Linked C .o files.\"")
  ^^ hardline
  ^^ string "else"
  ^^ nest
       4
       (hardline
        ^^ string "printf \"Failed to link *.o files in ${TEST_DIR}.\""
        ^^ hardline
        ^^ string "exit 1")
  ^^ hardline
  ^^ string "fi"
  ^^ twice hardline
  ^^ string "# Run"
  ^^ hardline
  ^^
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
  cmd
  ^^ hardline
  ^^ string "test_exit_code=$? # Save tests exit code for later"
  ^^ twice hardline
  ^^ hardline
  ^^ (if Config.is_coverage () then
        hardline
        ^^ string "# Coverage"
        ^^ hardline
        ^^ string ("if gcov \"" ^ test_file ^ "\"; then")
        ^^ nest 4 (hardline ^^ string "echo \"Recorded coverage via gcov.\"")
        ^^ hardline
        ^^ string "else"
        ^^ nest
             4
             (hardline
              ^^ string "printf \"Failed to record coverage.\""
              ^^ hardline
              ^^ string "exit 1")
        ^^ hardline
        ^^ string "fi"
        ^^ twice hardline
        ^^ string "if lcov --capture --directory . --output-file coverage.info; then"
        ^^ nest 4 (hardline ^^ string "echo \"Collected coverage via lcov.\"")
        ^^ hardline
        ^^ string "else"
        ^^ nest
             4
             (hardline
              ^^ string "printf \"Failed to collect coverage.\""
              ^^ hardline
              ^^ string "exit 1")
        ^^ hardline
        ^^ string "fi"
        ^^ twice hardline
        ^^ separate_map
             space
             string
             [ "if";
               "genhtml";
               "--output-directory";
               "html";
               "\"coverage.info\";";
               "then"
             ]
        ^^ nest
             4
             (hardline
              ^^ string "echo \"Generated HTML report at \\\"${TEST_DIR}/html/\\\".\"")
        ^^ hardline
        ^^ string "else"
        ^^ nest
             4
             (hardline
              ^^ string "printf \"Failed to generate HTML report.\""
              ^^ hardline
              ^^ string "exit 1")
        ^^ hardline
        ^^ string "fi"
      else
        empty)
  ^^ twice hardline
  ^^ string "popd > /dev/null"
  ^^ twice hardline
  ^^ string "exit $test_exit_code"
  ^^ hardline


let save ?(perm = 0o666) (output_dir : string) (filename : string) (doc : Pp.document)
  : unit
  =
  let oc =
    Stdlib.open_out_gen
      [ Open_wronly; Open_creat; Open_trunc; Open_text ]
      perm
      (Filename.concat output_dir filename)
  in
  output_string oc (Pp.plain ~width:80 doc);
  close_out oc


let generate
  ~(output_dir : string)
  ~(filename : string)
  ~(without_ownership_checking : bool)
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (prog5 : unit Mucore.file)
  : unit
  =
  if !Cerb_debug.debug_level > 0 then
    debug_log_file
    := Some
         (let open Stdlib in
          open_out "generatorCompilation.log");
  let insts = prog5 |> Executable_spec_extract.collect_instrumentation |> fst in
  let selected_fsyms =
    Check.select_functions
      (SymSet.of_list
         (List.map
            (fun (inst : Executable_spec_extract.instrumentation) -> inst.fn)
            insts))
  in
  let insts =
    insts
    |> List.filter (fun (inst : Executable_spec_extract.instrumentation) ->
      Option.is_some inst.internal && SymSet.mem inst.fn selected_fsyms)
  in
  if List.is_empty insts then failwith "No testable functions";
  let filename_base = filename |> Filename.basename |> Filename.chop_extension in
  let generators_doc =
    compile_generators
      sigma
      prog5
      (List.filter (fun inst -> not (should_be_unit_test sigma inst)) insts)
  in
  let generators_fn = filename_base ^ "_gen.h" in
  save output_dir generators_fn generators_doc;
  let tests_doc =
    compile_tests ~without_ownership_checking filename_base sigma prog5 insts
  in
  let test_file = filename_base ^ "_test.c" in
  save output_dir test_file tests_doc;
  let script_doc = compile_script ~output_dir ~test_file in
  save ~perm:0o777 output_dir "run_tests.sh" script_doc;
  ()
