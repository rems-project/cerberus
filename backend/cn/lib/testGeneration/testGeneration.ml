module CF = Cerb_frontend
module A = CF.AilSyntax
module C = CF.Ctype
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module CtA = Cn_internal_to_ail
module ESpecInternal = Executable_spec_internal
module Config = TestGenConfig

type config = Config.t

let default_cfg : config = Config.default

let is_constant_function
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (inst : Executable_spec_extract.instrumentation)
  =
  let _, _, decl = List.assoc Sym.equal inst.fn sigma.declarations in
  match decl with
  | Decl_function (_, _, args, _, _, _) ->
    List.is_empty args
    && Sym.Set.is_empty
         (LAT.free_vars (fun _ -> Sym.Set.empty) (AT.get_lat (Option.get inst.internal)))
  | Decl_object _ -> failwith __LOC__


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
  ^^ hardline


let pp_label ?(width : int = 30) (label : string) (doc : Pp.document) : Pp.document =
  let padding = max 2 ((width - (String.length label + 2)) / 2) in
  let width = max width (String.length label + 6) in
  let open Pp in
  if PPrint.requirement doc = 0 then
    empty
  else
    repeat width slash
    ^^ hardline
    ^^ repeat
         (if String.length label mod 2 = 1 then
            padding + 1
          else
            padding)
         slash
    ^^ space
    ^^ string label
    ^^ space
    ^^ repeat padding slash
    ^^ hardline
    ^^ repeat width slash
    ^^ twice hardline
    ^^ doc


let compile_test_file
  ~(without_ownership_checking : bool)
  (filename_base : string)
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (prog5 : unit Mucore.file)
  (insts : Executable_spec_extract.instrumentation list)
  =
  let for_constant, for_generator = List.partition (is_constant_function sigma) insts in
  let constant_tests, constant_tests_defs =
    SpecTests.compile_constant_tests for_constant
  in
  let generator_tests, generator_tests_defs =
    SpecTests.compile_generator_tests sigma prog5 for_generator
  in
  let tests = [ constant_tests; generator_tests ] in
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
  ^^ pp_label
       "Assume Ownership Functions"
       (compile_assumes ~without_ownership_checking sigma prog5 insts)
  ^^ pp_label "Constant function tests" constant_tests_defs
  ^^ pp_label "Generator-based tests" generator_tests_defs
  ^^ pp_label
       "Main function"
       (string "int main"
        ^^ parens (string "int argc, char* argv[]")
        ^^ break 1
        ^^ braces
             (nest
                2
                (hardline
                 ^^ separate_map
                      (twice hardline)
                      (separate_map hardline (fun test ->
                         let macro = Test.registration_macro test in
                         string macro
                         ^^ parens
                              (string test.suite ^^ comma ^^ space ^^ string test.test)
                         ^^ semi))
                      tests
                 ^^ twice hardline
                 ^^ string "return cn_test_main(argc, argv);")
              ^^ hardline))
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


let save_generators
  ~output_dir
  ~filename_base
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (prog5 : unit Mucore.file)
  (insts : Executable_spec_extract.instrumentation list)
  : unit
  =
  let generators_doc =
    SpecTests.compile_generators
      sigma
      prog5
      (List.filter (fun inst -> not (is_constant_function sigma inst)) insts)
  in
  let generators_fn = filename_base ^ "_gen.h" in
  save output_dir generators_fn generators_doc


let save_tests
  ~output_dir
  ~filename_base
  ~without_ownership_checking
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (prog5 : unit Mucore.file)
  (insts : Executable_spec_extract.instrumentation list)
  : string
  =
  let tests_doc =
    compile_test_file ~without_ownership_checking filename_base sigma prog5 insts
  in
  let test_file = filename_base ^ "_test.c" in
  save output_dir test_file tests_doc;
  test_file


let save_build_script ~output_dir ~test_file =
  let script_doc = BuildScript.generate ~output_dir ~test_file in
  save ~perm:0o777 output_dir "run_tests.sh" script_doc


let run
  ~output_dir
  ~filename
  ~without_ownership_checking
  (cfg : config)
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (prog5 : unit Mucore.file)
  : unit
  =
  Config.initialize cfg;
  Cerb_debug.begin_csv_timing ();
  let insts = prog5 |> Executable_spec_extract.collect_instrumentation |> fst in
  let selected_fsyms =
    Check.select_functions
      (Sym.Set.of_list
         (List.map
            (fun (inst : Executable_spec_extract.instrumentation) -> inst.fn)
            insts))
  in
  let insts =
    insts
    |> List.filter (fun (inst : Executable_spec_extract.instrumentation) ->
      Option.is_some inst.internal && Sym.Set.mem inst.fn selected_fsyms)
  in
  let filename_base = filename |> Filename.basename |> Filename.chop_extension in
  save_generators ~output_dir ~filename_base sigma prog5 insts;
  let test_file =
    save_tests ~output_dir ~filename_base ~without_ownership_checking sigma prog5 insts
  in
  save_build_script ~output_dir ~test_file;
  Cerb_debug.end_csv_timing "specification test generation"
