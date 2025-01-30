module CF = Cerb_frontend
module A = CF.AilSyntax
module C = CF.Ctype
module AT = ArgumentTypes
module LAT = LogicalArgumentTypes
module CtA = Fulminate.Cn_internal_to_ail
module ESpecInternal = Fulminate.Executable_spec_internal
module FExtract = Fulminate.Executable_spec_extract
module Config = TestGenConfig

type config = Config.t

let default_cfg : config = Config.default

let set_config = Config.initialize

let is_constant_function
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (inst : FExtract.instrumentation)
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
  (insts : FExtract.instrumentation list)
  : Pp.document
  =
  let declarations, function_definitions =
    List.split
      (List.map
         (fun ctype ->
           CtA.generate_assume_ownership_function ~without_ownership_checking ctype)
         (let module CtypeSet =
            Set.Make (struct
              type t = C.ctype

              let compare a b = compare (Hashtbl.hash a) (Hashtbl.hash b)
            end)
          in
         !CtA.ownership_ctypes |> CtypeSet.of_list |> CtypeSet.to_seq |> List.of_seq)
       @ CtA.cn_to_ail_assume_predicates_internal
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


let compile_includes ~filename_base =
  let open Pp in
  string "#include "
  ^^ dquotes (string (filename_base ^ "_gen.h"))
  ^^ hardline
  ^^
  if Config.with_static_hack () then
    string "#include "
    ^^ dquotes (string (filename_base ^ "-exec.c"))
    ^^ hardline
    ^^ string "#include "
    ^^ dquotes (string "cn.c")
  else
    string "#include " ^^ dquotes (string "cn.h")


let compile_test test =
  let open Pp in
  let macro = Test.registration_macro test in
  string macro ^^ parens (string test.suite ^^ comma ^^ space ^^ string test.test) ^^ semi


let compile_test_file
  ~(without_ownership_checking : bool)
  (filename_base : string)
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (prog5 : unit Mucore.file)
  (insts : FExtract.instrumentation list)
  =
  let for_constant, for_generator = List.partition (is_constant_function sigma) insts in
  let constant_tests, constant_tests_defs =
    SpecTests.compile_constant_tests sigma for_constant
  in
  let generator_tests, generator_tests_defs =
    SpecTests.compile_generator_tests sigma prog5 for_generator
  in
  let tests = [ constant_tests; generator_tests ] in
  let open Pp in
  compile_includes ~filename_base
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
                      (separate_map hardline compile_test)
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
  (insts : FExtract.instrumentation list)
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
  (insts : FExtract.instrumentation list)
  : unit
  =
  let tests_doc =
    compile_test_file ~without_ownership_checking filename_base sigma prog5 insts
  in
  save output_dir (filename_base ^ "_test.c") tests_doc


let save_build_script ~output_dir ~filename_base =
  let script_doc = BuildScript.generate ~output_dir ~filename_base in
  save ~perm:0o777 output_dir "run_tests.sh" script_doc


(** Workaround for https://github.com/rems-project/cerberus/issues/784 *)
let needs_static_hack
  ~(with_warning : bool)
  (cabs_tunit : CF.Cabs.translation_unit)
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (inst : FExtract.instrumentation)
  =
  let (TUnit decls) = cabs_tunit in
  let is_static_func () =
    List.exists
      (fun decl ->
        match decl with
        | CF.Cabs.EDecl_func
            (FunDef
              ( loc,
                _,
                { storage_classes; _ },
                Declarator
                  (_, DDecl_function (DDecl_identifier (_, Identifier (_, fn')), _)),
                _ ))
          when String.equal (Sym.pp_string inst.fn) fn'
               && List.exists
                    (fun scs -> match scs with CF.Cabs.SC_static -> true | _ -> false)
                    storage_classes ->
          if with_warning then
            Cerb_colour.with_colour
              (fun () ->
                Pp.(
                  warn
                    loc
                    (string "Static function"
                     ^^^ squotes (Sym.pp inst.fn)
                     ^^^ string "could not be tested."
                     ^/^ string "Try again with '--with-static-hack'")))
              ();
          true
        | _ -> false)
      decls
  in
  let _, _, _, args, _ = List.assoc Sym.equal inst.fn sigma.function_definitions in
  let depends_on_static_glob () =
    let global_syms =
      inst.internal
      |> Option.get
      |> AT.get_lat
      |> LAT.free_vars (fun _ -> Sym.Set.empty)
      |> Sym.Set.to_seq
      |> List.of_seq
      |> List.filter (fun x ->
        not
          (List.mem (fun x y -> String.equal (Sym.pp_string x) (Sym.pp_string y)) x args))
    in
    let static_globs =
      List.filter_map
        (fun sym ->
          match List.assoc Sym.equal sym sigma.declarations with
          | loc, _, Decl_object ((Static, _), _, _, _) -> Some (sym, loc)
          | _ -> None)
        global_syms
    in
    if List.is_empty static_globs then
      false
    else (
      if with_warning then
        Cerb_colour.with_colour
          (fun () ->
            List.iter
              (fun (sym, loc) ->
                Pp.(
                  warn
                    loc
                    (string "Function"
                     ^^^ squotes (Sym.pp inst.fn)
                     ^^^ string "relies on static global"
                     ^^^ squotes (Sym.pp sym)
                     ^^ comma
                     ^^^ string "so could not be tested."
                     ^^^ string "Try again with '--with-static-hack'.")))
              static_globs)
          ();
      true)
  in
  is_static_func () || depends_on_static_glob ()


(** Workaround for https://github.com/rems-project/cerberus/issues/765 *)
let needs_enum_hack
  ~(with_warning : bool)
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (inst : FExtract.instrumentation)
  =
  match List.assoc Sym.equal inst.fn sigma.declarations with
  | loc, _, Decl_function (_, (_, ret_ct), cts, _, _, _) ->
    if
      List.exists
        (fun (_, ct, _) ->
          match ct with C.Ctype (_, Basic (Integer (Enum _))) -> true | _ -> false)
        cts
    then (
      if with_warning then
        Cerb_colour.with_colour
          (fun () ->
            Pp.(
              warn
                loc
                (string "Function"
                 ^^^ squotes (Sym.pp inst.fn)
                 ^^^ string "has enum arguments and so could not be tested."
                 ^/^ string "Try again with '--with-static-hack'")))
          ();
      true)
    else if match ret_ct with C.Ctype (_, Basic (Integer (Enum _))) -> true | _ -> false
    then (
      if with_warning then
        Cerb_colour.with_colour
          (fun () ->
            Pp.(
              warn
                loc
                (string "Function"
                 ^^^ squotes (Sym.pp inst.fn)
                 ^^^ string "has an enum return type and so could not be tested."
                 ^/^ string "Try again with '--with-static-hack'")))
          ();
      true)
    else
      false
  | _ -> false


let functions_under_test
  ~(with_warning : bool)
  (cabs_tunit : CF.Cabs.translation_unit)
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (prog5 : unit Mucore.file)
  : FExtract.instrumentation list
  =
  let insts = prog5 |> FExtract.collect_instrumentation |> fst in
  let selected_fsyms =
    Check.select_functions
      (Sym.Set.of_list
         (List.map (fun (inst : FExtract.instrumentation) -> inst.fn) insts))
  in
  insts
  |> List.filter (fun (inst : FExtract.instrumentation) ->
    Option.is_some inst.internal
    && Sym.Set.mem inst.fn selected_fsyms
    && (Config.with_static_hack ()
        || not
             (needs_static_hack ~with_warning cabs_tunit sigma inst
              || needs_enum_hack ~with_warning sigma inst)))


let run
  ~output_dir
  ~filename
  ~without_ownership_checking
  (cabs_tunit : CF.Cabs.translation_unit)
  (sigma : CF.GenTypes.genTypeCategory A.sigma)
  (prog5 : unit Mucore.file)
  : unit
  =
  Cerb_debug.begin_csv_timing ();
  let insts = functions_under_test ~with_warning:false cabs_tunit sigma prog5 in
  let filename_base = filename |> Filename.basename |> Filename.chop_extension in
  save_generators ~output_dir ~filename_base sigma prog5 insts;
  save_tests ~output_dir ~filename_base ~without_ownership_checking sigma prog5 insts;
  save_build_script ~output_dir ~filename_base;
  Cerb_debug.end_csv_timing "specification test generation"
