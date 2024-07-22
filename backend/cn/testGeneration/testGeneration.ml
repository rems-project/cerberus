(** Test Generation
    Generates RapidCheck tests for functions
    with CN specifications, where inputs are
    guaranteed to satisfy the CN precondition.
    **)

module AT = ArgumentTypes
module BT = BaseTypes
module RP = ResourcePredicates
module IT = IndexTerms
module LS = LogicalSorts
module RET = ResourceTypes
module LC = LogicalConstraints
module LAT = LogicalArgumentTypes
module CF = Cerb_frontend

type test_framework = Codify.test_framework

let test_frameworks = [ ("gtest", Codify.GTest) ]

let rec get_lat_from_at (at : _ AT.t) : _ LAT.t =
  match at with AT.Computational (_, _, at') -> get_lat_from_at at' | AT.L lat -> lat


let get_args (sigma : _ CF.AilSyntax.sigma) (fun_name : Sym.sym)
  : (Sym.sym * CF.Ctype.ctype) list
  =
  let lookup_fn (x, _) = Utils.sym_codified_equal x fun_name in
  let fn_decl = List.filter lookup_fn sigma.declarations in
  let fn_def = List.filter lookup_fn sigma.function_definitions in
  let arg_types, arg_syms =
    match (fn_decl, fn_def) with
    | ( (_, (_, _, Decl_function (_, _, arg_types, _, _, _))) :: _,
        (_, (_, _, _, arg_syms, _)) :: _ ) ->
      let arg_types = List.map (fun (_, ctype, _) -> ctype) arg_types in
      (arg_types, arg_syms)
    | _ -> ([], [])
  in
  List.combine arg_syms arg_types


let generate_pbt
  (max_unfolds : int)
  (sigma : _ CF.AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  (tf : Codify.test_framework)
  (oc : out_channel)
  (instrumentation : Core_to_mucore.instrumentation)
  : unit
  =
  let args = get_args sigma instrumentation.fn in
  let lat =
    Option.get instrumentation.internal |> get_lat_from_at |> LAT.map (fun _ -> ())
  in
  List.iteri
    (fun i g ->
      output_string oc ("/* Collected:\n" ^ Constraints.string_of_goal g ^ "*/\n\n");
      let g = Constraints.simplify g in
      output_string oc ("/* Simplified:\n" ^ Constraints.string_of_goal g ^ "*/\n\n");
      let gtx = Dsl.compile g in
      output_string oc ("/* Compiled:\n" ^ Dsl.string_of_gen_context gtx ^ "\n*/\n\n");
      let gtx = Dsl.optimize gtx in
      output_string oc ("/* Optimized:\n" ^ Dsl.string_of_gen_context gtx ^ "\n*/\n\n");
      Codify.codify_pbt tf sigma instrumentation args i oc gtx)
    (Constraints.collect ~max_unfolds sigma prog5 args lat)


let run
  ~(output_dir : string)
  ~(filename : string)
  ~(max_unfolds : int)
  (sigma : _ CF.AilSyntax.sigma)
  (prog5 : unit Mucore.mu_file)
  (tf : Codify.test_framework)
  : unit
  =
  let instrumentation_list, _symbol_table =
    Core_to_mucore.collect_instrumentation prog5
  in
  let instrumentation_list =
    instrumentation_list
    |> List.filter (fun (inst : Core_to_mucore.instrumentation) ->
      match Cerb_location.get_filename inst.fn_loc with
      | Some filename' -> String.equal filename filename'
      | None -> false)
  in
  let oc =
    Stdlib.open_out
      (output_dir
       ^ "test_"
       ^ (filename |> Filename.basename |> Filename.chop_extension)
       ^ ".cpp")
  in
  Codify.codify_prelude tf oc;
  List.iter (generate_pbt max_unfolds sigma prog5 tf oc) instrumentation_list
