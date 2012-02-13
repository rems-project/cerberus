open Batteries_uni
open Process_file


let backends = ref []
let opt_print_types = ref false
let opt_library = ref None
let ocaml_lib = ref []
let hol_lib = ref []
let coq_lib = ref []
let isa_lib = ref []
let opt_file_arguments = ref ([]:string list)

let options = Arg.align [
  ( "-tex", 
    Arg.Unit (fun b -> if not (List.mem (Some(Typed_ast.Target_tex)) !backends) then
                backends := Some(Typed_ast.Target_tex)::!backends),
    "                  generate LaTeX");
  ( "-hol", 
    Arg.Unit (fun b -> if not (List.mem (Some(Typed_ast.Target_hol)) !backends) then
                backends := Some(Typed_ast.Target_hol)::!backends),
    "                  generate HOL");
  ( "-ocaml", 
    Arg.Unit (fun b -> if not (List.mem (Some(Typed_ast.Target_ocaml)) !backends) then
                backends := Some(Typed_ast.Target_ocaml)::!backends),
    "                  generate OCaml");
  ( "-isa",
    Arg.Unit (fun b -> if not (List.mem (Some(Typed_ast.Target_isa)) !backends) then
                backends := Some(Typed_ast.Target_isa)::!backends),
    "                  generate Isabelle");
  ( "-coq",
    Arg.Unit (fun b -> if not (List.mem (Some(Typed_ast.Target_coq)) !backends) then
                backends := Some(Typed_ast.Target_coq)::!backends),
    "                  generate Coq");
  ( "-ident",
    Arg.Unit (fun b -> if not (List.mem None !backends) then
                backends := None::!backends),
    "                  generate input on stdout");
  ( "-print_types",
    Arg.Unit (fun b -> opt_print_types := true),
    "                  print types on stdout");
  ( "-lib", 
    Arg.String (fun l -> opt_library := Some l),
    "                  library path");
  ( "-ocaml_lib", 
    Arg.String (fun l -> ocaml_lib := l::!ocaml_lib),
    "                  add to OCaml library");
  ( "-hol_lib", 
    Arg.String (fun l -> hol_lib := l::!hol_lib),
    "                  add to HOL library");
  ( "-isa_lib", 
    Arg.String (fun l -> isa_lib := l::!isa_lib),
    "                  add to Isabelle library");
  ( "-coq_lib", 
    Arg.String (fun l -> coq_lib := l::!coq_lib),
    "                  add to Coq library");
] 

let usage_msg = 
    ("Lem 0.2\n"
     ^ "example usage:       lem -hol -ocaml -lib ../lem/library test.lem\n" 
    )

let _ = 
  Arg.parse options 
    (fun s -> 
      opt_file_arguments := (!opt_file_arguments) @ [s])
    usage_msg

(* Do the transformations for a given target, and then generate the output files
 * *)
let per_target libpath modules (def_info,env) consts alldoc_accum alldoc_inc_accum targ =
  let module C = struct
    let consts = List.assoc targ consts
    let (d,i) = def_info
  end
  in
  let module T = Target_trans.Make(C) in
  let (trans,avoid) = T.get_transformation targ in
    try
      let (_,transformed_m) = 
        List.fold_left 
          (fun (env,new_mods) old_mod -> 
             let (env,m) = trans env old_mod in
               (env,m::new_mods))
          (env,[])
          modules
      in
       output libpath targ avoid def_info (List.rev transformed_m) alldoc_accum alldoc_inc_accum
    with
      | Trans.Trans_error(l,msg) ->
          Process_file.print_msg l "Translation error" msg;
          raise Exit
      | Types.No_type(l,msg) ->
          Process_file.print_msg l "LEM internal error" msg;
          raise Exit

let main () =
  let lib_path = 
    match !opt_library with
      | None -> (try 
                let lp = Sys.getenv("LEMLIB") in
                if Filename.is_relative lp 
                then Filename.concat (Sys.getcwd ()) lp
                else lp
            with 
                | Not_found _ -> raise (Failure("must specify a -lib argument or have a LEMLIB environment variable")))
      | Some lp -> 
          if Filename.is_relative lp then
            Filename.concat (Sys.getcwd ()) lp
          else
            lp
  in
  let _ = 
    List.iter
      (fun f ->
         try
           if String.compare ".lem" (String.sub f (String.length f - 4) 4) <> 0 then
             raise (Failure("Files must have .lem extension"))
         with 
           | Invalid_argument _ -> 
             raise (Failure("Files must have .lem extension")))
      (!opt_file_arguments @ !ocaml_lib @ !hol_lib @ !isa_lib @ !coq_lib)
  in
  let _ = 
    List.iter
      (fun f ->
         if not (Str.string_match (Str.regexp "[A-Za-z]") (Filename.basename f) 0) then
           raise (Failure(".lem filenames must start with a letter")))
      (!opt_file_arguments @ !ocaml_lib @ !hol_lib @ !isa_lib @ !coq_lib)
  in
  let init =
    try
      let inchannel = open_in (Filename.concat lib_path "lib_cache") in
      let v = input_value inchannel in
        close_in inchannel;
        v
    with
      | Sys_error _ ->
          let module I = Initial_env.Initial_libs(struct let path = lib_path end) in
          let outchannel = open_out (Filename.concat lib_path "lib_cache") in
            output_value outchannel I.init;
            close_out outchannel;
            I.init
  in
  (* TODO: These should go into the sets of top-level constant names *)
  let init = List.fold_right (Initial_env.add_to_init Typed_ast.Target_hol) !hol_lib init in
  let init = List.fold_right (Initial_env.add_to_init Typed_ast.Target_ocaml) !ocaml_lib init in
  let init = List.fold_right (Initial_env.add_to_init Typed_ast.Target_isa) !isa_lib init in
  let init = List.fold_right (Initial_env.add_to_init Typed_ast.Target_coq) !coq_lib init in
  let consts = 
    List.map
      (fun (x,y) ->
         (x,List.fold_left
              (fun s c -> Typed_ast.NameSet.add (Name.from_rope c) s)
              Typed_ast.NameSet.empty
              y))
      (snd init)
  in
  let type_info : (Types.type_defs * instances) * Typed_ast.env = fst init in
  (* Parse and typecheck all of the .lem sources *)
  let (modules, type_info, _) =
    List.fold_left
      (fun (mods, (def_info,env), previously_processed_modules) f ->
         let ast = parse_file f in
         let f' = Filename.basename (Filename.chop_extension f) in
         let mod_name = String.capitalize f' in
         let mod_name_name = Name.from_rope (BatRope.of_latin1 mod_name) in
         let ((tdefs,instances,new_instances),new_env,tast) = 
           check_ast [mod_name_name] (def_info,env) ast
         in
         let e = { env with Typed_ast.m_env = Typed_ast.Nfmap.insert env.Typed_ast.m_env (mod_name_name,new_env) } in
         let module_record = 
           { Typed_ast.filename = f;
             Typed_ast.module_name = mod_name;
             Typed_ast.predecessor_modules = previously_processed_modules;
             Typed_ast.untyped_ast = ast;
             Typed_ast.typed_ast = tast; }
         in
           if !opt_print_types then
             begin
               Format.fprintf Format.std_formatter "%s@\nenvironment:@\n" f;
               Typed_ast.pp_env Format.std_formatter new_env;
               Format.fprintf Format.std_formatter "@\ninstances:@\n";
               Typed_ast.pp_instances Format.std_formatter new_instances;
               Format.fprintf Format.std_formatter "@\n@\n"
             end;
           (module_record::mods, ((tdefs,instances),e), mod_name::previously_processed_modules))
      ([],type_info,[])
      !opt_file_arguments
  in
  let alldoc_accum = ref ([] : BatRope.t list) in
  let alldoc_inc_accum = ref ([] : BatRope.t list) in
    ignore (List.iter (per_target lib_path (List.rev modules) type_info consts alldoc_accum alldoc_inc_accum) !backends);
    (if List.mem (Some(Typed_ast.Target_tex)) !backends then 
       output_alldoc "alldoc" (String.concat " " !opt_file_arguments) alldoc_accum alldoc_inc_accum)

let _ = 
  try 
    ignore(main ()) 
  with 
    | Exit -> exit 1
    | Failure(s) ->
        print_string (s ^ "\n");
        exit 1
