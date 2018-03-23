module Instance : Instance_manager.Instance = struct
  let name = Ocaml_mem.name
  let translate = Translation.translate
end

let () =
  print_endline ("Loading " ^ Ocaml_mem.name);
  Instance_manager.add_model (module Instance)
