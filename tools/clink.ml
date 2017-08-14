type symbol_type =
  | Unresolved
  | DefinedFunction
  | GlobalData
  | Unknown

(* File names to unresolved symbols list *)
let unresolved : (string, string list) Hashtbl.t = Hashtbl.create 10

(* Global functions symbols to translation units *)
let funs : (string, string) Hashtbl.t = Hashtbl.create 10

(* File names to global variables list *)
let data : (string, string list) Hashtbl.t = Hashtbl.create 10

let lines_of_channel chan =
  Stream.from (fun _ -> try Some (input_line chan) with End_of_file -> None)

let symbols_of_line str =
  Stream.of_list (Str.split (Str.regexp "[ \t]+") str)

let add_syms name syms = function
  | Unresolved -> Hashtbl.add unresolved name syms
  | DefinedFunction ->
    List.map (fun s -> Hashtbl.add funs s name) syms |> ignore
  | GlobalData -> Hashtbl.add data name syms
  | Unknown -> if syms != [] then raise (Failure "Unknown symbol type!")

let process_input filename =
  let chan = open_in filename in
  let name = Filename.chop_extension filename in
  try
    let symtyp = ref Unknown in
    let acc = ref [] in
    let process sym =
      if String.get sym 0 = '.' then begin
        add_syms name !acc !symtyp;
        acc := [];
        symtyp := match sym with
          | ".unresolved" -> Unresolved
          | ".funs" -> DefinedFunction
          | ".data" -> GlobalData
          | _ -> raise (Failure ("Unknown symbol type " ^ sym))
      end
      else acc := sym :: !acc
    in
    let process_line line =
      symbols_of_line line |> Stream.iter process
    in
    Stream.iter process_line (lines_of_channel chan);
    add_syms name !acc !symtyp;
    close_in chan
  with e ->
    close_in chan;
    raise e

let process_input_files () =
  Array.to_list Sys.argv
  |> List.tl
  |> List.map process_input
  |> ignore

let resolution usyms =
  List.fold_left (fun acc us ->
      try (us, Hashtbl.find funs us)::acc
      with Not_found -> acc) [] usyms

let extern_globals ms =
  List.fold_left (fun acc mname ->
      try
        let prefix = String.capitalize_ascii mname ^ "." in
        Hashtbl.find data mname
        |> List.map (fun x -> (prefix ^ "glob_" ^ x, prefix ^ x))
        |> List.rev_append acc
      with Not_found -> acc) [] ms

let resolve () =
  Hashtbl.fold
    begin fun name usyms acc ->
      let resolved_syms = resolution usyms in
      let ext_glbs = extern_globals (List.map snd resolved_syms) in
      (name, resolution usyms, ext_glbs)::acc
    end unresolved []

let print_line chan (f, m) =
  Printf.fprintf chan "let %s = %s.%s\n" f (String.capitalize_ascii m) f

let print_globals chan xs =
  let rec string_of_list = function
    | [] -> ""
    | [(x, y)] -> "(" ^ x ^ ", " ^ y ^ ")"
    | (x,y)::xs -> "(" ^ x ^ ", " ^ y ^ ");\n\t" ^ string_of_list xs
  in Printf.fprintf chan "let ext_globals = [%s]\n" (string_of_list xs)

let process_output (name, funs, ext_glbs) =
  let chan = open_out (name ^ "I.ml") in
  List.map (print_line chan) funs |> ignore;
  print_globals chan ext_glbs;
  close_out chan

let process_output_files files =
  List.map process_output files |> ignore

let () =
  process_input_files ()
  |> resolve
  |> process_output_files
