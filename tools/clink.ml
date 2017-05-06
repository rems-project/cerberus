module StrMap = Map.Make(String)

(* TODO: very naive parsing *)
let parse fn =
  let exts = ref [] in
  let impls = ref [] in
  let line = ref "" in
  let chan = open_in fn in
  try
    line := input_line chan;
    if compare !line "extern:" != 0 then
      raise (Failure ("Wrong file format: " ^ fn));
    line := input_line chan;
    while compare !line "impl:" != 0 do
      exts := !line :: !exts;
      line := input_line chan
    done;
    while true do
      impls := input_line chan :: !impls
    done;
    raise (Failure "fatal error")
  with End_of_file ->
    close_in chan; (!exts, !impls)

let add_to_map (mE, mI) name (exts, impls) =
  let mE' = match exts with
    | [] -> mE
    | _ -> StrMap.add name exts mE
  in
  let mI' =
    List.fold_left (fun acc i -> StrMap.add i name acc) mI impls
  in (mE', mI')

let rec create_maps n acc =
  if n = 0 then acc
  else
    let fl = Filename.chop_extension Sys.argv.(n) in
    create_maps (n-1) (add_to_map acc fl (parse Sys.argv.(n)))

let print_line chan ext mo =
  Printf.fprintf chan "let %s = %s.%s"
    ext (String.capitalize_ascii mo) ext

let print_file fl es m =
  let fli = fl ^ "I.ml" in
  let chan = open_out fli in
  let mname e =
    try StrMap.find e m
    with Not_found -> raise (Failure ("name " ^ e ^ " not found in any file"))
  in
  ignore (List.map (fun e -> print_line chan e (mname e)) es);
  close_out chan


let () =
  let (mE, mI) =
    create_maps (Array.length Sys.argv - 1) (StrMap.empty, StrMap.empty)
  in
  StrMap.fold (fun fn es () -> print_file fn es mI) mE ()
