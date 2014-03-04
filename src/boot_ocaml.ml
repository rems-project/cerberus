open Global

let assert_false str =
  Pervasives.failwith ("[Impossible error>\n" ^ str)

let debug_level = ref 0


let dprint str =
  if !debug_level > 0 then
    Pervasives.output_string Pervasives.stderr ("\x1b[31m" ^ str ^ "\x1b[0m\n")

let print_debug str k =
  if !debug_level > 0 then
    let _ = Pervasives.output_string Pervasives.stderr ("\x1b[31mDEBUG: " ^ str ^ "\x1b[0m\n") in k
  else
    k

let pickList = function
  | []  -> failwith ""
  | [x] -> ([], x, [])
  | xs  -> let l = List.length xs in
           let (ys,z::zs) = Lem_list.split_at (Random.int l) xs in
           (ys, z, zs)

(* Pretty printing *)
let to_plain_string d =
  let buf = Buffer.create 50 in
  PPrint.ToBuffer.compact buf d;
  let str = Buffer.contents buf in
  Buffer.clear buf;
  str


let pp_ail_ctype ty = to_plain_string (Pp_ail.pp_ctype ty)
let pp_ail_expr e = to_plain_string (Pp_ail.pp_expression e)
let pp_core_expr e = to_plain_string (Pp_core.pp_expr e)



let pp_cabs0_definition def = to_plain_string (Pp_cabs0.pp_definition def)



(* TODO: this is massive hack, just to make csmith programs work *)
let fake_printf str args =
  match (str, args) with
  | ("\"%d\"", [Cmm_aux.Cint n]) ->
      Big_int.string_of_big_int n

  | ("\"checksum = %x\\n\"", [Cmm_aux.Cint n]) ->
      Printf.sprintf "checksum = %x\n" (Big_int.int_of_big_int n)

  | ("\"checksum = %X\\n\"", [Cmm_aux.Cint n]) ->
      Printf.sprintf "checksum = %X\n" (Big_int.int_of_big_int n)

  | ("\"...checksum after hashing %s : %X\\n\"", [Cmm_aux.Cstring str; Cmm_aux.Cint n]) ->
      Printf.sprintf "...checksum after hashing %s : %X\n" str (Big_int.int_of_big_int n)

  | ("\"...checksum after hashing %s : %lX\n\"", [Cmm_aux.Cstring str; Cmm_aux.Cint n]) ->
      Printf.sprintf "...checksum after hashing %s : %lX\n" str (Big_int.int32_of_big_int n)

  | ("\"%s %d\\n\"", [Cmm_aux.Cstring str; Cmm_aux.Cint n]) ->
      Printf.sprintf "%s %d\n" str (Big_int.int_of_big_int n)

  | (str, []) ->
      str
  | _ ->
      print_endline "TODO: error in Boot_ocaml.fake_printf";
      Printf.printf "str= %s\n" str;
      Printf.printf "|args|= %d\n" (List.length args);
      exit 1
