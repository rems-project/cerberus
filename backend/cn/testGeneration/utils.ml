module CF = Cerb_frontend
open CF

let codify_sym (s : Sym.sym) : string =
  let (Symbol (_, n, sd)) = s in
  match sd with
  | SD_Id x | SD_CN_Id x | SD_ObjectAddress x | SD_FunArgValue x -> x
  | SD_None -> "fresh_" ^ string_of_int n
  | _ -> failwith ("Symbol `" ^ Sym.show_raw s ^ "` cannot be codified")


(** Only cares what their names in generated code will be *)
let sym_codified_equal (s1 : Sym.sym) (s2 : Sym.sym) =
  String.equal (codify_sym s1) (codify_sym s2)


let string_of_ctype (ty : Ctype.ctype) : string =
  String_ail.string_of_ctype ~is_human:true Ctype.no_qualifiers ty ^ " "
