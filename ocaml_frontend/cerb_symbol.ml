
module Identifier = struct
  type t = {
    loc: Cerb_location.t;
    str: string;
  }
  let mk loc str = { loc; str }
  let equal ident1 ident2 = String.equal ident1.str ident2.str
  let compare ident1 ident2 = String.compare ident1.str ident2.str
  let to_string ident = ident.str (* FOR LEM *)
  let get_loc ident = ident.loc (* FOR LEM *)
  let freshify ident n = { ident with str= ident.str ^ string_of_int n }
end


module Sym = struct
  type description =
    | SD_None
    | SD_unnamed_tag of Cerb_location.t
    | SD_Id of string
    | SD_CN_Id of string
    | SD_ObjectAddress of string
    | SD_Return
    | SD_FunArgValue of string
    | SD_FunArg of Cerb_location.t * int

  let show_description = function
    | SD_None -> "SD_None"
    | SD_unnamed_tag _ -> "SD_unnamed_tag"
    | SD_Id str -> "SD_Id(" ^ str ^ ")"
    | SD_CN_Id str -> "SD_CN_Id(" ^ str ^ ")"
    | SD_ObjectAddress str -> "SD_ObjectAddress" ^ str
    | SD_Return -> "SD_Return"
    | SD_FunArgValue str -> "SD_FunArgValue" ^ "(" ^ str ^ ")"
    | SD_FunArg (_, idx) -> "SD_FunArg" ^ "(" ^ string_of_int idx ^ ")"

  type t = {
    tunit: Digest.t;
    id: int;
    desc: description
  }

  let mk tunit id desc = { tunit; id; desc }

  let equal sym1 sym2 =
    if
      Digest.equal sym1.tunit sym2.tunit &&
      Int.equal sym1.id sym2.id
    then (
      if
        Cerb_debug.get_debug_level () >= 5 &&
        not (String.equal (show_description sym1.desc) (show_description sym2.desc))
      then (
        Cerb_debug.print_debug 5 [] (fun () ->
          "[Sym.equal] suspicious equality => " ^
          show_description sym1.desc ^ " <-> " ^
          show_description sym2.desc
        )
      );
      true
    ) else false

  let compare sym1 sym2 =
    if Digest.equal sym1.tunit sym2.tunit then
      Int.compare sym1.id sym2.id
    else
      Digest.compare sym1.tunit sym2.tunit

  let show sym =
    "Symbol(" ^ string_of_int sym.id ^ ", "
      ^ show_description sym.desc ^ ")"

  let show_raw sym =
    "Symbol(" ^ Digest.to_hex sym.tunit ^ ", " ^
    string_of_int sym.id ^ ", " ^
    show_description sym.desc ^ ")"

  let match_id = function
    | { desc= SD_Id str; _} -> Some str
    | _ -> None

  (* FOR LEM *)
  let get_desc sym = sym.desc
  let set_desc sym desc = { sym with desc }

  let from_same_translation_unit sym1 sym2 =
    0 = Digest.compare sym1.tunit sym2.tunit

  let fresh () =
    { tunit= Cerb_fresh.digest (); id= Cerb_fresh.int (); desc= SD_None }

  let fresh_pretty str =
    { tunit= Cerb_fresh.digest (); id= Cerb_fresh.int (); desc= SD_Id str }

  let fresh_cn str =
    { tunit= Cerb_fresh.digest (); id= Cerb_fresh.int (); desc= SD_CN_Id str }

  let fresh_pretty_with_id f =
    let id = Cerb_fresh.int () in
    { tunit= Cerb_fresh.digest (); id; desc= SD_Id (f id) }

  let fresh_funarg loc idx =
    { tunit= Cerb_fresh.digest (); id= Cerb_fresh.int (); desc= SD_FunArg (loc, idx) }

  let fresh_with_description desc =
    { tunit= Cerb_fresh.digest (); id= Cerb_fresh.int (); desc }

  let fresh_object_address str =
    { tunit= Cerb_fresh.digest (); id= Cerb_fresh.int (); desc= SD_ObjectAddress str }

  let fresh_unnamed_tag loc =
    { tunit= Cerb_fresh.digest (); id= Cerb_fresh.int (); desc= SD_unnamed_tag loc }

  (* FOR LEM related code *)
  let empty_pmap =
    Pmap.empty compare
end


type prefix =
  | PrefSource of Cerb_location.t * Sym.t list
  | PrefFunArg of Cerb_location.t * Digest.t * int
  | PrefStringLiteral of Cerb_location.t * Digest.t
  | PrefCompoundLiteral of Cerb_location.t * Digest.t
  | PrefMalloc
  | PrefTemporaryLifetime of Cerb_location.t * Digest.t
  | PrefOther of string

(* All these are only for LEM *)
let mk_funarg_prefix loc n = PrefFunArg (loc, Cerb_fresh.digest (), n)
let compound_literal_prefix loc sym = PrefCompoundLiteral (loc, sym.Sym.tunit)
let source_prefix loc syms = PrefSource (loc, syms)
let temporary_lifetime_prefix loc sym = PrefTemporaryLifetime (loc, sym.Sym.tunit)
let string_literal_prefix loc sym = PrefStringLiteral (loc, sym.Sym.tunit)
let other_prefix str = PrefOther str
