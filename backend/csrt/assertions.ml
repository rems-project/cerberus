open Pp
open TypeErrors
open Resultat

module CF = Cerb_frontend
module StringMap = Map.Make(String)
(* module IT = IndexTerms *)
module AST = Parse_ast
module LC = LogicalConstraints
open AST


(* probably should record source location information *)
(* stealing some things from core_parser *)


open O
open OOA
open IndexTerms

let find_name loc names str = 
  begin match StringMap.find_opt str names with
  | Some sym -> return sym
  | None -> fail loc (Generic !^(str ^ " unbound"))
  end

let resolve_obj loc (objs : (string OOA.t * Sym.t) list) (obj : string OOA.t) : (Sym.t, type_error) m = 
  let found = 
    List.find_opt (fun (obj',sym) -> 
        OOA.compare String.compare obj obj' = 0
      ) objs
  in
  match found with
  | None -> 
     fail loc (Generic (!^"term" ^^^ OOA.pp obj ^^^ !^"does not apply"))
  | Some (_, sym) -> 
     return sym





(* change this to return unit IT.term, then apply index term type
   checker *)
let rec resolve_index_term loc objs (it: string index_term) 
        : (BT.t IT.term, type_error) m =
  let aux = resolve_index_term loc objs in
  let (IndexTerm (l, it_)) = it in
  match it_ with
  | Num n -> 
     return (IT.Num n)
  | Bool b -> 
     return (IT.Bool b)
  | Add (it, it') -> 
     let* it = aux it in
     let* it' = aux it' in
     return (IT.Add (it, it'))
  | Sub (it, it') -> 
     let* it = aux it in
     let* it' = aux it' in
     return (IT.Sub (it, it'))
  | Mul (it, it') -> 
     let* it = aux it in
     let* it' = aux it' in
     return (IT.Mul (it, it'))
  | Div (it, it') -> 
     let* it = aux it in
     let* it' = aux it' in
     return (IT.Div (it, it'))
  | Min (it, it') -> 
     let* it = aux it in
     let* it' = aux it' in
     return (IT.Min (it, it'))
  | Max (it, it') -> 
     let* it = aux it in
     let* it' = aux it' in
     return (IT.Max (it, it'))
  | EQ (it, it') -> 
     let* it = aux it in
     let* it' = aux it' in
     return (IT.EQ (it, it'))
  | NE (it, it') -> 
     let* it = aux it in
     let* it' = aux it' in
     return (IT.NE (it, it'))
  | LT (it, it') -> 
     let* it = aux it in
     let* it' = aux it' in
     return (IT.LT (it, it'))
  | GT (it, it') -> 
     let* it = aux it in
     let* it' = aux it' in
     return (IT.GT (it, it'))
  | LE (it, it') -> 
     let* it = aux it in
     let* it' = aux it' in
     return (IT.LE (it, it'))
  | GE (it, it') -> 
     let* it = aux it in
     let* it' = aux it' in
     return (IT.GE (it, it'))
  | Object obj -> 
     let* s = resolve_obj loc objs obj in
     return (IT.S s)

  | MIN_U32 -> return (IT.min_u32 ())
  | MIN_U64 -> return (IT.min_u64 ())
  | MAX_U32 -> return (IT.max_u32 ())
  | MAX_U64 -> return (IT.max_u64 ())
  | MIN_I32 -> return (IT.min_i32 ())
  | MIN_I64 -> return (IT.min_i64 ())
  | MAX_I32 -> return (IT.max_i32 ())
  | MAX_I64 -> return (IT.max_i64 ())


let resolve_definition loc objs (Definition (name, obj)) = 
  let* s = resolve_obj loc objs obj in
  return (Obj (Id name), s)

(* https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html *)
(* stealing from core_parser_driver *)

let parse loc entry s =
  let lexbuf = Lexing.from_string s in
  try return (entry Lexer.read lexbuf) with
  | Lexer.SyntaxError c ->
     (* let loc = Locations.point @@ Lexing.lexeme_start_p lexbuf in *)
     fail loc (Generic !^("invalid symbol: " ^ c))
  | Parser.Error ->
     (* let loc = 
      *   let startp = Lexing.lexeme_start_p lexbuf in
      *   let endp = Lexing.lexeme_end_p lexbuf in
      *   Locations.region (startp, endp) None 
      * in *)
     fail loc (Generic !^("unexpected token: " ^ Lexing.lexeme lexbuf))
  | Failure msg ->
     Debug_ocaml.error "assertion parsing error"

  




let get_attribute_args kind (CF.Annot.Attrs attrs) =
  let argses = 
    List.filter_map (fun a -> 
        if String.equal kind (Id.s a.CF.Annot.attr_id) 
        then Some a.attr_args else None
      ) attrs 
  in
  List.concat argses


let pre_or_post loc kind attrs = 
  let* requirements = 
    ListM.mapM 
      (fun (loc',str) -> 
        parse (Locations.update loc loc') Parser.condition_entry str
      ) (get_attribute_args kind attrs)
  in
  let* (ownership,constraints) = 
    ListM.fold_leftM (fun (ownership, constrs) p ->
        match p with
        | Ownership (obj,o) -> 
           let in_prefix = 
             List.find_opt (fun (obj',_) -> AST.O.equal_or_in_prefix String.compare obj obj') ownership 
           in
           begin match constrs, in_prefix with
           | _ :: _, _ -> 
              fail loc (Generic !^"please specify all ownership constraints first, other constraints second")
           | _, Some (obj',_) ->
              fail loc (Generic (!^"already specified ownership for" ^^^ AST.O.pp obj'))
           | _, None -> 
              return (ownership @ [(obj,o)], constrs)
           end
        | Constraint p_it -> 
           return (ownership, constrs @ [p_it])
      ) ([], []) requirements
  in
  return (ownership,constraints)
  
let resolve_constraints loc known_objs its =
  ListM.mapM (fun p_it ->
      let* it = resolve_index_term loc known_objs p_it in
      return (LC.LC it)
    ) its
  

let definitions loc attrs known_objs = 
  ListM.mapM 
    (fun (loc',str) -> 
      let* it = parse (Locations.update loc loc') Parser.definition_entry str in
      resolve_definition loc known_objs it
    ) (get_attribute_args "define" attrs)

  
let requires loc attrs =
  pre_or_post loc "requires" attrs

let ensures loc attrs =
  pre_or_post loc "ensures" attrs



     
