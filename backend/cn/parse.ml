open Resultat
open TypeErrors
open Ast
open Pp
module CF = Cerb_frontend
module Loc = Locations

open CF.Annot

(* adapting from core_parser_driver.ml *)

let set_default_label label = 
  function 
  | None -> Some label
  | Some label' -> Some label'

let parse_condition default_label (loc, string) = 
  let lexbuf = Lexing.from_string string in
  let () = 
    let open Location_ocaml in
    Lexing.set_position lexbuf
      (* revisit *)
      begin match Location_ocaml.to_raw loc with
      | Loc_unknown -> lexbuf.lex_curr_p
      | Loc_other _ -> lexbuf.lex_curr_p
      | Loc_point pos -> pos
      (* start, end, cursor *)
      | Loc_region (pos, _, _ ) -> pos
      | Loc_regions ([],_) -> lexbuf.lex_curr_p 
      | Loc_regions ((pos,_) :: _, _) -> pos
      end
  in
  let () = match Location_ocaml.get_filename loc with
    | Some filename -> lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname= filename }
    | None -> () 
  in
  let* parsed_spec =
    try return (Assertion_parser.start Assertion_lexer.main lexbuf) with
    | Assertion_lexer.Error ->
       let loc = Location_ocaml.point @@ Lexing.lexeme_start_p lexbuf in
       fail loc (Generic !^"invalid symbol")
    | Assertion_parser.Error ->
       let loc = Location_ocaml.region (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) None in
       fail loc (Generic !^ ("Unexpected token " ^ Lexing.lexeme lexbuf))
  in
  return (loc, Ast.map_labels (set_default_label default_label) parsed_spec)

type cn_attribute = {
    keyword : Loc.t * string;
    arguments: (Loc.t * string) list
  }

let cn_attributes attributes =
  let open CF.Symbol in
  List.filter_map (fun attr ->
      match attr.attr_ns with
      | Some (Identifier (_, id)) when String.equal id "cn"  ->
         let (Identifier (loc, keyword)) = attr.attr_id in
         let arguments = 
           List.map (fun (loc, arg, _) -> 
               (loc, arg)
             ) attr.attr_args
         in
         Some {keyword = (loc, keyword); arguments}
      | _ -> None
    ) attributes



let make_accessed globals (loc, name) =
  let rec aux = function
    | [] -> fail loc (Generic !^("'"^name^"' is not a global variable"))
    | garg :: gargs when String.equal garg.name name ->
       begin match garg.accessed with
       | Some _ -> fail loc (Generic !^("already specified '"^name^"' as accessed"))
       | None -> return ({ garg with accessed = Some loc } :: gargs)
       end
    | garg :: gargs -> 
       let* gargs = aux gargs in
       return (garg :: gargs)
  in
  aux globals


let give_name sym = 
  match Sym.name sym with
  | Some name -> name
  | None -> Sym.pp_string sym

let parse_function 
      (globals : (Sym.t * Sym.t * Sctypes.t) list)
      (arguments : (Sym.t * Sctypes.t) list)
      (return_type : Sctypes.t)
      (Attrs attributes)
  = 
  (* TODO: make it so reverse does not need to happen here *)
  let attributes = List.rev attributes in
  let cn_attributes = cn_attributes attributes in
  let globals = 
    List.map (fun (asym, lsym, typ) ->
        {name = give_name asym; asym; lsym; typ; accessed = None}
      ) globals 
  in
  let* (globals, pre, post) = 
    ListM.fold_leftM (fun (globals,pre,post) attr ->
        match snd attr.keyword with
        | "accesses" -> 
           let* globals = 
             ListM.fold_leftM (fun globals arg ->
                 make_accessed globals arg
               ) globals attr.arguments
           in
           return (globals, pre, post)
        | "requires" -> 
           let* new_pre = ListM.mapM (parse_condition "start") attr.arguments in
           return (globals, pre @ new_pre, post)
        | "ensures" -> 
           let* new_post = ListM.mapM (parse_condition "end") attr.arguments in
           return (globals, pre, post @ new_post)
        | "inv" ->
           fail (fst attr.keyword) (Generic !^"'inv' is for loop specifications")
        | other ->
           fail (fst attr.keyword) (Generic !^("unknown keyword '"^other^"'"))
      ) (globals, [], []) cn_attributes
  in
  let global_arguments = globals in
  let function_arguments = 
    List.map (fun (asym, typ) -> 
        {name = give_name asym; asym; typ}
      ) arguments in
  let function_return = { name = "return"; vsym = Sym.fresh (); typ = return_type } in
  let pre_condition = pre in
  let post_condition = post in
  return { 
      global_arguments; 
      function_arguments; 
      function_return; 
      pre_condition; 
      post_condition 
    }

let parse_label 
      (lname : string)
      arguments
      (function_spec : Ast.function_spec)
      (Attrs attributes)
  = 
  (* TODO: make it so reverse does not need to happen here *)
  let attributes = List.rev attributes in
  let cn_attributes = cn_attributes attributes in
  let arguments = 
    List.map (fun (asym, typ) -> 
        {name = give_name asym; asym; typ}
      ) arguments 
  in
  let* inv = 
    ListM.fold_leftM (fun inv attr ->
        match snd attr.keyword with
        | "accesses" -> 
           fail (fst attr.keyword) (Generic !^"'accesses' is for function specifications")
        | "requires" -> 
           fail (fst attr.keyword) (Generic !^"'requires' is for function specifications")
        | "ensures" -> 
           fail (fst attr.keyword) (Generic !^"'ensures' is for function specifications")
        | "inv" ->
           let* new_inv = ListM.mapM (parse_condition lname) attr.arguments in
           return (inv @ new_inv)
        | other ->
           fail (fst attr.keyword) (Generic !^("unknown keyword '"^other^"'"))
      ) [] cn_attributes
  in
  return { 
      global_arguments = function_spec.global_arguments; 
      function_arguments = function_spec.function_arguments; 
      label_arguments = arguments; 
      invariant = inv
    }
