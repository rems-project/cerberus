open Resultat
open Effectful.Make(Resultat)
open TypeErrors
open Ast
open Pp
module CF = Cerb_frontend
module Loc = Locations

open CF.Annot

(* adapting from core_parser_driver.ml *)

let parse parser_start (loc, string) = 
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
  let@ parsed_spec =
    try return (parser_start Assertion_lexer.main lexbuf) with
    | Assertion_lexer.Error ->
       let loc = Location_ocaml.point @@ Lexing.lexeme_start_p lexbuf in
       fail {loc; msg = Generic !^"invalid symbol"}
    | Assertion_parser.Error ->
       let loc = Location_ocaml.(region (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) NoCursor) in
       fail {loc; msg = Generic !^ ("Unexpected token " ^ Lexing.lexeme lexbuf)}
  in
  return (loc, parsed_spec)

type cn_attribute = {
    keyword : Loc.t * string;
    arguments: (Loc.t * string) list
  }

let cn_attributes attributes =
  let open CF.Symbol in
  List.concat_map (fun attr ->
      match Option.map Id.s (attr.attr_ns), Id.s attr.attr_id with
      | Some "cn", _ ->
         let (Identifier (loc, keyword)) = attr.attr_id in
         let arguments = 
           List.map (fun (loc, arg, _) -> 
               (loc, arg)
             ) attr.attr_args
         in
         [{keyword = (loc, keyword); arguments}]
      | _ ->
      (* | Some "cerb", "magic" -> *)
         print stdout !^"here************* ";
         print stdout
           (item "args" (Pp.list (fun (loc, name, asd) ->
                             parens (Loc.pp loc ^^ comma ^^^ !^name ^^ comma ^^^
                                       Pp.list (fun (aloc, str) -> parens (Loc.pp aloc ^^ comma ^^^ !^str)) asd)
                           ) attr.attr_args));
         []
      (* | _ ->  *)
      (*    [] *)
    ) attributes



let make_accessed globals (loc, name) =
  let rec aux = function
    | [] -> 
       fail {loc; msg = Generic !^("'"^name^"' is not a global variable")}
    | garg :: gargs ->
      match CF.Symbol.symbol_description garg.asym with
      | SD_ObjectAddress name' when String.equal name name' ->
         begin match garg.accessed with
         | Some _ -> 
            fail {loc; msg = Generic !^("already specified '"^name^"' as accessed")}
         | None -> 
            return ({ garg with accessed = Some loc } :: gargs)
         end
      | _ -> 
         let@ gargs = aux gargs in
         return (garg :: gargs)
  in
  aux globals

let make_accessed_id globals (CF.Symbol.Identifier (loc, name)) =
  make_accessed globals (loc, name)


let parse_function 
      (globals : (Sym.t * Sym.t * Sctypes.t) list)
      trusted
      (arguments : (Sym.t * Sctypes.t) list)
      (return_type : Sctypes.t)
      (Attrs attributes)
  = 
  (* TODO: make it so reverse does not need to happen here *)
  let attributes = List.rev attributes in
  let globals = 
    List.map (fun (asym, lsym, typ) ->
        {asym; lsym; typ; accessed = None}
      ) globals 
  in
  let@ (trusted, globals, pre, post) = 
    ListM.fold_leftM (fun (trusted, globals, pre, post) attr ->
        let pre_before_post loc post = 
          match post with
          | [] -> return ()
          | _ -> 
             let () = print stdout (Pp.int (List.length post)) in
             fail {loc = loc; msg = Generic !^"please specify the pre-conditions before the post-conditions"}
        in
        let no_inv loc = 
          fail {loc; msg = Generic !^"'inv' is for loop specifications"}
        in
        match Option.map Id.s (attr.attr_ns), Id.s (attr.attr_id) with
        (* handling attribute syntax *)
        | Some "cn", _ ->
           let Identifier (keyword_loc, keyword) = attr.attr_id in
           let arguments = List.map (fun (loc, arg, _) -> (loc, arg)) attr.attr_args in
           begin match keyword with
           | "trusted" ->
              let@ () = match attr.attr_args with
                | [] -> return ()
                | _ -> fail {loc = keyword_loc; 
                             msg = Generic !^"'trusted' takes no arguments"}
              in
              return (CF.Mucore.Trusted keyword_loc, globals, pre, post)
           | "accesses" -> 
              let@ globals = ListM.fold_leftM make_accessed globals arguments in
              return (trusted, globals, pre, post)
           | "requires" -> 
              let@ () = pre_before_post keyword_loc post in
              let@ new_pre = ListM.mapM (parse Assertion_parser.start) arguments in
              return (trusted, globals, pre @ new_pre, post)
           | "ensures" -> 
              let@ new_post = ListM.mapM (parse Assertion_parser.start) arguments in
              return (trusted, globals, pre, post @ new_post)
           | "inv" -> no_inv keyword_loc
           | other -> fail {loc = keyword_loc; msg = Generic !^("unknown keyword '"^other^"'")}
           end
        (* handling magic comment syntax *)
        | Some "cerb", "magic" ->
           let@ keyword_conditions = 
             ListM.mapM (fun (loc, arg, _) ->
                 parse Assertion_parser.keyword_condition (loc, arg)
               ) attr.attr_args
           in
           ListM.fold_leftM (fun (trusted, globals, pre, post) (loc, keyword_condition) ->
               match keyword_condition with
               | Trusted ->
                  return (CF.Mucore.Trusted loc, globals, pre, post)
               | Accesses a ->
                  let@ globals = ListM.fold_leftM make_accessed_id globals a in
                  return (trusted, globals, pre, post)
               | Requires condition ->
                  let@ () = pre_before_post loc post in
                  return (trusted, globals, pre @ condition, post)
               | Ensures condition ->
                  return (trusted, globals, pre, post @ condition)
               | Inv _ ->
                  no_inv loc
             ) (trusted, globals, pre, post) keyword_conditions
        | _ ->
           return (trusted, globals, pre, post)
      ) (trusted, globals, [], []) attributes
  in
  let global_arguments = globals in
  let function_arguments = 
    List.map (fun (esym, typ) -> {esym; typ}) arguments in
  let function_return = { vsym = Sym.fresh_description SD_Return; typ = return_type } in
  let pre_condition = pre in
  let post_condition = post in
  return { 
      trusted;
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
  (* seems to no longer be needed, unclear why *)
  (* let attributes = List.rev attributes in *)
  let arguments = 
    List.map (fun (asym, typ) -> {asym; typ}) arguments 
  in
  let function_arguments = 
    List.map (fun {esym; typ} ->
        {asym = esym; typ}
      ) function_spec.function_arguments
  in
  let@ inv = 
    ListM.fold_leftM (fun inv attr ->
        let no_trusted loc = 
          fail {loc; msg = Generic !^("currently 'trusted' only works for functions, not labels")}
        in
        let no_accesses loc =
          fail {loc; msg = Generic !^"'accesses' is for function specifications"}
        in
        let no_requires loc = 
          fail {loc; msg = Generic !^"'requires' is for function specifications"}
        in
        let no_ensures loc =
          fail {loc; msg = Generic !^"'ensures' is for function specifications"}
        in
        match Option.map Id.s (attr.attr_ns), Id.s attr.attr_id with
        | Some "cn", id ->
           let Identifier (keyword_loc, keyword) = attr.attr_id in
           let arguments = List.map (fun (loc, arg, _) -> (loc, arg)) attr.attr_args in
           begin match id with
           | "trusted" -> no_trusted keyword_loc
           | "accesses" -> no_accesses keyword_loc
           | "requires" -> no_requires keyword_loc
           | "ensures" -> no_ensures keyword_loc
           | "inv" ->
              let@ new_inv = ListM.mapM (parse Assertion_parser.start) arguments in
              return (inv @ new_inv)
           | other ->
              fail {loc = keyword_loc; msg = Generic !^("unknown keyword '"^other^"'")}
           end
        | Some "cerb", "magic" ->
           let@ keyword_conditions = 
             ListM.mapM (fun (loc, arg, _) ->
                 parse Assertion_parser.keyword_condition (loc, arg)
               ) attr.attr_args
           in
           ListM.fold_leftM (fun inv (loc, keyword_condition) ->
               match keyword_condition with
               | Trusted -> no_trusted loc
               | Accesses _ -> no_accesses loc
               | Requires _ -> no_requires loc
               | Ensures _ -> no_ensures loc
               | Inv condition -> return (inv @ condition)
             ) inv keyword_conditions
        | _, _ ->
           return inv
      ) [] attributes
  in
  return { 
      global_arguments = function_spec.global_arguments; 
      function_arguments = function_arguments; 
      label_arguments = arguments; 
      invariant = inv
    }
