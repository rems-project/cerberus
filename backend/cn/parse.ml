(* open Cerb_frontend *)
open Cerb_frontend.Annot
open Resultat
open Effectful.Make(Resultat)
open TypeErrors
open Ast
open Pp


module Loc = Locations

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
      match Sym.symbol_description garg.asym with
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

let make_accessed_id globals (Sym.Identifier (loc, name)) =
  make_accessed globals (loc, name)


let parse_function 
      (globals : (Sym.t * Sym.t * Sctypes.t) list)
      trusted
      (arguments : (Sym.t * Sctypes.t) list)
      (return_type : Sctypes.t)
      (Attrs attributes)
  = 
  let arguments = List.map_fst (Sym.fresh_same) arguments in
  (* TODO: make it so reverse does not need to happen here *)
  let attributes = List.rev attributes in
  let globals = 
    List.map (fun (asym, lsym, typ) ->
        {asym; lsym; typ; accessed = None}
      ) globals 
  in
  let@ (trusted, globals, pre, post, defines_log_funs) =
    ListM.fold_leftM (fun (trusted, globals, pre, post, def_log) attr ->
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
              return (Mucore.Trusted keyword_loc, globals, pre, post, def_log)
           | "accesses" -> 
              let@ globals = ListM.fold_leftM make_accessed globals arguments in
              return (trusted, globals, pre, post, def_log)
           | "requires" -> 
              let@ () = pre_before_post keyword_loc post in
              let@ new_pre = ListM.mapM (parse Assertion_parser.start) arguments in
              return (trusted, globals, pre @ new_pre, post, def_log)
           | "ensures" -> 
              let@ new_post = ListM.mapM (parse Assertion_parser.start) arguments in
              return (trusted, globals, pre, post @ new_post, def_log)
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
           ListM.fold_leftM (fun (trusted, globals, pre, post, def_log)
               (loc, keyword_condition) ->
               match keyword_condition with
               | Trusted ->
                  return (Mucore.Trusted loc, globals, pre, post, def_log)
               | Accesses a ->
                  let@ globals = ListM.fold_leftM make_accessed_id globals a in
                  return (trusted, globals, pre, post, def_log)
               | Requires condition ->
                  let@ () = pre_before_post loc post in
                  return (trusted, globals, pre @ condition, post, def_log)
               | Ensures condition ->
                  return (trusted, globals, pre, post @ condition, def_log)
               | Inv _ ->
                  no_inv loc
               | Make_Function id ->
                  return (trusted, globals, pre, post, id :: def_log)
             ) (trusted, globals, pre, post, def_log) keyword_conditions
        | _ ->
           return (trusted, globals, pre, post, def_log)
      ) (trusted, globals, [], [], []) attributes
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
      post_condition;
      defines_log_funs;
    }

let parse_label 
      (lname : string)
      arguments
      global_arguments
      (Attrs attributes)
  = 
  (* TODO: make it so reverse does not need to happen here *)
  (* seems to no longer be needed, unclear why *)
  (* let attributes = List.rev attributes in *)
  let arguments = 
    List.map (fun (asym, typ) -> {asym; typ}) arguments 
  in
  let@ inv = 
    ListM.fold_leftM (fun inv attr ->
        let not_inv loc =
          fail {loc; msg = Generic !^("only 'inv' assertions can be used at label scope")}
        in
        match Option.map Id.s (attr.attr_ns), Id.s attr.attr_id with
        | Some "cn", id ->
           let Identifier (keyword_loc, keyword) = attr.attr_id in
           let arguments = List.map (fun (loc, arg, _) -> (loc, arg)) attr.attr_args in
           begin match id with
           | "trusted" -> not_inv keyword_loc
           | "accesses" -> not_inv keyword_loc
           | "requires" -> not_inv keyword_loc
           | "ensures" -> not_inv keyword_loc
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
               | Inv condition -> return (inv @ condition)
               | _ -> not_inv loc
             ) inv keyword_conditions
        | _, _ ->
           return inv
      ) [] attributes
  in
  return { 
      global_arguments = global_arguments; 
      label_arguments = arguments; 
      invariant = inv
    }
