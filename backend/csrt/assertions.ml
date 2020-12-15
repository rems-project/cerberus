open Pp
open TypeErrors
open Resultat

module CF = Cerb_frontend
module StringMap = Map.Make(String)
module IT = IndexTerms
module AST = Parse_ast
module LC = LogicalConstraints
module PIT = Parse_ast.IndexTerms
open Parse_ast




(* probably should record source location information *)
(* stealing some things from core_parser *)


let find_name loc names str = 
  begin match StringMap.find_opt str names with
  | Some sym -> return sym
  | None -> fail loc (Generic !^(str ^ " unbound"))
  end

let resolve_path loc (mapping : mapping) (o : Path.t) : (BT.t * Sym.t, type_error) m = 
  (* print stderr (item "mapping" (Mapping.pp mapping));
   * print stderr (item "o" (Path.pp o)); *)
  let open Mapping in
  let found = List.find_opt (fun {path;_} -> Path.equal path o) mapping in
  match found with
  | None -> 
     fail loc (Generic (!^"term" ^^^ Path.pp o ^^^ !^"does not apply"))
  | Some {sym; bt; _} -> 
     return (bt, sym)





(* change this to return unit IT.term, then apply index term type
   checker *)
let rec resolve_index_term loc mapping (it: PIT.index_term) 
        : (BT.t IT.term, type_error) m =
  let aux = resolve_index_term loc mapping in
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
  | Path o -> 
     let* (bt,s) = resolve_path loc mapping o in
     return (IT.S (bt, s))
  | MinInteger it ->
     return (IT.MinInteger it)
  | MaxInteger it ->
     return (IT.MaxInteger it)
  | IntegerToPointerCast it ->
     let* it = aux it in
     return (IT.IntegerToPointerCast it)
  | PointerToIntegerCast it -> 
     let* it = aux it in
     return (IT.PointerToIntegerCast it)



(* https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html *)
(* stealing from core_parser_driver *)

let parse_condition loc default_label s =
  let module P = Parser.Make(struct let default_label = default_label end) in
  let lexbuf = Lexing.from_string s in
  try return (P.spec_entry Lexer.read lexbuf) with
  | Lexer.SyntaxError c ->
     (* let loc = Locations.point @@ Lexing.lexeme_start_p lexbuf in *)
     fail loc (Generic !^("invalid symbol: " ^ c))
  | P.Error ->
     (* let loc = 
      *   let startp = Lexing.lexeme_start_p lexbuf in
      *   let endp = Lexing.lexeme_end_p lexbuf in
      *   Locations.region (startp, endp) None 
      * in *)
     fail loc (Generic !^("unexpected token: " ^ Lexing.lexeme lexbuf))
  | Failure msg ->
     Debug_ocaml.error "assertion parsing error"

  






type pre_or_post = 
  | Pre 
  | Post
  | Inv of string

let label_name = function
  | Pre -> "start"
  | Post -> "end"
  | Inv label -> label


let accesses loc (CF.Annot.Attrs attrs) = 
  let attribute_name = "accesses" in
  let relevant = 
    List.concat_map (fun a -> 
        if String.equal attribute_name (Id.s a.CF.Annot.attr_id) 
        then a.attr_args else []
      ) attrs 
  in
  List.map (fun (loc',str) -> 
      let loc = Locations.update loc loc' in
      (loc, str)
    ) relevant

let pre_or_post loc kind (CF.Annot.Attrs attrs) = 
  let attribute_name = match kind with
    | Pre -> "requires"
    | Post -> "ensures"
    | Inv _ -> "inv"
  in 
  let relevant = 
    List.concat_map (fun a -> 
        if String.equal attribute_name (Id.s a.CF.Annot.attr_id) 
        then a.attr_args else []
      ) attrs 
  in
  (* print stderr (item "number" (!^(string_of_int (List.length relevant)))); *)
  let* requirements = 
    ListM.mapM 
      (fun (loc',str) -> 
        let loc' = Locations.update loc loc' in
        let* c = parse_condition loc' (label_name kind) str in
        return (loc', c)
      ) relevant
  in
  let* (ownership,constraints) = 
    ListM.fold_leftM (fun (ownership, constrs) (loc, p) ->
        match p with
        | R (path,pred) -> 
           (* begin match constrs with
            * | _ :: _ -> 
            *    fail loc (Generic !^"please specify all ownership constraints first, other constraints second")
            * | _ ->  *)
              let r = [(loc, (path,pred))] in
              return (ownership @ r, constrs)
           (* end *)
        | C p_it -> 
           return (ownership, constrs @ [(loc, p_it)])
      ) ([], []) requirements
  in
  return (ownership,constraints)


  
let resolve_constraints mapping its =
  ListM.mapM (fun (loc,lc) ->
      let* it = resolve_index_term loc mapping lc in
      return (LC.LC it)
    ) its
  


let requires loc attrs =
  pre_or_post loc Pre attrs

let ensures loc attrs =
  pre_or_post loc Post attrs

let inv label loc attrs =
  pre_or_post loc (Inv label) attrs



     





let named_ctype_to_aarg loc (sym, ct) =
  let name = match Sym.name sym with
    | Some name -> name
    | None -> Sym.pp_string sym
  in
  { name; asym = sym; typ = ct }

let named_ctype_to_varg loc (sym, ct) =
  let name = match Sym.name sym with
    | Some name -> name
    | None -> Sym.pp_string sym
  in
  { name; vsym = sym; typ = ct }

let named_ctype_to_garg loc accesses (sym, lsym, ct) =
  let name = match Sym.name sym with
    | Some name -> name
    | None -> Sym.pp_string sym
  in
  let accessed = List.mem name accesses in
  { name; lsym = lsym; typ = ct; accessed }



(* open Ownership *)



let parse_function_type loc attrs glob_cts ((ret_ct, arg_cts) : (Sctypes.t * (Sym.t * Sctypes.t) list)) =
  (* collect information *)
  let accessed = accesses loc attrs in
  let* (pre_resources, pre_constraints) = requires loc attrs in
  let* (post_resources, post_constraints) = ensures loc attrs in
  let* () = 
    let accessed_not_glob = 
      List.find_opt (fun (loc, name) ->
          not (List.exists (fun (gsym, _, _) ->
                   Option.equal String.equal (Some name) (Sym.name gsym)
                 ) glob_cts
            )
        ) accessed
    in
    match accessed_not_glob with
    | None -> return ()
    | Some (loc, name) -> fail loc (Generic !^(name ^ " not a global"))
  in
  let fargs = List.map (named_ctype_to_aarg loc) arg_cts in
  let globs = List.map (named_ctype_to_garg loc (List.map snd accessed)) glob_cts in
  let ret = { name = "ret"; vsym = Sym.fresh_named "ret"; typ = ret_ct } in
  let ft =
    FT (FA {globs; fargs}, 
        FPre (pre_resources, pre_constraints),
        FRet ret,
        FPost (post_resources, post_constraints))
  in
  return ft




let parse_label_type loc lname attrs globs (fargs : aarg list) (larg_cts : (Sym.t * Sctypes.t) list) =
  (* collect information *)
  let* (pre_resources, pre_constraints) = inv lname loc attrs in
  let largs = List.map (named_ctype_to_varg loc) larg_cts in
  let lt =
    LT (LA {globs; fargs; largs}, LInv (pre_resources, pre_constraints))
  in
  return lt


  (* (\* apply ownership *\)
   * let* (globs, pre_left) = apply_ownerships_aargs fargs pre_ownership in
   * let* (fargs, pre_left) = apply_ownerships_aargs fargs pre_left in
   * let* (largs, pre_left) = apply_ownerships_vargs largs pre_left in
   * let* () = ensure_none_left pre_left in
   * (\* plug together *\)
   * let open AST in
   * let label_args = LA {globs; fargs; largs} in
   * let linv = LInv pre_constraints in
   * let lt = LT (label_args, linv) in
   * return lt *)
