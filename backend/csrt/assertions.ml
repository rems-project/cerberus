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
open ECT
open Object



(* probably should record source location information *)
(* stealing some things from core_parser *)


let find_name loc names str = 
  begin match StringMap.find_opt str names with
  | Some sym -> return sym
  | None -> fail loc (Generic !^(str ^ " unbound"))
  end

let resolve_object loc (mapping : mapping) (o : Object.t) : (BT.t * Sym.t, type_error) m = 
  (* print stderr (item "mapping" (Mapping.pp mapping));
   * print stderr (item "o" (Object.pp o)); *)
  let open Object.Mapping in
  let found = List.find_opt (fun {obj;res} -> Object.equal obj o) mapping in
  match found with
  | None -> 
     fail loc (Generic (!^"term" ^^^ Object.pp o ^^^ !^"does not apply"))
  | Some {res; _} -> 
     return res





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
  | Object o -> 
     let* (bt,s) = resolve_object loc mapping o in
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

  




let get_attribute_args (CF.Annot.Attrs attrs) attribute_name =
  List.concat_map (fun a -> 
      if String.equal attribute_name (Id.s a.CF.Annot.attr_id) 
      then a.attr_args else []
    ) attrs 


type pre_or_post = 
  | Pre 
  | Post
  | Inv of string

let label_name = function
  | Pre -> "start"
  | Post -> "end"
  | Inv label -> label


let pre_or_post loc kind attrs = 

  let attribute_name = match kind with
    | Pre -> "requires"
    | Post -> "ensures"
    | Inv _ -> "inv"
  in 
  let relevant = get_attribute_args attrs attribute_name in
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
        | Ownership {pred;access} -> 
           (* begin match constrs with
            * | _ :: _ -> 
            *    fail loc (Generic !^"please specify all ownership constraints first, other constraints second")
            * | _ ->  *)
              let r = [(loc, Ownership.{pred; access})] in
              return (ownership @ r, constrs)
           (* end *)
        | Constraint p_it -> 
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
  { name; asym = sym; typ = ECT.of_ct loc ct }

let named_ctype_to_varg loc (sym, ct) =
  let name = match Sym.name sym with
    | Some name -> name
    | None -> Sym.pp_string sym
  in
  { name; vsym = sym; typ = ECT.of_ct loc ct }



open BaseName
open Ownership

let apply_ownership {name = {label;v}; derefs} ownership loc typ = 
  let rec aux so_far_derefs todo_derefs (Typ (annots, typ_)) =
    let pp_so_far () = pp_access {name = {v; label}; derefs =so_far_derefs} in
    match todo_derefs with
    | Pointee :: todo ->
       begin match typ_ with
       | Pointer (qualifiers, _, Owned, typ2) ->
          let* typ2 = aux (so_far_derefs @ [Pointee]) todo typ2 in
          let typ_ = Pointer (qualifiers, loc, Owned, typ2) in
          return (Typ (annots, typ_))
       | Pointer (_, _, _, _) ->
          fail loc (Generic (pp_so_far () ^^^ !^"is not an owned pointer"))
       | _ ->
          fail loc (Generic (pp_so_far () ^^^ !^"is not a pointer"))
       end
    | [] ->
       begin match typ_ with
       | Pointer (qualifiers, _, existing_ownership, typ2) 
            when not (Pred.equal existing_ownership default_pointer_ownership) ->
          fail loc (Generic (!^"ownership of" ^^^ pp_so_far () ^^^ !^"already specified"))
       | Pointer (qualifiers, _, _, typ2) ->
          return (Typ (annots, Pointer (qualifiers, loc, ownership, typ2)))
       | _ -> 
          fail loc (Generic (pp_so_far () ^^^ !^"is not a pointer"))
       end
  in
  aux [] derefs typ
     
     

(* returns the requirements that weren't applied *)
let apply_ownerships name typ requirements =
  let rec aux typ = function
    | [] -> 
       return (typ, [])
    | (loc, {pred; access}) :: rest when String.equal name access.name.v ->
       let* typ = apply_ownership access pred loc typ in
       aux typ rest
    | tn :: rest ->
       let* (typ, left) = aux typ rest in
       return (typ, tn :: rest)
    in
    aux typ requirements



let apply_ownerships_varg (varg: varg) requirements =
  let* (typ,left) = apply_ownerships varg.name varg.typ requirements in
  return ({varg with typ}, left)

let apply_ownerships_aarg (aarg: aarg) requirements =
  let* (typ,left) = apply_ownerships aarg.name aarg.typ requirements in
  return ({aarg with typ}, left)


let rec apply_ownerships_vargs (vargs: vargs) requirements =
  match vargs with
  | [] -> 
     return ([], requirements)
  | varg :: vargs -> 
     let* (varg, left) = apply_ownerships_varg varg requirements in
     let* (vargs, left) = apply_ownerships_vargs vargs left in
     return (varg :: vargs, left)

let rec apply_ownerships_aargs (aargs: aargs) requirements =
  match aargs with
  | [] -> 
     return ([], requirements)
  | aarg :: aargs -> 
     let* (aarg, left) = apply_ownerships_aarg aarg requirements in
     let* (aargs, left) = apply_ownerships_aargs aargs left in
     return (aarg :: aargs, left)

let ensure_none_left = function
  | [] -> return ()
  | (loc, {pred; access}) :: _ -> 
     fail loc (Unbound_name (String access.name.v))


let parse_function_type loc attrs glob_cts ((ret_ct, arg_cts) : (Sctypes.t * (Sym.t * Sctypes.t) list)) =
  (* collect information *)
  let* (pre_ownership, pre_constraints) = requires loc attrs in
  let* (post_ownership, post_constraints) = ensures loc attrs in
  let globs = List.map (named_ctype_to_aarg loc) glob_cts in
  let args_original = List.map (named_ctype_to_aarg loc) arg_cts in
  let ret = { name = "ret"; vsym = Sym.fresh (); typ = ECT.of_ct loc ret_ct } in
  (* apply ownership *)
  let* (globs, pre_left) = apply_ownerships_aargs globs pre_ownership in
  let* (args, pre_left) = apply_ownerships_aargs args_original pre_left in
  let* () = ensure_none_left pre_left in
  let* (glob_rets, post_left) = apply_ownerships_aargs globs post_ownership in
  let* (arg_rets, post_left) = apply_ownerships_aargs args_original post_ownership in
  let* (ret, post_left) = apply_ownerships_varg ret post_left in
  let* () = ensure_none_left post_left in
  (* plug together *)
  let fpost = FPost post_constraints in
  let frt = FRT {ret; glob_rets = glob_rets; arg_rets} in
  let fret = FRet (frt, fpost) in
  let fpre = FPre (pre_constraints, fret) in
  let fa = FA {globs; args} in
  let ft = FT (fa, fpre) in
  return ft



let parse_label_type loc lname attrs globs (fargs : aarg list) (larg_cts : (Sym.t * Sctypes.t) list) =
  (* collect information *)
  let* (pre_ownership, pre_constraints) = inv lname loc attrs in
  let largs = List.map (named_ctype_to_varg loc) larg_cts in
  (* apply ownership *)
  let* (globs, pre_left) = apply_ownerships_aargs fargs pre_ownership in
  let* (fargs, pre_left) = apply_ownerships_aargs fargs pre_left in
  let* (largs, pre_left) = apply_ownerships_vargs largs pre_left in
  let* () = ensure_none_left pre_left in
  (* plug together *)
  let open AST in
  let label_args = LA {globs; fargs; largs} in
  let linv = LInv pre_constraints in
  let lt = LT (label_args, linv) in
  return lt
