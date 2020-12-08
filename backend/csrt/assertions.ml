open Pp
open TypeErrors
open Resultat

module CF = Cerb_frontend
module StringMap = Map.Make(String)
(* module IT = IndexTerms *)
module AST = Parse_ast
module LC = LogicalConstraints
open AST
open IndexTerms
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
  let open Object.Mapping in
  let found = List.find_opt (fun {obj;res} -> Object.equal obj o) mapping in
  match found with
  | None -> 
     fail loc (Generic (!^"term" ^^^ Object.pp o ^^^ !^"does not apply"))
  | Some {res; _} -> 
     return res





(* change this to return unit IT.term, then apply index term type
   checker *)
let rec resolve_index_term loc mapping (it: index_term) 
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
  print stderr (item "number" (!^(string_of_int (List.length relevant))));
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
           begin match constrs with
           | _ :: _ -> 
              fail loc (Generic !^"please specify all ownership constraints first, other constraints second")
           | _ -> 
              let r = [(loc, Ownership.{pred; access})] in
              return (ownership @ r, constrs)
           end
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



     

let rec ct_to_ct loc ((Sctypes.Sctype (annots,raw_ctype)) : Sctypes.t) =
  let loc = Loc.update loc (CF.Annot.get_loc_ annots) in
  match raw_ctype with
  | Sctypes.Void -> 
     Typ (loc, Void)
  | Sctypes.Integer it -> 
     Typ (loc, Integer it)
  | Pointer (qualifiers, ct) ->
     let t = ct_to_ct loc ct in
     Typ (loc, Pointer (qualifiers, Owned t))
  | Struct tag ->
     Typ (loc, Struct tag)

let named_ctype_to_aarg loc (sym, ct) =
  let name = match Sym.name sym with
    | Some name -> name
    | None -> Sym.pp_string sym
  in
  { name; asym = sym; typ = ct_to_ct loc ct }

let named_ctype_to_varg loc (sym, ct) =
  let name = match Sym.name sym with
    | Some name -> name
    | None -> Sym.pp_string sym
  in
  { name; vsym = sym; typ = ct_to_ct loc ct }



open BaseName
open Ownership

let apply_ownership {name = {label;v}; derefs} ownership loc typ = 
  let rec aux so_far_derefs todo_derefs (Typ (annots, typ_)) =
    let pp_so_far () = pp_access {name = {v; label}; derefs =so_far_derefs} in
    begin match todo_derefs, typ_, ownership with
    | Pointee :: todo, Pointer (qualifiers, Owned typ2), _ ->
       let* typ2 = aux (so_far_derefs @ [Pointee]) todo typ2 in
       let typ_ = Pointer (qualifiers, Owned typ2) in
       return (Typ (annots, typ_))
    | [], Pointer (qualifiers, Owned t), AST.Pred.OUnowned ->
       let typ_ = Pointer (qualifiers, Unowned (loc, t)) in
       return (Typ (annots, typ_))
    | [], Pointer (qualifiers, Owned t), AST.Pred.OBlock ->
       let typ_ = Pointer (qualifiers, Block (loc, t)) in
       return (Typ (annots, typ_))
    | [], Pointer (qualifiers, Owned t), AST.Pred.OPred s ->
       let typ_ = Pointer (qualifiers, Pred (loc, s, t)) in
       return (Typ (annots, typ_))
    | _, Pointer (qualifiers, Unowned (loc,_)), _ ->
       fail loc (Generic (pp_so_far () ^^^ !^"was specified as unowned"))
    | _, Pointer (qualifiers, Block (loc, _)), _ ->
       fail loc (Generic (pp_so_far () ^^^ !^"was specified as uninitialised"))
    | _, _, (OUnowned | OBlock | OPred _) -> 
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

let parse_function_type loc attrs (raw_function_type : (Sctypes.t * (Sym.t * Sctypes.t) list)) =
  let (ret_ct, arg_cts) = raw_function_type in
  let* (pre_ownership, pre_constraints) = requires loc attrs in
  let* (post_ownership, post_constraints) = ensures loc attrs in
  (* print stderr (item "pre_ownership" (Pp.list Ownership.pp (List.map snd pre_ownership)));
   * print stderr (item "post_ownership" (Pp.list Ownership.pp (List.map snd post_ownership))); *)
  let* args = 
    let args = List.map (named_ctype_to_aarg loc) arg_cts in
    let* (args, left) = apply_ownerships_aargs args pre_ownership in
    match left with
    | [] -> return args
    | (loc, {pred; access}) :: _ -> fail loc (Unbound_name (String access.name.v))
  in
  let* (arg_rets, ret) = 
    let arg_rets = List.map (named_ctype_to_aarg loc) arg_cts in
    let* (arg_rets, left) = apply_ownerships_aargs arg_rets post_ownership in
    let ret = { name = "ret"; vsym = Sym.fresh (); typ = ct_to_ct loc ret_ct } in
    let* (ret, left) = apply_ownerships_varg ret left in
    match left with
    | [] -> return (arg_rets, ret)
    | (loc, {access; _}) :: _ -> fail loc (Unbound_name (String access.name.v))
  in

  let ft = FunctionType (Args (args, Pre (pre_constraints, Ret (ret, arg_rets, Post post_constraints)))) in

  return ft



let parse_label_type loc lname attrs (fargs : aarg list) (larg_cts : (Sym.t * Sctypes.t) list) =
  let* (pre_ownership, pre_constraints) = inv lname loc attrs in
  let largs = List.map (named_ctype_to_varg loc) larg_cts in
  let* (fargs, left) = apply_ownerships_aargs fargs pre_ownership in
  let* (largs, left) = apply_ownerships_vargs largs left in
  let* () = match left with
    | [] -> return ()
    | (loc, {access; _}) :: _ -> fail loc (Unbound_name (String access.name.v))
  in
  let open AST in
  let lt = 
    LabelType (LArgs {function_arguments = fargs;
                      label_arguments = largs;
                      inv = LInv pre_constraints}) in

  return lt
