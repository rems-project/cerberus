open Pp
open Resultat

module CF = Cerb_frontend
module StringMap = Map.Make(String)
module IT = IndexTerms
module AST = Parse_ast
module LC = LogicalConstraints
module PIT = Parse_ast.IndexTerms
module TE = TypeErrors

open Parse_ast

(* probably should record better source location information *)

(* stealing some things from core_parser and core_parser_driver *)
(* and https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html *)





type cn_attribute = { 
    keyword : Id.t;
    args : (Loc.t * string) list;
  }


let cn_attribute a = 
  match a.CF.Annot.attr_ns with
  | Some ns when String.equal (Id.s ns) "cn" ->
     Some {keyword = a.attr_id; args = a.attr_args}
  | _ -> None

let cn_attributes (CF.Annot.Attrs attrs) = 
  List.filter_map cn_attribute attrs



type pre_or_post = 
  | Pre 
  | Post
  | Inv of string

let label_name = function
  | Pre -> "start"
  | Post -> "end"
  | Inv label -> label








let resolve_path loc (mapping : mapping) (o : Path.t) : (BT.t * Sym.t, TE.type_error) m = 
  let open Mapping in
  let found = List.find_opt (fun {path;_} -> Path.equal path o) mapping in
  match found with
  | Some {sym; bt; _} -> 
     return (bt, sym)
  | None -> 
     fail loc (TE.Generic (!^"term" ^^^ Path.pp o ^^^ !^"does not apply"))




(* change this to return unit IT.term, then apply index term type
   checker *)
let rec resolve_index_term loc mapping (it: PIT.index_term) 
        : (BT.t IT.term, TE.type_error) m =
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
  | Exp (it, it') -> 
     let* it = aux it in
     let* it' = aux it' in
     return (IT.Exp (it, it'))
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


let rec resolve_predarg loc mapping = function
  | Path.NumArg z -> 
     return (IT.Num z)
  | Add (p,a) -> 
     let* it = resolve_predarg loc mapping p in
     let* it' = resolve_predarg loc mapping a in
     return (IT.Add (it, it'))
  | Sub (p,a) -> 
     let* it = resolve_predarg loc mapping p in
     let* it' = resolve_predarg loc mapping a in
     return (IT.Sub (it, it'))
  | AddPointer (p,a) -> 
     let* it = resolve_predarg loc mapping p in
     let* it' = resolve_predarg loc mapping a in
     return (IT.AddPointer (it, it'))
  | SubPointer (p,a) -> 
     let* it = resolve_predarg loc mapping p in
     let* it' = resolve_predarg loc mapping a in
     return (IT.SubPointer (it, it'))
  | PathArg p ->
     let* (ls, s) = resolve_path loc mapping p in
     return (IT.S (ls, s))



let resolve_constraints mapping its =
  ListM.mapM (fun (loc,lc) ->
      let* it = resolve_index_term loc mapping lc in
      return (LC.LC it)
    ) its






let parse_condition default_label (loc, s) =
  let module Parser = Parser.Make(struct let default_label = default_label end) in
  let lexbuf = Lexing.from_string s in
  try return (loc, Parser.spec_entry Lexer.read lexbuf) with
  | Lexer.SyntaxError c ->
     (* let loc = Locations.point @@ Lexing.lexeme_start_p lexbuf in *)
     fail loc (TE.Generic !^("invalid symbol: " ^ c))
  | Parser.Error ->
     (* let loc = 
      *   let startp = Lexing.lexeme_start_p lexbuf in
      *   let endp = Lexing.lexeme_end_p lexbuf in
      *   Locations.region (startp, endp) None 
      * in *)
     fail loc (TE.Generic !^("unexpected token: " ^ Lexing.lexeme lexbuf))
  | Failure msg ->
     Debug_ocaml.error "assertion parsing error"



let parse_conditions label conditions =
  let* requirements = 
    ListM.mapM (parse_condition label) conditions in
  let (ownership,constraints) = 
    List.fold_left (fun (ownership, constrs) (loc, condition) ->
        match condition with
        | R (path,pred) -> 
           let r = [(loc, (path,pred))] in
           (ownership @ r, constrs)
        | C p_it -> 
           (ownership, constrs @ [(loc, p_it)])
      ) ([], []) requirements
  in
  return (ownership,constraints)



let check_accessed glob_cts (loc, name) =
  let exists = 
    List.exists (fun (gsym, _, _) ->
        Option.equal String.equal (Some name) (Sym.name gsym)
      ) glob_cts
  in
  if exists then return ()
  else fail loc (TE.Generic !^(name ^ " not a global"))


let name sym = 
  match Sym.name sym with
  | Some name -> name
  | None -> Sym.pp_string sym


let is_accessed accessed name = 
  List.find_map (fun (loc, n) ->
      if name = n then Some loc else None
    ) accessed

let parse_function_type attrs glob_cts ((ret_ct, arg_cts) : (Sctypes.t * (Sym.t * Sctypes.t) list)) =
  let cn_attributes = cn_attributes attrs in
  let* (accessed, (pre_r, pre_c), (post_r, post_c)) = 
    ListM.fold_leftM (fun (accessed, (pre_r, pre_c), (post_r, post_c)) attr ->
        match Id.s attr.keyword with
        | "accesses" -> 
           return (accessed @ attr.args, (pre_r, pre_c), (post_r, post_c))
        | "requires" -> 
           let* (r,c) = parse_conditions "start" attr.args in
           return (accessed, (pre_r @ r, pre_c @ c), (post_r, post_c))
        | "ensures" -> 
           let* (r,c) = parse_conditions "end" attr.args in
           return (accessed, (pre_r, pre_c), (post_r @ r, post_c @ c))
        | "inv" -> 
           fail (Id.loc attr.keyword) (TE.Generic !^"cannot use 'inv' here")
        | wrong -> 
           fail (Id.loc attr.keyword) (TE.Generic !^("unknown keyword '" ^ wrong ^ "'"))
      ) ([],([],[]),([],[])) cn_attributes
  in
  let* () = ListM.iterM (check_accessed glob_cts) accessed in
  let fargs = 
    List.map (fun (sym, ct) -> 
        { name = name sym; asym = sym; typ = ct })
      arg_cts 
  in
  let globs = 
    List.map (fun (sym, lsym, ct) ->
        let name = name sym in
        { name; lsym = lsym; typ = ct; 
          accessed = is_accessed accessed name}
      )
      glob_cts in
  let ret = { name = "return"; vsym = Sym.fresh_named "return"; typ = ret_ct } in
  let ft =
    FT (FA {globs; fargs}, 
        FPre (pre_r, pre_c), 
        FRet ret, FPost (post_r, post_c)
      )
  in
  return ft



let parse_label_type loc label attrs globs (fargs : aarg list) (larg_cts : (Sym.t * Sctypes.t) list) =
  let cn_attributes = cn_attributes attrs in
  let* (pre_r, pre_c) = 
    ListM.fold_leftM (fun (pre_r, pre_c) attr ->
        match Id.s attr.keyword with
        | "inv" -> 
           let* (r,c) = parse_conditions label attr.args in
           return (pre_r @ r, pre_c @ c)
        | "accesses" -> 
           fail (Id.loc attr.keyword) 
             (TE.Generic !^"cannot use 'accesses' here")
        | "requires" -> 
           fail (Id.loc attr.keyword) 
             (TE.Generic !^"cannot use 'requires' here")
        | "ensures" -> 
           fail (Id.loc attr.keyword) 
             (TE.Generic !^"cannot use 'ensures' here")
        | wrong -> 
           fail (Id.loc attr.keyword) (TE.Generic !^("unknown keyword '" ^ wrong ^ "'"))
      ) ([],[]) cn_attributes
  in
  let largs = 
    List.map (fun (sym, ct) ->
        { name = name sym; asym = sym; typ = ct }
      ) larg_cts 
  in
  let lt = LT (LA {globs; fargs; largs}, LInv (pre_r, pre_c)) in
  return lt
