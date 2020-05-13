open PPrint
open TypeErrors
open Sexplib
open Except


let parse_error (loc: Locations.t) (t : string) (sx : Sexp.t) =
  let fname = (!^) t in
  let err = parens fname ^^ space ^^ (!^ "unexpected token") ^^ 
              colon ^^ space ^^ (!^ (Sexp.to_string sx)) in
  fail loc (Generic_error err)



let parse_base_type loc (names : NameMap.t) sx = 
  let open BaseTypes in
  match sx with
  | Sexp.Atom "unit" -> 
     return (Unit,names)
  | Sexp.Atom "bool" -> 
     return (Bool,names)
  | Sexp.Atom "int" -> 
     return (Int,names)
  | Sexp.Atom "loc" -> 
     return (Loc,names)
  | Sexp.Atom "array" -> 
     return (Array,names)
  (* | Sexp.List [Sexp.Atom "list"; bt] -> 
   *    parse_base_type loc names bt >>= fun bt -> 
   *    return (List bt) *)
  | Sexp.List [Sexp.Atom "struct"; Sexp.Atom id] -> 
     NameMap.sym_of loc id names >>= fun sym ->
     return (Struct sym, names)
  (* | Sexp.List tuple_items -> 
   *    fold_leftM (parse_tuple_item loc) ([],names) tuple_items >>= fun (nbts,names) ->
   *    return (Tuple nbts,names) *)
  | a -> parse_error loc "base type" a

(* and parse_tuple_item loc (components, names) s = 
 *   match s with
 *   | Sexp.List [Sexp.Atom id; Sexp.Atom ":"; bt] ->
 *      let name = Sym.fresh_pretty id in
 *      let names = NameMap.record loc id name names in
 *      parse_base_type loc names bt >>= fun (bt,names) ->
 *      return (components @ [name,bt], names)     
 *   | a -> parse_error loc "base type" a *)



let rec parse_index_term loc (names : NameMap.t) sx = 
  let open IndexTerms in
  match sx with
  | Sexp.Atom str when Str.string_match (Str.regexp "[0-9]+") str 0 ->
     return (Num (Nat_big_num.of_string str))
  | Sexp.Atom "true" -> 
     return (Bool true)
  | Sexp.Atom "false" -> 
     return (Bool false)

  | Sexp.List [o1;Sexp.Atom "+";o2] -> 
     parse_index_term loc names o1 >>= fun o1 ->
     parse_index_term loc names o2 >>= fun o2 ->
     return (Add (o1, o2))
  | Sexp.List [o1;Sexp.Atom "-";o2] -> 
     parse_index_term loc names o1 >>= fun o1 ->
     parse_index_term loc names o2 >>= fun o2 ->
     return (Sub (o1, o2))
  | Sexp.List [o1;Sexp.Atom "*";o2] -> 
     parse_index_term loc names o1 >>= fun o1 ->
     parse_index_term loc names o2 >>= fun o2 ->
     return (Mul (o1, o2))
  | Sexp.List [o1;Sexp.Atom "/";o2] -> 
     parse_index_term loc names o1 >>= fun o1 ->
     parse_index_term loc names o2 >>= fun o2 ->
     return (Div (o1, o2))
  | Sexp.List [o1;Sexp.Atom "^";o2] -> 
     parse_index_term loc names o1 >>= fun o1 ->
     parse_index_term loc names o2 >>= fun o2 -> 
     return (Exp (o1, o2))
  | Sexp.List [Sexp.Atom "rem_t";o1;o2] -> 
     parse_index_term loc names o1 >>= fun o1 ->
     parse_index_term loc names o2 >>= fun o2 ->
     return (Rem_t (o1, o2))
  | Sexp.List [Sexp.Atom "rem_f";o1;o2] -> 
     parse_index_term loc names o1 >>= fun o1 ->
     parse_index_term loc names o2 >>= fun o2 ->
     return (Rem_f (o1, o2))
  | Sexp.List [o1;Sexp.Atom "=";o2]  -> 
     parse_index_term loc names o1 >>= fun o1 ->
     parse_index_term loc names o2 >>= fun o2 ->
     return (EQ (o1, o2))
  | Sexp.List [o1;Sexp.Atom "<>";o2] -> 
     parse_index_term loc names o1 >>= fun o1 ->
     parse_index_term loc names o2 >>= fun o2 ->
     return (NE (o1, o2))
  | Sexp.List [o1;Sexp.Atom "<";o2] -> 
     parse_index_term loc names o1 >>= fun o1 ->
     parse_index_term loc names o2 >>= fun o2 ->
     return (LT (o1, o2))
  | Sexp.List [o1;Sexp.Atom ">";o2]  -> 
     parse_index_term loc names o1 >>= fun o1 ->
     parse_index_term loc names o2 >>= fun o2 ->
     return (GT (o1, o2))
  | Sexp.List [o1;Sexp.Atom "<=";o2] -> 
     parse_index_term loc names o1 >>= fun o1 ->
     parse_index_term loc names o2 >>= fun o2 ->
     return (LE (o1, o2))
  | Sexp.List [o1;Sexp.Atom ">=";o2] -> 
     parse_index_term loc names o1 >>= fun o1 ->
     parse_index_term loc names o2 >>= fun o2 ->
     return (GE (o1, o2))    
  | Sexp.List [Sexp.Atom "null"; o1] -> 
     parse_index_term loc names o1 >>= fun o1 ->
     return (Null o1)
  | Sexp.List [o1; Sexp.Atom "&"; o2] -> 
     parse_index_term loc names o1 >>= fun o1 ->
     parse_index_term loc names o2 >>= fun o2 ->
     return (And (o1, o2))
  | Sexp.List [o1; Sexp.Atom "|"; o2] -> 
     parse_index_term loc names o1 >>= fun o1 ->
     parse_index_term loc names o2 >>= fun o2 ->
     return (Or (o1, o2))
  | Sexp.List [Sexp.Atom "not"; o1] -> 
     parse_index_term loc names o1 >>= fun o1 ->
     return (Not o1)    
  (* | Sexp.List [Sexp.Atom "list"; List (it :: its)] -> 
   *    parse_index_term loc names it >>= fun it ->
   *    mapM (parse_index_term loc names) its >>= fun its ->
   *    return (List (it, its)) *)

  | Sexp.List [Sexp.Atom str; Atom ":"; bt] -> 
     NameMap.sym_of loc str names >>= fun sym ->
     parse_base_type loc names bt >>= fun (bt,names) ->
     return (S (sym, bt))

  | t -> 
     parse_error loc "index term" t



let parse_logical_sort loc (names : NameMap.t) sx =
  let open LogicalSorts in
  parse_base_type loc names sx >>= fun (bt,names) ->
  return (Base bt, names)


let parse_resource loc (names : NameMap.t) sx = 
  let open Resources in
  match sx with 
  (* | Sexp.List [Sexp.Atom "block";it1;it2] -> 
   *    parse_index_terms loc names it1 >>= fun it1 ->
   *    parse_index_terms loc names it2 >>= fun it2 ->
   *    return (Block (it1, it2)) *)
  (* | Sexp.List [Sexp.Atom "bool"; it1; it2] ->
   *    parse_index_terms loc names it1 >>= fun it1 ->
   *    parse_index_terms loc names it2 >>= fun it2 ->
   *    return (Bool (it1, it2))
   * | Sexp.List [Sexp.Atom "int"; it1; it2] ->
   *    parse_index_terms loc names it1 >>= fun it1 ->
   *    parse_index_terms loc names it2 >>= fun it2 ->
   *    return (Int (it1, it2))
   * | Sexp.List [Sexp.Atom "array"; it1; it2] ->
   *    parse_index_terms loc names it1 >>= fun it1 ->
   *    parse_index_terms loc names it2 >>= fun it2 ->
   *    return (Array (it1, it2)) *)
  | Sexp.List [Sexp.Atom "points"; Sexp.Atom s1; Sexp.Atom s2; it3] ->
     NameMap.sym_of loc s1 names >>= fun sym1 ->
     NameMap.sym_of loc s2 names >>= fun sym2 ->
     parse_index_term loc names it3 >>= fun it3 ->
     return (Points (sym1, sym2, it3))
  (* | Sexp.List (Sexp.Atom p :: its) ->
   *    mapM (parse_index_terms loc names) its >>= fun its ->
   *    return (Pred (p, its)) *)
  | t -> parse_error loc "resource type" t





let parse_logical_constraint loc env s = 
  let open LogicalConstraints in
  parse_index_term loc env s >>= fun it ->
  return (LC it)



let parse_vartype_binder loc (names : NameMap.t) s = 
  let open VarTypes in
  let open Binders in
  let open Sexplib in
  let open Sexp in
  match s with
  | List [Atom id; Atom ":"; t] ->
     let name = Sym.fresh_pretty id in
     let names = NameMap.record loc id name names in
     parse_base_type loc names t >>= fun (t,names) ->
     return ({name; bound = A t}, names)
  | List [Atom "Logical"; Atom id; Atom ":"; ls] ->
     let name = Sym.fresh_pretty id in
     let names = NameMap.record loc id name names in
     parse_logical_sort loc names ls >>= fun (t,names) ->
     return ({name; bound = L t}, names)
  | List [Atom "Resource"; Atom id; Atom ":"; re] ->
     let name = Sym.fresh_pretty id in
     let names = NameMap.record loc id name names in
     parse_resource loc names re >>= fun t ->
     return ({name; bound = R t}, names)
  | List [Atom "Constraint"; Atom id; Atom ":"; lc] ->
     let name = Sym.fresh_pretty id in
     let names = NameMap.record loc id name names in
     parse_logical_constraint loc names lc >>= fun t ->
     return ({name; bound = C t}, names)
  | t -> 
     parse_error loc "binders" t





let parse_type loc (names : NameMap.t) s = 
  let open Sexplib in
  let rec aux names acc ts = 
    match ts with
    | [] -> return (List.rev acc, names)
    | b :: bs ->
       parse_vartype_binder loc names b >>= fun (b, names) ->
       aux names (b :: acc) bs
  in
  match s with
  | Sexp.List ts -> aux names [] ts
  | t -> parse_error loc "binders" t
