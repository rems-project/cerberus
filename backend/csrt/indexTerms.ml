open Utils
open List
open PPrint
open Pp_tools
open Sexplib
open Except
module Loc=Location



type t =
  | Num of num
  | Bool of bool

  | Add of t * t
  | Sub of t * t
  | Mul of t * t
  | Div of t * t
  | Exp of t * t
  | Rem_t of t * t
  | Rem_f of t * t

  | EQ of t * t
  | NE of t * t
  | LT of t * t
  | GT of t * t
  | LE of t * t
  | GE of t * t

  | Null of t
  | And of t * t
  | Or of t * t
  | Not of t

  (* | List of t * t list *)

  | S of Sym.t

let (%+) t1 t2 = Add (t1,t2)
let (%-) t1 t2 = Sub (t1,t2)
let (%*) t1 t2 = Mul (t1,t2)
let (%/) t1 t2 = Div (t1,t2)
let (%^) t1 t2 = Exp (t1,t2)

let (%=) t1 t2 = EQ (t1, t2)
let (%!=) t1 t2 = NE (t1, t2)
let (%<) t1 t2 = LT (t1, t2)
let (%>) t1 t2 = GT (t1, t2)
let (%<=) t1 t2 = LE (t1, t2)
let (%>=) t1 t2 = GE (t1, t2)

let (%&) t1 t2 = And (t1, t2)
let (%|) t1 t2 = Or (t1, t2)

let rec pp = function
  | Num i -> !^ (Nat_big_num.to_string i)
  | Bool b -> !^ (if b then "true" else "false")

  | Add (it1,it2) -> parens (pp it1 ^^^ plus ^^^ pp it2)
  | Sub (it1,it2) -> parens (pp it1 ^^^ minus ^^^ pp it2)
  | Mul (it1,it2) -> parens (pp it1 ^^^ star ^^^ pp it2)
  | Div (it1,it2) -> parens (pp it1 ^^^ slash ^^^ pp it2)
  | Exp (it1,it2) -> parens (pp it1 ^^^ caret ^^^ pp it2)
  | Rem_t (it1,it2) -> parens (!^ "rem_t" ^^^ pp it1 ^^^ pp it2)
  | Rem_f (it1,it2) -> parens (!^ "rem_f" ^^^ pp it1 ^^^ pp it2)

  | EQ (o1,o2) -> parens (pp o1 ^^^ eq ^^^ pp o2)
  | NE (o1,o2) -> parens (pp o1 ^^^ ne ^^^ pp o2)
  | LT (o1,o2) -> parens (pp o1 ^^^ lt ^^^ pp o2)
  | GT (o1,o2) -> parens (pp o1 ^^^ gt ^^^ pp o2)
  | LE (o1,o2) -> parens (pp o1 ^^^ le ^^^ pp o2)
  | GE (o1,o2) -> parens (pp o1 ^^^ ge ^^^ pp o2)

  | Null o1 -> parens (!^ "null" ^^^ pp o1)
  | And (o1,o2) -> parens (pp o1 ^^^ ampersand ^^^ pp o2)
  | Or (o1,o2) -> parens (pp o1 ^^^ bar ^^^ pp o2)
  | Not (o1) -> parens (!^ "not" ^^^ pp o1)

  (* | List (it, its) -> parens (!^ "list" ^^^ separate_map space pp (it :: its)) *)

  | S sym -> Sym.pp sym



let rec parse_sexp loc (names : NameMap.t) sx = 
  match sx with

  | Sexp.Atom str when Str.string_match (Str.regexp "[0-9]+") str 0 ->
     return (Num (Nat_big_num.of_string str))
  | Sexp.Atom "true" -> 
     return (Bool true)
  | Sexp.Atom "false" -> 
     return (Bool false)

  | Sexp.List [o1;Sexp.Atom "+";o2] -> 
     parse_sexp loc names o1 >>= fun o1 ->
     parse_sexp loc names o2 >>= fun o2 ->
     return (Add (o1, o2))
  | Sexp.List [o1;Sexp.Atom "-";o2] -> 
     parse_sexp loc names o1 >>= fun o1 ->
     parse_sexp loc names o2 >>= fun o2 ->
     return (Sub (o1, o2))
  | Sexp.List [o1;Sexp.Atom "*";o2] -> 
     parse_sexp loc names o1 >>= fun o1 ->
     parse_sexp loc names o2 >>= fun o2 ->
     return (Mul (o1, o2))
  | Sexp.List [o1;Sexp.Atom "/";o2] -> 
     parse_sexp loc names o1 >>= fun o1 ->
     parse_sexp loc names o2 >>= fun o2 ->
     return (Div (o1, o2))
  | Sexp.List [o1;Sexp.Atom "^";o2] -> 
     parse_sexp loc names o1 >>= fun o1 ->
     parse_sexp loc names o2 >>= fun o2 -> 
     return (Exp (o1, o2))
  | Sexp.List [Sexp.Atom "rem_t";o1;o2] -> 
     parse_sexp loc names o1 >>= fun o1 ->
     parse_sexp loc names o2 >>= fun o2 ->
     return (Rem_t (o1, o2))
  | Sexp.List [Sexp.Atom "rem_f";o1;o2] -> 
     parse_sexp loc names o1 >>= fun o1 ->
     parse_sexp loc names o2 >>= fun o2 ->
     return (Rem_f (o1, o2))
  | Sexp.List [o1;Sexp.Atom "=";o2]  -> 
     parse_sexp loc names o1 >>= fun o1 ->
     parse_sexp loc names o2 >>= fun o2 ->
     return (EQ (o1, o2))
  | Sexp.List [o1;Sexp.Atom "<>";o2] -> 
     parse_sexp loc names o1 >>= fun o1 ->
     parse_sexp loc names o2 >>= fun o2 ->
     return (NE (o1, o2))
  | Sexp.List [o1;Sexp.Atom "<";o2] -> 
     parse_sexp loc names o1 >>= fun o1 ->
     parse_sexp loc names o2 >>= fun o2 ->
     return (LT (o1, o2))
  | Sexp.List [o1;Sexp.Atom ">";o2]  -> 
     parse_sexp loc names o1 >>= fun o1 ->
     parse_sexp loc names o2 >>= fun o2 ->
     return (GT (o1, o2))
  | Sexp.List [o1;Sexp.Atom "<=";o2] -> 
     parse_sexp loc names o1 >>= fun o1 ->
     parse_sexp loc names o2 >>= fun o2 ->
     return (LE (o1, o2))
  | Sexp.List [o1;Sexp.Atom ">=";o2] -> 
     parse_sexp loc names o1 >>= fun o1 ->
     parse_sexp loc names o2 >>= fun o2 ->
     return (GE (o1, o2))    
  | Sexp.List [Sexp.Atom "null"; o1] -> 
     parse_sexp loc names o1 >>= fun o1 ->
     return (Null o1)
  | Sexp.List [o1; Sexp.Atom "&"; o2] -> 
     parse_sexp loc names o1 >>= fun o1 ->
     parse_sexp loc names o2 >>= fun o2 ->
     return (And (o1, o2))
  | Sexp.List [o1; Sexp.Atom "|"; o2] -> 
     parse_sexp loc names o1 >>= fun o1 ->
     parse_sexp loc names o2 >>= fun o2 ->
     return (Or (o1, o2))
  | Sexp.List [Sexp.Atom "not"; o1] -> 
     parse_sexp loc names o1 >>= fun o1 ->
     return (Not o1)    
  (* | Sexp.List [Sexp.Atom "list"; List (it :: its)] -> 
   *    parse_sexp loc names it >>= fun it ->
   *    mapM (parse_sexp loc names) its >>= fun its ->
   *    return (List (it, its)) *)

  | Sexp.Atom str -> 
     NameMap.sym_of loc str names >>= fun sym ->
     return (S sym)

  | t -> 
     parse_error loc "index term" t


let rec subst (sym : Sym.t) (with_it : Sym.t) it : t = 
  match it with
  | Num _ -> it
  | Bool _ -> it
  | Add (it, it') -> Add (subst sym with_it it, subst sym with_it it')
  | Sub (it, it') -> Sub (subst sym with_it it, subst sym with_it it')
  | Mul (it, it') -> Mul (subst sym with_it it, subst sym with_it it')
  | Div (it, it') -> Div (subst sym with_it it, subst sym with_it it')
  | Exp (it, it') -> Exp (subst sym with_it it, subst sym with_it it')
  | Rem_t (it, it') -> Rem_t (subst sym with_it it, subst sym with_it it')
  | Rem_f (it, it') -> Rem_f (subst sym with_it it, subst sym with_it it')
  | EQ (it, it') -> EQ (subst sym with_it it, subst sym with_it it')
  | NE (it, it') -> NE (subst sym with_it it, subst sym with_it it')
  | LT (it, it') -> LT (subst sym with_it it, subst sym with_it it')
  | GT (it, it') -> GT (subst sym with_it it, subst sym with_it it')
  | LE (it, it') -> LE (subst sym with_it it, subst sym with_it it')
  | GE (it, it') -> GE (subst sym with_it it, subst sym with_it it')
  | Null it -> Null (subst sym with_it it)
  | And (it, it') -> And (subst sym with_it it, subst sym with_it it')
  | Or (it, it') -> Or (subst sym with_it it, subst sym with_it it')
  | Not it -> Not (subst sym with_it it)
  (* | List (it, its) -> 
   *    List (subst sym with_it it, map (fun it -> subst sym with_it it) its) *)
  | S symbol -> S (Sym.sym_subst sym with_it symbol)

let rec unify it it' (res : ('a, Sym.t) Uni.t SymMap.t) = 
  match it, it' with
  | Num n, Num n' when n = n' -> return res
  | Bool b, Bool b' when b = b' -> return res

  | Add (it1, it2), Add (it1', it2')
  | Sub (it1, it2), Sub (it1', it2')
  | Mul (it1, it2), Mul (it1', it2')
  | Div (it1, it2), Div (it1', it2')
  | Exp (it1, it2), Exp (it1', it2')
  | Rem_t (it1, it2), Rem_t (it1', it2')
  | Rem_f (it1, it2), Rem_f (it1', it2')

  | EQ (it1, it2), EQ (it1', it2')
  | NE (it1, it2), NE (it1', it2')
  | LT (it1, it2), LT (it1', it2')
  | GT (it1, it2), GT (it1', it2')
  | LE (it1, it2), LE (it1', it2')
  | GE (it1, it2), GE (it1', it2')

  | And (it1, it2), And (it1', it2')
  | Or (it1, it2), Or (it1', it2')
    ->
     unify it1 it1' res >>= fun res ->
     unify it2 it2' res

  | Null it, Null it'
  | Not it, Not it' 
    -> 
     unify it it' res

  (* | List (it,its), List (it',its') -> 
   *    unify_list (it::its) (it'::its') res *)

  | S sym, S sym' when sym = sym' ->
     return res

  | S sym, S it' ->
     begin match SymMap.find_opt sym res with
     | None -> noloc_fail ()
     | Some uni ->
        match uni.resolved with
        | Some it when it = it' -> return res 
        | Some it -> noloc_fail ()
        | None -> 
           let uni = { uni with resolved = Some it' } in
           return (SymMap.add sym uni res)
     end

  | _, _ ->
     noloc_fail ()

and unify_list its its' res =
  match its, its' with
  | [], [] -> return res
  | (it :: its), (it' :: its') ->
     unify it it' res >>= fun res ->
     unify_list its its' res
  | _, _ ->
     noloc_fail ()

