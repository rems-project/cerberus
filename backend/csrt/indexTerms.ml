open Utils
open Option
open List
open PPrint
open Pp_tools
module Loc=Locations


module SymSet = Set.Make(Sym)

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

  | Tuple of t * t list
  | Nth of num * t (* of tuple *)

  | List of t * t list
  | Head of t
  | Tail of t

  | S of Sym.t * BaseTypes.t

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
  | Num i -> pp_num i
  | Bool b -> !^ (if b then "true" else "false")

  | Add (it1,it2) -> parens (pp it1 ^^^ plus ^^^ pp it2)
  | Sub (it1,it2) -> parens (pp it1 ^^^ minus ^^^ pp it2)
  | Mul (it1,it2) -> parens (pp it1 ^^^ star ^^^ pp it2)
  | Div (it1,it2) -> parens (pp it1 ^^^ slash ^^^ pp it2)
  | Exp (it1,it2) -> parens (pp it1 ^^^ caret ^^^ pp it2)
  | Rem_t (it1,it2) -> parens (!^ "rem_t" ^^^ pp it1 ^^^ pp it2)
  | Rem_f (it1,it2) -> parens (!^ "rem_f" ^^^ pp it1 ^^^ pp it2)

  | EQ (o1,o2) -> parens (pp o1 ^^^ equals ^^^ pp o2)
  | NE (o1,o2) -> parens (pp o1 ^^^ langle ^^ rangle ^^^ pp o2)
  | LT (o1,o2) -> parens (pp o1 ^^^ langle ^^^ pp o2)
  | GT (o1,o2) -> parens (pp o1 ^^^ rangle ^^^ pp o2)
  | LE (o1,o2) -> parens (pp o1 ^^^ langle ^^ equals ^^^ pp o2)
  | GE (o1,o2) -> parens (pp o1 ^^^ rangle ^^ equals ^^^ pp o2)

  | Null o1 -> parens (!^ "null" ^^^ pp o1)
  | And (o1,o2) -> parens (pp o1 ^^^ ampersand ^^^ pp o2)
  | Or (o1,o2) -> parens (pp o1 ^^^ bar ^^^ pp o2)
  | Not (o1) -> parens (!^ "not" ^^^ pp o1)

  | Tuple (it,its) -> parens (!^ "tuple" ^^^ separate_map space pp (it :: its))
  | Nth (n,it2) -> parens (!^"nth" ^^^ pp_num n ^^^ pp it2)
  | List (it, its) -> parens (!^ "list" ^^^ separate_map space pp (it :: its))
  | Head (o1) -> parens (!^ "hd" ^^^ pp o1)
  | Tail (o1) -> parens (!^ "tl" ^^^ pp o1)

  | S (sym,bt) -> parens (typ (Sym.pp sym) (BaseTypes.pp bt))



let rec syms_in it : SymSet.t = 
  match it with
  | Num _  
  | Bool _ -> 
     SymSet.empty
  | Add (it, it')
  | Sub (it, it') 
  | Mul (it, it') 
  | Div (it, it') 
  | Exp (it, it') 
  | Rem_t (it, it') 
  | Rem_f (it, it')
  | EQ (it, it') 
  | NE (it, it') 
  | LT (it, it') 
  | GT (it, it') 
  | LE (it, it') 
  | GE (it, it') 
  | And (it, it')
  | Or (it, it')  ->
     SymSet.union (syms_in it) (syms_in it')
  | Nth (_, it)
  | Null it
  | Not it 
  | Head it
  | Tail it -> 
     syms_in it
  | Tuple (it, its)
  | List (it, its) ->
     SymSet.union (syms_in it) (syms_in_list its)
  | S (symbol,_) -> SymSet.singleton symbol

and syms_in_list l = 
  List.fold_left (fun acc sym -> SymSet.union acc (syms_in sym))
    SymSet.empty l


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
  | Tuple (it, its) ->
     Tuple (subst sym with_it it, map (fun it -> subst sym with_it it) its)
  | Nth (n, it') ->
     Nth (n, subst sym with_it it')
  | List (it, its) -> 
     List (subst sym with_it it, map (fun it -> subst sym with_it it) its)
  | Head it ->
     Head (subst sym with_it it)
  | Tail it ->
     Tail (subst sym with_it it)
  | S (symbol,bt) -> S (Sym.subst sym with_it symbol, bt)


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
  | Head it, Head it' 
  | Tail it, Tail it' 
    -> 
     unify it it' res

  | Nth (n, it2), Nth (n', it2') when n = n'
    -> 
     unify it it' res

  | Tuple (it,its), Tuple (it',its')
  | List (it,its), List (it',its') -> 
     unify_list (it::its) (it'::its') res

  | S (sym, bt), S (sym',bt') when BaseTypes.type_equal bt bt' ->
     Sym.unify sym sym' res 

  | _, _ ->
     fail

and unify_list its its' res =
  match its, its' with
  | [], [] -> return res
  | (it :: its), (it' :: its') ->
     unify it it' res >>= fun res ->
     unify_list its its' res
  | _, _ ->
     fail

