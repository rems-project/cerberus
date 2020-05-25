open Tools
open Subst
open Sym
open Num
open Option
open List
open Pp
module Loc=Locations

module SymSet = Set.Make(Sym)


type t =
  | Num of Num.t
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

  | Tuple of t list
  | Nth of num * t (* of tuple *)

  | Struct of (Id.t * t) list
  | Field of t * Id.t

  | List of t list * BaseTypes.t
  | Head of t
  | Tail of t

  | S of Sym.t * LogicalSorts.t
  | StructDefField of string * BaseTypes.t

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

let rec pp atomic it : PPrint.document = 

  let mparens pped = if atomic then parens pped else pped in
  let pp = pp true in
  match it with
  | Num i -> Num.pp i
  | Bool true -> !^"true"
  | Bool false -> !^"false"

  | Add (it1,it2) -> mparens (pp it1 ^^^ plus ^^^ pp it2)
  | Sub (it1,it2) -> mparens (pp it1 ^^^ minus ^^^ pp it2)
  | Mul (it1,it2) -> mparens (pp it1 ^^^ star ^^^ pp it2)
  | Div (it1,it2) -> mparens (pp it1 ^^^ slash ^^^ pp it2)
  | Exp (it1,it2) -> mparens (pp it1 ^^^ caret ^^^ pp it2)
  | Rem_t (it1,it2) -> mparens (!^ "rem_t" ^^^ pp it1 ^^^ pp it2)
  | Rem_f (it1,it2) -> mparens (!^ "rem_f" ^^^ pp it1 ^^^ pp it2)

  | EQ (o1,o2) -> mparens (pp o1 ^^^ equals ^^^ pp o2)
  | NE (o1,o2) -> mparens (pp o1 ^^^ langle ^^ rangle ^^^ pp o2)
  | LT (o1,o2) -> mparens (pp o1 ^^^ langle ^^^ pp o2)
  | GT (o1,o2) -> mparens (pp o1 ^^^ rangle ^^^ pp o2)
  | LE (o1,o2) -> mparens (pp o1 ^^^ langle ^^ equals ^^^ pp o2)
  | GE (o1,o2) -> mparens (pp o1 ^^^ rangle ^^ equals ^^^ pp o2)

  | Null o1 -> mparens (!^"null" ^^^ pp o1)
  | And (o1,o2) -> mparens (pp o1 ^^^ ampersand ^^^ pp o2)
  | Or (o1,o2) -> mparens (pp o1 ^^^ bar ^^^ pp o2)
  | Not (o1) -> mparens (!^"not" ^^^ pp o1)

  | Nth (n,it2) -> mparens (!^"nth" ^^^ Num.pp n ^^^ pp it2)
  | Head (o1) -> mparens (!^"hd" ^^^ pp o1)
  | Tail (o1) -> mparens (!^"tl" ^^^ pp o1)

  | Tuple its -> mparens (!^"tuple" ^^^ separate_map space pp its)
  | List (its, bt) -> 
     mparens (brackets (separate_map comma pp its) ^^^ colon ^^ BaseTypes.pp false bt)
  | Struct fields -> 
     let pp_field (f,v) = dot ^^ Id.pp f ^^ equals ^^ pp v in
     braces (separate_map semi pp_field fields)
  | Field (t, s) ->
     pp t ^^ dot ^^ Id.pp s

  | S (sym,bt) -> mparens (typ (Sym.pp sym) (LogicalSorts.pp false bt))
  | StructDefField (id,bt) -> mparens (typ (!^id) (BaseTypes.pp false bt))


let rec vars_in it : SymSet.t = 
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
     SymSet.union (vars_in it) (vars_in it')
  | Nth (_, it)
  | Null it
  | Not it 
  | Head it
  | Tail it -> 
     vars_in it
  | Tuple its -> SymSet.union (vars_in it) (vars_in_list its)
  | Field (it,s) -> SymSet.union (vars_in it) (vars_in it)
  | Struct fields -> 
     List.fold_left (fun acc (f,v) -> SymSet.union acc (vars_in v))
       SymSet.empty fields
  | List (its,bt) ->
     SymSet.union (BaseTypes.vars_in bt) (vars_in_list its)
  | S (symbol,bt) -> SymSet.add symbol (LogicalSorts.vars_in bt)
  | StructDefField (_,bt) -> BaseTypes.vars_in bt

and vars_in_list l = 
  List.fold_left (fun acc sym -> SymSet.union acc (vars_in sym))
    SymSet.empty l


let rec subst_var subst it : t = 
  match it with
  | Num _ -> it
  | Bool _ -> it
  | Add (it, it') -> Add (subst_var subst it, subst_var subst it')
  | Sub (it, it') -> Sub (subst_var subst it, subst_var subst it')
  | Mul (it, it') -> Mul (subst_var subst it, subst_var subst it')
  | Div (it, it') -> Div (subst_var subst it, subst_var subst it')
  | Exp (it, it') -> Exp (subst_var subst it, subst_var subst it')
  | Rem_t (it, it') -> Rem_t (subst_var subst it, subst_var subst it')
  | Rem_f (it, it') -> Rem_f (subst_var subst it, subst_var subst it')
  | EQ (it, it') -> EQ (subst_var subst it, subst_var subst it')
  | NE (it, it') -> NE (subst_var subst it, subst_var subst it')
  | LT (it, it') -> LT (subst_var subst it, subst_var subst it')
  | GT (it, it') -> GT (subst_var subst it, subst_var subst it')
  | LE (it, it') -> LE (subst_var subst it, subst_var subst it')
  | GE (it, it') -> GE (subst_var subst it, subst_var subst it')
  | Null it -> Null (subst_var subst it)
  | And (it, it') -> And (subst_var subst it, subst_var subst it')
  | Or (it, it') -> Or (subst_var subst it, subst_var subst it')
  | Not it -> Not (subst_var subst it)
  | Tuple its ->
     Tuple (map (fun it -> subst_var subst it) its)
  | Nth (n, it') ->
     Nth (n, subst_var subst it')
  | List (its,bt) -> 
     List (map (fun it -> subst_var subst it) its,
           BaseTypes.subst_var subst bt)
  | Head it ->
     Head (subst_var subst it)
  | Tail it ->
     Tail (subst_var subst it)
  | Struct fields ->
     Struct (map (fun (f,v) -> (f, subst_var subst v)) fields)
  | Field (t,f) ->
     Field (subst_var subst t, f)
  | S (symbol,bt) -> S (Sym.subst subst symbol, 
                        LogicalSorts.subst_var subst bt)
  | StructDefField (id,bt) -> 
     StructDefField (id, BaseTypes.subst_var subst bt)

let subst_vars = make_substs subst_var


let rec concretise_field subst it : t = 
  match it with
  | Num _ -> it
  | Bool _ -> it
  | Add (it, it') -> Add (concretise_field subst it, 
                          concretise_field subst it')
  | Sub (it, it') -> Sub (concretise_field subst it, 
                          concretise_field subst it')
  | Mul (it, it') -> Mul (concretise_field subst it, 
                          concretise_field subst it')
  | Div (it, it') -> Div (concretise_field subst it, 
                          concretise_field subst it')
  | Exp (it, it') -> Exp (concretise_field subst it, 
                          concretise_field subst it')
  | Rem_t (it, it') -> Rem_t (concretise_field subst it, 
                              concretise_field subst it')
  | Rem_f (it, it') -> Rem_f (concretise_field subst it, 
                              concretise_field subst it')
  | EQ (it, it') -> EQ (concretise_field subst it, 
                        concretise_field subst it')
  | NE (it, it') -> NE (concretise_field subst it, 
                        concretise_field subst it')
  | LT (it, it') -> LT (concretise_field subst it, 
                        concretise_field subst it')
  | GT (it, it') -> GT (concretise_field subst it, 
                        concretise_field subst it')
  | LE (it, it') -> LE (concretise_field subst it, 
                        concretise_field subst it')
  | GE (it, it') -> GE (concretise_field subst it, 
                        concretise_field subst it')
  | Null it -> Null (concretise_field subst it)
  | And (it, it') -> And (concretise_field subst it, 
                          concretise_field subst it')
  | Or (it, it') -> Or (concretise_field subst it, 
                        concretise_field subst it')
  | Not it -> Not (concretise_field subst it)
  | Tuple its ->
     Tuple (map (fun it -> concretise_field subst it) its)
  | Nth (n, it') ->
     Nth (n, concretise_field subst it')
  | List (its,bt) -> 
     List (map (fun it -> concretise_field subst it) its, bt)
  | Head it ->
     Head (concretise_field subst it)
  | Tail it ->
     Tail (concretise_field subst it)
  | Struct fields ->
     Struct (map (fun (f,v) -> (f,concretise_field subst v)) fields)
  | Field (t,f) ->
     Field (concretise_field subst t, f)
  | S (s,bt) -> S (s, bt)
  | StructDefField (id,bt) -> 
     if id = subst.substitute then S (subst.swith, Base bt) 
     else StructDefField (id,bt)
     

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
     let* res = unify it1 it1' res in
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

  | Tuple its, Tuple its' ->
     unify_list (it::its) (it'::its') res
  | List (its,bt), List (its',bt') when BaseTypes.type_equal bt bt' ->
     unify_list its its' res

  | S (sym, bt), S (sym',bt') when BaseTypes.type_equal bt bt' ->
     Sym.unify sym sym' res 
  | StructDefField (id, bt), StructDefField (id',bt') 
       when id = id' && BaseTypes.type_equal bt bt' ->
     return res

  | _, _ ->
     fail

and unify_list its its' res =
  match its, its' with
  | [], [] -> return res
  | (it :: its), (it' :: its') ->
     let* res = unify it it' res in
     unify_list its its' res
  | _, _ ->
     fail

