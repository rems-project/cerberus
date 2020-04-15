open List
open Cerb_frontend
(* open Cerb_backend *)
open Core 
open Mucore
open Except
open Nat_big_num
open Sexplib
open Printf
open Sym

module Loc = Location


type num = Nat_big_num.num

let uncurry f (a,b)  = f a b
let curry f a b = f (a,b)
let flip f a b = f b a

let concatmap (f : 'a -> 'b list) (xs : 'a list) : 'b list = 
    List.concat (List.map f xs)

let rec filter_map (f : 'a -> 'b option) (xs : 'a list) : 'b list = 
  match xs with
  | [] -> []
  | x :: xs ->
     match f x with
     | None -> filter_map f xs
     | Some y -> y :: filter_map f xs




module SymMap = struct
  include Map.Make(Sym)
  let foldM 
        (f : key -> 'x -> 'y -> ('y,'e) m)
        (map : 'x t) (init: 'y) : ('y,'e) m =
    fold (fun k v a -> a >>= f k v) map (return init)

end

module SymSet = Set.Make(Sym)






let parse_error (t : string) (sx : Sexp.t) (loc: Loc.t) = 
  fail (sprintf "%s: unexpected %s: %s" (Loc.pp loc) t (Sexp.to_string sx))






type ('spec, 'res) uni = {
    spec_name : Sym.t;
    spec : 'spec;
    resolved : 'res option
  }



module BaseTypes = struct

  type t =
    | Unit 
    | Bool
    | Int
    | Loc
    | Array
    | List of t
    | Tuple of t list
    | Struct of Sym.t

  let rec pp = function
    | Unit -> "unit"
    | Bool -> "bool"
    | Int -> "int"
    | Loc -> "loc"
    | Array -> "array"
    | List bt -> sprintf "(list %s)" (pp bt)
    | Tuple bts -> sprintf "(tuple (%s))" (String.concat " " (map pp bts))
    | Struct id -> sprintf "(struct %s)" (Sym.pp id)
  
  let rec parse_sexp loc (names : namemap) sx = 
    match sx with
    | Sexp.Atom "unit" -> 
       return Unit
    | Sexp.Atom "bool" -> 
       return Bool
    | Sexp.Atom "int" -> 
       return Int
    | Sexp.Atom "loc" -> 
       return Loc
    | Sexp.Atom "array" -> 
       return Array
    | Sexp.List [Sexp.Atom "list"; bt] -> 
       parse_sexp loc names bt >>= fun bt -> 
       return (List bt)
    | Sexp.List [Sexp.Atom "tuple"; Sexp.List bts] -> 
       mapM (parse_sexp loc names) bts >>= fun bts ->
       return (Tuple bts)
    | Sexp.List [Sexp.Atom "struct"; Sexp.Atom id] -> 
       Sym.parse loc names id >>= fun sym ->
       return (Struct sym)
    | a -> parse_error "base type" a loc

  let type_equal t1 t2 = t1 = t2

  let types_equal ts1 ts2 = 
    for_all (fun (t1,t2) -> type_equal t1 t2) (combine ts1 ts2)

  let subst _sym _with_it bt = bt

end



module LogicalSorts = struct

  type t = 
    | Base of BaseTypes.t

  let pp = function
    | Base bt -> BaseTypes.pp bt
  
  let parse_sexp loc (names : namemap) sx =
    match sx with
    | sx ->
       BaseTypes.parse_sexp loc names sx >>= fun bt ->
       return (Base bt)

  let type_equal t1 t2 = t1 = t2

  let types_equal ts1 ts2 = 
    for_all (fun (t1,t2) -> type_equal t1 t2) (combine ts1 ts2)

  let subst _sym _with_it ls = ls


end



module IndexTerms = struct

  type t =
    | Num of num
    | Bool of bool

    | Add of t * t
    | Sub of t * t
    | Mul of t * t
    | Div of t * t
    | Exp of t * t
    | App of t * t
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

    | List of t * t list

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
    | Num i -> Nat_big_num.to_string i
    | Bool b -> if b then "true" else "false"

    | Add (it1,it2) -> sprintf "(%s + %s)" (pp it1) (pp it2)
    | Sub (it1,it2) -> sprintf "(%s - %s)" (pp it1) (pp it2)
    | Mul (it1,it2) -> sprintf "(%s * %s)" (pp it1) (pp it2)
    | Div (it1,it2) -> sprintf "(%s / %s)" (pp it1) (pp it2)
    | Exp (it1,it2) -> sprintf "(%s ^ %s)" (pp it1) (pp it2)
    | App (it1,it2) -> sprintf "(app %s %s)" (pp it1) (pp it2)
    | Rem_t (it1,it2) -> sprintf "(rem_t %s %s)" (pp it1) (pp it2)
    | Rem_f (it1,it2) -> sprintf "(rem_f %s %s)" (pp it1) (pp it2)

    | EQ (o1,o2) -> sprintf "(%s = %s)"  (pp o1) (pp o2)
    | NE (o1,o2) -> sprintf "(%s <> %s)" (pp o1) (pp o2)
    | LT (o1,o2) -> sprintf "(%s < %s)"  (pp o1) (pp o2)
    | GT (o1,o2) -> sprintf "(%s > %s)"  (pp o1) (pp o2)
    | LE (o1,o2) -> sprintf "(%s <= %s)" (pp o1) (pp o2)
    | GE (o1,o2) -> sprintf "(%s >= %s)" (pp o1) (pp o2)

    | Null o1 -> sprintf "(null %s)" (pp o1) 
    | And (o1,o2) -> sprintf "(%s & %s)" (pp o1) (pp o2)
    | Or (o1,o2) -> sprintf "(%s | %s)" (pp o1) (pp o2)
    | Not (o1) -> sprintf "(not %s)" (pp o1)

    | List (it, its) -> sprintf "(list (%s))" 
                    (String.concat " " (map pp (it :: its)))

    | S sym -> Sym.pp sym



  let rec parse_sexp loc (names : namemap) sx = 
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
    | Sexp.List [Sexp.Atom "app"; o1;o2] -> 
       parse_sexp loc names o1 >>= fun o1 ->
       parse_sexp loc names o2 >>= fun o2 ->
       return (App (o1, o2))
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
    | Sexp.List [Sexp.Atom "list"; List (it :: its)] -> 
       parse_sexp loc names it >>= fun it ->
       mapM (parse_sexp loc names) its >>= fun its ->
       return (List (it, its))
    
    | Sexp.Atom str -> 
       Sym.parse loc names str >>= fun sym ->
       return (S sym)
    
    | t -> 
       parse_error "index term" t loc


  let rec subst (sym : Sym.t) (with_it : t) it : t = 
    match it with
    | Num _ -> it
    | Bool _ -> it
    | Add (it, it') -> Add (subst sym with_it it, subst sym with_it it')
    | Sub (it, it') -> Sub (subst sym with_it it, subst sym with_it it')
    | Mul (it, it') -> Mul (subst sym with_it it, subst sym with_it it')
    | Div (it, it') -> Div (subst sym with_it it, subst sym with_it it')
    | Exp (it, it') -> Exp (subst sym with_it it, subst sym with_it it')
    | App (it, it') -> App (subst sym with_it it, subst sym with_it it')
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
    | List (it, its) -> 
       List (subst sym with_it it, map (fun it -> subst sym with_it it) its)
    | S symbol when symbol = sym -> with_it
    | S symbol -> S symbol

  let rec unify it it' (res : ('a, t) uni SymMap.t) = 
    match it, it' with
    | Num n, Num n' when n = n' -> return res
    | Bool b, Bool b' when b = b' -> return res

    | Add (it1, it2), Add (it1', it2')
    | Sub (it1, it2), Sub (it1', it2')
    | Mul (it1, it2), Mul (it1', it2')
    | Div (it1, it2), Div (it1', it2')
    | Exp (it1, it2), Exp (it1', it2')
    | App (it1, it2), App (it1', it2')
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

    | List (it,its), List (it',its') -> 
       unify_list (it::its) (it'::its') res

    | S sym, S sym' when sym = sym' ->
       return res

    | S sym, it' ->
       begin match SymMap.find_opt sym res with
       | None -> fail ()
       | Some uni ->
          match uni.resolved with
          | Some it when it = it'-> return res 
          | Some it -> fail ()
          | None -> 
             let uni = { uni with resolved = Some it' } in
             return (SymMap.add sym uni res)
       end

    | _, _ ->
       fail ()

  and unify_list its its' res =
    match its, its' with
    | [], [] -> return res
    | (it :: its), (it' :: its') ->
       unify it it' res >>= fun res ->
       unify_list its its' res
    | _, _ ->
       fail ()

end





module Resources = struct

  type t = 
    | Block of IndexTerms.t * IndexTerms.t
    | Int of IndexTerms.t * IndexTerms.t (* location and value *)
    | Points of IndexTerms.t * IndexTerms.t
    | Array of IndexTerms.t * IndexTerms.t
    | Pred of string * IndexTerms.t list

  let pp = function
    | Block (it1,it2) -> 
       sprintf "(block %s %s)" 
         (IndexTerms.pp it1)
         (IndexTerms.pp it2)
    | Int (it1,it2) -> 
       sprintf "(int %s %s)" 
         (IndexTerms.pp it1) 
         (IndexTerms.pp it2)
    | Array (it1,it2) -> 
       sprintf "(array %s %s)" 
         (IndexTerms.pp it1)
         (IndexTerms.pp it2)
    | Points (it1,it2) -> 
       sprintf "(points %s %s)" 
         (IndexTerms.pp it1)
         (IndexTerms.pp it2)
    | Pred (p,its) ->
       sprintf "(%s %s)" 
         p
         (String.concat " " (map IndexTerms.pp its))

  
  let parse_sexp loc (names : namemap) sx = 
    match sx with 
    | Sexp.List [Sexp.Atom "block";it1;it2] -> 
       IndexTerms.parse_sexp loc names it1 >>= fun it1 ->
       IndexTerms.parse_sexp loc names it2 >>= fun it2 ->
       return (Block (it1, it2))
    | Sexp.List [Sexp.Atom "int"; it1; it2] ->
       IndexTerms.parse_sexp loc names it1 >>= fun it1 ->
       IndexTerms.parse_sexp loc names it2 >>= fun it2 ->
       return (Int (it1, it2))
    | Sexp.List [Sexp.Atom "array"; it1; it2] ->
       IndexTerms.parse_sexp loc names it1 >>= fun it1 ->
       IndexTerms.parse_sexp loc names it2 >>= fun it2 ->
       return (Array (it1, it2))
    | Sexp.List [Sexp.Atom "points"; it1; it2] ->
       IndexTerms.parse_sexp loc names it1 >>= fun it1 ->
       IndexTerms.parse_sexp loc names it2 >>= fun it2 ->
       return (Points (it1, it2))
    | Sexp.List (Sexp.Atom p :: its) ->
       mapM (IndexTerms.parse_sexp loc names) its >>= fun its ->
       return (Pred (p, its))
    | t -> parse_error "resource type" t loc

  let subst sym with_it t = 
    match t with
    | Block (it, it') -> 
       Block (IndexTerms.subst sym with_it it, IndexTerms.subst sym with_it it')
    | Int (it, it') -> 
       Int (IndexTerms.subst sym with_it it, IndexTerms.subst sym with_it it')
    | Points (it, it') -> 
       Points (IndexTerms.subst sym with_it it, IndexTerms.subst sym with_it it')
    | Array (it, it') -> 
       Array (IndexTerms.subst sym with_it it, IndexTerms.subst sym with_it it')
    | Pred (p, its) ->
       Pred (p, map (IndexTerms.subst sym with_it) its)

  let type_equal env t1 t2 = 
    t1 = t2                       (* todo: maybe up to variable
                                     instantiation, etc. *)

  let types_equal env ts1 ts2 = 
    for_all (fun (t1,t2) -> type_equal env t1 t2) (combine ts1 ts2)

  let unify r1 r2 res = 
    match r1, r2 with
    | Block (it1, it2), Block (it1', it2') ->
       IndexTerms.unify it1 it1' res >>= fun res ->
       IndexTerms.unify it2 it2' res
    | Int (it1, it2), Int (it1', it2') -> 
       IndexTerms.unify it1 it1' res >>= fun res ->
       IndexTerms.unify it2 it2' res
    | Points (it1, it2), Points (it1', it2') -> 
       IndexTerms.unify it1 it1' res >>= fun res ->
       IndexTerms.unify it2 it2' res
    | Array (it1, it2), Array (it1', it2') -> 
       IndexTerms.unify it1 it1' res >>= fun res ->
       IndexTerms.unify it2 it2' res
    | Pred (p, its), Pred (p', its') when p = p' ->
       IndexTerms.unify_list its its' res
    | _, _ -> fail ()

end

module LogicalConstraints = struct

  type t = LC of IndexTerms.t

  let pp (LC c) = IndexTerms.pp c

  let parse_sexp loc env s = 
    IndexTerms.parse_sexp loc env s >>= fun it ->
    return (LC it)

  let subst sym with_it (LC c) = 
    LC (IndexTerms.subst sym with_it c)

end 

open LogicalConstraints
(* open Resources *)
open IndexTerms
open BaseTypes



module VarTypes = struct

  type t = 
    | A of BaseTypes.t
    | L of LogicalSorts.t
    | R of Resources.t
    | C of LogicalConstraints.t

  let subst sym with_it t = 
    match t with
    | A t -> A (BaseTypes.subst sym with_it t)
    | L t -> L (LogicalSorts.subst sym with_it t)
    | R t -> R (Resources.subst sym with_it t)
    | C t -> C (LogicalConstraints.subst sym with_it t)

   type kind = 
     | Argument
     | Logical
     | Resource
     | Constraint
 
   let kind_of_t = function
     | A _  -> Argument
     | L _  -> Logical
     | R _  -> Resource
     | C _  -> Constraint
 
   let pp_kind = function
     | Argument  -> "computational"
     | Logical  -> "logical"
     | Resource  -> "resource"
     | Constraint  -> "constraint"
 
end


module Binders = struct

  type t = {name: Sym.t; bound: VarTypes.t}


  let pp {name;bound} = 
    match bound with
    | A t -> 
       sprintf "(%s : %s)" (Sym.pp name) (BaseTypes.pp t)
    | L t  -> 
       sprintf "(Logical %s : %s)" (Sym.pp name) (LogicalSorts.pp t)
    | R t -> 
       sprintf "(Resource %s : %s)" (Sym.pp name) (Resources.pp t)
    | C t -> 
       sprintf "(Constraint %s : %s)" (Sym.pp name) (LogicalConstraints.pp t)


  let parse_sexp loc (names : namemap) s = 
    match s with
    | Sexp.List [Sexp.Atom id; Sexp.Atom ":"; t] ->
       let name = Sym.fresh_pretty id in
       let names = StringMap.add id (name,loc) names in
       BaseTypes.parse_sexp loc names t >>= fun t ->
       return ({name; bound = A t}, names)
    | Sexp.List [Sexp.Atom "Logical"; Sexp.Atom id; Sexp.Atom ":"; ls] ->
       let name = Sym.fresh_pretty id in
       let names = StringMap.add id (name,loc) names in
       LogicalSorts.parse_sexp loc names ls >>= fun t ->
       return ({name; bound = L t}, names)
    | Sexp.List [Sexp.Atom "Resource"; Sexp.Atom id; Sexp.Atom ":"; re] ->
       let name = Sym.fresh_pretty id in
       let names = StringMap.add id (name,loc) names in
       Resources.parse_sexp loc names re >>= fun t ->
       return ({name; bound = R t}, names)
    | Sexp.List [Sexp.Atom "Constraint"; Sexp.Atom id; Sexp.Atom ":"; lc] ->
       let name = Sym.fresh_pretty id in
       let names = StringMap.add id (name,loc) names in
       LogicalConstraints.parse_sexp loc names lc >>= fun t ->
       return ({name; bound = C t}, names)
    | t -> 
       parse_error "binders" t loc

      let subst sym with_it b = 
        { b with bound = VarTypes.subst sym with_it b.bound }
        

end


module Types = struct

  type t = Binders.t list

  let pp ts = 
    String.concat " , " (map Binders.pp ts)

  let parse_sexp loc (names : namemap) s = 
    let rec aux (names : namemap) acc ts = 
      match ts with
      | [] -> return (rev acc, names)
      | b :: bs ->
         Binders.parse_sexp loc names b >>= fun (b, names) ->
         aux names (b :: acc) bs
    in
    match s with
    | Sexp.List ts -> aux names [] ts
    | t -> parse_error "binders" t loc

  let subst sym with_it bs = 
    map (Binders.subst sym with_it) bs

end


module FunctionTypes = struct

  type t = F of {arguments: Types.t;return: Types.t}

  let subst sym sym' (F t) = 
    F { arguments = Types.subst sym sym' t.arguments;
        return = Types.subst sym sym' t.return }

  let pp (F t) = 
    sprintf "%s -> %s" (Types.pp t.arguments) (Types.pp t.return)
end

open FunctionTypes
open VarTypes
open Binders

      

module Err = struct

  type call_return_switch_error = 
    | Surplus_A of Sym.t * BaseTypes.t
    | Surplus_L of Sym.t * LogicalSorts.t
    | Surplus_R of Sym.t * Resources.t
    | Missing_A of Sym.t * BaseTypes.t
    | Missing_L of Sym.t * LogicalSorts.t
    | Missing_R of Sym.t * Resources.t
    | Mismatch of { mname: Sym.t option; has: VarTypes.t; expected: VarTypes.t; }
    | Unsat_constraint of Sym.t * LogicalConstraints.t
    | Unconstrained_l of Sym.t * LogicalSorts.t

  type type_error = 
    | Var_kind_error of {
        loc : Loc.t;
        sym: Sym.t;
        expected : VarTypes.kind;
        has : VarTypes.kind;
      }
    | Name_bound_twice of {
        loc : Loc.t;
        name: Sym.t
      }
    | Unreachable of {
        loc: Loc.t;
        unreachable : string;
      }
    | Illtyped_it of {
        loc: Loc.t;
        it: IndexTerms.t;
      }
    | Unsupported of { 
        loc: Loc.t;
        unsupported: string; 
      }
    | Unbound_name of {
        loc: Loc.t; 
        is_function: bool;
        unbound: Sym.t;
      }
    | Inconsistent_fundef of {
        loc: Loc.t;
        decl: FunctionTypes.t;
        defn: FunctionTypes.t;
      }
    | Variadic_function of {
        loc: Loc.t;
        fn: Sym.t;
      }
    | Return_error of 
        Loc.t * call_return_switch_error
    | Call_error of 
        Loc.t * call_return_switch_error
    | Switch_error of 
        Loc.t * call_return_switch_error
    | Integer_value_error of 
        Loc.t
    | Undefined_behaviour of
        Loc.t * Undefined.undefined_behaviour
    | Generic_error of Loc.t * string

  let pp_return_error loc = function
    | Surplus_A (_name,t) ->
       sprintf "Line %s. Returning unexpected value of type %s" 
         (Loc.pp loc) (BaseTypes.pp t)
    | Surplus_L (_name,t) ->
       sprintf "%s. Returning unexpected logical value of type %s" 
         (Loc.pp loc) (LogicalSorts.pp t)
    | Surplus_R (_name,t) ->
       sprintf "%s. Returning unexpected resource of type %s" 
         (Loc.pp loc) (Resources.pp t)
    | Missing_A (_name,t) ->
       sprintf "%s. Missing return value of type %s" 
         (Loc.pp loc) (BaseTypes.pp t)
    | Missing_L (_name,t) ->
       sprintf "%s. MIssing logical return value of type %s" 
         (Loc.pp loc) (LogicalSorts.pp t)
    | Missing_R (_name,t) ->
       sprintf "%s. Missing return resource of type %s" 
         (Loc.pp loc) (Resources.pp t)
    | Mismatch {mname; has; expected} ->
       let has_pp = match has with
         | A t -> sprintf "return value of type %s" (BaseTypes.pp t)
         | L t -> sprintf "logical return value of type %s" (LogicalSorts.pp t)
         | R t -> sprintf "return resource of type %s" (Resources.pp t)
         | C t -> sprintf "return constraint %s" (LogicalConstraints.pp t)
       in
       begin match expected with
       | A t ->
          sprintf "%s. Expected return value of type %s but found %s" 
            (Loc.pp loc) (BaseTypes.pp t) has_pp
       | L t ->
          sprintf "%s. Expected logical return value of type %s but found %s" 
            (Loc.pp loc) (LogicalSorts.pp t) has_pp
       | R t ->
          sprintf "%s. Expected return resource of type %s but found %s" 
            (Loc.pp loc) (Resources.pp t) has_pp
       | C t ->
          (* dead, I think *)
          sprintf "%s. Expected return constraint %s but found %s" 
            (Loc.pp loc) (LogicalConstraints.pp t) has_pp
       end
    | Unsat_constraint (name,c) ->
       sprintf "%s. Unsatisfied return constraint %s: %s" 
         (Loc.pp loc) (Sym.pp name) (LogicalConstraints.pp c)
    | Unconstrained_l (name, ls) ->
       sprintf "%s. Unconstrained logical variable %s: %s" 
         (Loc.pp loc) (Sym.pp name) (LogicalSorts.pp ls)
    

  let pp_call_error loc = function
    | Surplus_A (_name,t) ->
       sprintf "Line %s. Supplying unexpected argument of type %s" 
         (Loc.pp loc) (BaseTypes.pp t)
    | Surplus_L (_name,t) ->
       sprintf "%s. Supplying unexpected logical argument of type %s" 
         (Loc.pp loc) (LogicalSorts.pp t)
    | Surplus_R (_name,t) ->
       sprintf "%s. Supplying unexpected resource of type %s" 
         (Loc.pp loc) (Resources.pp t)
    | Missing_A (_name,t) ->
       sprintf "%s. Missing argument of type %s" 
         (Loc.pp loc) (BaseTypes.pp t)
    | Missing_L (_name,t) ->
       sprintf "%s. Missing logical argument of type %s" 
         (Loc.pp loc) (LogicalSorts.pp t)
    | Missing_R (_name,t) ->
       sprintf "%s. Missing resource argument of type %s" 
         (Loc.pp loc) (Resources.pp t)
    | Mismatch {mname; has; expected} ->
       let has_pp = match has with
         | A t -> sprintf "argument of type %s" (BaseTypes.pp t)
         | L t -> sprintf "logical argument of type %s" (LogicalSorts.pp t)
         | R t -> sprintf "resource argument of type %s" (Resources.pp t)
         | C t -> sprintf "constraint argument %s" (LogicalConstraints.pp t)
       in
       begin match expected with
       | A t ->
          sprintf "%s. Expected argument of type %s but found %s" 
            (Loc.pp loc) (BaseTypes.pp t) has_pp
       | L t ->
          sprintf "%s. Expected logical argument of type %s but found %s" 
            (Loc.pp loc) (LogicalSorts.pp t) has_pp
       | R t ->
          sprintf "%s. Expected resource argument of type %s but found %s" 
            (Loc.pp loc) (Resources.pp t) has_pp
       | C t ->
          (* dead, I think *)
          sprintf "%s. Expected constraint argument %s but found %s" 
            (Loc.pp loc) (LogicalConstraints.pp t) has_pp
       end
    | Unsat_constraint (name,lc) ->
       sprintf "%s. Unsatisfied return constraint %s: %s" 
         (Loc.pp loc) (Sym.pp name) (LogicalConstraints.pp lc)
    | Unconstrained_l (name,ls) ->
       sprintf "%s. Unconstrained logical variable %s: %s" 
         (Loc.pp loc) (Sym.pp name) (LogicalSorts.pp ls)

  let pp = function 
    | Var_kind_error err ->
       sprintf "%s. Expected kind %s but found kind %s"
         (Loc.pp err.loc) (VarTypes.pp_kind err.expected) (VarTypes.pp_kind err.has)
    | Name_bound_twice err ->
       sprintf "%s. Name bound twice: %s" 
         (Loc.pp err.loc) (Sym.pp err.name)
    | Generic_error (loc, err) ->
       sprintf "%s. %s" 
         (Loc.pp loc) err
    | Unreachable {loc; unreachable} ->
       sprintf "%s. Should be unreachable: %s" 
         (Loc.pp loc) unreachable
    | Illtyped_it {loc; it} ->
       sprintf "%s. Illtyped index term: %s" 
         (Loc.pp loc) (IndexTerms.pp it)
    | Unsupported {loc; unsupported} ->
       sprintf "%s. Unsupported feature: %s" 
         (Loc.pp loc) unsupported
    | Unbound_name {loc; is_function; unbound} ->
       sprintf "%s. Unbound %s %s"
         (Loc.pp loc) (if is_function then "function" else "symbol") (Sym.pp unbound)
    | Inconsistent_fundef {loc; decl; defn} ->
       sprintf "%s. Function definition inconsistent. Should be %s, is %s"
         (Loc.pp loc) (FunctionTypes.pp decl) (FunctionTypes.pp defn)
    | Variadic_function {loc; fn } ->
       sprintf "Line %s. Variadic functions unsupported (%s)" 
         (Loc.pp loc) (Sym.pp fn)
    | Return_error (loc, err) -> 
       pp_return_error loc err
    | Call_error (loc, err) -> 
       pp_call_error loc err
    | Switch_error (loc, err) -> 
       pp_call_error loc err
    | Integer_value_error loc ->
       sprintf "%s. integer_value_to_num return None"
         (Loc.pp loc)
    | Undefined_behaviour (loc, undef) ->
       sprintf "%s. Undefined behaviour: %s"
         (Loc.pp loc)
         (Undefined.pretty_string_of_undefined_behaviour undef)



end

open Err



module GEnv = struct 

  type t = 
    { struct_decls : Types.t SymMap.t ; 
      fun_decls : (Loc.t * FunctionTypes.t * Sym.t) SymMap.t; (* third item is return name *)
      names : namemap
    } 
  type genv = t


  let empty = 
    { struct_decls = SymMap.empty; 
      fun_decls = SymMap.empty;
      names = StringMap.empty }

  let pp_list pp l = String.concat "\n" (map pp l)

  let pp_struct_decls decls = 
    let pp_entry (sym, bs) = sprintf "%s: %s" (Sym.pp sym) (Types.pp bs) in
    pp_list pp_entry (SymMap.bindings decls)

  let pp_fun_decls decls = 
    let pp_entry (sym, (_, t, _ret)) = sprintf "%s: %s" (Sym.pp sym) (FunctionTypes.pp t) in
    pp_list pp_entry (SymMap.bindings decls)

  let pp_name_map m = 
    let pp_entry (name,(sym,_)) = sprintf "%s: %s" name (Sym.pp sym) in
    pp_list pp_entry (StringMap.bindings m)

  let pp genv = 
    sprintf ("\nStructs\n-------\n%s\n\nFunctions\n---------\n%s\n\nNames\n-----\n%s\n")
      (pp_struct_decls genv.struct_decls)
      (pp_fun_decls genv.fun_decls)
      (pp_name_map genv.names)

end

module LEnv = struct
  type t = VarTypes.t SymMap.t
  type lenv = t
  let empty = SymMap.empty
end

module Env = struct


  type t = 
    { local : LEnv.t ; 
      global : GEnv.t }

  type env = t

  let empty = 
    { local = LEnv.empty; 
      global = GEnv.empty }

  let with_fresh_local genv = 
    { global = genv; 
      local = LEnv.empty }

  let add_var (env : t) (sym, t) = 
    { env with local = SymMap.add sym t env.local }

  let add_vars env bindings = 
    fold_left add_var env bindings

  let add_rt env bindings = 
    fold_left (fun env b -> add_var env (b.name, b.bound))
      env bindings

  let add_Avar env (sym, t) = add_var env (sym, VarTypes.A t)
  let add_Lvar env (sym, t) = add_var env (sym, VarTypes.L t)
  let add_Rvar env (sym, t) = add_var env (sym, VarTypes.R t)
  let add_Cvar env (sym, t) = add_var env (sym, VarTypes.C t)

  let add_Avars env vars = List.fold_left add_Avar env vars


  let remove_var env sym = 
    { env with local = SymMap.remove sym env.local }

  let lookup ?is_function:(is_function=false) (loc : Loc.t) (env: 'v SymMap.t) (name: Sym.t) =
    match SymMap.find_opt name env with
    | None -> fail (Unbound_name {loc; is_function; unbound = name})
    | Some v -> return v

  let get_var (loc : Loc.t) (env: t) (name: Sym.t) =
    lookup loc env.local name >>= function
    | VarTypes.A t -> return (`A t)
    | VarTypes.L t -> return (`L t)
    | VarTypes.R t -> return (`R (t, remove_var env name))
    | VarTypes.C t -> return (`C t)


  let kind = function
    | `A _ -> VarTypes.Argument
    | `L _ -> VarTypes.Logical
    | `R _ -> VarTypes.Resource
    | `C _ -> VarTypes.Constraint

  let get_Avar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | `A t -> return t
    | t -> fail (Var_kind_error {loc; sym; expected = VarTypes.Argument; has = kind t})

  let get_Lvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | `L t -> return t
    | t -> fail (Var_kind_error {loc; sym; expected = VarTypes.Logical; has = kind t})

  let get_Rvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | `R (t, env) -> return (t, env)
    | t -> fail (Var_kind_error {loc; sym; expected = VarTypes.Resource; has = kind t})

  let get_Cvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | `C t -> return t
    | t -> fail (Var_kind_error {loc; sym; expected = VarTypes.Constraint; has = kind t})

end

open Env



let rec infer_it loc env it = 
  match it with
  | Num _ -> return BaseTypes.Int
  | Bool _ -> return BaseTypes.Bool

  | Add (it,it')
  | Sub (it,it')
  | Mul (it,it')
  | Div (it,it')
  | Exp (it,it')
  | App (it,it')
  | Rem_t (it,it')
  | Rem_f (it,it') ->
     check_it loc env it BaseTypes.Int >>
     check_it loc env it' BaseTypes.Int >>
     return BaseTypes.Int

  | EQ (it,it')
  | NE (it,it')
  | LT (it,it')
  | GT (it,it')
  | LE (it,it')
  | GE (it,it') ->
     check_it loc env it BaseTypes.Int >>
     check_it loc env it' BaseTypes.Int >>
     return BaseTypes.Bool

  | Null it ->
     check_it loc env it BaseTypes.Loc >>
     return BaseTypes.Bool

  | And (it,it')
  | Or (it,it') ->
     check_it loc env it BaseTypes.Int >>
     check_it loc env it' BaseTypes.Int >>
     return BaseTypes.Bool

  | Not it ->
     check_it loc env it BaseTypes.Bool >>
     return BaseTypes.Bool

  | List (it, its) ->
     infer_it loc env it >>= fun bt ->
     check_it loc env it bt >>
     return (List bt)

  | S sym ->
     get_var loc env sym >>= function
     | `A t -> return t
     | `L (LogicalSorts.Base t) -> return t
     | `R _ -> fail (Illtyped_it {loc; it})
     | `C _ -> fail (Illtyped_it {loc; it})


and check_it loc env it bt =
  infer_it loc env it >>= fun bt' ->
  if bt = bt' then return ()
  else fail (Illtyped_it {loc; it})

and check_its loc env its bt = 
  match its with
  | [] -> return ()
  | it :: its -> 
     check_it loc env it bt >>
     check_its loc env its bt




let constraint_holds loc env (LC c) = 
  true                          (* todo: call z3 *)

let rec constraints_hold loc env = function
  | [] -> return ()
  | (n, t) :: constrs ->
     if constraint_holds loc env t 
     then constraints_hold loc env constrs
     else fail (Call_error (loc, (Unsat_constraint (n, t))))




let subtype loc env rt1 rt2 = 

  let open Binders in

  let rec check env rt1 rt2 =
    match rt1, rt2 with
    | [], [] -> 
       return env
    | {name; bound = A r1} :: _, [] -> 
       fail (Return_error (loc, Surplus_A (name, r1)))
    | {name; bound = L r1} :: _, [] -> 
       fail (Return_error (loc, Surplus_L (name, r1)))
    | {name; bound = R r1} :: _, [] -> 
       fail (Return_error (loc, Surplus_R (name, r1)))

    | [], {name; bound = A r2} :: _ -> 
       fail (Return_error (loc, Missing_A (name, r2)))
    | [], {name; bound = L r2} :: _ -> 
       fail (Return_error (loc, Missing_L (name, r2)))
    | [], {name; bound = R r2} :: _ -> 
       fail (Return_error (loc, Missing_R (name, r2)))
    | {name; bound = C c1} :: rt1', _ ->
       check (add_var env (name,C c1)) rt1' rt2
    | _, {name = n2; bound = C c2} :: rt2' ->
       if constraint_holds loc env c2 
       then check env rt1 rt2'
       else fail (Return_error (loc, Unsat_constraint (n2, c2)))
    | (r1 :: rt1), (r2 :: rt2) ->
       match r1, r2 with
       | {name = n1; bound = A t1}, {name = n2; bound = VarTypes.A t2} 
            when BaseTypes.type_equal t1 t2 ->
          check (add_var env (n1, A t1)) rt1 (Types.subst n2 (S n1) rt2)
       | {name = n1; bound = L t1}, {name = n2; bound = L t2} 
            when LogicalSorts.type_equal t1 t2 ->
          check (add_var env (n1, L t1)) rt1 (Types.subst n2 (S n1) rt2)
       | {name = n1; bound = R t1}, {name = n2; bound = R t2} 
            when Resources.type_equal env t1 t2 ->
          check env rt1 rt2
       | _, _ ->
          let msm = Mismatch {mname = Some r1.name; 
                              has = r1.bound; 
                              expected = r2.bound} in
          fail (Return_error (loc, msm))
  in

  check env rt1 rt2






let rec bt_of_core_base_type loc cbt : (BaseTypes.t, type_error) m = 

  let bt_of_core_object_type loc = function
    | OTy_integer -> 
       return BaseTypes.Int
    | OTy_floating -> 
       fail (Unsupported {loc; unsupported = "float"})
    | OTy_pointer -> 
       return BaseTypes.Loc
    | OTy_array cbt -> 
       return BaseTypes.Array
    | OTy_struct sym -> 
       return (Struct sym)
    | OTy_union _sym -> 
       failwith "todo: union types"
  in

  match cbt with
  | Core.BTy_unit -> 
     return BaseTypes.Unit
  | Core.BTy_boolean -> 
     return BaseTypes.Bool
  | Core.BTy_ctype -> 
     fail (Unsupported {loc; unsupported = "ctype"})
  | Core.BTy_list bt -> 
     bt_of_core_base_type loc bt >>= fun bt ->
     return (BaseTypes.List bt)
  | Core.BTy_tuple bts -> 
     mapM (bt_of_core_base_type loc) bts >>= fun bts ->
     return (BaseTypes.Tuple bts)
  | Core.BTy_object ot -> 
     bt_of_core_object_type loc ot
  | Core.BTy_loaded ot -> 
     bt_of_core_object_type loc ot
  | Core.BTy_storable -> 
     fail (Unsupported {loc; unsupported = "BTy_storable"})








let sym_or_fresh (msym : Sym.t option) : Sym.t = 
  match msym with
  | Some sym -> sym
  | None -> Sym.fresh ()



let ensure_type loc mname has expected : (unit, type_error) m = 
  if BaseTypes.type_equal has expected 
  then return ()
  else fail (Call_error (loc, Mismatch {mname; has; expected}))


let args_same_typ (mtyp : BaseTypes.t option) (args_bts : (BaseTypes.t * Loc.t) list) =
  fold_leftM (fun mt (bt,loc) ->
      match mt with
      | None -> return (Some bt)
      | Some t -> 
         ensure_type loc None (A bt) (A t) >>
         return (Some t)
    ) mtyp args_bts


let make_Aargs_bts env tsyms = 
  mapM (fun tsym ->
      let (sym, loc) = Sym.lof_asym tsym in
      get_Avar loc env sym >>= fun t ->
      return (t, loc)) tsyms



let infer_object_value (env : env) loc name ov = 

  let integer_value_to_num loc iv = 
    of_maybe (Integer_value_error loc) 
      (Impl_mem.eval_integer_value iv)
  in

  match ov with
  | M_OVinteger iv ->
     integer_value_to_num loc iv >>= fun i ->
     let t = {name; bound = A Int} in
     let constr = {name = fresh (); bound = C (LC (S name %= Num i))} in
     return [t; constr]
  | M_OVfloating iv ->
     fail (Unsupported {loc; unsupported = "floats"})
  | M_OVpointer p ->
     Impl_mem.case_ptrval p
       ( fun _cbt -> 
         let t = {name; bound = A Loc} in
         let constr = {name = fresh (); bound = C (LC (Null (S name)))} in
         return [t; constr] )
       ( fun sym -> 
         fail (Unsupported {loc; unsupported = "function pointers"}) )
       ( fun _prov loc ->
         let t = {name; bound = A Loc} in
         let constr = {name = fresh (); bound = C (LC (S name %= Num loc))} in
         return [t; constr] )
       ( fun _ ->
         fail (Unsupported {loc; unsupported = "unspecified pointer value"}) )
  | M_OVarray items ->
     make_Aargs_bts env items >>= fun args_bts ->
     args_same_typ None args_bts >>
     return [{name; bound = A Array}]
  | M_OVstruct (sym, fields) ->
     failwith "todo: struct"
  | M_OVunion _ -> 
     failwith "todo: union types"

let infer_loaded_value env loc name lv = 
  match lv with
 | M_LVspecified ov ->
    infer_object_value env loc name ov 
 | M_LVunspecified _ct ->
    failwith "todo: LV unspecified"


let infer_value loc name env v = 
  match v with
  | M_Vobject ov ->
     infer_object_value env loc name ov
  | M_Vloaded lv ->
     infer_loaded_value env loc name lv
  | M_Vunit ->
     let t = {name; bound = A Unit} in
     return [t]
  | M_Vtrue ->
     let t = {name; bound = A Bool} in
     let constr = {name = fresh (); bound = C (LC (S name))} in
     return [t; constr]
  | M_Vfalse -> 
     let t = {name; bound = A Bool} in
     let constr = {name = fresh (); bound = C (LC (Not (S name)))} in
     return [t; constr]
  | M_Vlist (cbt, asyms) ->
     bt_of_core_base_type loc cbt >>= fun bt ->
     begin match bt with
     | List i_t ->
        make_Aargs_bts env asyms >>= fun args_bts ->
        args_same_typ (Some i_t) args_bts >>
        (* maybe record list length? *)
        let t = {name; bound = A (List i_t)} in
        return [t]
     | bt ->
        fail (Generic_error (loc, "Cnil without list type"))
     end 
  | M_Vtuple args ->
     make_Aargs_bts env args >>= fun args_bts ->
     let t = {name; bound = A (Tuple (List.map fst args_bts))} in
     return [t]


let call_typ loc_call env decl_typ args =    

  let logical_variables_resolved env unis = 
    SymMap.foldM
      (fun usym {spec_name; spec; resolved} substs ->
        match resolved with
        | None -> 
           fail (Call_error (loc_call, Unconstrained_l (spec_name,spec)))
        | Some it -> 
           let (Base bt) = spec in
           check_it loc_call env it bt >>
           return ((usym, it) :: substs)
      ) unis []
  in

  let rec check_and_refine env asyms (F ftyp) unis constrs = 
    match ftyp.arguments with
    | [] -> 
       begin match asyms with
       | [] -> 
          logical_variables_resolved env unis >>= fun substs ->
          let ret = 
            fold_left (fun ret (s, subst) -> Types.subst s subst ret)
              ftyp.return substs 
          in
          let constrs = 
            fold_left (fun constrs (s, subst) -> 
                map (fun (n,lc) -> (n, LogicalConstraints.subst s subst lc)) constrs)
              constrs substs
          in
          constraints_hold loc_call env constrs >>
          return (ret,env)
          
       | asym :: asyms' -> 
          let (sym,loc) = Sym.lof_asym asym in
          get_var loc env sym >>= function
          | `A t' -> fail (Call_error (loc, Surplus_A (sym, t')))
          | `L t' -> fail (Call_error (loc, Surplus_L (sym, t')))
          | `R (t',_) -> fail (Call_error (loc, Surplus_R (sym, t')))
          | `C t' -> check_and_refine (add_Cvar env (sym, t')) 
                        asyms' (F ftyp) unis constrs
       end

    | {name = n; bound =  A t} :: args' ->
       begin match asyms with
       | asym :: asyms' ->
          let (sym,loc) = Sym.lof_asym asym in
          get_Avar loc env sym >>= fun t' ->
          let ftyp = FunctionTypes.subst n (S sym) 
                       (F {ftyp with arguments = args'}) in
          if BaseTypes.type_equal t' t
          then check_and_refine env asyms' ftyp unis constrs
          else 
            let msm = Mismatch {mname = Some sym; has = A t'; expected = A t} in
            fail (Call_error (loc, msm))
       | [] ->
          fail (Call_error (loc_call, Missing_A (n, t)))
       end

    | {name = n; bound = R t} :: args' -> 

       begin match asyms with
       | asym :: _ -> 
          let (sym,loc) = Sym.lof_asym asym in 
          get_Rvar loc env sym >>= fun (t',env) ->
          tryM (Resources.unify t t' unis)
            (let err = Mismatch {mname = Some sym; has = R t'; expected = R t} in
             fail (Call_error (loc, err))) >>= fun res ->
          check_and_refine env asyms (F {ftyp with arguments = args'}) unis constrs
       | [] -> 
          fail (Call_error (loc_call, (Missing_R (n, t))))
       end

    | {name = n; bound = L t} :: args' -> 
       let sym = Sym.fresh () in
       let uni = { spec_name = n; spec = t; resolved = None } in
       let unis' = SymMap.add sym uni unis in
       let ftyp' = FunctionTypes.subst n (S sym) (F {ftyp with arguments = args'}) in
       check_and_refine env asyms ftyp' unis' constrs

    | {name = n; bound = C t} :: args' ->        
       let constrs' = (constrs @ [(n, t)]) in
       check_and_refine env asyms (F {ftyp with arguments = args'}) unis constrs'

  in
  check_and_refine env args decl_typ SymMap.empty []


let call_typ_fn loc_call name env args =
  match name with
  | Core.Impl _ -> 
     failwith "todo implementation-defined constrant"
  | Core.Sym sym ->
     lookup ~is_function:true loc_call env.global.fun_decls sym >>= fun decl ->
     let (_loc,decl_typ,_ret_name) = decl in 
     call_typ loc_call env decl_typ args


let ctor_typ loc ctor (args_bts : ((BaseTypes.t * Loc.t) list)) = 
  match ctor with
  | Cnil cbt ->
     bt_of_core_base_type loc cbt >>= fun bt ->
     begin match bt, args_bts with
     | List _, [] ->
        return bt
     | _, [] ->
        fail (Generic_error (loc, "Cnil without list type"))
     | _, args -> 
        let err = sprintf "Cons applied to %d argument(s)" (List.length args) in
        fail (Generic_error (loc, err))
     end
  | Ccons ->
     begin match args_bts with
     | [(hd_bt,hd_loc); (tl_bt,tl_loc)] ->
        ensure_type tl_loc None (A tl_bt) (A (List hd_bt)) >>
        let t = List tl_bt in
        return t
     | args ->
        let err = sprintf "Cons applied to %d argument(s)" 
                    (List.length args) in
        fail (Generic_error (loc, err))
     end
  | Ctuple ->
     return (BaseTypes.Tuple (List.map fst args_bts))
  | Carray -> 
     args_same_typ None args_bts >>
     return BaseTypes.Array
  | Civmax
  | Civmin
  | Civsizeof
  | Civalignof
  | CivCOMPL
  | CivAND
  | CivOR
  | CivXOR -> failwith "todo"
  | Cspecified ->
    begin match args_bts with
    | [(bt,_)] ->
       return bt
    | args ->
       let err = sprintf "Cspecified applied to %d argument(s)" 
                   (List.length args) in
       fail (Generic_error (loc, err))
    end
  | Cunspecified ->
     failwith "todo: LV unspecified"
  | Cfvfromint -> 
     fail (Unsupported {loc; unsupported = "floats"})
  | Civfromfloat -> 
     fail (Unsupported {loc; unsupported = "floats"})


let infer_pat pat = 

  let rec check_disjointness names acc bindings =
    match bindings with
    | [] -> 
       return (List.rev acc)
    | ((name, bt), loc) :: bindings when SymSet.mem name names ->
       let acc = ((name, bt), loc) :: acc in
       let names = SymSet.add name names in
       check_disjointness names acc bindings
    | ((name, _), loc) :: _ ->
       fail (Name_bound_twice {name; loc})
  in

  let rec aux pat = 
    let (Core.Pattern (annots, pat_)) = pat in
    let loc = Annot.get_loc_ annots in
    match pat_ with
    | CaseBase (None, cbt) ->
       bt_of_core_base_type loc cbt >>= fun bt ->
       return ([((Sym.fresh (), bt), loc)], (bt, loc))
    | CaseBase (Some sym, cbt) ->
       bt_of_core_base_type loc cbt >>= fun bt ->
       return ([((sym, bt), loc)], (bt, loc))
    | CaseCtor (ctor, args) ->
       mapM aux args >>= fun bindingses_args_bts ->
       let bindingses, args_bts = List.split bindingses_args_bts in
       check_disjointness SymSet.empty [] 
         (List.concat bindingses) >>= fun bindings ->
       ctor_typ loc ctor args_bts >>= fun bt ->
       return (bindings, (bt, loc))
  in

  aux pat >>= fun (bindings, (bt, loc)) ->
  let (bindings,_) = List.split bindings in
  return (bindings, bt, loc)

     

let infer_binop name env loc op sym1 sym2 = 

  let make_binop_constr (v1 : IndexTerms.t) (v2 : IndexTerms.t) =
    match op with
    | OpAdd -> Add (v1, v2)
    | OpSub -> Sub (v1, v2)
    | OpMul -> Mul (v1, v2)
    | OpDiv -> Div (v1, v2) 
    | OpRem_t -> Rem_t (v1, v2)
    | OpRem_f -> Rem_f (v1, v2)
    | OpExp -> Exp (v1, v2)
    | OpEq -> EQ (v1, v2)
    | OpGt -> GT (v1, v2)
    | OpLt -> LT (v1, v2)
    | OpGe -> GE (v1, v2)
    | OpLe -> LE (v1, v2)
    | OpAnd -> And (v1, v2)
    | OpOr -> Or (v1, v2)
  in

  let bt_of_binop : ((BaseTypes.t * BaseTypes.t) * BaseTypes.t) = 
    match op with
    | OpAdd -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Int)
    | OpSub -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Int)
    | OpMul -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Int)
    | OpDiv -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Int)
    | OpRem_t -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Int)
    | OpRem_f -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Int)
    | OpExp -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Int)
    | OpEq -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Bool)
    | OpGt -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Bool)
    | OpLt -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Bool)
    | OpGe -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Bool)
    | OpLe -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Bool)
    | OpAnd -> ((BaseTypes.Bool, BaseTypes.Bool), BaseTypes.Bool)
    | OpOr -> ((BaseTypes.Bool, BaseTypes.Bool), BaseTypes.Bool)
  in

  let (sym1, loc1) = Sym.lof_asym sym1 in
  let (sym2, loc2) = Sym.lof_asym sym2 in
  get_Avar loc env sym1 >>= fun t1 ->
  get_Avar loc env sym2 >>= fun t2 ->
  let ((st1,st2),rt) = bt_of_binop in
  ensure_type loc1 (Some sym1) (A t1) (A st1) >>
  ensure_type loc2 (Some sym2) (A t2) (A st2) >>
  let constr = LC (S name %= (make_binop_constr (S sym1) (S sym2))) in
  let env = add_Cvar env (fresh (), constr) in
  let t = {name; bound = A rt} in
  return ([t], env)


let rec infer_pexpr name env (pe : 'bty mu_pexpr) = 
  let (M_Pexpr (annots, _bty, pe_)) = pe in
  let loc = Annot.get_loc_ annots in
  match pe_ with
  | M_PEsym sym ->
     get_Avar loc env sym >>= fun b ->
     let t = {name; bound = A b} in
     return ([t], env)
  | M_PEimpl _ ->
     failwith "todo PEimpl"
  | M_PEval v ->
     infer_value loc name env v >>= fun t ->
     return (t, env)
  | M_PEconstrained _ ->
     failwith "todo PEconstrained"
  | M_PEundef _ ->
     failwith "PEundef in inferring position"
  | M_PEerror _ ->
     failwith "todo PEerror"
  | M_PEctor (ctor, args) ->
     make_Aargs_bts env args >>= fun args_bts ->
     ctor_typ loc ctor args_bts >>= fun t ->
     let t = [{name; bound = A t}] in
     return (t, env)
  | M_PEcase (asym, pats_es) ->
     failwith "PEcase in inferring position"
  | M_PEarray_shift _ ->
     failwith "todo PEarray_shift"
  | M_PEmember_shift _ ->
     failwith "todo PEmember_shift"
  | M_PEnot sym ->
     let (sym,a_loc) = Sym.lof_asym sym in
     get_Avar loc env sym >>= fun t ->
     ensure_type a_loc (Some sym) (A t) (A BaseTypes.Bool) >>
     let constr = LC ((S name) %= Not (S sym)) in
     let env = add_Cvar env (name, constr) in
     let t = {name; bound = A t} in
     return ([t], env)
  | M_PEop (op,sym1,sym2) ->
     infer_binop name env loc op sym1 sym2
  | M_PEstruct _ ->
     failwith "todo PEstruct"
  | M_PEunion _ ->
     failwith "todo PEunion"
  | M_PEmemberof _ ->
     failwith "todo M_PEmemberof"
  | M_PEcall (mu_name, asyms) ->
     (* include the resource arguments into asyms *)
     (* let env = call_resources annots env in *)
     call_typ_fn loc mu_name env asyms
  | M_PElet (p, e1, e2) ->
     begin match p with 
     | M_symbol (Annotated (_annots, _, name2)) ->
        infer_pexpr name2 env e1 >>= fun (rt, env) ->
        infer_pexpr name (add_rt env rt ) e2
     | M_normal_pattern (Pattern (_annot, CaseBase (mname2,_cbt))) ->
        let name2 = sym_or_fresh mname2 in
        infer_pexpr name2 env e1 >>= fun (rt, env) ->
        infer_pexpr name (add_rt env rt) e2
     | M_normal_pattern (Pattern (_annot, CaseCtor _)) ->
        failwith "todo ctor pattern"
     end
  | M_PEif (sym1,sym2,sym3) ->
     let sym1, loc1 = Sym.lof_asym sym1 in
     let sym2, loc2 = Sym.lof_asym sym2 in
     let sym3, loc3 = Sym.lof_asym sym3 in
     get_Avar loc env sym1 >>= fun t1 ->
     get_Avar loc env sym2 >>= fun t2 ->
     get_Avar loc env sym3 >>= fun t3 ->
     ensure_type loc1 (Some sym1) (A t1) (A Bool) >>
     ensure_type loc3 (Some sym3) (A t3) (A t2) >>
     let constr = 
       {name = Sym.fresh ();
        bound = C (LC ( (S sym1 %& (S name %= S sym2)) %| 
                        ((Not (S sym1)) %& (S name %= S sym3)) ) )}
     in
     let t = {name; bound = A t2} in
     return ([t; constr], env)
  | M_PEensure_specified (asym1, _ct) ->
     let sym1, loc1 = Sym.lof_asym asym1 in
     get_Avar loc env sym1 >>= fun t1 ->
     return ([{name = sym1; bound = A t1}], env)


and check_pexpr env (e : 'bty mu_pexpr) ret = 
  let (M_Pexpr (annots, _, e_)) = e in
  let loc = Annot.get_loc_ annots in
  match e_ with
  | M_PEcase (asym, pats_es) ->
     let (esym,eloc) = Sym.lof_asym asym in
     get_Avar eloc env esym >>= fun bt ->
     mapM (fun (pat,pe) ->
         (* check pattern type against bt *)
         infer_pat pat >>= fun (bindings, bt', ploc) ->
         ensure_type ploc None (A bt') (A bt) >>
         (* check body type against spec *)
         let env' = add_Avars env bindings in
         check_pexpr env' pe ret
       ) pats_es >>
     return env
  | M_PEundef (loc, undef) ->
     if constraint_holds loc env (LC (Bool false)) 
     then return env
     else fail (Undefined_behaviour (loc, undef))
  | _ ->
     let name = Sym.fresh () in    (* fix *)
     infer_pexpr name env e >>= fun (t, env) ->
     subtype loc env t ret >>= fun env ->
     return env



let rec infer_expr name env (e : ('a,'bty) mu_expr) = 
  let (M_Expr (annots, e_)) = e in
  (* let loc = Annot.get_loc_ annots in *)
  match e_ with
  | M_Epure pe -> 
     infer_pexpr name env pe
  | M_Ememop _ ->
     failwith "todo ememop"
  | M_Eaction (M_Paction (_pol, M_Action (aloc,_,action_))) ->
     begin match action_ with
     | M_Create (sym1,ct,_prefix) -> 
        failwith "Create"
     | M_CreateReadOnly (sym1, ct, sym2, _prefix) -> 
        failwith "CreateReadOnly"
     | M_Alloc (ct, sym, _prefix) -> 
        failwith "Alloc"
     | M_Kill (_is_dynamic, sym) -> 
        failwith "Kill"
     | M_Store (_is_locking,ct, sym1, sym2, mo) -> 
        failwith "Store"
     | M_Load (ct, sym, mo) -> 
        failwith "Load"
     | M_RMW (ct, sym1, sym2, sym3, mo1, mo2) -> 
        failwith "RMW"
     | M_Fence mo -> 
        failwith "Fence"
     | M_CompareExchangeStrong (ct, sym1, sym2, sym3, mo1, mo2) -> 
        failwith "CompareExchangeStrong"
     | M_CompareExchangeWeak (ct, sym1, sym2, sym3, mo1, mo2) -> 
        failwith "CompareExchangeWeak"
     | M_LinuxFence mo -> 
        failwith "LinuxFemce"
     | M_LinuxLoad (ct, sym1, mo) -> 
        failwith "LinuxLoad"
     | M_LinuxStore (ct, sym1, sym2, mo) -> 
        failwith "LinuxStore"
     | M_LinuxRMW (ct, sym1, sym2, mo) -> 
failwith "LinuxRMW"
     end
  | M_Ecase _ ->
     failwith "todo ecase"
  | M_Elet (p, e1, e2) ->
     begin match p with 
     | M_symbol (Annotated (_annots, _, name2)) ->
        infer_pexpr name2 env e1 >>= fun (rt, env) ->
        infer_expr name (add_rt env rt) e2
     | M_normal_pattern (Pattern (_annot, CaseBase (mname2,_cbt))) ->
        let name2 = sym_or_fresh mname2 in
        infer_pexpr name2 env e1 >>= fun (rt, env) ->
        infer_expr name (add_rt env rt) e2
     | M_normal_pattern (Pattern (_annot, CaseCtor _)) ->
        failwith "todo ctor pattern"
     end
  | M_Eif _ ->
     failwith "todo eif"
  | M_Eskip -> 
     return ([], env)
  | M_Eccall (_a, asym, asd, asyms) ->
     failwith "todo eccall"
  | M_Eproc _ ->
     failwith "todo eproc"
  | M_Ewseq (p, e1, e2) ->      (* for now, the same as Esseq *)
     begin match p with 
     | Pattern (_annot, CaseBase (mname2,_cbt)) ->
        let name2 = sym_or_fresh mname2 in
        infer_expr name2 env e1 >>= fun (rt, env) ->
        infer_expr name (add_rt env rt) e2
     | Pattern (_annot, CaseCtor _) ->
        failwith "todo ctor pattern"
     end
  | M_Esseq (p, e1, e2) ->
     begin match p with 
     | Pattern (_annot, CaseBase (mname2,_cbt)) ->
        let name2 = sym_or_fresh mname2 in
        infer_expr name2 env e1 >>= fun (rt, env) ->
        infer_expr name (add_rt env rt) e2
     | Pattern (_annot, CaseCtor _) ->
        failwith "todo ctor pattern"
     end
  | M_Ebound (n, e) ->
     infer_expr name env e
  | M_End _ ->
     failwith "todo end"
  | M_Esave _ ->
     failwith "todo esave"
  | M_Erun _ ->
     failwith "todo erun"

and check_expr env (e : ('a,'bty) mu_expr) ret = 
  let (M_Expr (annots, e_)) = e in
  let loc = Annot.get_loc_ annots in
  match e_ with
  | M_Eif (asym1, e2, e3) ->
     let sym1, loc1 = Sym.lof_asym asym1 in
     get_Avar loc env sym1 >>= fun t1 -> 
     ensure_type loc1 (Some sym1) (A t1) (A Bool) >>
     let then_constr = (Sym.fresh (), LC (S sym1 %= Bool true)) in
     let else_constr = (Sym.fresh (), LC (S sym1 %= Bool true)) in
     check_expr (add_Cvar env then_constr) e2 ret >>
     check_expr (add_Cvar env else_constr) e3 ret
  | M_Ecase (asym, pats_es) ->
     let (esym,eloc) = Sym.lof_asym asym in
     get_Avar eloc env esym >>= fun bt ->
     mapM (fun (pat,pe) ->
         (* check pattern type against bt *)
         infer_pat pat >>= fun (bindings, bt', ploc) ->
         ensure_type ploc None (A bt') (A bt) >>
         (* check body type against spec *)
         let env' = add_Avars env bindings in
         check_expr env' pe ret
       ) pats_es >>
     return env     
  | M_Epure pe -> 
     check_pexpr env pe ret
  | _ ->
     let name = Sym.fresh () in    (* fix *)
     infer_expr name env e >>= fun (t, env) ->
     subtype loc env t ret >>= fun env ->
     return env





let check_function_body (type a bty) genv name (body : (a,bty) mu_expr) (F decl_typ) = 
  let env = with_fresh_local genv in
  let env = add_rt env decl_typ.arguments in
  check_expr (* name *) env body decl_typ.return >>= fun _env ->
  return ()



let embed_fun_proc body = 
  let (M_Pexpr (annots, _, _)) = body in
  M_Expr (annots, M_Epure (body))



let check_function (type bty a) genv fsym (fn : (bty,a) mu_fun_map_decl) = 

  let forget = 
    filter_map (function {name; bound = A t} -> Some (name,t) | _ -> None) in


  let binding_of_core_base_type loc (sym,cbt) = 
    bt_of_core_base_type loc cbt >>= fun bt ->
    return {name = sym; bound = A bt}
  in

  let check_consistent loc decl args ret = 
    mapM (binding_of_core_base_type loc) args >>= fun args ->
    binding_of_core_base_type loc ret >>= fun ret ->
    let (F decl_typ) = decl in
    if BaseTypes.types_equal (forget decl_typ.arguments) (forget args) &&
         BaseTypes.types_equal (forget decl_typ.return) (forget [ret])
    then return ()
    else 
      let defn = F {arguments = args; return = [ret]} in
      fail (Inconsistent_fundef {loc; decl; defn = defn})
  in

  match fn with
  | M_Fun (ret, args, body) ->
     let loc = Loc.unknown in
     lookup ~is_function:true loc genv.GEnv.fun_decls fsym >>= fun decl ->
     let (loc,decl_typ,ret_name) = decl in
     check_consistent loc decl_typ args (ret_name,ret) >>
     check_function_body genv fsym (embed_fun_proc body) decl_typ
  | M_Proc (loc, ret, args, body) ->
     lookup ~is_function:true loc genv.fun_decls fsym >>= fun decl ->
     let (loc,decl_typ,ret_name) = decl in
     check_consistent loc decl_typ args (ret_name,ret) >>
     check_function_body genv fsym body decl_typ
  | M_ProcDecl _
  | M_BuiltinDecl _ -> 
     return ()


let check_functions (type a bty) env (fns : (bty,a) mu_fun_map) =
  pmap_iterM (check_function env) fns

                             



(* according to https://en.wikipedia.org/wiki/C_data_types *)
(* and *)
(* https://en.wikibooks.org/wiki/C_Programming/stdint.h#Exact-width_integer_types *)
let bt_and_constr_of_integerBaseType signed ibt = 

  let make f t = 
    let ft = IndexTerms.Num (of_string f) in
    let tt = IndexTerms.Num (of_string t) in
    let constr name = (name %>= ft) %& (name %<= tt) in
    (BaseTypes.Int, constr)
  in

  match signed, ibt with
  | true,  Ctype.Ichar    -> make "-127" "127"
  | true,  Ctype.Short    -> make "-32767" "32767"
  | true,  Ctype.Int_     -> make "-32767" "32767"
  | true,  Ctype.Long     -> make "-2147483647" "2147483647"
  | true,  Ctype.LongLong -> make "-9223372036854775807" "9223372036854775807"
  | false, Ctype.Ichar    -> make "0" "255"
  | false, Ctype.Short    -> make "0" "65535"
  | false, Ctype.Int_     -> make "0" "65535"
  | false, Ctype.Long     -> make "0" "4294967295"
  | false, Ctype.LongLong -> make "0" "18446744073709551615"
  | true, Ctype.IntN_t n -> 
     begin match n with
     | 8 ->  make "-127" "127"
     | 16 -> make "-32768" "32767"
     | 32 -> make "-2147483648" "2147483647"
     | 64 -> make "-9223372036854775808" "9223372036854775807"
     | _ -> failwith (sprintf "IntN_t %d" n)
     end
  | false, Ctype.IntN_t n -> 
     begin match n with
     | 8 ->  make "0" "255"
     | 16 -> make "0" "65535"
     | 32 -> make "0" "4294967295"
     | 64 -> make "0" "18446744073709551615"
     | _ -> failwith (sprintf "UIntN_t %d" n)
     end
  | _, Ctype.Int_leastN_t n -> 
     failwith "todo standard library types"
  | _, Ctype.Int_fastN_t n -> 
     failwith "todo standard library types"
  | _, Ctype.Intmax_t -> 
     failwith "todo standard library types"
  | _, Ctype.Intptr_t -> 
     failwith "todo standard library types"

let bt_and_constr_of_integerType it = 
  match it with
  | Ctype.Char -> 
     failwith "todo char"
  | Ctype.Bool -> 
     (BaseTypes.Bool, None)
  | Ctype.Signed ibt -> 
     let (bt,constr) = bt_and_constr_of_integerBaseType true ibt in
     (bt, Some constr)
  | Ctype.Unsigned ibt -> 
     let (bt,constr) = bt_and_constr_of_integerBaseType false ibt in
     (bt, Some constr)
  | Ctype.Enum _sym -> 
     failwith "todo enum"
  | Ctype.Wchar_t ->
     failwith "todo wchar_t"
  | Ctype.Wint_t ->
     failwith "todo wint_t"
  | Ctype.Size_t ->
     failwith "todo size_t"
  | Ctype.Ptrdiff_t -> 
     failwith "todo standard library types"

let rec bt_and_constr_of_ctype (Ctype.Ctype (annots, ct)) = 
  let loc = Annot.get_loc_ annots in
  match ct with
  | Ctype.Void -> (* check *)
     return (Unit, None)
  | Ctype.Basic (Integer it) -> 
     return (bt_and_constr_of_integerType it)
  | Ctype.Basic (Floating _) -> 
     fail (Unsupported {loc; unsupported = "floats"} )
  | Ctype.Array (ct, _maybe_integer) -> 
     return (BaseTypes.Array, None)
  | Ctype.Function _ -> 
     fail (Unsupported {loc; unsupported = "function pointers"})
  | Ctype.Pointer (_qualifiers, ctype) ->
     return (Loc, None)
  | Ctype.Atomic ct ->              (* check *)
     bt_and_constr_of_ctype ct
  | Ctype.Struct sym -> 
     return (Struct sym, None)
  | Ctype.Union sym ->
     failwith "todo: union types"


let record_fun sym (loc,_attrs,ret_ctype,args,is_variadic,_has_proto) fun_decls =

  let binding_of_ctype ctype name = 
    bt_and_constr_of_ctype ctype >>= function
    | (bt, Some c) -> 
       return [{name; bound = A bt}; {name = fresh (); bound = C (LC (c (S name)))}]
    | (bt, None) -> 
       return [{name; bound = A bt}]
  in

  let make_arg_t (msym,ctype) = binding_of_ctype ctype (sym_or_fresh msym) in
  if is_variadic 
  then fail (Variadic_function {loc; fn = sym})
  else 
    let ret_name = Sym.fresh () in
    mapM make_arg_t args >>= fun args_types ->
    let arguments = concat args_types in
    binding_of_ctype ret_ctype ret_name >>= fun ret ->
    let ft = F {arguments; return = ret} in
    let fun_decls = SymMap.add sym (loc, ft, ret_name) fun_decls in
    return fun_decls

let record_funinfo genv funinfo = 
  pmap_foldM record_fun funinfo genv.GEnv.fun_decls >>= fun fun_decls ->
  return { genv with GEnv.fun_decls = fun_decls }



let record_tagDef sym def genv =

  match def with
  | Ctype.UnionDef _ -> 
     failwith "todo: union types"
  | Ctype.StructDef fields ->

     fold_leftM (fun (names,fields) (id, (_attributes, _qualifier, ctype)) ->
       let name = Id.s id in
       let sym = Sym.fresh_pretty name in
       let names = (name, (sym, Loc.unknown)) :: names in
       bt_and_constr_of_ctype ctype >>= fun bt_constr ->
       let fields = match bt_constr with
         | (bt, Some c) -> 
            fields @ [{name = sym; bound = A bt}; 
                      {name = fresh (); bound = C (LC (c (S sym)))}]
         | (bt, None) -> 
            fields @ [{name = sym; bound = A bt}]
       in
       return (names, fields)
     ) ([],[]) fields >>= fun (names,fields) ->

     let struct_decls = SymMap.add sym fields genv.GEnv.struct_decls in
     let names = fold_left (fun m (k,v) -> StringMap.add k v m) genv.names names in
     return { genv with names = names; struct_decls = struct_decls }

let record_tagDefs genv tagDefs = 
  pmap_foldM record_tagDef tagDefs genv







let pp_fun_map_decl funinfo = 
  let pp = Pp_core.All.pp_funinfo_with_attributes funinfo in
  print_string (Pp_utils.to_plain_string pp)




let check mu_file =
  let env = GEnv.empty in
  record_tagDefs env mu_file.mu_tagDefs >>= fun env ->
  record_funinfo env mu_file.mu_funinfo >>= fun env ->
  let () = print_endline (GEnv.pp env) in
  check_functions env mu_file.mu_funs

let check_and_report core_file = 
  match check core_file with
  | Result () -> ()
  | Exception err -> print_endline (pp err)
