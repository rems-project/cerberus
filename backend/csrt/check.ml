open Cerb_frontend
(* open Cerb_backend *)
(* open Lem_pervasives  *)
open Core 
open Mucore
open Nat_big_num
open Sexplib
open Printf


module List = struct

  include List
        
  let concatmap (f : 'a -> 'b list) (xs : 'a list) : 'b list = 
    List.concat (List.map f xs)

  let rec filter_map (f : 'a -> 'b option) (xs : 'a list) : 'b list = 
    match xs with
    | [] -> []
    | x :: xs ->
       match f x with
       | None -> filter_map f xs
       | Some y -> y :: filter_map f xs

end

open List


let uncurry f (a,b)  = f a b
let curry f a b = f (a,b)
let flip f a b = f b a


type num = Nat_big_num.num


(* error monad *)

module Ex = struct
  open Exception
  type ('a,'e) m = ('a,'e) exceptM
  let return : 'a -> ('a,'e) m = except_return
  let fail : 'e -> ('a,'e) m = fail
  let (>>=) = except_bind
  let (>>) m m' = m >>= fun _ -> m'
  let liftM = except_fmap
  let seq = except_sequence
  let of_maybe = of_maybe
  let to_bool = to_bool
  let mapM : ('a -> ('b,'e) m) -> 'a list -> ('b list, 'e) m = 
    except_mapM
  let concatmapM f l = 
    seq (map f l) >>= fun xs ->
    return (concat xs)
  let fold_leftM (f : 'a -> 'b -> ('c,'e) m) (a : 'a) (bs : 'b list) =
    fold_left (fun a b -> a >>= fun a -> f a b) (return a) bs
  let pmap_foldM 
        (f : 'k -> 'x -> 'y -> ('y,'e) m)
        (map : ('k,'x) Pmap.map) (init: 'y) : ('y,'e) m =
    Pmap.fold (fun k v a -> a >>= f k v) map (return init)
  let pmap_iterM f m = 
    Pmap.fold (fun k v a -> a >> f k v) 
      m (return ())

  let tryM (m : ('a,'e1) exceptM) (m' : ('a,'e2) exceptM) =
    match m with
    | Result a -> Result a
    | Exception _ -> m'

  let rec tryMs (m : ('a,'e1) exceptM) (ms : (('a,'e2) exceptM) list) =
    match m, ms with
    | Result a, _ -> Result a
    | Exception _, m' :: ms' -> tryMs m' ms'
    | Exception e, [] -> Exception e

end


open Ex


module Loc = struct
  include Location_ocaml
  let pp loc = 
    Pp_utils.to_plain_string (Location_ocaml.pp_location loc)
end


module StringMap = Map.Make(String)



module Sym = struct

  type t = Symbol.sym

  let fresh = Symbol.fresh
  let fresh_pretty = Symbol.fresh_pretty
  let pp = Pp_symbol.to_string_pretty

  let of_asym (s : 'bty Mucore.asym) = 
    let (Annotated (_, _, sym)) = s in sym

  let lof_asym (s : 'bty Mucore.asym) = 
    let (Annotated (annots, _, sym)) = s in 
    (sym, Annot.get_loc_ annots)

  let compare = Symbol.symbol_compare

  let parse loc (names : (t * Loc.t) StringMap.t) name = 
    match StringMap.find_opt name names with
    | Some (sym,_) -> return sym
    | None -> fail (sprintf "%s. Unbound variable %s" (Loc.pp loc) name)

  (* let subst sym sym' symbol : t = 
   *   if symbol = sym then sym' else symbol *)

end

module NameMap = struct
  include StringMap
  type map = (Sym.t * Loc.t) StringMap.t
end

module Id = struct
  type t= Symbol.identifier
  let s (Symbol.Identifier (_,s)) = s
  let pp = s
  let compare id id' = 
    String.compare (s id) (s id')
  let parse loc id = 
    Symbol.Identifier (loc,id)
end


module SymMap = struct
  include Map.Make(Sym)
  let foldM 
        (f : key -> 'x -> 'y -> ('y,'e) m)
        (map : 'x t) (init: 'y) : ('y,'e) m =
    fold (fun k v a -> a >>= f k v) map (return init)
end

module SymSet = Set.Make(Sym)



let parse_error (t : string) (sx : Sexp.t) = 
  let err = sprintf "unexpected %s: %s" t (Sexp.to_string sx) in
  fail err






type ('spec, 'res) uni = {
    spec_name : Sym.t;
    spec : 'spec;
    resolved : 'res option
  }



module BT = struct

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
  
  let rec parse_sexp loc (names : NameMap.map) sx = 
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
    | a -> parse_error "base type" a

  let type_equal t1 t2 = t1 = t2

  let types_equal ts1 ts2 = 
    for_all (fun (t1,t2) -> type_equal t1 t2) (combine ts1 ts2)

  let subst _sym _neu bt = bt

end



module LS = struct

  type t = 
    | Base of BT.t

  let pp = function
    | Base bt -> BT.pp bt
  
  let parse_sexp loc (names : NameMap.map) sx =
    match sx with
    | sx ->
       BT.parse_sexp loc names sx >>= fun bt ->
       return (Base bt)

  let type_equal t1 t2 = t1 = t2

  let types_equal ts1 ts2 = 
    for_all (fun (t1,t2) -> type_equal t1 t2) (combine ts1 ts2)

  let subst _sym _neu ls = ls


end



module IT = struct

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



  let rec parse_sexp loc (names : NameMap.map) sx = 
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
       parse_error "index term" t


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


open IT


open BT

module RE = struct

  type t = 
    | Block of IT.t * IT.t
    | Int of IT.t * IT.t (* location and value *)
    | Points of IT.t * IT.t
    | Array of IT.t * IT.t
    | Pred of string * IT.t list

  let pp = function
    | Block (it1,it2) -> 
       sprintf "(block %s %s)" 
         (IT.pp it1)
         (IT.pp it2)
    | Int (it1,it2) -> 
       sprintf "(int %s %s)" 
         (IT.pp it1) 
         (IT.pp it2)
    | Array (it1,it2) -> 
       sprintf "(array %s %s)" 
         (IT.pp it1)
         (IT.pp it2)
    | Points (it1,it2) -> 
       sprintf "(points %s %s)" 
         (IT.pp it1)
         (IT.pp it2)
    | Pred (p,its) ->
       sprintf "(%s %s)" 
         p
         (String.concat " " (map IT.pp its))

  
  let parse_sexp loc (names : NameMap.map) sx = 
    match sx with 
    | Sexp.List [Sexp.Atom "block";it1;it2] -> 
       IT.parse_sexp loc names it1 >>= fun it1 ->
       IT.parse_sexp loc names it2 >>= fun it2 ->
       return (Block (it1, it2))
    | Sexp.List [Sexp.Atom "int"; it1; it2] ->
       IT.parse_sexp loc names it1 >>= fun it1 ->
       IT.parse_sexp loc names it2 >>= fun it2 ->
       return (Int (it1, it2))
    | Sexp.List [Sexp.Atom "array"; it1; it2] ->
       IT.parse_sexp loc names it1 >>= fun it1 ->
       IT.parse_sexp loc names it2 >>= fun it2 ->
       return (Array (it1, it2))
    | Sexp.List [Sexp.Atom "points"; it1; it2] ->
       IT.parse_sexp loc names it1 >>= fun it1 ->
       IT.parse_sexp loc names it2 >>= fun it2 ->
       return (Points (it1, it2))
    | Sexp.List (Sexp.Atom p :: its) ->
       mapM (IT.parse_sexp loc names) its >>= fun its ->
       return (Pred (p, its))
    | t -> parse_error "resource type" t

  let subst sym neu t = 
    match t with
    | Block (it, it') -> 
       Block (IT.subst sym neu it, IT.subst sym neu it')
    | Int (it, it') -> 
       Int (IT.subst sym neu it, IT.subst sym neu it')
    | Points (it, it') -> 
       Points (IT.subst sym neu it, IT.subst sym neu it')
    | Array (it, it') -> 
       Array (IT.subst sym neu it, IT.subst sym neu it')
    | Pred (p, its) ->
       Pred (p, map (IT.subst sym neu) its)

  let type_equal env t1 t2 = 
    t1 = t2                       (* todo: maybe up to variable
                                     instantiation, etc. *)

  let types_equal env ts1 ts2 = 
    for_all (fun (t1,t2) -> type_equal env t1 t2) (combine ts1 ts2)

  let unify r1 r2 res = 
    match r1, r2 with
    | Block (it1, it2), Block (it1', it2') ->
       IT.unify it1 it1' res >>= fun res ->
       IT.unify it2 it2' res
    | Int (it1, it2), Int (it1', it2') -> 
       IT.unify it1 it1' res >>= fun res ->
       IT.unify it2 it2' res
    | Points (it1, it2), Points (it1', it2') -> 
       IT.unify it1 it1' res >>= fun res ->
       IT.unify it2 it2' res
    | Array (it1, it2), Array (it1', it2') -> 
       IT.unify it1 it1' res >>= fun res ->
       IT.unify it2 it2' res
    | Pred (p, its), Pred (p', its') when p = p' ->
       IT.unify_list its its' res
    | _, _ -> fail ()

end


module LC = struct

  type t = LC of IT.t

  let pp (LC c) = IT.pp c

  let parse_sexp loc env s = 
    IT.parse_sexp loc env s >>= fun it ->
    return (LC it)

  let subst sym sym' (LC c) = 
    LC (IT.subst sym sym' c)

end

open LC


module T = struct

  type t = 
    | A of BT.t
    | L of LS.t
    | R of RE.t
    | C of LC.t

  type kind = 
    | Argument
    | Logical
    | Resource
    | Constraint

  let kind_of_t = function
    | A _ -> Argument
    | L _ -> Logical
    | R _ -> Resource
    | C _ -> Constraint

  let pp_kind = function
    | Argument -> "computational"
    | Logical -> "logical"
    | Resource -> "resource"
    | Constraint -> "constraint"


  let subst sym sym' t = 
    match t with
    | A t -> A (BT.subst sym sym' t)
    | L t -> L (LS.subst sym sym' t)
    | R t -> R (RE.subst sym sym' t)
    | C t -> C (LC.subst sym sym' t)


end


module B = struct

  open T
         
  type t = Sym.t * T.t

  let pp = function
    | (id, A typ) -> 
       sprintf "(%s : %s)" (Sym.pp id) (BT.pp typ)
    | (id, L ls)  -> 
       sprintf "(Logical %s : %s)" (Sym.pp id) (LS.pp ls)
    | (id, R re) -> 
       sprintf "(Resource %s : %s)" (Sym.pp id) (RE.pp re)
    | (id, C lc) -> 
       sprintf "(Constraint %s : %s)" (Sym.pp id) (LC.pp lc)

  let parse_sexp loc (names : NameMap.map) s = 
    match s with
    | Sexp.List [Sexp.Atom id; Sexp.Atom ":"; t] ->
       let sym = Sym.fresh_pretty id in
       let names = NameMap.add id (sym,loc) names in
       BT.parse_sexp loc names t >>= fun bt ->
       return ((sym, A bt), names)
    | Sexp.List [Sexp.Atom "Logical"; Sexp.Atom id; Sexp.Atom ":"; ls] ->
       let sym = Sym.fresh_pretty id in
       let names = NameMap.add id (sym,loc) names in
       LS.parse_sexp loc names ls >>= fun ls ->
       return ((sym, L ls), names)
    | Sexp.List [Sexp.Atom "Resource"; Sexp.Atom id; Sexp.Atom ":"; re] ->
       let sym = Sym.fresh_pretty id in
       let names = NameMap.add id (sym,loc) names in
       RE.parse_sexp loc names re >>= fun re ->
       return ((sym, R re), names)
    | Sexp.List [Sexp.Atom "Constraint"; Sexp.Atom id; Sexp.Atom ":"; lc] ->
       let sym = Sym.fresh_pretty id in
       let names = NameMap.add id (sym,loc) names in
       LC.parse_sexp loc names lc >>= fun lc ->
       return ((sym, C lc), names)
    | t -> 
       parse_error "return type" t
         
  let subst sym (neu : IT.t) (symbol, t) = 
    (symbol, T.subst sym neu t)

end


module Bs = struct

  type t = B.t list

  let pp ts = 
    String.concat " , " (map B.pp ts)

  let parse_sexp fstr loc (names : NameMap.map) s = 
    let rec aux (names : NameMap.map) acc ts = 
      match ts with
      | [] -> return (rev acc, names)
      | b :: bs ->
         B.parse_sexp loc names b >>= fun (b, names) ->
         aux names (b :: acc) bs
    in
    match s with
    | Sexp.List ts -> aux names [] ts
    | t -> parse_error fstr t

  let subst sym neu bs = 
    map (B.subst sym neu) bs

end


module A = struct
  type t = A of Bs.t
  let pp (A ts) = Bs.pp ts
  let parse_sexp loc names s = 
    Bs.parse_sexp "argument type" loc names s >>= fun (bs, names) ->
    return (A bs, names)
  let subst sym neu (A ts) = 
    A (Bs.subst sym neu ts)
end


module R = struct
  type t = R of Bs.t
  let pp (R ts) = Bs.pp ts
  let parse_sexp loc names s = 
    Bs.parse_sexp "return type" loc names s >>= fun (bs, names) ->
    return (R bs, names)
  let subst sym neu (R ts) = 
    R (Bs.subst sym neu ts)
end


module F = struct
  type t = F of A.t * R.t
  let subst sym sym' (F (a,r)) = 
    F (A.subst sym sym' a, R.subst sym sym' r)
  let pp (F (a,r)) = 
    sprintf "%s -> %s" (A.pp a) (R.pp r)
end
  

open A
open R
open F

      

module Err = struct

  type call_return_switch_error = 
    | Surplus_A of Sym.t * BT.t
    | Surplus_L of Sym.t * LS.t
    | Surplus_R of Sym.t * RE.t
    | Missing_A of Sym.t * BT.t
    | Missing_L of Sym.t * LS.t
    | Missing_R of Sym.t * RE.t
    | Mismatch of { has : B.t; expected: B.t; }
    | Unsat_constraint of Sym.t * LC.t
    | Unconstrained_l of Sym.t * LS.t

  type type_error = 
    | Var_kind_error of {
        loc : Loc.t;
        sym: Sym.t;
        expected : T.kind;
        has : T.kind;
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
        it: IT.t;
      }
    | Unsupported of { 
        loc: Loc.t;
        unsupported: string; 
      }
    | Unbound_name of {
        loc: Loc.t; 
        unbound: Sym.t;
      }
    | Inconsistent_fundef of {
        loc: Loc.t;
        decl: F.t;
        defn: F.t;
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
    | Generic_error of Loc.t * string

  let pp_return_error loc = function
    | Surplus_A (_name,t) ->
       sprintf "Line %s. Returning unexpected value of type %s" 
         (Loc.pp loc) (BT.pp t)
    | Surplus_L (_name,t) ->
       sprintf "%s. Returning unexpected logical value of type %s" 
         (Loc.pp loc) (LS.pp t)
    | Surplus_R (_name,t) ->
       sprintf "%s. Returning unexpected resource of type %s" 
         (Loc.pp loc) (RE.pp t)
    | Missing_A (_name,t) ->
       sprintf "%s. Missing return value of type %s" 
         (Loc.pp loc) (BT.pp t)
    | Missing_L (_name,t) ->
       sprintf "%s. MIssing logical return value of type %s" 
         (Loc.pp loc) (LS.pp t)
    | Missing_R (_name,t) ->
       sprintf "%s. Missing return resource of type %s" 
         (Loc.pp loc) (RE.pp t)
    | Mismatch {has; expected} ->
       let has_pp = match has with
         | (_, T.A t) -> sprintf "return value of type %s" (BT.pp t)
         | (_, T.L t) -> sprintf "logical return value of type %s" (LS.pp t)
         | (_, T.R t) -> sprintf "return resource of type %s" (RE.pp t)
         | (_, T.C t) -> sprintf "return constraint %s" (LC.pp t)
       in
       begin match expected with
       | (_, T.A t) ->
          sprintf "%s. Expected return value of type %s but found %s" 
            (Loc.pp loc) (BT.pp t) has_pp
       | (_, T.L t) ->
          sprintf "%s. Expected logical return value of type %s but found %s" 
            (Loc.pp loc) (LS.pp t) has_pp
       | (_, T.R t) ->
          sprintf "%s. Expected return resource of type %s but found %s" 
            (Loc.pp loc) (RE.pp t) has_pp
       | (_, T.C t) ->
          (* dead, I think *)
          sprintf "%s. Expected return constraint %s but found %s" 
            (Loc.pp loc) (LC.pp t) has_pp
       end
    | Unsat_constraint (name,c) ->
       sprintf "%s. Unsatisfied return constraint %s: %s" 
         (Loc.pp loc) (Sym.pp name) (LC.pp c)
    | Unconstrained_l (name, ls) ->
       sprintf "%s. Unconstrained logical variable %s: %s" 
         (Loc.pp loc) (Sym.pp name) (LS.pp ls)
    

  let pp_call_error loc = function
    | Surplus_A (_name,t) ->
       sprintf "Line %s. Supplying unexpected argument of type %s" 
         (Loc.pp loc) (BT.pp t)
    | Surplus_L (_name,t) ->
       sprintf "%s. Supplying unexpected logical argument of type %s" 
         (Loc.pp loc) (LS.pp t)
    | Surplus_R (_name,t) ->
       sprintf "%s. Supplying unexpected resource of type %s" 
         (Loc.pp loc) (RE.pp t)
    | Missing_A (_name,t) ->
       sprintf "%s. Missing argument of type %s" 
         (Loc.pp loc) (BT.pp t)
    | Missing_L (_name,t) ->
       sprintf "%s. Missing logical argument of type %s" 
         (Loc.pp loc) (LS.pp t)
    | Missing_R (_name,t) ->
       sprintf "%s. Missing resource argument of type %s" 
         (Loc.pp loc) (RE.pp t)
    | Mismatch {has; expected} ->
       let has_pp = match has with
         | (_, T.A t) -> sprintf "argument of type %s" (BT.pp t)
         | (_, T.L t) -> sprintf "logical argument of type %s" (LS.pp t)
         | (_, T.R t) -> sprintf "resource argument of type %s" (RE.pp t)
         | (_, T.C t) -> sprintf "constraint argument %s" (LC.pp t)
       in
       begin match expected with
       | (_, T.A t) ->
          sprintf "%s. Expected argument of type %s but found %s" 
            (Loc.pp loc) (BT.pp t) has_pp
       | (_, T.L t) ->
          sprintf "%s. Expected logical argument of type %s but found %s" 
            (Loc.pp loc) (LS.pp t) has_pp
       | (_, T.R t) ->
          sprintf "%s. Expected resource argument of type %s but found %s" 
            (Loc.pp loc) (RE.pp t) has_pp
       | (_, T.C t) ->
          (* dead, I think *)
          sprintf "%s. Expected constraint argument %s but found %s" 
            (Loc.pp loc) (LC.pp t) has_pp
       end
    | Unsat_constraint (name,lc) ->
       sprintf "%s. Unsatisfied return constraint %s: %s" 
         (Loc.pp loc) (Sym.pp name) (LC.pp lc)
    | Unconstrained_l (name,ls) ->
       sprintf "%s. Unconstrained logical variable %s: %s" 
         (Loc.pp loc) (Sym.pp name) (LS.pp ls)

  let pp = function 
    | Var_kind_error err ->
       sprintf "%s. Expected kind %s but found kind %s"
         (Loc.pp err.loc) (T.pp_kind err.expected) (T.pp_kind err.has)
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
         (Loc.pp loc) (IT.pp it)
    | Unsupported {loc; unsupported} ->
       sprintf "%s. Unsupported feature: %s" 
         (Loc.pp loc) unsupported
    | Unbound_name {loc; unbound} ->
       sprintf "%s. Unbound symbol %s"
         (Loc.pp loc) (Sym.pp unbound)
    | Inconsistent_fundef {loc; decl; defn} ->
       sprintf "%s. Function definition inconsistent. Should be %s, is %s"
         (Loc.pp loc) (F.pp decl) (F.pp defn)
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


end

open Err



module Env = struct

  type global_env = 
    { struct_decls : Bs.t SymMap.t ; 
      fun_decls : (Loc.t * F.t * Sym.t) SymMap.t; (* third item is return name *)
      names : NameMap.map
    } 

  type local_env = T.t SymMap.t

  type env = 
    { local : local_env ; 
      global : global_env }

  let empty_global = 
    { struct_decls = SymMap.empty; 
      fun_decls = SymMap.empty;
      names = NameMap.empty }

  let empty_local = SymMap.empty

  let empty_env = 
    { local = empty_local; 
      global = empty_global }

  let with_fresh_local global_env = 
    { global = global_env; 
      local = empty_local }

  let add_var (env : env) (sym, t) = 
    { env with local = SymMap.add sym t env.local }

  let add_vars env bindings = 
    fold_left add_var env bindings

  let add_Avar env (sym, t) = add_var env (sym, T.A t)
  let add_Lvar env (sym, t) = add_var env (sym, T.L t)
  let add_Rvar env (sym, t) = add_var env (sym, T.R t)
  let add_Cvar env (sym, t) = add_var env (sym, T.C t)

  let remove_var env sym = 
    { env with local = SymMap.remove sym env.local }

  let lookup (loc : Loc.t) (env: 'v SymMap.t) (name: Sym.t) =
    match SymMap.find_opt name env with
    | None -> fail (Unbound_name {loc; unbound = name})
    | Some v -> return v

  let get_var (loc : Loc.t) (env: env) (name: Sym.t) =
    lookup loc env.local name >>= function
    | T.A t -> return (`A t)
    | T.L t -> return (`L t)
    | T.R t -> return (`R (t, remove_var env name))
    | T.C t -> return (`C t)


  let kind = function
    | `A _ -> T.Argument
    | `L _ -> T.Logical
    | `R _ -> T.Resource
    | `C _ -> T.Constraint

  let get_Avar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | `A t -> return t
    | t -> fail (Var_kind_error {loc; sym; expected = T.Argument; has = kind t})

  let get_Lvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | `L t -> return t
    | t -> fail (Var_kind_error {loc; sym; expected = T.Logical; has = kind t})

  let get_Rvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | `R (t, env) -> return (t, env)
    | t -> fail (Var_kind_error {loc; sym; expected = T.Resource; has = kind t})

  let get_Cvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | `C t -> return t
    | t -> fail (Var_kind_error {loc; sym; expected = T.Constraint; has = kind t})

end

open Env



let rec infer_it loc env it = 
  match it with
  | Num _ -> return BT.Int
  | Bool _ -> return BT.Bool

  | Add (it,it')
  | Sub (it,it')
  | Mul (it,it')
  | Div (it,it')
  | Exp (it,it')
  | App (it,it')
  | Rem_t (it,it')
  | Rem_f (it,it') ->
     check_it loc env it BT.Int >>
     check_it loc env it' BT.Int >>
     return BT.Int

  | EQ (it,it')
  | NE (it,it')
  | LT (it,it')
  | GT (it,it')
  | LE (it,it')
  | GE (it,it') ->
     check_it loc env it BT.Int >>
     check_it loc env it' BT.Int >>
     return BT.Bool

  | Null it ->
     check_it loc env it BT.Loc >>
     return BT.Bool

  | And (it,it')
  | Or (it,it') ->
     check_it loc env it BT.Int >>
     check_it loc env it' BT.Int >>
     return BT.Bool

  | Not it ->
     check_it loc env it BT.Bool >>
     return BT.Bool

  | List (it, its) ->
     infer_it loc env it >>= fun bt ->
     check_it loc env it bt >>
     return (List bt)

  | S sym ->
     get_var loc env sym >>= function
     | `A t -> return t
     | `L (LS.Base t) -> return t
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



let rec bt_of_core_base_type loc cbt : (BT.t, type_error) m = 

  let bt_of_core_object_type loc = function
    | OTy_integer -> 
       return BT.Int
    | OTy_floating -> 
       fail (Unsupported {loc; unsupported = "float"})
    | OTy_pointer -> 
       return BT.Loc
    | OTy_array cbt -> 
       return BT.Array
    | OTy_struct sym -> 
       return (Struct sym)
    | OTy_union _sym -> 
       failwith "todo: union types"
  in

  match cbt with
  | Core.BTy_unit -> 
     return BT.Unit
  | Core.BTy_boolean -> 
     return BT.Bool
  | Core.BTy_ctype -> 
     fail (Unsupported {loc; unsupported = "ctype"})
  | Core.BTy_list bt -> 
     bt_of_core_base_type loc bt >>= fun bt ->
     return (BT.List bt)
  | Core.BTy_tuple bts -> 
     mapM (bt_of_core_base_type loc) bts >>= fun bts ->
     return (BT.Tuple bts)
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



let ensure_type loc has expected : (unit, type_error) Ex.m = 
  if BT.type_equal has expected 
  then return ()
  else fail (Call_error (loc, Mismatch {has; expected}))


let args_same_typ (mtyp : BT.t option) (args_bts : (BT.t * Loc.t) list) =
  fold_leftM (fun mt (bt,loc) ->
      match mt with
      | None -> return (Some bt)
      | Some t -> 
         ensure_type loc 
           (Sym.fresh (), T.A bt)
           (Sym.fresh (), T.A t) >>
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
     let t = (name, T.A BT.Int) in
     let constr = (Sym.fresh (), T.C (LC (S name %= Num i))) in
     return [t; constr]
  | M_OVfloating iv ->
     fail (Unsupported {loc; unsupported = "floats"})
  | M_OVpointer p ->
     Impl_mem.case_ptrval p
       ( fun _cbt -> 
         let t = (name, T.A BT.Loc) in
         let constr = (Sym.fresh (), T.C (LC (Null (S name)))) in
         return [t; constr] )
       ( fun sym -> 
         fail (Unsupported {loc; unsupported = "function pointers"}) )
       ( fun _prov loc ->
         let t = (name, T.A BT.Loc) in
         let constr = (Sym.fresh (), T.C (LC (S name %= Num loc))) in
         return [t; constr] )
       ( fun _ ->
         fail (Unsupported {loc; unsupported = "unspecified pointer value"}) )
  | M_OVarray items ->
     make_Aargs_bts env items >>= fun args_bts ->
     args_same_typ None args_bts >>
     return [(name,T.A BT.Array)]
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
     let t = (name, T.A BT.Unit) in
     return [t]
  | M_Vtrue ->
     let t = (name, T.A BT.Bool) in
     let constr = (Sym.fresh (), T.C (LC (S name))) in
     return [t; constr]
  | M_Vfalse -> 
     let t = (name, T.A BT.Bool) in
     let constr = (Sym.fresh (), T.C (LC (Not (S name)))) in
     return [t; constr]
  | M_Vlist (_, asyms) ->
     (* bt_of_core_base_type loc cbt >>= fun i_t -> *)
     begin make_Aargs_bts env asyms >>= function
     | [] ->
        failwith "empty list case"
     | (bt, _) :: args_bts ->
        args_same_typ (Some bt) args_bts >>= fun i_t ->
        (* maybe record list length? *)
        let t = (name, T.A (BT.List bt)) in
        return [t]
     end
  | M_Vtuple args ->
     make_Aargs_bts env args >>= fun args_bts ->
     let t = (name, T.A (BT.Tuple (List.map fst args_bts))) in
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

  let rec check_and_refine env asyms ftyp unis constrs = 
    let (F (A.A args, ret)) = ftyp in
    match args with
    | [] -> 
       begin match asyms with
       | [] -> 
          logical_variables_resolved env unis >>= fun substs ->
          let ret = 
            fold_left (fun ret (s, subst) -> R.subst s subst ret)
              ret substs 
          in
          let constrs = 
            fold_left (fun constrs (s, subst) -> 
                map (fun (n,lc) -> (n, LC.subst s subst lc)) constrs)
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
                        asyms' ftyp unis constrs
       end

    | (n, T.A t) :: args' ->
       begin match asyms with
       | asym :: asyms' ->
          let (sym,loc) = Sym.lof_asym asym in
          get_Avar loc env sym >>= fun t' ->
          let ftyp = F.subst n (S sym) (F (A.A args', ret)) in
          if BT.type_equal t' t
          then check_and_refine env asyms' ftyp unis constrs
          else fail (Call_error (loc, Mismatch {has = (sym, T.A t'); expected = (n, T.A t)}))
       | [] ->
          fail (Call_error (loc_call, Missing_A (n, t)))
       end

    | (n, T.R t) :: args' -> 

       begin match asyms with
       | asym :: _ -> 
          let (sym,loc) = Sym.lof_asym asym in 
          get_Rvar loc env sym >>= fun (t',env) ->
          tryM (RE.unify t t' unis)
            (let err = Mismatch {has = (sym, T.R t'); expected = (n, T.R t)} in
             fail (Call_error (loc, err))) >>= fun res ->
          check_and_refine env asyms (F (A.A args', ret)) unis constrs
       | [] -> 
          fail (Call_error (loc_call, (Missing_R (n, t))))
       end

    | (n, T.L t) :: args' -> 
       let sym = Sym.fresh () in
       let uni = { spec_name = n; spec = t; resolved = None } in
       let unis' = SymMap.add sym uni unis in
       let ftyp' = F.subst n (S sym) (F (A.A args', ret)) in
       check_and_refine env asyms ftyp' unis' constrs

    | (n, T.C t) :: args' ->        
       let constrs' = (constrs @ [(n, t)]) in
       check_and_refine env asyms (F (A.A args', ret)) unis constrs'

  in
  check_and_refine env args decl_typ SymMap.empty []


let call_typ_fn loc_call name env args =
  match name with
  | Core.Impl _ -> 
     failwith "todo implementation-defined constrant"
  | Core.Sym sym ->
     lookup loc_call env.global.fun_decls sym >>= fun decl ->
     let (_loc,decl_typ,_ret_name) = decl in 
     call_typ loc_call env decl_typ args


let ctor_typ loc ctor (args_bts : ((BT.t * Loc.t) list)) = 
  match ctor with
  | Cnil _ ->
    begin match args_bts with 
    | [] -> 
       failwith "nil case"
       (* bt_of_core_base_type loc cbt >>= fun bt ->
        * let t = BT.List bt in
        * return t *)
    | args ->
       let err = sprintf "Cons applied to %d argument(s)" 
                   (List.length args) in
       fail (Generic_error (loc, err))
    end
  | Ccons ->
     begin match args_bts with
     | [(hd_bt,hd_loc); (tl_bt,tl_loc)] ->
        ensure_type tl_loc (Sym.fresh (), T.A tl_bt) 
          (Sym.fresh (), T.A (List hd_bt)) >>
        let t = List tl_bt in
        return t
     | args ->
        let err = sprintf "Cons applied to %d argument(s)" 
                    (List.length args) in
        fail (Generic_error (loc, err))
     end
  | Ctuple ->
     return (BT.Tuple (List.map fst args_bts))
  | Carray -> 
     args_same_typ None args_bts >>
     return BT.Array
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

     

(* let cases_union_rt env (loc1, rt1, cs1) (loc2, rt2, cs2) =
 * 
 *   let rec it_ands = function
 *     | [] -> IT.Bool true
 *     | [it] -> it
 *     | it :: its -> IT.And (it, it_ands its)
 *   in
 * 
 *   let rec aux (acc : Bs.t) (rt1, cs1) (rt2, cs2) =
 * 
 *     match rt1, rt2 with
 *     | [], [] -> 
 *        let cnstr = IT.Or (it_ands cs1, it_ands cs2) in
 *        let rt = ((List.rev acc) @ [(Sym.fresh (), T.C (LC.LC cnstr))]) in
 *        return rt
 * 
 *     | (n, T.C (LC.LC t)) :: rt1, rt2 ->
 *        aux acc (rt1, t :: cs1) (rt2, cs2)
 *     | rt1, (n, T.C (LC.LC t)) :: rt2 ->
 *        aux acc (rt1, cs1) (rt2, t :: cs2)
 *     | (n, t) :: _, []
 *     | [], (n, t) :: _ ->
 *        fail (Generic_error (loc2, "case switch: different number of return values"))
 * 
 * 
 *     | (r1 :: rt1), (r2 :: rt2) ->
 *        begin match r1, r2 with
 *        | (n1, T.A t1), (n2, T.A t2) when BT.type_equal t1 t2 ->
 *           let rt2 = Bs.subst n2 (S n1) rt2 in
 *           let cs2 = List.map (IT.subst n2 (S n1)) cs2 in
 *           aux ((n1, T.A t1) :: acc) (rt1, cs1) (rt2, cs2)
 *        | (n1, T.L t1), (n2, T.L t2) when LS.type_equal t1 t2 ->
 *           let rt2 = Bs.subst n2 (S n1) rt2 in
 *           let cs2 = List.map (IT.subst n2 (S n1)) cs2 in
 *           aux ((n1, T.L t1) :: acc) (rt1, cs1) (rt2, cs2)
 *        | (n1, T.R t1), (n2, T.R t2) when RE.type_equal env t1 t2 ->
 *           let rt2 = Bs.subst n2 (S n1) rt2 in
 *           let cs2 = List.map (IT.subst n2 (S n1)) cs2 in
 *           aux ((n1, T.R t1) :: acc) (rt1, cs1) (rt2, cs2)
 *        | _, _ ->
 *           fail (Switch_error (loc2, Mismatch {has = r1; expected = r2}))
 *        end
 * 
 *   in
 * 
 *   aux [] (rt1, cs1) (rt2, cs2) *)
    


let infer_binop name env loc op sym1 sym2 = 

  let make_binop_constr (v1 : IT.t) (v2 : IT.t) =
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

  let bt_of_binop : ((BT.t * BT.t) * BT.t) = 
    match op with
    | OpAdd -> ((BT.Int, BT.Int), BT.Int)
    | OpSub -> ((BT.Int, BT.Int), BT.Int)
    | OpMul -> ((BT.Int, BT.Int), BT.Int)
    | OpDiv -> ((BT.Int, BT.Int), BT.Int)
    | OpRem_t -> ((BT.Int, BT.Int), BT.Int)
    | OpRem_f -> ((BT.Int, BT.Int), BT.Int)
    | OpExp -> ((BT.Int, BT.Int), BT.Int)
    | OpEq -> ((BT.Int, BT.Int), BT.Bool)
    | OpGt -> ((BT.Int, BT.Int), BT.Bool)
    | OpLt -> ((BT.Int, BT.Int), BT.Bool)
    | OpGe -> ((BT.Int, BT.Int), BT.Bool)
    | OpLe -> ((BT.Int, BT.Int), BT.Bool)
    | OpAnd -> ((BT.Bool, BT.Bool), BT.Bool)
    | OpOr -> ((BT.Bool, BT.Bool), BT.Bool)
  in

  let (sym1, loc1) = Sym.lof_asym sym1 in
  let (sym2, loc2) = Sym.lof_asym sym2 in
  get_Avar loc env sym1 >>= fun t1 ->
  get_Avar loc env sym2 >>= fun t2 ->
  let ((st1,st2),rt) = bt_of_binop in
  ensure_type loc1 (sym1, T.A t1) (sym1, T.A st1) >>
  ensure_type loc2 (sym2, T.A t2) (sym1, T.A st2) >>
  let constr = LC (S name %= (make_binop_constr (S sym1) (S sym2))) in
  let env = add_Cvar env (Sym.fresh (), constr) in
  let t = (name, T.A rt) in
  return ([t], env)


let rec infer_pexpr name env (pe : 'bty mu_pexpr) = 
  let (M_Pexpr (annots, _bty, pe_)) = pe in
  let loc = Annot.get_loc_ annots in
  match pe_ with
  | M_PEsym sym ->
     get_Avar loc env sym >>= fun b ->
     let t = (name, T.A b) in
     return ([t], env)
  | M_PEimpl _ ->
     failwith "todo PEimpl"
  | M_PEval v ->
     infer_value loc name env v >>= fun t ->
     return (t, env)
  | M_PEconstrained _ ->
     failwith "todo PEconstrained"
  | M_PEundef _ ->
     failwith "todo PEundef"
  | M_PEerror _ ->
     failwith "todo PEerror"
  | M_PEctor (ctor, args) ->
     make_Aargs_bts env args >>= fun args_bts ->
     ctor_typ loc ctor args_bts >>= fun t ->
     return ([(name, T.A t)], env)
  | M_PEcase (asym, pats_es) ->
     (* let (esym,eloc) = Sym.lof_asym asym in
      * lookup eloc env.local.a esym >>= fun bt ->
      * fold_leftM (fun (pat_bt,m_body_bt) (pat,pe) ->
      *     (\* check pattern type against bt *\)
      *     infer_pat pat >>= fun (bindings, bt', ploc) ->
      *     let n = Sym.fresh () in
      *     ensure_type ploc (n, T.A bt') (n, T.A bt) >>
      *     (\* check body type against that of other cases and union *\)
      *     let env' = add_avars env bindings in
      *     infer_pexpr (Sym.fresh ()) env' pe >>= fun (env',body_t') ->
      *     match m_body_bt with
      *     | None -> return (pat_bt, Some body_t')
      *     | Some body_t ->
      *        cases_union_rt env body_t body_t' >>= fun body_t'' ->
      *        return (Some body_t'')
      *   ) (bt,None) pats_es >>= fun (_, Some body_t) ->
      * return (env, body_t) *)
     failwith "todo"
  | M_PEarray_shift _ ->
     failwith "todo PEarray_shift"
  | M_PEmember_shift _ ->
     failwith "todo PEmember_shift"
  | M_PEnot sym ->
     let (sym,a_loc) = Sym.lof_asym sym in
     get_Avar loc env sym >>= fun t ->
     ensure_type a_loc (sym, T.A t) (sym, T.A BT.Bool) >>
     let constr = LC ((S name) %= Not (S sym)) in
     let env = add_Cvar env (name, constr) in
     let t = (name, T.A t) in
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
     call_typ_fn loc mu_name env asyms >>= fun (R.R t, env) ->
     return (t, env)
  | M_PElet (p, e1, e2) ->
     (* todo: check against cbt? *)
     begin match p with 
     | M_symbol (Annotated (_annots, _, name2)) ->
        infer_pexpr name2 env e1 >>= fun (rt, env) ->
        infer_pexpr name (add_vars env rt) e2
     | M_normal_pattern (Pattern (_annot, CaseBase (mname2,_cbt))) ->
        let name2 = sym_or_fresh mname2 in
        infer_pexpr name2 env e1 >>= fun (rt, env) ->
        infer_pexpr name (add_vars env rt) e2
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
     ensure_type loc1 (sym1, T.A t1) (sym1, T.A BT.Bool) >>
     ensure_type loc3 (sym3, T.A t3) (sym1, T.A t2) >>
     let constr = 
       (Sym.fresh (), 
        T.C (LC ( (S sym1 %& (S name %= S sym2)) %| 
                    ((Not (S sym1)) %& (S name %= S sym3)) ) ))
     in
     let t = (name, T.A t2) in
     return ([t; constr], env)
  | M_PEensure_specified (asym1, _ct) ->
     let sym1, loc1 = Sym.lof_asym asym1 in
     get_Avar loc env sym1 >>= fun t1 ->
     return ([(sym1, T.A t1)], env)


let subtype loc env rt1 (R.R rt2) = 

  let rec check env rt1 rt2 =
    match rt1, rt2 with
    | [], [] -> 
       return env
    | (n, T.A r1) :: _, [] -> 
       fail (Return_error (loc, Surplus_A (n, r1)))
    | (n, T.L r1) :: _, [] -> 
       fail (Return_error (loc, Surplus_L (n, r1)))
    | (n, T.R r1) :: _, [] -> 
       fail (Return_error (loc, Surplus_R (n, r1)))

    | [], (n, T.A r2) :: _ -> 
       fail (Return_error (loc, Missing_A (n, r2)))
    | [], (n, T.L r2) :: _ -> 
       fail (Return_error (loc, Missing_L (n, r2)))
    | [], (n, T.R r2) :: _ -> 
       fail (Return_error (loc, Missing_R (n, r2)))
    | ((_, T.C c1) as r1) :: rt1', _ ->
       check (add_var env r1) rt1' rt2
    | _, (n2, T.C c2) :: rt2' ->
       if constraint_holds loc env c2 
       then check env rt1 rt2'
       else fail (Return_error (loc, Unsat_constraint (n2, c2)))
    | (r1 :: rt1), (r2 :: rt2) ->
       match r1, r2 with
       | (n1, T.A t1), (n2, T.A t2) when BT.type_equal t1 t2 ->
          check (add_var env r1) rt1 (Bs.subst n2 (S n1) rt2)
       | (n1, T.L t1), (n2, T.L t2) when LS.type_equal t1 t2 ->
          check (add_var env r1) rt1 (Bs.subst n2 (S n1) rt2)
       | (n1, T.R t1), (n2, T.R t2) when RE.type_equal env t1 t2 ->
          check env rt1 rt2
       | _, _ ->
          fail (Return_error (loc, Mismatch {has = r1; expected = r2}))
  in

  check env rt1 rt2



let rec infer_expr name env (e : ('a,'bty) mu_expr) = 
  let (M_Expr (annots, e_)) = e in
  (* let loc = Annot.get_loc_ annots in *)
  match e_ with
  | M_Epure pe -> 
     infer_pexpr name env pe
  | M_Ememop _ ->
     failwith "todo ememop"
  | M_Eaction _ ->
     failwith "todo eaction"
  | M_Ecase _ ->
     failwith "todo ecase"
  | M_Elet (p, e1, e2) ->
     begin match p with 
     | M_symbol (Annotated (_annots, _, name2)) ->
        infer_pexpr name2 env e1 >>= fun (rt, env) ->
        infer_expr name (add_vars env rt) e2
     | M_normal_pattern (Pattern (_annot, CaseBase (mname2,_cbt))) ->
        let name2 = sym_or_fresh mname2 in
        infer_pexpr name2 env e1 >>= fun (rt, env) ->
        infer_expr name (add_vars env rt) e2
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
        infer_expr name (add_vars env rt) e2
     | Pattern (_annot, CaseCtor _) ->
        failwith "todo ctor pattern"
     end
  | M_Esseq (p, e1, e2) ->
     begin match p with 
     | Pattern (_annot, CaseBase (mname2,_cbt)) ->
        let name2 = sym_or_fresh mname2 in
        infer_expr name2 env e1 >>= fun (rt, env) ->
        infer_expr name (add_vars env rt) e2
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


let check_expr (type a bty) fname env (e : (a,bty) mu_expr) ret = 
  let (M_Expr (annots, _)) = e in
  let loc = Annot.get_loc_ annots in
  let name = Sym.fresh () in    (* fix *)
  infer_expr name env e >>= fun (t, env) ->
  subtype loc env t ret >>= fun env ->
  return env






let check_function_body (type a bty) genv name (body : (a,bty) mu_expr) decl_typ = 
  let (F (A args, ret)) = decl_typ in
  let env = with_fresh_local genv in
  let env = add_vars env args in
  check_expr name env body ret >>= fun _env ->
  return ()



let embed_fun_proc body = 
  let (M_Pexpr (annots, _, _)) = body in
  M_Expr (annots, M_Epure (body))



let check_function (type bty a) genv fsym (fn : (bty,a) mu_fun_map_decl) = 

  let forget = 
    filter_map (function (_,T.A t) -> Some t | _ -> None) in


  let binding_of_core_base_type loc (sym,cbt) = 
    bt_of_core_base_type loc cbt >>= fun bt ->
    return (sym, T.A bt)
  in

  let check_consistent loc decl args ret = 
    mapM (binding_of_core_base_type loc) args >>= fun args ->
    binding_of_core_base_type loc ret >>= fun ret ->
    let (F (A decl_args, R decl_ret)) = decl in
    if BT.types_equal (forget decl_args) (forget args) &&
         BT.types_equal (forget decl_ret) (forget [ret])
    then return ()
    else 
      let defn = F (A args,R [ret]) in
      fail (Inconsistent_fundef {loc; decl; defn = defn})
  in

  match fn with
  | M_Fun (ret, args, body) ->
     let loc = Loc.unknown in
     lookup loc genv.fun_decls fsym >>= fun decl ->
     let (loc,decl_typ,ret_name) = decl in
     check_consistent loc decl_typ args (ret_name,ret) >>
     check_function_body genv fsym (embed_fun_proc body) decl_typ
  | M_Proc (loc, ret, args, body) ->
     lookup loc genv.fun_decls fsym >>= fun decl ->
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
    let ft = IT.Num (of_string f) in
    let tt = IT.Num (of_string t) in
    let constr name = (name %>= ft) %& (name %<= tt) in
    (BT.Int, constr)
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
     (BT.Bool, None)
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
  | Void -> (* check *)
     return (Unit, None)
  | Basic (Integer it) -> 
     return (bt_and_constr_of_integerType it)
  | Basic (Floating _) -> 
     fail (Unsupported {loc; unsupported = "floats"} )
  | Array (ct, _maybe_integer) -> 
     return (Array, None)
  | Function _ -> 
     fail (Unsupported {loc; unsupported = "function pointers"})
  | Pointer (_qualifiers, ctype) ->
     return (Loc, None)
  | Atomic ct ->              (* check *)
     bt_and_constr_of_ctype ct
  | Struct sym -> 
     return (Struct sym, None)
  | Union sym ->
     failwith "todo: union types"


let record_fun sym (loc,_attrs,ret_ctype,args,is_variadic,_has_proto) fun_decls =

  let binding_of_ctype ctype name = 
    bt_and_constr_of_ctype ctype >>= function
    | (bt, Some c) -> 
       return [(name, T.A bt); (Sym.fresh (), T.C (LC (c (S name))))]
    | (bt, None) -> 
       return [(name, T.A bt)]
  in

  let make_arg_t (msym,ctype) = binding_of_ctype ctype (sym_or_fresh msym) in
  if is_variadic 
  then fail (Variadic_function {loc; fn = sym})
  else 
    let ret_name = Sym.fresh () in
    mapM make_arg_t args >>= fun args_types ->
    let args_type = concat args_types in
    binding_of_ctype ret_ctype ret_name >>= fun ret_type ->
    let ft = F.F (A args_type,R ret_type) in
    let fun_decls = SymMap.add sym (loc, ft, ret_name) fun_decls in
    return fun_decls

let record_funinfo genv funinfo = 
  pmap_foldM record_fun funinfo genv.fun_decls >>= fun fun_decls ->
  return { genv with fun_decls = fun_decls }



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
            fields @ [(sym, T.A bt); (Sym.fresh (), T.C (LC (c (S sym))))]
         | (bt, None) -> 
            fields @ [(sym, T.A bt)]
       in
       return (names, fields)
     ) ([],[]) fields >>= fun (names,fields) ->

     let struct_decls = SymMap.add sym fields genv.struct_decls in
     let names = fold_left (fun m (k,v) -> NameMap.add k v m) genv.names names in
     return { genv with names = names; struct_decls = struct_decls }

let record_tagDefs genv tagDefs = 
  pmap_foldM record_tagDef tagDefs genv










let test_infer_expr () = 
  failwith "not implemented"


let pp_fun_map_decl funinfo = 
  let pp = Pp_core.All.pp_funinfo_with_attributes funinfo in
  print_string (Pp_utils.to_plain_string pp)




let check mu_file =
  let env = empty_global in
  record_tagDefs env mu_file.mu_tagDefs >>= fun env ->
  record_funinfo env mu_file.mu_funinfo >>= fun env ->
  check_functions env mu_file.mu_funs

let check_and_report core_file = 
  match check core_file with
  | Result () -> ()
  | Exception err -> print_endline (pp err)
