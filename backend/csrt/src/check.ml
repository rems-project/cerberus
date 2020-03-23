(* open Lem_pervasives  *)
open Core 
open Mucore
open Impl_mem
open Nat_big_num
open Sexplib
open Printf




type num = Nat_big_num.num

let concatmap (f : 'a -> 'b list) (xs : 'a list) : 'b list = 
  List.concat (List.map f xs)

let rec filter_map (f : 'a -> 'b option) (xs : 'a list) : 'b list = 
  match xs with
  | [] -> []
  | x :: xs ->
     match f x with
     | None -> filter_map f xs
     | Some y -> y :: filter_map f xs




(* error monad *)

module Ex = struct

  type ('a,'e) m = ('a,'e) Exception.exceptM
  let return : 'a -> ('a,'e) m = Exception.except_return
  let fail : 'e -> ('a,'e) m = Exception.fail
  let (>>=) = Exception.except_bind
  let (>>) m m' = m >>= fun () -> m'
  let liftM = Exception.except_fmap
  let seq = Exception.except_sequence
  let of_maybe = Exception.of_maybe
  let to_bool = Exception.to_bool
  let mapM = Exception.except_mapM
  let concatmapM f l = 
    seq (List.map f l) >>= fun xs ->
    return (List.concat xs)

  let pmap_foldM 
        (f : 'k -> 'x -> 'y -> ('y,'e) m)
        (map : ('k,'x) Pmap.map) (init: 'y) : ('y,'e) m =
    Pmap.fold (fun k v a -> a >>= f k v) map (return init)

  let pmap_iterM f m = 
    Pmap.fold (fun k v a -> a >> f k v) 
      m (return ())
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

  let of_tsymbol (s : 'bty Mucore.tsymbol) = 
    let (TSym (_, _, sym)) = s in sym

  let lof_tsymbol (s : 'bty Mucore.tsymbol) = 
    let (TSym (annots, _, sym)) = s in 
    (sym, Annot.get_loc_ annots)

  let compare = Symbol.symbol_compare

  let parse (env : t StringMap.t) name = 
    match StringMap.find_opt name env with
    | Some sym -> return sym
    | None -> fail (sprintf "unbound variable %s" name)

  let subst sym sym' symbol : t = 
    if symbol = sym then sym' else symbol

end

module Id = struct
  type id = Symbol.identifier
  type mid = id option
  let pp_id (Symbol.Identifier (_,s)) = s
end


module SymMap = Map.Make(Sym)







let parse_error (t : string) (sx : Sexp.t) = 
  let err = sprintf "unexpected %s: %s" t (Sexp.to_string sx) in
  fail err


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

    | List of t list

    | V of Sym.t
    | F of Id.id

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

    | List its -> sprintf "(list (%s))" 
                    (String.concat " " (List.map pp its))

    | F id -> Id.pp_id id
    | V sym -> Sym.pp sym



  let rec parse_sexp (env : Sym.t StringMap.t) sx = 
    match sx with

    | Sexp.Atom str when Str.string_match (Str.regexp "[0-9]+") str 0 ->
       return (Num (Nat_big_num.of_string str))
    | Sexp.Atom "true" -> 
       return (Bool true)
    | Sexp.Atom "false" -> 
       return (Bool false)

    | Sexp.List [o1;Sexp.Atom "+";o2] -> 
       parse_sexp env o1 >>= fun o1 ->
       parse_sexp env o2 >>= fun o2 ->
       return (Add (o1, o2))
    | Sexp.List [o1;Sexp.Atom "-";o2] -> 
       parse_sexp env o1 >>= fun o1 ->
       parse_sexp env o2 >>= fun o2 ->
       return (Sub (o1, o2))
    | Sexp.List [o1;Sexp.Atom "*";o2] -> 
       parse_sexp env o1 >>= fun o1 ->
       parse_sexp env o2 >>= fun o2 ->
       return (Mul (o1, o2))
    | Sexp.List [o1;Sexp.Atom "/";o2] -> 
       parse_sexp env o1 >>= fun o1 ->
       parse_sexp env o2 >>= fun o2 ->
       return (Div (o1, o2))
    | Sexp.List [o1;Sexp.Atom "^";o2] -> 
       parse_sexp env o1 >>= fun o1 ->
       parse_sexp env o2 >>= fun o2 -> 
       return (Exp (o1, o2))
    | Sexp.List [Sexp.Atom "app"; o1;o2] -> 
       parse_sexp env o1 >>= fun o1 ->
       parse_sexp env o2 >>= fun o2 ->
       return (App (o1, o2))
    | Sexp.List [Sexp.Atom "rem_t";o1;o2] -> 
       parse_sexp env o1 >>= fun o1 ->
       parse_sexp env o2 >>= fun o2 ->
       return (Rem_t (o1, o2))
    | Sexp.List [Sexp.Atom "rem_f";o1;o2] -> 
       parse_sexp env o1 >>= fun o1 ->
       parse_sexp env o2 >>= fun o2 ->
       return (Rem_f (o1, o2))
    | Sexp.List [o1;Sexp.Atom "=";o2]  -> 
       parse_sexp env o1 >>= fun o1 ->
       parse_sexp env o2 >>= fun o2 ->
       return (EQ (o1, o2))
    | Sexp.List [o1;Sexp.Atom "<>";o2] -> 
       parse_sexp env o1 >>= fun o1 ->
       parse_sexp env o2 >>= fun o2 ->
       return (NE (o1, o2))
    | Sexp.List [o1;Sexp.Atom "<";o2] -> 
       parse_sexp env o1 >>= fun o1 ->
       parse_sexp env o2 >>= fun o2 ->
       return (LT (o1, o2))
    | Sexp.List [o1;Sexp.Atom ">";o2]  -> 
       parse_sexp env o1 >>= fun o1 ->
       parse_sexp env o2 >>= fun o2 ->
       return (GT (o1, o2))
    | Sexp.List [o1;Sexp.Atom "<=";o2] -> 
       parse_sexp env o1 >>= fun o1 ->
       parse_sexp env o2 >>= fun o2 ->
       return (LE (o1, o2))
    | Sexp.List [o1;Sexp.Atom ">=";o2] -> 
       parse_sexp env o1 >>= fun o1 ->
       parse_sexp env o2 >>= fun o2 ->
       return (GE (o1, o2))

    | Sexp.List [Sexp.Atom "null"; o1] -> 
       parse_sexp env o1 >>= fun o1 ->
       return (Null o1)
    | Sexp.List [o1; Sexp.Atom "&"; o2] -> 
       parse_sexp env o1 >>= fun o1 ->
       parse_sexp env o2 >>= fun o2 ->
       return (And (o1, o2))
    | Sexp.List [o1; Sexp.Atom "|"; o2] -> 
       parse_sexp env o1 >>= fun o1 ->
       parse_sexp env o2 >>= fun o2 ->
       return (Or (o1, o2))
    | Sexp.List [Sexp.Atom "not"; o1] -> 
       parse_sexp env o1 >>= fun o1 ->
       return (Not o1)

    | Sexp.List [Sexp.Atom "list"; List its] -> 
       mapM (parse_sexp env) its >>= fun its ->
       return (List its)

    | Sexp.Atom str -> 
       begin match Sym.parse env str with
       | Result sym -> return (V sym)
       | _ -> return (F (Identifier (Location_ocaml.unknown, str)))
       end

    | t -> 
       parse_error "index term" t


  let rec subst (sym : Sym.t) (sym' : Sym.t) it : t = 
    match it with
    | Num _ -> it
    | Bool _ -> it

    | Add (it, it') -> Add (subst sym sym' it, subst sym sym' it')
    | Sub (it, it') -> Sub (subst sym sym' it, subst sym sym' it')
    | Mul (it, it') -> Mul (subst sym sym' it, subst sym sym' it')
    | Div (it, it') -> Div (subst sym sym' it, subst sym sym' it')
    | Exp (it, it') -> Exp (subst sym sym' it, subst sym sym' it')
    | App (it, it') -> App (subst sym sym' it, subst sym sym' it')
    | Rem_t (it, it') -> Rem_t (subst sym sym' it, subst sym sym' it')
    | Rem_f (it, it') -> Rem_f (subst sym sym' it, subst sym sym' it')

    | EQ (it, it') -> EQ (subst sym sym' it, subst sym sym' it')
    | NE (it, it') -> NE (subst sym sym' it, subst sym sym' it')
    | LT (it, it') -> LT (subst sym sym' it, subst sym sym' it')
    | GT (it, it') -> GT (subst sym sym' it, subst sym sym' it')
    | LE (it, it') -> LE (subst sym sym' it, subst sym sym' it')
    | GE (it, it') -> GE (subst sym sym' it, subst sym sym' it')

    | Null it -> Null (subst sym sym' it)
    | And (it, it') -> And (subst sym sym' it, subst sym sym' it')
    | Or (it, it') -> Or (subst sym sym' it, subst sym sym' it')
    | Not it -> Not (subst sym sym' it)


    | List its -> List (List.map (fun it -> subst sym sym' it) its)

    | V symbol -> V (Sym.subst sym sym' symbol)
    | F id -> F id

end


open IT

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
    | Tuple bts -> sprintf "(tuple (%s))" (String.concat " " (List.map pp bts))
    | Struct sym -> sprintf "(struct %s)" (Sym.pp sym)
  
  let rec parse_sexp (env : Sym.t StringMap.t) sx = 
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
       parse_sexp env bt >>= fun bt -> 
       return (List bt)
    | Sexp.List [Sexp.Atom "tuple"; Sexp.List bts] -> 
       mapM (parse_sexp env) bts >>= fun bts ->
       return (Tuple bts)
    | Sexp.List [Sexp.Atom "struct"; Sexp.Atom id] -> 
       Sym.parse env id >>= fun id ->
       return (Struct id)
    | a -> parse_error "base type" a

  let subst _sym _sym' t = t

end


open BT

module RE = struct

  type t = 
    | Block of IT.t * IT.t
    | Int of IT.t * IT.t (* location and value *)
    | Points of IT.t * IT.t
    | Array of IT.t * IT.t
   (* Array (pointer, list pointer) *)

  let rec pp = function
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

  
  let rec parse_sexp (env : Sym.t StringMap.t) sx = 
    let open Sexp in
    match sx with 
    | Sexp.List [Sexp.Atom "block";it1;it2] -> 
       IT.parse_sexp env it1 >>= fun it1 ->
       IT.parse_sexp env it2 >>= fun it2 ->
       return (Block (it1, it2))
    | Sexp.List [Sexp.Atom "int"; it1; it2] ->
       IT.parse_sexp env it1 >>= fun it1 ->
       IT.parse_sexp env it2 >>= fun it2 ->
       return (Int (it1, it2))
    | Sexp.List [Sexp.Atom "array"; it1; it2] ->
       IT.parse_sexp env it1 >>= fun it1 ->
       IT.parse_sexp env it2 >>= fun it2 ->
       return (Array (it1, it2))
    | Sexp.List [Sexp.Atom "points"; it1; it2] ->
       IT.parse_sexp env it1 >>= fun it1 ->
       IT.parse_sexp env it2 >>= fun it2 ->
       return (Points (it1, it2))
    | t -> parse_error "resource type" t

  let subst sym sym' t = 
    match t with
    | Block (it, it') -> 
       Block (IT.subst sym sym' it, IT.subst sym sym' it')
    | Int (it, it') -> 
       Int (IT.subst sym sym' it, IT.subst sym sym' it')
    | Points (it, it') -> 
       Points (IT.subst sym sym' it, IT.subst sym sym' it')
    | Array (it, it') -> 
       Array (IT.subst sym sym' it, IT.subst sym sym' it')

end


module LS = struct

  type t = 
    | Base of BT.t
    | List of BT.t
    | Fun of t * t


  let rec pp = function
    | List ls -> 
       sprintf "(list %s)" 
         (BT.pp ls)
    | Fun (ls1,ls2) -> 
       sprintf "(%s -> %s)" 
         (pp ls1)
         (pp ls2)
    | Base bt -> 
         BT.pp bt
  
  let rec parse_sexp (env : Sym.t StringMap.t) sx =
    match sx with
    | Sexp.List [Sexp.Atom "list"; a] ->
       BT.parse_sexp env a >>= fun a ->
       return (List a)
    | Sexp.List [o1; Sexp.Atom "->"; o2] ->
       parse_sexp env o1 >>= fun o1 ->
       parse_sexp env o2 >>= fun o2 ->
       return (Fun (o1, o2))
    | sx ->
       BT.parse_sexp env sx >>= fun bt ->
       return (Base bt)

  let subst _sym _sym' t = t

end


module LC = struct

  type t = LC of IT.t

  let pp (LC c) = IT.pp c

  let parse_sexp env s = 
    IT.parse_sexp env s >>= fun it ->
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

  let parse_sexp (env : Sym.t StringMap.t) s = 
    let open Sexp in
    match s with
    | Sexp.List [Sexp.Atom id; Sexp.Atom ":"; t] ->
       let sym = Sym.fresh_pretty id in
       let env = StringMap.add id sym env in
       BT.parse_sexp env t >>= fun bt ->
       return ((sym, A bt), env)
    | Sexp.List [Sexp.Atom "Logical"; Sexp.Atom id; Sexp.Atom ":"; ls] ->
       let sym = Sym.fresh_pretty id in
       let env = StringMap.add id sym env in
       LS.parse_sexp env ls >>= fun ls ->
       return ((sym, L ls), env)
    | Sexp.List [Sexp.Atom "Resource"; Sexp.Atom id; Sexp.Atom ":"; re] ->
       let sym = Sym.fresh_pretty id in
       let env = StringMap.add id sym env in
       RE.parse_sexp env re >>= fun re ->
       return ((sym, R re), env)
    | Sexp.List [Sexp.Atom "Constraint"; Sexp.Atom id; Sexp.Atom ":"; lc] ->
       let sym = Sym.fresh_pretty id in
       let env = StringMap.add id sym env in
       LC.parse_sexp env lc >>= fun lc ->
       return ((sym, C lc), env)
    | t -> 
       parse_error "return type" t
         
  let subst sym sym' (symbol, t) = 
    (Sym.subst sym sym' symbol, T.subst sym sym' t)

end


module Bs = struct

  type t = B.t list

  let pp ts = 
    String.concat " , " (List.map B.pp ts)

  let parse_sexp fstr (env : Sym.t StringMap.t) s = 
    let rec aux (env : Sym.t StringMap.t) acc ts = 
      match ts with
      | [] -> return (List.rev acc, env)
      | b :: bs ->
         B.parse_sexp env b >>= fun (b, env) ->
         aux env (b :: acc) bs
    in
    match s with
    | Sexp.List ts -> aux env [] ts
    | t -> parse_error fstr t

  let subst sym sym' bs = 
    List.map (B.subst sym sym') bs

end


type fbinding = Id.mid * T.t
type fbindings = fbinding list


module A = struct
  type t = A of Bs.t
  let pp (A ts) = Bs.pp
  let parse_sexp env s = 
    Bs.parse_sexp "argument type" env s >>= fun (bs, env) ->
    return (A bs, env)
  let subst sym sym' (A ts) = 
    A (Bs.subst sym sym' ts)
end


module R = struct
  type t = R of Bs.t
  let pp (R ts) = Bs.pp
  let parse_sexp env s = 
    Bs.parse_sexp "return type" env s >>= fun (bs, env) ->
    return (R bs, env)
  let subst sym sym' (R ts) = 
    R (Bs.subst sym sym' ts)
end


module F = struct
  type t = F of A.t * R.t
  let forget (F (A args, R ret)) = 
    let args = List.filter (function (_,T.A _) -> true | _ -> false) args in
    let ret = List.filter (function (_,T.A _) -> true | _ -> false) ret in
    F (A args, R ret)
  let subst sym sym' (F (a,r)) = 
    F (A.subst sym sym' a, R.subst sym sym' r)
end
  

open A
open R
open F

      

module Err = struct

  type subtype_error = 
    | SE_Surplus_A of (Sym.t * BT.t)
    | SE_Surplus_L of (Sym.t * LS.t)
    | SE_Surplus_R of (Sym.t * RE.t)
    | SE_Missing_A of (Sym.t * BT.t)
    | SE_Missing_L of (Sym.t * LS.t)
    | SE_Missing_R of (Sym.t * RE.t)
    | SE_Mismatch_ret of B.t * B.t
    | SE_Unsat_constraint of Sym.t * LC.t

  type type_error = 
    | Unsupported of { 
        loc: Loc.t;
        it: string; 
      }
    | Subtype_error of 
        subtype_error * Loc.t
    | Unbound_symbol of 
        Sym.t
    | Wrong_bt of { 
        e: Sym.t; 
        e_has: BT.t; 
        e_loc: Loc.t;
        expected: BT.t;
        context: Loc.t;
      }
    | Surplus_fun_arg of Loc.t
    | Missing_fun_arg of Loc.t
    | Inconsistent_fundef of {
        loc: Loc.t;
        decl: F.t;
        defn: F.t;
      }
    | Variadic_function of {
        loc: Loc.t;
        fn: Sym.t;
      }


  let unsupported loc s = 
    fail (Unsupported { loc = loc; it = s })

  let wrong_bt (sym, has, loc) (expected, kloc) = 
    fail (Wrong_bt { e = sym; e_has = has; e_loc = loc; 
                     expected = expected; context = kloc })

  let surplus_fun_arg loc = 
    fail (Surplus_fun_arg loc)

  let missing_fun_arg loc = 
    fail (Missing_fun_arg loc)


  let subtype_error loc se = 
    fail (Subtype_error (se, loc))

  let subtype_surplus_A loc n b = 
    subtype_error loc (SE_Surplus_A (n,b))

  let subtype_surplus_L loc n b = 
    subtype_error loc (SE_Surplus_L (n,b))

  let subtype_surplus_R loc n b = 
    subtype_error loc (SE_Surplus_R (n,b))

  let subtype_missing_A loc n b = 
    subtype_error loc (SE_Missing_A (n,b))

  let subtype_missing_L loc n b = 
    subtype_error loc (SE_Missing_L (n,b))

  let subtype_missing_R loc n b = 
    subtype_error loc (SE_Missing_R (n,b))

  let subtype_mismatch_ret loc b b' = 
    subtype_error loc (SE_Mismatch_ret (b, b'))

  let subtype_unsat_constraint loc sym lc = 
    subtype_error loc (SE_Unsat_constraint (sym, lc))

  let inconsistent_fundef loc decl defn = 
    fail (Inconsistent_fundef {loc = loc; decl = decl; defn = defn})

  let variadic_function loc fn = 
    fail (Variadic_function {loc = loc; fn = fn})


  let pp = function 
    | Unsupported {loc; it} ->
       sprintf "Line %s. unsupported feature: %s" 
         (Loc.pp loc) it
    | Subtype_error (SE_Surplus_A (_name, t), loc) ->
       sprintf "Line %s. returning unexpected value of type %s" 
         (Loc.pp loc) (BT.pp t)
        


end

open Err


type global_env = 
  { struct_decls : fbindings SymMap.t ; 
    fun_decls : (Loc.t * F.t * Sym.t) SymMap.t } (* third item is return name *)

type local_env = 
  { a: BT.t SymMap.t; 
    l: LS.t SymMap.t; 
    r: RE.t SymMap.t; 
    c: LC.t SymMap.t; }

type env = 
  { local : local_env ; 
    global : global_env }

let empty_global = 
  { struct_decls = SymMap.empty; 
    fun_decls = SymMap.empty }

let empty_local = 
  { a = SymMap.empty;
    l = SymMap.empty;
    r = SymMap.empty;
    c = SymMap.empty; }

let empty_env = 
  { local = empty_local; 
    global = empty_global }


let add_avar env (sym, t) = 
  { env with local = { env.local with a = SymMap.add sym t env.local.a } }
let add_lvar env (sym, t) = 
  { env with local = { env.local with l = SymMap.add sym t env.local.l } }
let add_rvar env (sym, t) = 
  { env with local = { env.local with r = SymMap.add sym t env.local.r } }
let add_cvar env (sym, t) = 
  { env with local = { env.local with c = SymMap.add sym t env.local.c } }


let add_avars env bindings = 
  List.fold_left add_avar env bindings

let add_var env (sym, t) = 
  match t with
  | T.A t -> add_avar env (sym, t)
  | T.L t -> add_lvar env (sym, t)
  | T.R t -> add_rvar env (sym, t)
  | T.C t -> add_cvar env (sym, t)

let add_vars env bindings = 
  List.fold_left add_var env bindings

let lookup (loc : Loc.t) (env: 'v SymMap.t) (sym: Sym.t) =
  of_maybe (Unbound_symbol sym) (SymMap.find_opt sym env)






let core_type_value ov = 
  Core_typing.typeof_object_value 
    Location_ocaml.unknown 
    Core_typing_aux.empty_env ov

(* let rec sizeof_ov ov = 
 *   Impl_mem.sizeof_ival (core_type_value ov) *)

let ensure_type (sym, has, loc) (expected, kloc) = 
  if has = expected 
  then return ()
  else wrong_bt (sym, has, loc) (expected, kloc)




let make_binop op (v1 : IT.t) (v2 : IT.t) =
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

let bt_of_binop (op : Core.binop) : ((BT.t * BT.t) * BT.t) = 
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

          


let bt_of_core_object_type loc = function
  | OTy_integer -> 
     return BT.Int
  | OTy_floating -> 
     unsupported loc "float"
  | OTy_pointer -> 
     return BT.Loc
  | OTy_array cbt -> 
     return BT.Array
  | OTy_struct sym -> 
     return (Struct sym)
  | OTy_union _sym -> 
     unsupported loc "union types"

let rec bt_of_core_base_type loc = function
  | Core.BTy_unit -> 
     return BT.Unit
  | Core.BTy_boolean -> 
     return BT.Bool
  | Core.BTy_ctype -> 
     unsupported loc "ctype"
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
     failwith "BTy_storable"

let binding_of_core_base_type loc (sym,ctype) = 
  bt_of_core_base_type loc ctype >>= fun bt ->
  return (sym, T.A bt)


let make_int_type f t = 
  let ft = IT.Num (of_string f) in
  let tt = IT.Num (of_string t) in
  let constr name = (name %>= ft) %& (name %<= tt) in
  (BT.Int, constr)

(* according to https://en.wikipedia.org/wiki/C_data_types *)
(* todo: check *)
let bt_and_constr_of_integerBaseType signed ibt = 
  let make = make_int_type in
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
  | _, Ctype.IntN_t n -> 
     failwith "todo standard library types"
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
     unsupported loc "floats"
  | Array (ct, _maybe_integer) -> 
     return (Array, None)
  | Function _ -> 
     unsupported loc "function pointers"
  | Pointer (_qualifiers, ctype) ->
     return (Loc, None)
  | Atomic ct ->              (* check *)
     bt_and_constr_of_ctype ct
  | Struct sym -> 
     return (Struct sym, None)
  | Union sym ->
     failwith "todo: union types"

let binding_of_ctype ctype name = 
  bt_and_constr_of_ctype ctype >>= function
  | (bt, Some c) -> 
     return [(name, T.A bt); (Sym.fresh (), T.C (LC (c (V name))))]
  | (bt, None) -> 
     return [(name, T.A bt)]

let fbinding_of_ctype ctype (id : Id.id) = 
  bt_and_constr_of_ctype ctype >>= function
  | (bt, Some c) -> 
     return [(Some id, T.A bt); (None, T.C (LC (c (F id))))]
  | (bt, None) -> 
     return [(Some id, T.A bt)]

let sym_or_fresh (msym : Sym.t option) : Sym.t = 
  match msym with
  | Some sym -> sym
  | None -> Sym.fresh ()


let integer_value_to_num iv = 
  match (Impl_mem.eval_integer_value iv) with
  | Some i -> i
  | None -> failwith "integer_value_to_num: None"

let infer_object_value loc name ov = 
  match ov with
  | M_OVinteger iv ->
     let constr = LC (V name %= Num (integer_value_to_num iv)) in
     let t = R [(name, A BT.Int); (Sym.fresh (), C constr)] in
     return t
  | M_OVfloating iv ->
     unsupported loc "floats"
  | M_OVpointer p ->
     Impl_mem.case_ptrval p
       ( fun _cbt -> 
         let constr = LC (Null (V name)) in
         let t = R [(name, A (BT.Loc)); (Sym.fresh (), C constr)] in
         return t )
       ( fun sym -> 
         unsupported loc "function pointers" )
       ( fun _prov loc ->
         let constr = LC (V name %= Num loc) in
         let t = R [(name, A (BT.Loc)); (Sym.fresh (), C constr)] in
         return t )
       ( fun _ ->
         unsupported loc "unspecified pointer value" )
  | M_OVarray _ ->
     failwith "todo: array"
  | M_OVstruct (sym, fields) ->
     failwith "todo: struct"
  | M_OVunion _ -> 
     failwith "todo: union types"

let infer_loaded_value loc name lv = 
  match lv with
 | M_LVspecified ov ->
    infer_object_value loc name ov 
 | M_LVunspecified _ct ->
    failwith "todo: LV unspecified"


let infer_value loc name env v = 
  match v with
  | M_Vobject ov ->
     infer_object_value loc name ov
  | M_Vloaded lv ->
     infer_loaded_value loc name lv
  | M_Vunit ->
     return (R [(name, A BT.Unit)])
  | M_Vtrue ->
     let constr = LC (V name) in
     let t = R [(name, A BT.Bool); (Sym.fresh (), C constr)] in
     return t
  | M_Vfalse -> 
     let constr = LC (Not (V name)) in
     let t = R [(name, A BT.Bool); (Sym.fresh (), C constr)] in
     return t
  | M_Vctype ct ->
     failwith "todo ctype"
  | M_Vlist (cbt, tsyms) ->
     bt_of_core_base_type loc cbt >>= fun i_t ->
     let check_item tsym =
       let (sym,iloc) = Sym.lof_tsymbol tsym in
       lookup loc env.local.a sym >>= fun typ ->
       ensure_type (sym, typ, iloc) (i_t, loc) in
     let _ = List.map check_item tsyms in
     (* maybe record list length? *)
     let t = R [(name, A (BT.List i_t))] in
     return t
  | M_Vtuple tsyms ->
     let syms = List.map Sym.of_tsymbol tsyms in
     mapM (lookup loc env.local.a) syms >>= fun ts ->
     let t = R [(name, A (BT.Tuple ts))] in
     return t


(* let call_typ loc_call env name args =
 *   let rec check env decl_args args = 
 *     match decl_args, args with
 *     | A [], [] -> return true
 *     | A [], _ -> surplus_fun_arg loc_call
 *     | A _, [] -> missing_fun_arg loc_call
 * 
 *   in
 * 
 *   match name with
 *   | Core.Impl _ -> 
 *      failwith "todo implementation-defined constrant"
 *   | Core.Sym sym ->
 *      lookup loc_call env.global.fun_decls sym >>= fun decl ->
 *      let (loc,decl_typ,_ret_name) = decl in 
 *      let (F (A decl_args, decl_ret)) = decl_typ in
 *      
 *      return () *)

let call_typ _ _ _ _ = failwith "todo"


let rec infer_pexpr name env (M_Pexpr (annots, _bty, pe)) = 
  let loc = Annot.get_loc_ annots in
  match pe with
  | M_PEsym sym ->
     lookup loc env.local.a sym >>= fun b ->
     return (R [(name, T.A b)])
  | M_PEimpl _ ->
     failwith "todo PEimpl"
  | M_PEval v ->
     infer_value loc name env v
  | M_PEconstrained _ ->
     failwith "todo PEconstrained"
  | M_PEundef _ ->
     failwith "todo PEundef"
  | M_PEerror _ ->
     failwith "todo PEerror"
  | M_PEctor _ ->
     failwith "todo PEctor"
  | M_PEcase _ ->
     failwith "todo PEcase"
  | M_PEarray_shift _ ->
     failwith "todo PEarray_shift"
  | M_PEmember_shift _ ->
     failwith "todo PEmember_shift"
  | M_PEnot sym ->
     let (sym,a_loc) = Sym.lof_tsymbol sym in
     lookup loc env.local.a sym >>= fun t ->
     ensure_type (sym, t, a_loc) (BT.Bool, loc) >>
     let constr = LC ((V name) %= Not (V sym)) in
     let t = R [(name, A t); (name, C constr)] in
     return t
  | M_PEop (op,sym1,sym2) ->
     let (sym1, loc1) = Sym.lof_tsymbol sym1 in
     let (sym2, loc2) = Sym.lof_tsymbol sym2 in
     lookup loc env.local.a sym1 >>= fun t1 ->
     lookup loc env.local.a sym2 >>= fun t2 ->
     let ((st1,st2),rt) = bt_of_binop op in
     ensure_type (sym1, t1, loc1) (st1, loc) >>
     ensure_type (sym2, t2, loc2) (st2, loc) >>
     let constr = LC (V name %= (make_binop op (V sym1) (V sym2))) in
     let t = R [(name, A rt); (Sym.fresh (), C constr)] in
     return t
  | M_PEstruct _ ->
     failwith "todo PEstruct"
  | M_PEunion _ ->
     failwith "todo PEunion"
  | M_PEcfunction _ ->
     failwith "todo PEcfunction"
  | M_PEmemberof _ ->
     failwith "todo M_PEmemberof"
  | M_PEcall _ ->
     failwith "todo M_PEcall"
  | M_PElet (p, e1, e2) ->
     (* todo: check against cbt? *)
     begin match p with 
     | Pattern (_annot, CaseBase (mname2,_cbt)) ->
        let name2 = sym_or_fresh mname2 in
        infer_pexpr name2 env e1 >>= fun (R rt) ->
        infer_pexpr name (add_vars env rt) e1
     | Pattern (_annot, CaseCtor _) ->
        failwith "todo ctor pattern"
     end
  | M_PEif (sym1,sym2,sym3) ->
     let sym1, loc1 = Sym.lof_tsymbol sym1 in
     let sym2, loc2 = Sym.lof_tsymbol sym2 in
     let sym3, loc3 = Sym.lof_tsymbol sym3 in
     lookup loc env.local.a sym1 >>= fun t1 ->
     lookup loc env.local.a sym2 >>= fun t2 ->
     lookup loc env.local.a sym3 >>= fun t3 ->
     ensure_type (sym1, t1, loc1) (BT.Bool, loc) >>
     ensure_type (sym3, t3, loc3) (t2, loc) >>
     let constr = 
       LC ( (V sym1 %& (V name %= V sym2)) %| 
              ((Not (V sym1)) %& (V name %= V sym3)) )
     in
     let t = R [(name, A t2); (Sym.fresh (), C constr)] in
     return t
  | M_PEis_scalar _ ->
     failwith "todo M_PEis_scalar"
  | M_PEis_integer _ ->
     failwith "todo M_PEis_integer"
  | M_PEis_signed _ ->
     failwith "todo M_PEis_signed"
  | M_PEis_unsigned _ ->
     failwith "todo M_PEis_unsigned"
  | M_PEbmc_assume _ ->
     failwith "todo M_PEbmc_assume"
  | M_PEare_compatible _ ->
     failwith "todo M_PEare_compatible"





let constraints_hold env (LC c) = 
  true                          (* todo: call z3 *)


let resource_typ_equal env t1 t2 = 
  t1 = t2                       (* todo: maybe up to variable
                                   instantiations or so *)


let subtype loc env (R.R r1) (R.R r2) = 

  let rec check env rt1 rt2 =
    match rt1, rt2 with
    | [], [] -> 
       return env
    | (n, T.A r1) :: _, [] -> 
       subtype_surplus_A loc n r1
    | (n, T.L r1) :: _, [] -> 
       subtype_surplus_L loc n r1
    | (n, T.R r1) :: _, [] -> 
       subtype_surplus_R loc n r1
    | [], (n, T.A r2) :: _ -> 
       subtype_missing_A loc n r2
    | [], (n, T.L r2) :: _ -> 
       subtype_missing_L loc n r2
    | [], (n, T.R r2) :: _ -> 
       subtype_missing_R loc n r2
    | ((_, T.C c1) as r1) :: rt1', _ ->
       check (add_var env r1) rt1' rt2
    | _, (n2, T.C c2) :: rt2' ->
       if constraints_hold env c2 
       then check env rt1 rt2'
       else subtype_unsat_constraint loc n2 c2
    | ((_, T.A t1) as r1) :: rt1', (_, T.A t2) :: rt2'
           when t1 = t2 ->
       check (add_var env r1) rt1 rt2
    | ((_, T.L t1) as r1) :: rt1', (_, T.L t2) :: rt2'
         when t1 = t2 ->
       check (add_var env r1) rt1 rt2
    | (_, T.R t1) :: rt1', (_,T.R t2) :: rt2'
         when resource_typ_equal env t1 t2 ->
       check env rt1 rt2
    | r1 :: _, r2 :: _ ->
       subtype_mismatch_ret loc r1 r2
  in

  check env r1 r2




let check_expr fname env (M_Expr (annots, e)) ret = 
  let loc = Annot.get_loc_ annots in
  let name = Sym.fresh () in    (* fix *)
  match e with
  | M_Epure pe -> 
     infer_pexpr name env pe >>= fun t ->
     subtype loc env t ret >>= fun env ->
     return ()
  | M_Ememop _ ->
     failwith "todo ememop"
  | M_Eaction _ ->
     failwith "todo eaction"
  | M_Ecase _ ->
     failwith "todo ecase"
  | M_Elet _ ->
     failwith "todo elet"
  | M_Eif _ ->
     failwith "todo eif"
  | M_Eskip -> 
     failwith "todo eskip" 
  | M_Eccall _ ->
     failwith "todo eccall"
  | M_Eproc _ ->
     failwith "todo eproc"
  | M_Ewseq _ ->
     failwith "todo ewseq"
  | M_Esseq _ ->
     failwith "todo esseq"
  | M_Ebound _ ->
     failwith "todo ebound"
  | M_End _ ->
     failwith "todo end"
  | M_Esave _ ->
     failwith "todo esave"
  | M_Erun _ ->
     failwith "todo erun"
     


let test_infer_expr () = 
  failwith "not implemented"






let check_function_body env name body decl_typ = 
  let (F (A args, ret)) = decl_typ in
  let env = add_vars env args in
  check_expr name env body ret



let embed_fun_proc body = 
  let (M_Pexpr (annots, _, _)) = body in
  M_Expr (annots, M_Epure (body))



let check_function env fsym fn = 

  let check_consistent loc decl_typ args ret = 
    mapM (binding_of_core_base_type loc) args >>= fun args ->
    binding_of_core_base_type loc ret >>= fun ret ->
    let ft_def = F (A args,R [ret]) in 
    if forget ft_def = forget decl_typ 
    then return ()
    else inconsistent_fundef loc decl_typ ft_def
  in

  match fn with
  | M_Fun (ret, args, body) ->
     let loc = Loc.unknown in
     lookup loc env.global.fun_decls fsym >>= fun decl ->
     let (loc,decl_typ,ret_name) = decl in
     check_consistent loc decl_typ args (ret_name,ret) >>
     check_function_body env fsym (embed_fun_proc body) decl_typ
  | M_Proc (loc, ret, args, body) ->
     lookup loc env.global.fun_decls fsym >>= fun decl ->
     let (loc,decl_typ,ret_name) = decl in
     check_consistent loc decl_typ args (ret_name,ret) >>
     check_function_body env fsym body decl_typ
  | M_ProcDecl _
  | M_BuiltinDecl _ -> 
     return ()


let check_functions env fns =
  pmap_iterM (check_function env) fns

                             

let record_fun sym (loc,_attrs,ret_ctype,args,is_variadic,_has_proto) fun_decls =
  let make_arg_t (msym,ctype) = binding_of_ctype ctype (sym_or_fresh msym) in
  if is_variadic 
  then variadic_function loc sym
  else 
    let ret_name = Sym.fresh_pretty "__return_val__" in
    mapM make_arg_t args >>= fun args_types ->
    let args_type = List.concat args_types in
    binding_of_ctype ret_ctype ret_name >>= fun ret_type ->
    let ft = F.F (A args_type,R ret_type) in
    let fun_decls = SymMap.add sym (loc, ft, ret_name) fun_decls in
    return fun_decls

let record_funinfo env funinfo = 
  pmap_foldM record_fun funinfo env.global.fun_decls >>= fun fun_decls ->
  return { env with global = { env.global with fun_decls = fun_decls } }



let record_tagDef sym def (struct_decls : fbindings SymMap.t)=
  let make_field_and_constraint (id, (_attributes, _qualifier, ctype)) =
    fbinding_of_ctype ctype id in
  match def with
  | Ctype.UnionDef _ -> 
     failwith "todo: union types"
  | Ctype.StructDef fields ->
     concatmapM make_field_and_constraint fields >>= fun fields ->
     return (SymMap.add sym fields struct_decls)

let record_tagDefs env tagDefs = 
  pmap_foldM record_tagDef tagDefs env.global.struct_decls >>= fun struct_decls ->
  return { env with global = {env.global with struct_decls = struct_decls } }







let pp_fun_map_decl f = 
  let pp = Pp_core.All.pp_funinfo_with_attributes f in
  print_string (Pp_utils.to_plain_string pp)


let print_core_file core_file filename = 
  let pp = Pp_core.Basic.pp_file core_file in
  Pipeline.run_pp (Some (filename,"core")) pp
  (* write_file filename (Pp_utils.to_plain_pretty_string pp) *)

let init core_file mu_file = 
  Colour.do_colour := false;
  Tags.set_tagDefs core_file.tagDefs;
  pp_fun_map_decl core_file.funinfo;
  print_core_file core_file "out1";
  print_core_file (mu_to_core__file mu_file) "out2"
  

let check (core_file : unit Core.typed_file) =
  let mu_file = Core_anormalise.normalise_file core_file in
  let () = init core_file mu_file in
  let env = empty_env in
  record_tagDefs env mu_file.mu_tagDefs >>= fun env ->
  record_funinfo env mu_file.mu_funinfo >>= fun env ->
  check_functions env mu_file.mu_funs

let check_and_report core_file = 
  match check core_file with
  | Result () -> ()
  | Exception err -> print_endline (pp err)
