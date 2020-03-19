(* open Lem_pervasives  *)
open Core 
open Mucore
open Impl_mem
open Nat_big_num
open Sexplib
open Printf

let concatmap (f : 'a -> 'b list) (xs : 'a list) : 'b list = 
  List.concat (List.map f xs)

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

  let parse_opt (env : t StringMap.t) name = 
    StringMap.find_opt name env

  let parse (env : t StringMap.t) name = 
    match parse_opt env name with
    | Some sym -> sym
    | None -> failwith (sprintf "unbound variable %s" name)

end

module Id = struct
  type id = Symbol.identifier
  type mid = id option
  let pp_id (Symbol.Identifier (_,s)) = s
end


let pp_loc loc = 
  Pp_utils.to_plain_string (Location_ocaml.pp_location loc)


module SymMap = Map.Make(Sym)







type num = Nat_big_num.num

let parse_error (t : string) (sx : Sexp.t) = 
  let err = sprintf "unexpected %s: %s" t (Sexp.to_string sx) in
  raise (Invalid_argument err)

let unreachable () = failwith "unreachable"


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
       Num (Nat_big_num.of_string str)
    | Sexp.Atom "true" -> 
       Bool true
    | Sexp.Atom "false" -> 
       Bool false

    | Sexp.List [o1;Sexp.Atom "+";o2] -> 
       Add (parse_sexp env o1, parse_sexp env o2)
    | Sexp.List [o1;Sexp.Atom "-";o2] -> 
       Sub (parse_sexp env o1, parse_sexp env o2)
    | Sexp.List [o1;Sexp.Atom "*";o2] -> 
       Mul (parse_sexp env o1, parse_sexp env o2)
    | Sexp.List [o1;Sexp.Atom "/";o2] -> 
       Div (parse_sexp env o1, parse_sexp env o2)
    | Sexp.List [o1;Sexp.Atom "^";o2] -> 
       Exp (parse_sexp env o1, parse_sexp env o2)
    | Sexp.List [Sexp.Atom "app"; o1;o2] -> 
       App (parse_sexp env o1, parse_sexp env o2)
    | Sexp.List [Sexp.Atom "rem_t";o1;o2] -> 
       Rem_t (parse_sexp env o1, parse_sexp env o2)
    | Sexp.List [Sexp.Atom "rem_f";o1;o2] -> 
       Rem_f (parse_sexp env o1, parse_sexp env o2)

    | Sexp.List [o1;Sexp.Atom "=";o2]  -> 
       EQ (parse_sexp env o1, parse_sexp env o2)
    | Sexp.List [o1;Sexp.Atom "<>";o2] -> 
       NE (parse_sexp env o1, parse_sexp env o2)
    | Sexp.List [o1;Sexp.Atom "<";o2]  -> 
       LT (parse_sexp env o1, parse_sexp env o2)
    | Sexp.List [o1;Sexp.Atom ">";o2]  -> 
       GT (parse_sexp env o1, parse_sexp env o2)
    | Sexp.List [o1;Sexp.Atom "<=";o2] -> 
       LE (parse_sexp env o1, parse_sexp env o2)
    | Sexp.List [o1;Sexp.Atom ">=";o2] -> 
       GE (parse_sexp env o1, parse_sexp env o2)

    | Sexp.List [Sexp.Atom "null";op] -> 
       Null (parse_sexp env op)
    | Sexp.List [o1; Sexp.Atom "&"; o2] -> 
       And (parse_sexp env o1, parse_sexp env o2)
    | Sexp.List [o1; Sexp.Atom "|"; o2] -> 
       Or (parse_sexp env o1, parse_sexp env o2)
    | Sexp.List [Sexp.Atom "not";op] -> 
       Not (parse_sexp env op)

    | Sexp.List [Sexp.Atom "list"; List its] -> 
       let its = List.map (parse_sexp env) its in
       List its

    | Sexp.Atom str -> 
       begin match Sym.parse_opt env str with
       | Some sym -> V sym
       | None -> F (Identifier (Location_ocaml.unknown, str))
       end

    | t -> 
       parse_error "index term" t

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
    | Sexp.Atom "unit" -> Unit
    | Sexp.Atom "bool" -> Bool
    | Sexp.Atom "int" -> Int
    | Sexp.Atom "loc" -> Loc
    | Sexp.Atom "array" -> Array
    | Sexp.List [Sexp.Atom "list"; bt] -> List (parse_sexp env bt)
    | Sexp.List [Sexp.Atom "tuple"; Sexp.List bts] -> Tuple (List.map (parse_sexp env) bts)
    | Sexp.List [Sexp.Atom "struct"; Sexp.Atom id] -> Struct (Sym.parse env id)
    | a -> parse_error "base type" a

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
       Block (IT.parse_sexp env it1,
              IT.parse_sexp env it2)
    | Sexp.List [Sexp.Atom "int"; it1; it2] ->
       Int (IT.parse_sexp env it1, 
            IT.parse_sexp env it2)
    | Sexp.List [Sexp.Atom "array"; it1; it2] ->
       Array (IT.parse_sexp env it1, 
              IT.parse_sexp env it2)
    | Sexp.List [Sexp.Atom "points"; it1; it2] ->
       Points (IT.parse_sexp env it1, 
               IT.parse_sexp env it2)
    | t -> parse_error "resource type" t

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
       List (BT.parse_sexp env a)
    | Sexp.List [o1; Sexp.Atom "->"; o2] ->
       Fun (parse_sexp env o1, parse_sexp env o2)
    | Sexp.Atom _ -> 
       Base (BT.parse_sexp env sx)
    | ls -> parse_error "logical sort" ls

end



module T = struct

  type t = 
    | A of BT.t
    | L of LS.t
    | R of RE.t
    | C of IT.t

  let pp = function
    | (id, A typ) -> 
       sprintf "(%s : %s)" (Sym.pp id) (BT.pp typ)
    | (id, L ls)  -> 
       sprintf "(Logical %s : %s)" (Sym.pp id) (LS.pp ls)
    | (id, R re) -> 
       sprintf "(Resource %s : %s)" (Sym.pp id) (RE.pp re)
    | (id, C lc) -> 
       sprintf "(Constraint %s : %s)" (Sym.pp id) (IT.pp lc)

  let parse_sexp (env : Sym.t StringMap.t) s = 
    let open Sexp in
    match s with
    | Sexp.List [Sexp.Atom id; Sexp.Atom ":"; t] ->
       let sym = Sym.fresh_pretty id in
       let env = StringMap.add id sym env in
       ((sym, A (BT.parse_sexp env t)), env)
    | Sexp.List [Sexp.Atom "Logical"; Sexp.Atom id; Sexp.Atom ":"; ls] ->
       let sym = Sym.fresh_pretty id in
       let env = StringMap.add id sym env in
       ((sym, L (LS.parse_sexp env ls)), env)
    | Sexp.List [Sexp.Atom "Resource"; Sexp.Atom id; Sexp.Atom ":"; re] ->
       let sym = Sym.fresh_pretty id in
       let env = StringMap.add id sym env in
       ((sym, R (RE.parse_sexp env re)), env)
    | Sexp.List [Sexp.Atom "Constraint"; Sexp.Atom id; Sexp.Atom ":"; lc] ->
       let sym = Sym.fresh_pretty id in
       let env = StringMap.add id sym env in
       ((sym, C (IT.parse_sexp env lc)), env)
    | t -> 
       parse_error "rturn type" t
         
  type binding = Sym.t * t
  type bindings = binding list

  type fbinding = Id.mid * t
  type fbindings = fbinding list

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


  let pp_list ts = 
    String.concat " , " (List.map pp ts)

  let parse_sexp_list fstr (env : Sym.t StringMap.t) s = 
    let rec aux (env : Sym.t StringMap.t) acc ts = 
      match ts with
      | [] -> (List.rev acc, env)
      | t :: ts ->
         let (b, env) = parse_sexp env t in
         aux env (b :: acc) ts
    in
    match s with
    | Sexp.List ts -> aux env [] ts
    | t -> parse_error fstr t
         
end

module A = struct
  type t = A of T.bindings
  let make (ts : T.bindings) = A ts
  let extr (A ts) = ts
  let pp (A ts) = T.pp_list ts
  let parse_sexp env s = 
    let bs, env = T.parse_sexp_list "argument type" env s in
    (make bs, env)
end


module R = struct
  type t = R of T.bindings
  let make (ts : T.bindings) = R ts
  let extr (R ts) = ts
  let pp (R ts) = T.pp_list ts
  let parse_sexp env s = 
    let bs, env = T.parse_sexp_list "return type" env s in
    (make bs, env)
end

module F = struct

  type t = F of A.t * R.t

end
  

      

type global_env = 
  { struct_decls : T.fbindings SymMap.t ; 
    fun_decls : F.t SymMap.t }

type local_env = 
  { a: BT.t SymMap.t; 
    l: LS.t SymMap.t; 
    r: RE.t SymMap.t; 
    c: IT.t SymMap.t; }

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

let lookup_var (env: 'v SymMap.t) (sym: Sym.t) : 'v = 
  match SymMap.find_opt sym env with
  | Some t -> t
  | None -> failwith (sprintf "unbound variable %s" (Sym.pp sym))


let core_type_value ov = 
  Core_typing.typeof_object_value 
    Location_ocaml.unknown 
    Core_typing_aux.empty_env ov

(* let rec sizeof_ov ov = 
 *   Impl_mem.sizeof_ival (core_type_value ov) *)


(* let incorrect_kind (sym, has, loc) (should_be, kloc) = 
 *   let err = 
 *     sprintf "%s: variable %s (%s) has kind %s but is expected to have kind %s" 
 *       (pp_loc kloc)
 *       (Sym.pp sym) 
 *       (pp_loc loc)
 *       (T.pp_kind has)
 *       (T.pp_kind should_be) 
 *   in
 *   failwith err *)

let incorrect_bt (sym, has, loc) (should_be, kloc) = 
  let err = 
    sprintf "%s: variable %s (%s) has type %s but is expected to have kind %s" 
      (pp_loc kloc)
      (Sym.pp sym) 
      (pp_loc loc)
      (BT.pp has)
      (BT.pp should_be) 
  in
  failwith err

let ensure_type (sym, has, loc) (should_be, kloc) = 
  if has = should_be then () 
  else incorrect_bt (sym, has, loc) (should_be, kloc)


(* let ensure_akind (sym, kind, loc) kloc = 
 *   match kind with 
 *   | T.A bt -> bt
 *   | b -> incorrect_kind (sym, T.kind_of_t b, loc) (T.Argument,kloc) *)


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

          


let rec bt_of_core_object_type = function
  | OTy_integer -> BT.Int
  | OTy_floating -> failwith "floats not supported"
  | OTy_pointer -> BT.Loc
  | OTy_array cbt -> BT.Array
  | OTy_struct sym -> Struct sym
  | OTy_union _sym -> failwith "todo: union types"

let rec bt_of_core_base_type = function
  | Core.BTy_unit -> BT.Unit
  | Core.BTy_boolean -> BT.Bool
  | Core.BTy_ctype -> failwith "BT ctype"
  | Core.BTy_list bt -> BT.List (bt_of_core_base_type bt)
  | Core.BTy_tuple bts -> BT.Tuple (List.map bt_of_core_base_type bts)
  | Core.BTy_object ot -> bt_of_core_object_type ot
  | Core.BTy_loaded ot -> bt_of_core_object_type ot
  | Core.BTy_storable -> unreachable ()


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
  | _, Ctype.IntN_t n -> failwith "todo standard library types"
  | _, Ctype.Int_leastN_t n -> failwith "todo standard library types"
  | _, Ctype.Int_fastN_t n -> failwith "todo standard library types"
  | _, Ctype.Intmax_t -> failwith "todo standard library types"
  | _, Ctype.Intptr_t -> failwith "todo standard library types"

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

let rec bt_and_constr_of_ctype (Ctype.Ctype (_annots, ct)) = 
  match ct with
  | Void -> 
     (Unit, None)               (* check *)
  | Basic (Integer it) -> 
     bt_and_constr_of_integerType it
  | Basic (Floating _) -> 
     failwith "floats not supported"
  | Array (ct, _maybe_integer) -> 
     (Array, None)
  | Function _ -> 
     failwith "function pointers not supported"
  | Pointer (_qualifiers, ctype) ->
     (Loc, None)
  | Atomic ct ->              (* check *)
     bt_and_constr_of_ctype ct
  | Struct sym -> 
     (Struct sym, None)
  | Union sym ->
     failwith "todo: union types"

let binding_of_ctype ctype name = 
  match bt_and_constr_of_ctype ctype with
  | (bt, Some c) -> [(name, T.A bt); (Sym.fresh (), T.C (c (V name)))]
  | (bt, None) -> [(name, T.A bt)]

let fbinding_of_ctype ctype (id : Id.id) = 
  match bt_and_constr_of_ctype ctype with
  | (bt, Some c) -> [(Some id, T.A bt); (None, T.C (c (F id)))]
  | (bt, None) -> [(Some id, T.A bt)]

let sym_or_fresh (msym : Sym.t option) : Sym.t = 
  match msym with
  | Some sym -> sym
  | None -> Sym.fresh ()


let integer_value_to_num iv = 
  match (Impl_mem.eval_integer_value iv) with
  | Some i -> i
  | None -> failwith "integer_value_to_num: None"

let infer_object_value name ov = 
  match ov with
  | M_OVinteger iv ->
     let constr = V name %= Num (integer_value_to_num iv) in
     R.make [(name, A BT.Int); (Sym.fresh (), C constr)]
  | M_OVfloating iv ->
     failwith "floats not supported"
  | M_OVpointer p ->
     Impl_mem.case_ptrval p
       (fun _cbt -> 
         let constr = Null (V name) in
         R.make [(name, A (BT.Loc)); (Sym.fresh (), C constr)]
       )
       (fun sym -> 
         failwith "function pointers not supported"
       )
       (fun _prov loc ->
         let constr = V name %= Num loc in
         R.make [(name, A (BT.Loc)); (Sym.fresh (), C constr)]
       )
       (fun _ ->
         failwith "unspecified pointer value"
       )
  | M_OVarray _ ->
     failwith "todo: array"
  | M_OVstruct (sym, fields) ->
     failwith "todo: struct"
  | M_OVunion _ -> 
     failwith "todo: union types"

let infer_loaded_value name env lv = 
     failwith "todo object_value"

let infer_value name env v vloc = 
  match v with
  | M_Vobject ov ->
     infer_object_value name ov
  | M_Vloaded lv ->
     infer_loaded_value name env lv
  | M_Vunit ->
     R.make [(name, A BT.Unit)]
  | M_Vtrue ->
     let constr = V name in
     R.make [(name, A BT.Bool); (Sym.fresh (), C constr)]
  | M_Vfalse -> 
     let constr = Not (V name) in
     R.make [(name, A BT.Bool); (Sym.fresh (), C constr)]
  | M_Vctype ct ->
     failwith "todo ctype"
  | M_Vlist (cbt, tsyms) ->
     let t = bt_of_core_base_type cbt in
     let check_item tsym =
       let (sym,loc) = Sym.lof_tsymbol tsym in
       let typ = lookup_var env.local.a sym in
       ensure_type (sym, typ, loc) (t, vloc) in
     let _ = List.map check_item tsyms in
     (* maybe record list length? *)
     R.make [(name, A (BT.List t))]
  | M_Vtuple tsyms ->
     let syms = List.map Sym.of_tsymbol tsyms in
     let ts = List.map (lookup_var env.local.a) syms in
     R.make [(name, A (BT.Tuple ts))]


let rec infer_pexpr name env (M_Pexpr (annots, _bty, pe)) = 
  let kloc = Annot.get_loc_ annots in
  match pe with
  | M_PEsym sym ->
     let b = lookup_var env.local.a sym in
     R.make [(name, T.A b)]
  | M_PEimpl _ ->
     failwith "todo PEimpl"
  | M_PEval v ->
     infer_value name env v kloc
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
     let (sym,loc) = Sym.lof_tsymbol sym in
     let t = lookup_var env.local.a sym in
     let () = ensure_type (sym, t, loc) (BT.Bool, kloc) in
     let constr = (V name) %= Not (V sym) in
     R.make [(name, A t); (name, C constr)]
  | M_PEop (op,sym1,sym2) ->
     let (sym1, loc1) = Sym.lof_tsymbol sym1 in
     let (sym2, loc2) = Sym.lof_tsymbol sym2 in
     let t1 = lookup_var env.local.a sym1 in
     let t2 = lookup_var env.local.a sym2 in
     let ((st1,st2),rt) = bt_of_binop op in
     let () = ensure_type (sym1, t1, loc1) (st1, kloc) in
     let () = ensure_type (sym2, t2, loc2) (st2, kloc) in
     let constr = V name %= (make_binop op (V sym1) (V sym2)) in
     R.make [(name, A rt); (Sym.fresh (), C constr)]
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
        let rt = infer_pexpr name2 env e1 in
        infer_pexpr name (add_vars env (R.extr rt)) e1
     | Pattern (_annot, CaseCtor _) ->
        failwith "todo ctor pattern"
     end
  | M_PEif (sym1,sym2,sym3) ->
     let sym1, loc1 = Sym.lof_tsymbol sym1 in
     let sym2, loc2 = Sym.lof_tsymbol sym2 in
     let sym3, loc3 = Sym.lof_tsymbol sym3 in
     let t1, t2, t3 = 
       lookup_var env.local.a sym1,
       lookup_var env.local.a sym2, 
       lookup_var env.local.a sym3 
     in
     let () = ensure_type (sym1, t1, loc1) (BT.Bool, kloc) in
     let () = ensure_type (sym3, t3, loc3) (t2, kloc) in
     let constr = 
       (V sym1 %& (V name %= V sym2)) %| 
       ((Not (V sym1)) %& (V name %= V sym3)) 
     in
     R.make [(name, A t2); (Sym.fresh (), C constr)]
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


let check_expr _fname env (M_Expr (_annots, e)) : unit = 
  match e with
 | M_Epure pe -> 
    let t = infer_pexpr  in
    failwith "epure"
 | M_Ememop _ ->
    failwith "ememop"
 | M_Eaction _ ->
    failwith "eaction"
 | M_Ecase _ ->
    failwith "ecase"
 | M_Elet _ ->
    failwith "elet"
 | M_Eif _ ->
    failwith "eif"
 | M_Eskip -> 
    failwith "eskip" 
 | M_Eccall _ ->
    failwith "eccall"
 | M_Eproc _ ->
    failwith "eproc"
 | M_Ewseq _ ->
    failwith "ewseq"
 | M_Esseq _ ->
    failwith "esseq"
 | M_Ebound _ ->
    failwith "ebound"
 | M_End _ ->
    failwith "ebound"
 | M_Esave _ ->
    failwith "esave"
 | M_Erun _ ->
    failwith "erun"
     


let test_infer_expr () = 
  failwith "not implemented"


let check_pure_function_body env name args body = 
  ()

let check_function_body env name args body = 
  let env = env in
  check_expr name env body


let check_function env name fn = 
  match fn with
  | M_Fun (_bt, args, body) ->
     check_pure_function_body env name args body
  | M_Proc (_loc, _bt, args, body) ->
     check_function_body env name args body
  | M_ProcDecl _
  | M_BuiltinDecl _ -> ()


let check_functions env fns =
  Pmap.iter (check_function env) fns

                             

let record_funinfo sym (_loc,_attrs,ret_ctype,args,is_variadic,_has_proto) fun_decls =
  let make_arg_t (msym,ctype) = binding_of_ctype ctype (sym_or_fresh msym) in
  if is_variadic then failwith "variadic functions not supported"
  else 
    let args_type = A.make (concatmap make_arg_t args) in
    let ret_type = R.make (binding_of_ctype ret_ctype (Sym.fresh ()) )in
    SymMap.add sym (F.F (args_type,ret_type)) fun_decls

let record_funinfo env funinfo = 
  { env with fun_decls = Pmap.fold record_funinfo funinfo env.fun_decls }



let record_tagDef sym def struct_decls =
  let make_field_and_constraint (id, (_attributes, _qualifier, ctype)) =
    fbinding_of_ctype ctype id in
  match def with
  | Ctype.UnionDef _ -> 
     failwith "todo: union types"
  | Ctype.StructDef fields ->
     SymMap.add sym (concatmap make_field_and_constraint fields) struct_decls

let record_tagDefs env tagDefs = 
  { env with struct_decls = Pmap.fold record_tagDef tagDefs env.struct_decls }







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
  let env = empty_global in
  let env = record_tagDefs env mu_file.mu_tagDefs in
  let env = record_funinfo env mu_file.mu_funinfo in
  check_functions env mu_file.mu_funs
