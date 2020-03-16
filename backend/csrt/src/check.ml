(* open Lem_pervasives  *)
open Core 
open Mucore
open Impl_mem
open Nat_big_num
open Sexplib
open Sexp
open Printf


module Symbol = struct
  type t = Symbol.sym
  let fresh = Symbol.fresh
  let fresh_pretty = Symbol.fresh_pretty
  let pp = Pp_symbol.to_string_pretty
  let of_tsymbol (s : 'bty Mucore.tsymbol) = 
    let (TSym (_, _, sym)) = s in sym
  let compare = Symbol.symbol_compare
end

module Sym = struct
  include Symbol
  module Env = struct
    module Map = Map.Make(String)
    type t = Symbol.t Map.t
    let empty = Map.empty
    let find_opt = Map.find_opt
    let add = Map.add
  end
  let parse (env : Env.t) name = 
    match Env.find_opt name env with
    | None -> failwith (sprintf "unbound variable %s" name)
    | Some sym -> sym
end




type num = Nat_big_num.num
type loc = num

let pp_num = string_of_int
let parse_num = int_of_string

let parse_error t sx = 
  let err = sprintf "unexpected %s: %s" t (to_string sx) in
  raise (Invalid_argument err)

let pp_to_sexp_list f xs = 
  "(" ^ (String.concat " " (List.map f xs)) ^ ")"

let parse_sexp_list f = function
  | Atom _ -> failwith "expected List"
  | List sxs -> List.map f sxs

let unreachable () = failwith "unreachable"


module IT = struct

  type t =

    | V of Sym.t
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
  let (%>=) t1 t2 = GE (t1, t2)

  (* let rec pp = function
   *   | V sym -> Sym.pp sym
   *   | Num i -> Nat_big_num.to_string i
   *   | Bool true -> "true"
   *   | Bool false -> "false"
   *   | Add (it1,it2) -> sprintf "(%s + %s)" (pp it1) (pp it2)
   *   | Sub (it1,it2) -> sprintf "(%s - %s)" (pp it1) (pp it2)
   *   | Mul (it1,it2) -> sprintf "(%s * %s)" (pp it1) (pp it2)
   *   | Div (it1,it2) -> sprintf "(%s / %s)" (pp it1) (pp it2)
   *   | Exp (it1,it2) -> sprintf "(%s ^ %s)" (pp it1) (pp it2)
   *   | App (it1,it2) -> sprintf "(%s %s)" (pp it1) (pp it2)
   *   | List its -> sprintf "(list %s)" (pp_to_sexp_list pp its)
 *     | EQ (o1,o2) -> sprintf "(%s = %s)"  (IT.pp o1) (IT.pp o2)
 *     | NE (o1,o2) -> sprintf "(%s <> %s)" (IT.pp o1) (IT.pp o2)
 *     | LT (o1,o2) -> sprintf "(%s < %s)"  (IT.pp o1) (IT.pp o2)
 *     | GT (o1,o2) -> sprintf "(%s > %s)"  (IT.pp o1) (IT.pp o2)
 *     | LE (o1,o2) -> sprintf "(%s <= %s)" (IT.pp o1) (IT.pp o2)
 *     | GE (o1,o2) -> sprintf "(%s >= %s)" (IT.pp o1) (IT.pp o2)
 *     | Null o1 -> sprintf "(null %s)" (IT.pp o1) 
   *   | And (o1,o2) -> sprintf "(%s & %s)" (pp o1) (pp o2)
   *   | Not (o1) -> sprintf "(not %s)" (pp o1)
   *   | P p -> LP.pp p *)


(*   let rec parse_sexp (env : Sym.Env.t) sx = 
 *     match sx with
 *     | Atom "true" -> 
 *        Bool true
 *     | Atom "false" -> 
 *        Bool false
 *     | Atom str when Str.string_match (Str.regexp "[0-9]+") str 0 ->
 *        Num (Nat_big_num.of_string str)
 *     | Atom str -> V (Sym.parse env str)
 *     | List [o1;Atom "+";o2] -> 
 *        Add (parse_sexp env o1, parse_sexp env o2)
 *     | List [o1;Atom "-";o2] -> 
 *        Sub (parse_sexp env o1, parse_sexp env o2)
 *     | List [o1;Atom "*";o2] -> 
 *        Mul (parse_sexp env o1, parse_sexp env o2)
 *     | List [o1;Atom "/";o2] -> 
 *        Div (parse_sexp env o1, parse_sexp env o2)
 *     | List [o1;Atom "^";o2] -> 
 *        Exp (parse_sexp env o1, parse_sexp env o2)
 *     | List [Atom "list"; its] -> 
 *        List (parse_sexp_list (parse_sexp env) its)
 *     | List [o1;o2] -> 
 *        App (parse_sexp env o1, parse_sexp env o2)
 *     | List [o1;Atom "=";o2]  -> 
 *        EQ (IT.parse_sexp env o1, IT.parse_sexp env o2)
 *     | List [o1;Atom "<>";o2] -> 
 *        NE (IT.parse_sexp env o1, IT.parse_sexp env o2)
 *     | List [o1;Atom "<";o2]  -> 
 *        LT (IT.parse_sexp env o1, IT.parse_sexp env o2)
 *     | List [o1;Atom ">";o2]  -> 
 *        GT (IT.parse_sexp env o1, IT.parse_sexp env o2)
 *     | List [o1;Atom "<=";o2] -> 
 *        LE (IT.parse_sexp env o1, IT.parse_sexp env o2)
 *     | List [o1;Atom ">=";o2] -> 
 *        GE (IT.parse_sexp env o1, IT.parse_sexp env o2)
 *     | t -> 
 *        parse_error "logical predicate" t
   *   | List [Atom "not";op] -> Not (parse_sexp env op)
   *   | List [o1; Atom "&"; o2] -> And (parse_sexp env o1, parse_sexp env o2)
   *   | l -> P (LP.parse_sexp env l) *)

end


open Sym
open IT

module BT = struct

  type t = 
    | Unit
    | Bool
    | Int
    | Loc
    | Struct of Sym.t

  let rec pp = function
    | Unit -> "unit"
    | Bool -> "bool"
    | Int -> "int"
    | Loc -> "loc"
    | Struct sym -> sprintf "(struct %s)" (Sym.pp sym)
  
  (* let rec parse_sexp (env : Sym.Env.t) sx = 
   *   match sx with
   *   | Atom "unit" -> Unit
   *   | Atom "bool" -> Bool
   *   | Atom "int" -> Int
   *   | Atom "loc" -> Loc
   *   | List [Atom "struct"; Atom id] -> Struct (Sym.parse env id)
   *   | a -> parse_error "base type" a *)

end


module RE = struct

  type t = 
    | Block of IT.t * IT.t
    | Int of IT.t * IT.t (* location and value *)
    | Points of IT.t * IT.t
    | Array of IT.t * IT.t list
   (* Array (pointer, list pointer) *)

  (* let rec pp = function
   *   | Block (it1,it2) -> 
   *      sprintf "(block %s %s)" 
   *        (IT.pp it1)
   *        (IT.pp it2)
   *   | Int (it1,it2) -> 
   *      sprintf "(int %s %s)" 
   *        (IT.pp it1) 
   *        (IT.pp it2)
   *   | Array (it1,it2) -> 
   *      sprintf "(array %s %s)" 
   *        (IT.pp it1)
   *        (IT.pp it2)
   *   | Points (it1,it2) -> 
   *      sprintf "(points %s %s)" 
   *        (IT.pp it1)
   *        (IT.pp it2)
   *   | Uninit (it1,it2,rt) -> 
   *      sprintf "(uninit %s %s %s)" 
   *        (IT.pp it1)
   *        (IT.pp it2)
   *        (pp rt)
   * 
   * let rec parse_sexp (env : Sym.Env.t) sx = 
   *   match sx with 
   *   | List [Atom "block";it1;it2] -> 
   *      Block (IT.parse_sexp env it1,
   *             IT.parse_sexp env it2)
   *   | List [Atom "int"; it1; it2] ->
   *      Int (IT.parse_sexp env it1, 
   *           IT.parse_sexp env it2)
   *   | List [Atom "array"; it1; it2] ->
   *      Array (IT.parse_sexp env it1, 
   *             IT.parse_sexp env it2)
   *   | List [Atom "points"; it1; it2] ->
   *      Points (IT.parse_sexp env it1, 
   *              IT.parse_sexp env it2)
   *   | List [Atom "uninit"; it1; it2; rt] ->
   *      Uninit (IT.parse_sexp env it1, 
   *              IT.parse_sexp env it2, 
   *              parse_sexp env rt)
   *   | t -> parse_error "resource type" t *)

end


module LS = struct

  type t = 
    | Base of BT.t
    | List of BT.t
    | Fun of t * t


  (* let rec pp = function
   *   | List ls -> 
   *      sprintf "(list %s)" 
   *        (BT.pp ls)
   *   | Fun (ls1,ls2) -> 
   *      sprintf "(%s -> %s)" 
   *        (pp ls1)
   *        (pp ls2)
   *   | Base bt -> 
   *        BT.pp bt
   * 
   * let rec parse_sexp (env : Sym.Env.t) sx =
   *   match sx with
   *   | Sexp.List [Atom "list"; a] ->
   *      List (BT.parse_sexp env a)
   *   | Sexp.List [o1; Atom "->"; o2] ->
   *      Fun (parse_sexp env o1, parse_sexp env o2)
   *   | ((Sexp.Atom _) as a) -> 
   *      Base (BT.parse_sexp env a)
   *   | ls -> parse_error "logical sort" ls *)

end



type t = 
  | A of BT.t
  | L of LS.t
  | R of RE.t
  | C of IT.t         

type binding = Sym.t * t


module RT = struct

  type t = RT of binding list
 
  let make (ts : binding list) = RT ts


  (* type t = list binding
   *   | A of (Sym.t * BT.t) * t
   *   | L of (Sym.t * LS.t) * t
   *   | R of (Sym.t * RE.t) * t
   *   | C of (Sym.t * IT.t) * t
   *   | I
   * 
   * type tT = t -> t
   * 
   * let a sym bt : tT = fun t -> A ((sym,bt),t)
   * let l sym ls : tT = fun t -> L ((sym,ls),t)
   * let r sym re : tT = fun t -> R ((sym,re),t)
   * let c sym lc : tT = fun t -> C ((sym,lc),t)
   * 
   * let comb f g x = f (g (x))
   * 
   * let rec combine (ris : tT list) : tT = 
   *   match ris with
   *   | [] -> (fun ri -> ri)
   *   | ri :: ris -> comb ri (combine ris)
   * 
   * let make ris = combine ris I *)


  (* let rec pp = function
   *   | A ((id, typ), rt) -> 
   *      sprintf "EC (%s : %s) . %s" (Sym.pp id) (BT.pp typ) (pp rt)
   *   | L ((id, ls), rt)  -> 
   *      sprintf "EL (%s : %s) . %s" (Sym.pp id) (LS.pp ls) (pp rt)
   *   | R ((id, re), rt) -> 
   *      sprintf "(%s : %s) * %s" (Sym.pp id) (RE.pp re) (pp rt)
   *   | C ((id, lc), rt) -> 
   *      sprintf "(%s : %s) & %s" (Sym.pp id) (LC.pp lc) (pp rt)
   *   | I -> 
   *      "I"
   * 
   * let rec parse_sexp (env : Sym.Env.t) = function
   *   | Atom "EC" :: List [Atom id; Atom ":"; t] :: Atom "." :: rt ->
   *      let sym = Sym.fresh_pretty id in
   *      let env' = Sym.Env.add id sym env in
   *      A ((sym, BT.parse_sexp env t), parse_sexp env' rt)
   *   | Atom "EL" :: List [Atom id; Atom ":"; ls] :: Atom "." :: rt ->
   *      let sym = Sym.fresh_pretty id in
   *      let env' = Sym.Env.add id sym env in
   *      L ((sym, LS.parse_sexp env ls), parse_sexp env' rt)
   *   | List [Atom id; Atom ":"; re] :: Atom "*" :: rt ->
   *      let sym = Sym.fresh_pretty id in
   *      let env' = Sym.Env.add id sym env in
   *      R ((sym, RE.parse_sexp env re), parse_sexp env' rt)
   *   | List [Atom id; Atom ":"; lc] :: Atom "&" :: rt ->
   *      let sym = Sym.fresh_pretty id in
   *      let env' = Sym.Env.add id sym env in
   *      C ((sym, LC.parse_sexp env lc), parse_sexp env' rt)
   *   | Atom "I" :: [] -> 
   *      I
   *   | rt -> 
   *      parse_error "rturn type" (List rt) *)

end



module FT = struct

  
  (* basically the same as return_item, so could unify if it stays
     like this? *)
  (* type t = 
   *   | A of Sym.t * BT.t
   *   | L of Sym.t * LS.t
   *   | R of Sym.t * RE.t
   *   | C of Sym.t * IT.t
   *   | RT
   * 
   * type t = Fn of args * RT.t *)

  type t_argument = binding
  type t_arguments = t_argument list

  type t = FT of t_arguments * RT.t


  (* let rec pp_arguments = function
   *   | A (sym, bt) :: args -> 
   *      sprintf "AC (%s : %s) . %s" (Sym.pp sym) (BT.pp bt) (pp_arguments args)
   *   | L (sym, ls) :: args -> 
   *      sprintf "AL (%s : %s) . %s" (Sym.pp sym) (LS.pp ls) (pp_arguments args)
   *   | R (sym, rt) :: args ->
   *      sprintf "(%s : %s) =* %s" (Sym.pp sym) (RE.pp rt) (pp_arguments args)
   *   | C (sym, lc) :: args ->
   *      sprintf "(%s : %s) => %s" (Sym.pp sym) (LC.pp lc) (pp_arguments args)
   *   | [] -> 
   *      ""
   * 
   * let pp (Fn (args, rt)) = 
   *   sprintf "%s%s" (pp_arguments args) (RT.pp rt)
   * 
   * let rec parse_sexp_aux acc (env : Sym.Env.t) = function
   *   | Atom "AC" :: List [Atom id; Atom ":"; bt] :: Atom "." :: args ->
   *      let sym = Sym.fresh_pretty id in
   *      let env' = Sym.Env.add id sym env in
   *      parse_sexp_aux (A (sym, BT.parse_sexp env bt) :: acc) env' args
   *   | Atom "AL":: List [Atom id; Atom ":"; ls] :: Atom "." :: args ->
   *      let sym = Sym.fresh_pretty id in
   *      let env' = Sym.Env.add id sym env in
   *      parse_sexp_aux (L (sym, LS.parse_sexp env ls) :: acc) env' args
   *   | List [Atom id; Atom ":"; re] :: Atom "=*" :: args ->
   *      let sym = Sym.fresh_pretty id in
   *      let env' = Sym.Env.add id sym env in
   *      parse_sexp_aux (R (sym, RE.parse_sexp env re) :: acc) env' args
   *   | List [Atom id; Atom ":"; lc] :: Atom "=>" :: args ->
   *      let sym = Sym.fresh_pretty id in
   *      let env' = Sym.Env.add id sym env in
   *      parse_sexp_aux (C (sym, LC.parse_sexp env lc) :: acc) env' args
   *   | rt -> 
   *      Fn (List.rev acc, RT.parse_sexp env rt)
   * 
   * let parse_sexp (env : Sym.Env.t) = function
   *   | List ft -> parse_sexp_aux [] env ft
   *   | t -> parse_error "function type" t *)
         
end
  

module SymMap = Map.Make(Sym)

      
type kind = 
  | Argument
  | Logical
  | Resource
  | Constraint

let kind_of_binding = function
  | A _ -> Argument
  | L _ -> Logical
  | R _ -> Resource
  | C _ -> Constraint

let string_of_kind = function
  | Argument -> "computational"
  | Logical -> "logical"
  | Resource -> "resource"
  | Constraint -> "constraint"




type env = 
  { vars : binding SymMap.t
  ; struct_decls : Ctype.tag_definition SymMap.t
  }

let empty_env = 
  { vars = SymMap.empty
  ; struct_decls = SymMap.empty
  }




let option_get = function
  | Some a -> a
  | None -> failwith "get None"


let core_type_value ov = 
  Core_typing.typeof_object_value 
    Location_ocaml.unknown 
    Core_typing_aux.empty_env ov

(* let rec sizeof_ov ov = 
 *   Impl_mem.sizeof_ival (core_type_value ov) *)


let unbound sym = 
  let err = sprintf "unbound variable %s" (Sym.pp sym) in
  failwith err

let lookup sym env = 
  match SymMap.find_opt sym env with
  | None -> unbound sym
  | Some t -> t





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
  | OpEq -> ((BT.Int, BT.Int), BT.Int)
  | OpGt -> ((BT.Int, BT.Int), BT.Int)
  | OpLt -> ((BT.Int, BT.Int), BT.Int)
  | OpGe -> ((BT.Int, BT.Int), BT.Int)
  | OpLe -> ((BT.Int, BT.Int), BT.Int)
  | OpAnd -> ((BT.Bool, BT.Bool), BT.Bool)
  | OpOr -> ((BT.Bool, BT.Bool), BT.Bool)

          
let incorrect_kind sym has should_be = 
  let err = sprintf "variable %s has kind %s but is expected to have kind %s" 
              (Sym.pp sym) (string_of_kind has) (string_of_kind should_be)
  in
  failwith err

let incorrect_bt sym has should_be = 
  let err = sprintf "variable %s has type %s but is expected to have type %s" 
              (Sym.pp sym) (BT.pp has) (BT.pp should_be)
  in
  failwith err

let ensure_type sym has should_be = 
  if has = should_be then () else incorrect_bt sym has should_be

let infer_pexpr env pe = 

  match pe with
  | M_PEsym sym ->
     RT.make [(sym, (lookup sym env))]
  | M_PEimpl _ ->
     failwith "todo PEimpl"
  | M_PEval v ->
     failwith "todo PEval"
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
     let sym = of_tsymbol sym in
     begin match SymMap.find_opt sym env with
     | None -> 
        unbound sym
     | Some (A t) -> 
        let () = ensure_type sym t BT.Bool in
        let newsym = fresh () in
        let constr = (V newsym) %= Not (V newsym) in
        RT.make [(newsym, A t); (fresh (), C constr)]
     | Some b -> 
        incorrect_kind sym (kind_of_binding b) Argument
     end
  | M_PEop (op,sym1,sym2) ->
     let sym1, sym2 = of_tsymbol sym1, of_tsymbol sym2 in
     begin match SymMap.find_opt sym1 env, 
                 SymMap.find_opt sym2 env with
     | None, _ -> unbound sym1
     | _, None ->  unbound sym2
     | Some (A t1), Some (A t2) -> 
        let ((st1,st2),rt) = bt_of_binop op in
        let () = ensure_type sym1 t1 st1 in
        let () = ensure_type sym2 t2 st2 in
        let newsym = fresh () in
        let constr = V newsym %= (make_binop op (V sym1) (V sym2)) in
        RT.make [(newsym, A rt); (fresh (), C constr)]
     | Some b, Some (A _) -> 
        incorrect_kind sym1 (kind_of_binding b) Argument
     | _, Some b -> 
        incorrect_kind sym2 (kind_of_binding b) Argument
     end
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
  | M_PElet _ ->
     failwith "todo M_PElet"
  | M_PEif _ ->
     failwith "todo M_PEif"
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
 
     


let pp_fun_map_decl f = 
  let pp = Pp_core.All.pp_funinfo_with_attributes f in
  print_string (Pp_utils.to_plain_string pp)

(* (\* from https://ocaml.org/learn/tutorials/file_manipulation.html *\)
 * let write_file file string =
 *   let oc = open_out file in
 *   fprintf oc "%s\n" string;
 *   close_out oc *)


let print_core_file core_file filename = 
  let pp = Pp_core.Basic.pp_file core_file in
  Pipeline.run_pp (Some (filename,"core")) pp
  (* write_file filename (Pp_utils.to_plain_pretty_string pp) *)

let check (core_file : unit Core.typed_file) =
  Colour.do_colour := false;
  let mu_file = Core_anormalise.normalise_file core_file in
  Tags.set_tagDefs core_file.tagDefs;
  pp_fun_map_decl core_file.funinfo;
  print_core_file core_file "out1";
  print_core_file (mu_to_core__file mu_file) "out2";
  (* test_parse (); *)
  (* test_value_infer (); *)

