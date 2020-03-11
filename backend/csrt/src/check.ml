(* open Lem_pervasives  *)
open Core
open Impl_mem
open Nat_big_num
open Sexplib
open Sexp
open Printf



module Sym = struct

  type sym = Symbol.sym

  module Env = struct
    type t = (string, Symbol.sym) Pmap.map
    let new_env = Pmap.empty String.compare
    let lookup name env = Pmap.lookup name env
    let add name sym env = Pmap.add name sym env
  end

  let fresh = Symbol.fresh
  let fresh_pretty = Symbol.fresh_pretty
  let pp = Pp_symbol.to_string_pretty

  let parse (env : Env.t) name = 
    match Env.lookup name env with
    | None -> failwith (sprintf "unbound variable %s" name)
    | Some sym -> sym

end

open Sym



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

  type index_term =
    | Var of sym
    | Num of num
    | Bool of bool
    | Add of index_term * index_term
    | Sub of index_term * index_term
    | Mul of index_term * index_term
    | Div of index_term * index_term
    | Exp of index_term * index_term
    | App of index_term * index_term
    | List of index_term list

  let var sym = Var sym

  let rec pp = function
    | Var sym -> Sym.pp sym
    | Num i -> Nat_big_num.to_string i
    | Bool true -> "true"
    | Bool false -> "false"
    | Add (it1,it2) -> sprintf "(%s + %s)" (pp it1) (pp it2)
    | Sub (it1,it2) -> sprintf "(%s - %s)" (pp it1) (pp it2)
    | Mul (it1,it2) -> sprintf "(%s * %s)" (pp it1) (pp it2)
    | Div (it1,it2) -> sprintf "(%s / %s)" (pp it1) (pp it2)
    | Exp (it1,it2) -> sprintf "(%s ^ %s)" (pp it1) (pp it2)
    | App (it1,it2) -> sprintf "(%s %s)" (pp it1) (pp it2)
    | List its -> sprintf "(list %s)" (pp_to_sexp_list pp its)


  let rec parse_sexp (env : Sym.Env.t) sx = 
    match sx with
    | Atom "true" -> 
       Bool true
    | Atom "false" -> 
       Bool false
    | Atom str when Str.string_match (Str.regexp "[0-9]+") str 0 ->
       Num (Nat_big_num.of_string str)
    | Atom str -> Var (Sym.parse env str)
    | List [o1;Atom "+";o2] -> 
       Add (parse_sexp env o1, parse_sexp env o2)
    | List [o1;Atom "-";o2] -> 
       Sub (parse_sexp env o1, parse_sexp env o2)
    | List [o1;Atom "*";o2] -> 
       Mul (parse_sexp env o1, parse_sexp env o2)
    | List [o1;Atom "/";o2] -> 
       Div (parse_sexp env o1, parse_sexp env o2)
    | List [o1;Atom "^";o2] -> 
       Exp (parse_sexp env o1, parse_sexp env o2)
    | List [Atom "list"; its] -> 
       List (parse_sexp_list (parse_sexp env) its)
    | List [o1;o2] -> 
       App (parse_sexp env o1, parse_sexp env o2)
    | t -> 
       parse_error "index term" t
end


module LP = struct

  type logical_predicate = 
    | EQ of IT.index_term * IT.index_term
    | NE of IT.index_term * IT.index_term
    | LT of IT.index_term * IT.index_term
    | GT of IT.index_term * IT.index_term
    | LE of IT.index_term * IT.index_term
    | GE of IT.index_term * IT.index_term
    | Null of IT.index_term

  let pp = function
    | EQ (o1,o2) -> sprintf "(%s = %s)"  (IT.pp o1) (IT.pp o2)
    | NE (o1,o2) -> sprintf "(%s <> %s)" (IT.pp o1) (IT.pp o2)
    | LT (o1,o2) -> sprintf "(%s < %s)"  (IT.pp o1) (IT.pp o2)
    | GT (o1,o2) -> sprintf "(%s > %s)"  (IT.pp o1) (IT.pp o2)
    | LE (o1,o2) -> sprintf "(%s <= %s)" (IT.pp o1) (IT.pp o2)
    | GE (o1,o2) -> sprintf "(%s >= %s)" (IT.pp o1) (IT.pp o2)
    | Null o1 -> sprintf "(null %s)" (IT.pp o1)

  let parse_sexp (env : Sym.Env.t) sx =
    match sx with 
    | List [o1;Atom "=";o2]  -> 
       EQ (IT.parse_sexp env o1, IT.parse_sexp env o2)
    | List [o1;Atom "<>";o2] -> 
       NE (IT.parse_sexp env o1, IT.parse_sexp env o2)
    | List [o1;Atom "<";o2]  -> 
       LT (IT.parse_sexp env o1, IT.parse_sexp env o2)
    | List [o1;Atom ">";o2]  -> 
       GT (IT.parse_sexp env o1, IT.parse_sexp env o2)
    | List [o1;Atom "<=";o2] -> 
       LE (IT.parse_sexp env o1, IT.parse_sexp env o2)
    | List [o1;Atom ">=";o2] -> 
       GE (IT.parse_sexp env o1, IT.parse_sexp env o2)
    | t -> 
       parse_error "logical predicate" t
end


module LC = struct

  type logical_constraint =
    | And of logical_constraint * logical_constraint
    | Not of logical_constraint
    | Pred of LP.logical_predicate

  let rec pp = function
    | And (o1,o2) -> sprintf "(%s & %s)" (pp o1) (pp o2)
    | Not (o1) -> sprintf "(not %s)" (pp o1)
    | Pred p -> LP.pp p

  let rec parse_sexp (env : Sym.Env.t) sx =
    match sx with
    | List [Atom "not";op] -> Not (parse_sexp env op)
    | List [o1; Atom "&"; o2] -> And (parse_sexp env o1, parse_sexp env o2)
    | l -> Pred (LP.parse_sexp env l)

end


module BT = struct

  type base_type = 
    | Unit
    | Bool
    | Int
    | Loc
    | Struct of sym

  let rec pp = function
    | Unit -> "unit"
    | Bool -> "bool"
    | Int -> "int"
    | Loc -> "loc"
    | Struct sym -> sprintf "(struct %s)" (Sym.pp sym)

  let rec parse_sexp (env : Sym.Env.t) sx = 
    match sx with
    | Atom "unit" -> Unit
    | Atom "bool" -> Bool
    | Atom "int" -> Int
    | Atom "loc" -> Loc
    | List [Atom "struct"; Atom id] -> Struct (Sym.parse env id)
    | a -> parse_error "base type" a

end


module RE = struct

  type resource = 
    | Block of IT.index_term * IT.index_term
    | Int of IT.index_term * IT.index_term (* location and value *)
    | Points of IT.index_term * IT.index_term
    | Uninit of IT.index_term * IT.index_term * resource
    | Array of IT.index_term * IT.index_term
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
    | Uninit (it1,it2,rt) -> 
       sprintf "(uninit %s %s %s)" 
         (IT.pp it1)
         (IT.pp it2)
         (pp rt)

  let rec parse_sexp (env : Sym.Env.t) sx = 
    match sx with 
    | List [Atom "block";it1;it2] -> 
       Block (IT.parse_sexp env it1,
              IT.parse_sexp env it2)
    | List [Atom "int"; it1; it2] ->
       Int (IT.parse_sexp env it1, 
            IT.parse_sexp env it2)
    | List [Atom "array"; it1; it2] ->
       Array (IT.parse_sexp env it1, 
              IT.parse_sexp env it2)
    | List [Atom "points"; it1; it2] ->
       Points (IT.parse_sexp env it1, 
               IT.parse_sexp env it2)
    | List [Atom "uninit"; it1; it2; rt] ->
       Uninit (IT.parse_sexp env it1, 
               IT.parse_sexp env it2, 
               parse_sexp env rt)
    | t -> parse_error "resource type" t
end


module LS = struct

  type logical_sort = 
    | Base of BT.base_type
    | List of BT.base_type
    | Fun of logical_sort * logical_sort


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

  let rec parse_sexp (env : Sym.Env.t) sx =
    match sx with
    | Sexp.List [Atom "list"; a] ->
       List (BT.parse_sexp env a)
    | Sexp.List [o1; Atom "->"; o2] ->
       Fun (parse_sexp env o1, parse_sexp env o2)
    | ((Sexp.Atom _) as a) -> 
       Base (BT.parse_sexp env a)
    | ls -> parse_error "logical sort" ls

end





module RT = struct

  type return_type = 
    | A of (sym * BT.base_type) * return_type
    | L of (sym * LS.logical_sort) * return_type
    | R of (sym * RE.resource) * return_type
    | C of (sym * LC.logical_constraint) * return_type
    | I

  let a sym bt rt = A ((sym,bt),rt)
  let l sym ls rt = L ((sym,ls),rt)
  let r sym re rt = R ((sym,re),rt)
  let c sym lc rt = C ((sym,lc),rt)

  let comb f g x = f (g (x))

  let rec combine (ris : (return_type -> return_type) list) : return_type -> return_type = 
    match ris with
    | [] -> (fun ri -> ri)
    | ri :: ris -> comb ri (combine ris)

  let make ris = combine ris I


  let rec pp = function
    | A ((id, typ), rt) -> 
       sprintf "EC (%s : %s) . %s" (Sym.pp id) (BT.pp typ) (pp rt)
    | L ((id, ls), rt)  -> 
       sprintf "EL (%s : %s) . %s" (Sym.pp id) (LS.pp ls) (pp rt)
    | R ((id, re), rt) -> 
       sprintf "(%s : %s) * %s" (Sym.pp id) (RE.pp re) (pp rt)
    | C ((id, lc), rt) -> 
       sprintf "(%s : %s) & %s" (Sym.pp id) (LC.pp lc) (pp rt)
    | I -> 
       "I"

  let rec parse_sexp (env : Sym.Env.t) = function
    | Atom "EC" :: List [Atom id; Atom ":"; t] :: Atom "." :: rt ->
       let sym = Sym.fresh_pretty id in
       let env' = Sym.Env.add id sym env in
       A ((sym, BT.parse_sexp env t), parse_sexp env' rt)
    | Atom "EL" :: List [Atom id; Atom ":"; ls] :: Atom "." :: rt ->
       let sym = Sym.fresh_pretty id in
       let env' = Sym.Env.add id sym env in
       L ((sym, LS.parse_sexp env ls), parse_sexp env' rt)
    | List [Atom id; Atom ":"; re] :: Atom "*" :: rt ->
       let sym = Sym.fresh_pretty id in
       let env' = Sym.Env.add id sym env in
       R ((sym, RE.parse_sexp env re), parse_sexp env' rt)
    | List [Atom id; Atom ":"; lc] :: Atom "&" :: rt ->
       let sym = Sym.fresh_pretty id in
       let env' = Sym.Env.add id sym env in
       C ((sym, LC.parse_sexp env lc), parse_sexp env' rt)
    | Atom "I" :: [] -> 
       I
    | rt -> 
       parse_error "rturn type" (List rt)

end



module FT = struct

  
  (* basically the same as return_item, so could unify if it stays
     like this? *)
  type argument = 
    | A of sym * BT.base_type
    | L of sym * LS.logical_sort
    | R of sym * RE.resource
    | C of sym * LC.logical_constraint

  type arguments = argument list

  type function_type = Fn of arguments * RT.return_type

  let rec pp_arguments = function
    | A (sym, bt) :: args -> 
       sprintf "AC (%s : %s) . %s" (Sym.pp sym) (BT.pp bt) (pp_arguments args)
    | L (sym, ls) :: args -> 
       sprintf "AL (%s : %s) . %s" (Sym.pp sym) (LS.pp ls) (pp_arguments args)
    | R (sym, rt) :: args ->
       sprintf "(%s : %s) =* %s" (Sym.pp sym) (RE.pp rt) (pp_arguments args)
    | C (sym, lc) :: args ->
       sprintf "(%s : %s) => %s" (Sym.pp sym) (LC.pp lc) (pp_arguments args)
    | [] -> 
       ""

  let pp (Fn (args, rt)) = 
    sprintf "%s%s" (pp_arguments args) (RT.pp rt)

  let rec parse_sexp_aux acc (env : Sym.Env.t) = function
    | Atom "AC" :: List [Atom id; Atom ":"; bt] :: Atom "." :: args ->
       let sym = Sym.fresh_pretty id in
       let env' = Sym.Env.add id sym env in
       parse_sexp_aux (A (sym, BT.parse_sexp env bt) :: acc) env' args
    | Atom "AL":: List [Atom id; Atom ":"; ls] :: Atom "." :: args ->
       let sym = Sym.fresh_pretty id in
       let env' = Sym.Env.add id sym env in
       parse_sexp_aux (L (sym, LS.parse_sexp env ls) :: acc) env' args
    | List [Atom id; Atom ":"; re] :: Atom "=*" :: args ->
       let sym = Sym.fresh_pretty id in
       let env' = Sym.Env.add id sym env in
       parse_sexp_aux (R (sym, RE.parse_sexp env re) :: acc) env' args
    | List [Atom id; Atom ":"; lc] :: Atom "=>" :: args ->
       let sym = Sym.fresh_pretty id in
       let env' = Sym.Env.add id sym env in
       parse_sexp_aux (C (sym, LC.parse_sexp env lc) :: acc) env' args
    | rt -> 
       Fn (List.rev acc, RT.parse_sexp env rt)

  let parse_sexp (env : Sym.Env.t) = function
    | List ft -> parse_sexp_aux [] env ft
    | t -> parse_error "function type" t
         
end
  





(* Programs and terms *)

type 'a variable_context = (sym * 'a) list

type cv_context = BT.base_type variable_context
type lv_context = LS.logical_sort variable_context
type rv_context = RE.resource variable_context
type lc_context = LC.logical_constraint list

let empty_context = []



(* Typing rules *)

(* value type inference *)





open Core


let var_equal_to (sym : sym) (it : IT.index_term) = 
  LC.Pred (EQ (Var sym, it))

let var_null (sym : sym) = 
  LC.Pred (Null (Var sym))


let option_get = function
  | Some a -> a
  | None -> failwith "get None"


(* let core_type_value ov = 
 *   Core_typing.typeof_object_value 
 *     Location_ocaml.unknown 
 *     Core_typing_aux.empty_env ov
 * 
 * let rec sizeof_ov ov = 
 *   Impl_mem.sizeof_ival (core_type_value ov) *)

(* type struct_env = (Symbol.sym, Ctype.tag_definition) Pmap.map *)



(* let rec infer_lv lv : sym * (RT.return_type -> RT.return_type) = 
 *   match lv with
 *   | LVspecified ov -> infer_ov ov
 *   | LVunspecified _ -> failwith "LVunspecified not implemented" *)

(* and infer_ov ov : sym * (RT.return_type -> RT.return_type) = 
 *   match ov with
 *   | OVinteger i -> 
 *      let n, lc = fresh (), fresh () in
 *      let i = option_get (eval_integer_value i) in
 *      let constr = var_equal_to n (Num i) in
 *      (n, RT.combine [RT.a n BT.Int; RT.c lc constr])
 *   | OVfloating _ -> 
 *      failwith "floats not supported"
 *   | OVpointer p -> 
 *      let n = fresh () in
 *      let rt = 
 *        case_ptrval p 
 *          (fun _ctype ->  (\* case null *\)
 *            let lc = fresh () in
 *            RT.combine [RT.a n BT.Loc; RT.c lc (var_null n)])
 *          (fun _sym ->    (\* case function pointer *\)
 *            failwith "function pointers not supported")
 *          (fun _prov i -> (\* case concrete pointer *\)
 *            let constr = var_equal_to n (Num i) in
 *            let lc = fresh () in
 *            RT.combine [RT.a n BT.Loc; RT.c lc constr])
 *          (fun _ ->       (\* case unspecified_value *\)
 *            unreachable ())
 *      in
 *      (n, rt)
 *   | OVarray os -> 
 *      (\* let n = of_int (List.length os) in *\)
 *      let pointer = fresh () in
 *      let names, items = List.split (List.map infer_lv os) in
 *      let vars = List.map IT.var names in
 *      let r = fresh () in
 *      let ts = 
 *        ((RT.a pointer BT.Loc) :: List.concat items) @
 *        [RT.r r (Array (IT.Var pointer, IT.List vars))]
 *      in
 *      (pointer, RT.make ts)
 *   | OVstruct (sym,flds) -> 
 *      failwith "OVstruct not implemented"
 *   | OVunion _ -> 
 *      failwith "OVunion not implemented"
 * 
 * let rec infer_v rt : (id * RT.return_type) m =
 *   match rt with
 *   | Vobject ov -> infer_ov ov
 *   | Vloaded lv -> infer_lv lv
 *   | Vunit -> 
 *      fresh >>= fun n ->
 *      return (n, [RT.A (n, BT.Unit)])
 *   | Vtrue -> 
 *      fresh >>= fun n ->
 *      return (n, [RT.A (n,BT.Bool); RT.C (var_equal_to n (Bool true))])
 *   | Vfalse ->
 *      fresh >>= fun n ->
 *      return (n, [RT.A (n,BT.Bool); RT.C (var_equal_to n (Bool false))])
 *   | Vctype _ -> 
 *      unreachable ()
 *   | Vlist _ ->  
 *      unreachable ()
 *   | Vtuple vs -> 
 *      unreachable () *)


type fenv = (Symbol.sym, FT.function_type) Pmap.map
type aenv = (Symbol.sym, BT.base_type) Pmap.map
type lenv = (Symbol.sym, LS.logical_sort) Pmap.map
type cenv = LC.logical_constraint list
type renv = (Symbol.sym, RE.resource) Pmap.map

let rec infer_p fenv aenv lenv renv c = ()




let test_parse () = 
  let s = "(not ((1 + (x * 3)) < (2 + (x * 3))))" in
  print_endline (LC.pp (LC.parse_sexp Sym.Env.new_env (of_string s)));
  let s = "(array x (4 10))" in
  print_endline (RE.pp (RE.parse_sexp Sym.Env.new_env (of_string s)));
  let s = "((list int) -> loc)" in
  print_endline (LS.pp (LS.parse_sexp Sym.Env.new_env (of_string s)));
  let s = "(A (x : loc) . A (i : int) . ForallL (n : int) . ForallL (f : (int -> int)) . ((0 <= i) & (i < n)) => (array x n f) =* EL (r : int) . (r = (f i)) & (array x n f) * I)" in
  print_endline (FT.pp (FT.parse_sexp Sym.Env.new_env (of_string s)));
  print_endline "\n";
  ()


(* let test_value_infer () = 
 *   let infer v = snd (fst (infer_v v ID.init)) in
 *   let t = Vtrue in
 *   let () = print_endline (RT.pp (infer t)) in
 *   let t = 
 *     Vtuple 
 *       [Vtrue; 
 *        Vtuple [Vfalse; 
 *                Vobject (OVinteger (integer_ival (of_int 123)))]; 
 *        Vunit]
 *   in
 *   let () = print_endline (RT.pp (infer t)) in
 *   () *)


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
  let () = Pipeline.run_pp (Some (filename,"core")) pp in
  ();;
  (* print_endline (Pp_utils.to_plain_pretty_string pp) *)

let check (core_file : unit Core.typed_file) =
  let mu_file = Core_anormalise.normalise_file core_file in
  Tags.set_tagDefs core_file.tagDefs;
  pp_fun_map_decl core_file.funinfo;
  print_core_file core_file "out1";
  print_core_file (Mucore.mu_to_core__file mu_file) "out2";
  (* test_parse (); *)
  (* test_value_infer (); *)

