(* open Lem_pervasives  *)
open Core
(* open Nat_big_num *)
open Sexplib
open Sexp
open Printf


(* type num = Nat_big_num.num *)
type integer = int
type num = integer
type size = integer

type id = string
type loc = integer


(* Types and sorts *)

let pp_integer = string_of_int
let parse_integer = int_of_string


let parse_error t sx = 
  let err = sprintf "unexpected %s: %s" t (Sexp.to_string sx) in
  raise (Invalid_argument err)


let pp_list f xs = 
  "[" ^ (String.concat ", " (List.map f xs)) ^ "]"

let sexp_list_to f = function
  | Atom _ -> failwith "expected List"
  | List sxs -> List.map f sxs


type index_term =
  | IT_Var of id
  | IT_Num of num
  (* | IT_Loc of loc *)
  | IT_Add of index_term * index_term
  | IT_Sub of index_term * index_term
  | IT_Mul of index_term * index_term
  | IT_Div of index_term * index_term
  | IT_Exp of index_term * index_term
  | IT_Fun of id * index_term
  | IT_App of index_term * index_term


let rec pp_index_term = function
  | IT_Var id -> 
     id
  | IT_Num num -> 
     pp_integer num
  | IT_Add (it1,it2) -> 
     sprintf "(%s + %s)" (pp_index_term it1) (pp_index_term it2)
  | IT_Sub (it1,it2) -> 
     sprintf "(%s - %s)" (pp_index_term it1) (pp_index_term it2)
  | IT_Mul (it1,it2) -> 
     sprintf "(%s * %s)" (pp_index_term it1) (pp_index_term it2)
  | IT_Div (it1,it2) -> 
     sprintf "(%s / %s)" (pp_index_term it1) (pp_index_term it2)
  | IT_Exp (it1,it2) -> 
     sprintf "(%s ^ %s)" (pp_index_term it1) (pp_index_term it2)
  | IT_Fun (id,it) ->
     sprintf "(fn %s %s)" id (pp_index_term it)
  | IT_App (it1,it2) ->
     sprintf "(%s %s)" (pp_index_term it1) (pp_index_term it2)


let rec sexp_to_index_term = function
  | Atom str -> 
     begin try IT_Num (parse_integer str) with
     | _ -> IT_Var str
     end
  | List [o1;Atom "+";o2] -> 
     IT_Add (sexp_to_index_term o1, sexp_to_index_term o2)
  | List [o1;Atom "-";o2] -> 
     IT_Sub (sexp_to_index_term o1, sexp_to_index_term o2)
  | List [o1;Atom "*";o2] -> 
     IT_Mul (sexp_to_index_term o1, sexp_to_index_term o2)
  | List [o1;Atom "/";o2] -> 
     IT_Div (sexp_to_index_term o1, sexp_to_index_term o2)
  | List [o1;Atom "^";o2] -> 
     IT_Exp (sexp_to_index_term o1, sexp_to_index_term o2)
  | List [Atom "fn";Atom id;it] -> 
     IT_Fun (id,sexp_to_index_term it)
  | List [o1;o2] -> 
     IT_App (sexp_to_index_term o1, sexp_to_index_term o2)
  | t -> parse_error "index term" t




type logical_predicate = 
  | LP_EQ of index_term * index_term
  | LP_NE of index_term * index_term
  | LP_LT of index_term * index_term
  | LP_GT of index_term * index_term
  | LP_LE of index_term * index_term
  | LP_GE of index_term * index_term

let pp_logical_predicate = function
  | LP_EQ (o1,o2) -> 
     sprintf "(%s = %s)" (pp_index_term o1) (pp_index_term o2)
  | LP_NE (o1,o2) -> 
     sprintf "(%s <> %s)" (pp_index_term o1) (pp_index_term o2)
  | LP_LT (o1,o2) -> 
     sprintf "(%s < %s)" (pp_index_term o1) (pp_index_term o2)
  | LP_GT (o1,o2) -> 
     sprintf "(%s > %s)" (pp_index_term o1) (pp_index_term o2)
  | LP_LE (o1,o2) -> 
     sprintf "(%s <= %s)" (pp_index_term o1) (pp_index_term o2)
  | LP_GE (o1,o2) -> 
     sprintf "(%s >= %s)" (pp_index_term o1) (pp_index_term o2)

let sexp_to_logical_predicate = function
  | List [o1;op;o2] -> 
     let lp_o1 = sexp_to_index_term o1 in
     let lp_o2 = sexp_to_index_term o2 in
     begin match op with
     | Atom "=" -> LP_EQ (lp_o1, lp_o2)
     | Atom "<>" -> LP_NE (lp_o1, lp_o2)
     | Atom "<" -> LP_LT (lp_o1, lp_o2)
     | Atom ">" -> LP_GT (lp_o1, lp_o2)
     | Atom "<=" -> LP_LE (lp_o1, lp_o2)
     | Atom ">=" -> LP_GE (lp_o1, lp_o2)
     | t -> parse_error "logical predicate" t
     end
  | t -> parse_error "logical predicate" t




type logical_constraint =
  | LC_Pred of logical_predicate
  | LC_And of logical_constraint * logical_constraint
  | LC_Not of logical_constraint


let rec pp_logical_constraint = function
  | LC_And (o1,o2) -> 
     sprintf "(%s & %s)" (pp_logical_constraint o1) (pp_logical_constraint o2)
  | LC_Not (o1) -> 
     sprintf "(not %s)" (pp_logical_constraint o1)
  | LC_Pred p -> 
     pp_logical_predicate p


let rec sexp_to_logical_constraint = function
  | List [Atom "not";op] -> 
     LC_Not (sexp_to_logical_constraint op)
  | List [o1; Atom "&"; o2] ->
     LC_And (sexp_to_logical_constraint o1, sexp_to_logical_constraint o2)
  | l -> LC_Pred (sexp_to_logical_predicate l)


type base_type = 
  | BT_Int
  | BT_Loc

let pp_base_type = function
  | BT_Int -> "int"
  | BT_Loc -> "loc"

let sexp_to_base_type = function
  | Atom "int" -> BT_Int
  | Atom "loc" -> BT_Loc
  | a -> parse_error "base type" a


type resource_type = 
  | RT_Block of index_term
  | RT_Int of index_term * index_term (* location and value *)
  | RT_Array of index_term * index_term * index_term
  | RT_Pointer of index_term * resource_type
  | RT_Uninit of index_term * resource_type * resource_type list

let rec pp_resource_type = function
  | RT_Block it -> 
     sprintf "(block %s)" 
       (pp_index_term it)
  | RT_Int (it1,it2) -> 
     sprintf "(int %s %s)" 
       (pp_index_term it1) 
       (pp_index_term it2)
  | RT_Array (it1,it2,it3) -> 
     sprintf "(array %s %s %s)" 
       (pp_index_term it1)
       (pp_index_term it2)
       (pp_index_term it3)
  | RT_Pointer (it,rt) -> 
     sprintf "(pointer %s %s)" 
       (pp_index_term it)
       (pp_resource_type rt)
  | RT_Uninit (it,rt,rts) -> 
     sprintf "(uninit %s %s %s)" 
       (pp_index_term it)
       (pp_resource_type rt)
       (pp_list pp_resource_type rts)

let rec sexp_to_resource_type = function
  | List [Atom "block";op] -> 
     RT_Block (sexp_to_index_term op)
  | List [Atom "int"; it1; it2] ->
     RT_Int (sexp_to_index_term it1, sexp_to_index_term it2)
  | List [Atom "array"; it1; it2; it3] ->
     RT_Array (sexp_to_index_term it1, 
               sexp_to_index_term it2, 
               sexp_to_index_term it3)
  | List [Atom "pointer"; it; rt] ->
     RT_Pointer (sexp_to_index_term it, sexp_to_resource_type rt)
  | List [Atom "uninit"; it; rt; rts] ->
     RT_Uninit (sexp_to_index_term it, 
                sexp_to_resource_type rt, 
                sexp_list_to (sexp_to_resource_type) rts)
  | t -> parse_error "resource type" t


type logical_sort = 
  | LS_Base of base_type
  | LS_List of base_type
  | LS_Fun of logical_sort * logical_sort


let rec pp_logical_sort = function
  | LS_List ls -> 
     sprintf "(list %s)" 
       (pp_base_type ls)
  | LS_Fun (ls1,ls2) -> 
     sprintf "(%s -> %s)" 
       (pp_logical_sort ls1)
       (pp_logical_sort ls2)
  | LS_Base bt -> 
       pp_base_type bt

let rec sexp_to_logical_sort = function
  | List [Atom "list"; a] ->
     LS_List (sexp_to_base_type a)
  | List [o1; Atom "->"; o2] ->
     LS_Fun (sexp_to_logical_sort o1, sexp_to_logical_sort o2)
  | ((Atom _) as a) -> LS_Base (sexp_to_base_type a)
  | ls -> parse_error "logical sort" ls



type return_type = 
  | RT_EC of (id * base_type) * return_type
  | RT_EL of (id * logical_sort) * return_type
  | RT_AndR of resource_type * return_type
  | RT_AndL of logical_constraint * return_type
  | RT_Done

let rec pp_list_return_type = function
  | RT_EC ((id,typ), rtyp) -> 
     sprintf "E (%s : %s) . %s" 
       id 
       (pp_base_type typ)
       (pp_list_return_type rtyp)
  | RT_EL ((id,ls), rtyp) ->
     sprintf "EL (%s : %s) %s" 
       id
       (pp_logical_sort ls)
       (pp_list_return_type rtyp)
  | RT_AndR (rt, rtyp) ->
     sprintf "%s * %s" 
       (pp_resource_type rt)
       (pp_list_return_type rtyp)
  | RT_AndL (lc, rtyp) ->
     sprintf "%s & %s"
       (pp_logical_constraint lc)
       (pp_list_return_type rtyp)
  | RT_Done ->
     "I"

let pp_return_type rt = 
  sprintf "(%s)" (pp_list_return_type rt)




let rec list_sexp_to_return_type = function
  | Atom "E" :: List [Atom id; Atom ":"; bt] :: Atom "." :: rtyp ->
     RT_EC ((id, sexp_to_base_type bt), list_sexp_to_return_type rtyp)
  | Atom "EL" :: List [Atom id; Atom ":"; ls] :: Atom "." :: rtyp ->
     RT_EL ((id, sexp_to_logical_sort ls), list_sexp_to_return_type rtyp)
  | rt :: Atom "*" :: rtyp ->
     RT_AndR (sexp_to_resource_type rt, list_sexp_to_return_type rtyp)
  | lc :: Atom "&" :: rtyp ->
     RT_AndL (sexp_to_logical_constraint lc, list_sexp_to_return_type rtyp)
  | Atom "I" :: [] -> RT_Done
  | rt -> parse_error "return type" (List rt)

let sexp_to_return_type rt = 
  match rt with
  | List rt -> list_sexp_to_return_type rt
  | Atom _ -> list_sexp_to_return_type [rt]


type function_type = 
  | FT_AC of (id * base_type) * function_type
  | FT_AL of (id * logical_sort) * function_type
  | FT_ImpR of resource_type * function_type
  | FT_ImpL of logical_constraint * function_type
  | FT_Return of return_type

let rec pp_list_function_type = function
  | FT_AC ((id,bt), ftyp) -> 
     sprintf "A (%s : %s) . %s" 
       id 
       (pp_base_type bt)
       (pp_list_function_type ftyp)
  | FT_AL ((id,ls), ftyp) -> 
     sprintf "AL (%s : %s) . %s"
       id 
       (pp_logical_sort ls)
       (pp_list_function_type ftyp)
  | FT_ImpR (rt,ftyp) ->
     sprintf "%s =* %s"
       (pp_resource_type rt)
       (pp_list_function_type ftyp)
  | FT_ImpL (lc,ftyp) ->
     sprintf "%s => %s"
       (pp_logical_constraint lc)
       (pp_list_function_type ftyp)
  | FT_Return rt ->
     pp_list_return_type rt

let pp_function_type ftyp = 
  sprintf "(%s)" (pp_list_function_type ftyp)
  

let rec list_sexp_to_function_type = function
  | Atom "A" :: List [Atom id; Atom ":"; bt] :: Atom "." :: ftyp ->
     FT_AC ((id, sexp_to_base_type bt), list_sexp_to_function_type ftyp)
  | Atom "AL":: List [Atom id; Atom ":"; ls] :: Atom "." :: ftyp ->
     FT_AL ((id, sexp_to_logical_sort ls), list_sexp_to_function_type ftyp)
  | rt :: Atom "=*" :: ftyp ->
     FT_ImpR (sexp_to_resource_type rt, list_sexp_to_function_type ftyp)
  | lc :: Atom "=>" :: ftyp ->
     FT_ImpL (sexp_to_logical_constraint lc, list_sexp_to_function_type ftyp)
  | rt -> FT_Return (list_sexp_to_return_type rt)


let sexp_to_function_type ftyp = 
  match ftyp with
  | List ftyp -> list_sexp_to_function_type ftyp
  | Atom a -> list_sexp_to_function_type [ftyp]


let test () = 
  let s = "(not ((1 + (x * 3)) < (2 + (x * 3))))" in
  print_endline (pp_logical_constraint (sexp_to_logical_constraint (of_string s)));
  let s = "(array x (1 + (5 * y)) (fn i (i + 10)))" in
  print_endline (pp_resource_type (sexp_to_resource_type (of_string s)));
  let s = "((list int) -> loc)" in
  print_endline (pp_logical_sort (sexp_to_logical_sort (of_string s)));
  let s = "(E (r : int) . (r = (f i)) & (array x n f) * I)" in
  print_endline (pp_return_type (sexp_to_return_type (of_string s)));
  let s = "(A (x : loc) . A (i : int) . AL (n : int) . AL (f : (int -> int)) . ((0 <= i) & (i < n)) => (array x n f) =* EL (r : int) . (r = (f i)) & (array x n f) * I)" in
  print_endline (pp_function_type (sexp_to_function_type (of_string s)));
  ()



let pp_fun_map_decl f = 
  print_string (Pp_utils.to_plain_string (Pp_core.All.pp_funinfo_with_attributes f))

let check core_file = 
  (* let _tags = Tags.tagDefs () in *)
  let _ = pp_fun_map_decl core_file.funinfo in
  test ()

