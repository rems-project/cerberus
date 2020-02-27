(* open Lem_pervasives  *)
open Core
open Impl_mem
open Nat_big_num
open Sexplib
open Printf


let o f g x = f (g (x))

let rec nest (fs : ('a -> 'a) list) = List.fold_right o fs (fun a -> a)


type integer_size


type ('a,'b) either = Left of 'a | Right of 'b

(* type num = Nat_big_num.num *)
type integer = Nat_big_num.num
type size = integer

type id = string
type loc = integer


(* Types and sorts *)

let pp_integer = string_of_int
let parse_integer = int_of_string

let pp_bool = function
  | true -> "true"
  | false -> "false"


let parse_error t sx = 
  let err = sprintf "unexpected %s: %s" t (Sexp.to_string sx) in
  raise (Invalid_argument err)


let pp_list f xs = 
  "[" ^ (String.concat ", " (List.map f xs)) ^ "]"

let sexp_list_to f = function
  | Sexp.Atom _ -> failwith "expected Sexp.List"
  | Sexp.List sxs -> List.map f sxs


let unreachable () = failwith "unreachable"



(* Types and sorts *)

module IT = struct

  type index_term =
    | Var of id
    | Int of integer
    | Bool of bool
    (* | IT_Loc of loc *)
    | Add of index_term * index_term
    | Sub of index_term * index_term
    | Mul of index_term * index_term
    | Div of index_term * index_term
    | Exp of index_term * index_term
    | Fun of id * index_term
    | App of index_term * index_term


  let rec pp_index_term = function
    | Var id -> 
       id
    | Int i -> 
       Nat_big_num.to_string i
    | Bool bool -> 
       pp_bool bool
    | Add (it1,it2) -> 
       sprintf "(%s + %s)" 
         (pp_index_term it1)
         (pp_index_term it2)
    | Sub (it1,it2) -> 
       sprintf "(%s - %s)" 
         (pp_index_term it1)
         (pp_index_term it2)
    | Mul (it1,it2) -> 
       sprintf "(%s * %s)" 
         (pp_index_term it1)
         (pp_index_term it2)
    | Div (it1,it2) -> 
       sprintf "(%s / %s)" 
         (pp_index_term it1)
         (pp_index_term it2)
    | Exp (it1,it2) -> 
       sprintf "(%s ^ %s)" 
         (pp_index_term it1)
         (pp_index_term it2)
    | Fun (id,it) ->
       sprintf "(fn %s %s)" 
         id 
         (pp_index_term it)
    | App (it1,it2) ->
       sprintf "(%s %s)" 
         (pp_index_term it1)
         (pp_index_term it2)


  let rec sexp_to_index_term sx = 
    let open Sexp in
    match sx with
    | Atom "true" -> 
       Bool true
    | Atom "false" -> 
       Bool false
    | Atom str -> 
       begin try Int (Nat_big_num.of_string str) with
       | _ -> Var str
       end
    | List [o1;Atom "+";o2] -> 
       Add (sexp_to_index_term o1, sexp_to_index_term o2)
    | List [o1;Atom "-";o2] -> 
       Sub (sexp_to_index_term o1, sexp_to_index_term o2)
    | List [o1;Atom "*";o2] -> 
       Mul (sexp_to_index_term o1, sexp_to_index_term o2)
    | List [o1;Atom "/";o2] -> 
       Div (sexp_to_index_term o1, sexp_to_index_term o2)
    | List [o1;Atom "^";o2] -> 
       Exp (sexp_to_index_term o1, sexp_to_index_term o2)
    | List [Atom "fn";Atom id;it] -> 
       Fun (id,sexp_to_index_term it)
    | List [o1;o2] -> 
       App (sexp_to_index_term o1, sexp_to_index_term o2)
    | t -> parse_error "index term" t

end

open IT

module LP = struct

  type logical_predicate = 
    | EQ of index_term * index_term
    | NE of index_term * index_term
    | LT of index_term * index_term
    | GT of index_term * index_term
    | LE of index_term * index_term
    | GE of index_term * index_term
    | Null of index_term

  let pp_logical_predicate = function
    | EQ (o1,o2) -> 
       sprintf "(%s = %s)" 
         (pp_index_term o1)
         (pp_index_term o2)
    | NE (o1,o2) -> 
       sprintf "(%s <> %s)" 
         (pp_index_term o1)
         (pp_index_term o2)
    | LT (o1,o2) -> 
       sprintf "(%s < %s)" 
         (pp_index_term o1)
         (pp_index_term o2)
    | GT (o1,o2) -> 
       sprintf "(%s > %s)" 
         (pp_index_term o1)
         (pp_index_term o2)
    | LE (o1,o2) -> 
       sprintf "(%s <= %s)" 
         (pp_index_term o1)
         (pp_index_term o2)
    | GE (o1,o2) -> 
       sprintf "(%s >= %s)" 
         (pp_index_term o1)
         (pp_index_term o2)
    | Null o1 ->
       sprintf "(null %s)" 
         (pp_index_term o1)

  let sexp_to_logical_predicate sx =
    let open Sexp in
    match sx with 
    | List [o1;op;o2] -> 
       let lp_o1 = sexp_to_index_term o1 in
       let lp_o2 = sexp_to_index_term o2 in
       begin match op with
       | Atom "=" -> EQ (lp_o1, lp_o2)
       | Atom "<>" -> NE (lp_o1, lp_o2)
       | Atom "<" -> LT (lp_o1, lp_o2)
       | Atom ">" -> GT (lp_o1, lp_o2)
       | Atom "<=" -> LE (lp_o1, lp_o2)
       | Atom ">=" -> GE (lp_o1, lp_o2)
       | t -> parse_error "logical predicate" t
       end
    | t -> parse_error "logical predicate" t
end

open LP

module LC = struct

  type logical_constraint =
    | Pred of logical_predicate
    | And of logical_constraint * logical_constraint
    | Not of logical_constraint


  let rec pp_logical_constraint = function
    | And (o1,o2) -> 
       sprintf "(%s & %s)" 
         (pp_logical_constraint o1)
         (pp_logical_constraint o2)
    | Not (o1) -> 
       sprintf "(not %s)" 
         (pp_logical_constraint o1)
    | Pred p -> 
       pp_logical_predicate p


  let rec sexp_to_logical_constraint sx =
    let open Sexp in
    match sx with
    | List [Atom "not";op] -> 
       Not (sexp_to_logical_constraint op)
    | List [o1; Atom "&"; o2] ->
       And (sexp_to_logical_constraint o1, sexp_to_logical_constraint o2)
    | l -> Pred (sexp_to_logical_predicate l)

end

open LC

module BT = struct

  type base_type = 
    | Unit
    | Bool
    | Int
    | Loc

  let pp_base_type = function
    | Unit -> "unit"
    | Bool -> "bool"
    | Int -> "int"
    | Loc -> "loc"

  let sexp_to_base_type sx = 
    let open Sexp in
    match sx with
    | Atom "unit" -> Unit
    | Atom "bool" -> Bool
    | Atom "int" -> Int
    | Atom "loc" -> Loc
    | a -> parse_error "base type" a

end

open BT

module RT = struct

  type resource_type = 
    | Block of index_term * index_term
    | Int of index_term * index_term (* location and value *)
    | Points of index_term * index_term
    | Uninit of index_term * index_term * resource_type
    | Array of index_term * index_term * index_term
   (* Array (pointer, size, (f : int -> loc)) *)

  let rec pp_resource_type = function
    | Block (it1,it2) -> 
       sprintf "(block %s %s)" 
         (pp_index_term it1)
         (pp_index_term it2)
    | Int (it1,it2) -> 
       sprintf "(int %s %s)" 
         (pp_index_term it1) 
         (pp_index_term it2)
    | Array (it1,it2,it3) -> 
       sprintf "(array %s %s %s)" 
         (pp_index_term it1)
         (pp_index_term it2)
         (pp_index_term it3)
    | Points (it1,it2) -> 
       sprintf "(points %s %s)" 
         (pp_index_term it1)
         (pp_index_term it2)
    | Uninit (it1,it2,rt) -> 
       sprintf "(uninit %s %s %s)" 
         (pp_index_term it1)
         (pp_index_term it2)
         (pp_resource_type rt)

  let rec sexp_to_resource_type sx = 
    let open Sexp in
    match sx with 
    | List [Atom "block";it1;it2] -> 
       Block (sexp_to_index_term it1,
              sexp_to_index_term it2)
    | List [Atom "int"; it1; it2] ->
       Int (sexp_to_index_term it1, 
            sexp_to_index_term it2)
    | List [Atom "array"; it1; it2; it3] ->
       Array (sexp_to_index_term it1, 
              sexp_to_index_term it2, 
              sexp_to_index_term it3)
    | List [Atom "points"; it1; it2] ->
       Points (sexp_to_index_term it1, 
               sexp_to_index_term it2)
    | List [Atom "uninit"; it1; it2; rt] ->
       Uninit (sexp_to_index_term it1, 
               sexp_to_index_term it2, 
               sexp_to_resource_type rt)
    | t -> parse_error "resource type" t
end

open RT


module LS = struct

  type logical_sort = 
    | Base of base_type
    | List of base_type
    | Fun of logical_sort * logical_sort


  let rec pp_logical_sort = function
    | List ls -> 
       sprintf "(list %s)" 
         (pp_base_type ls)
    | Fun (ls1,ls2) -> 
       sprintf "(%s -> %s)" 
         (pp_logical_sort ls1)
         (pp_logical_sort ls2)
    | Base bt -> 
         pp_base_type bt

  let rec sexp_to_logical_sort sx =
    match sx with
    | Sexp.List [Sexp.Atom "list"; a] ->
       List (sexp_to_base_type a)
    | Sexp.List [o1; Sexp.Atom "->"; o2] ->
       Fun (sexp_to_logical_sort o1, sexp_to_logical_sort o2)
    | ((Sexp.Atom _) as a) -> Base (sexp_to_base_type a)
    | ls -> parse_error "logical sort" ls

end

open LS


type return_type = 
  | ExistsC of id * base_type * return_type
  | ExistsL of id * logical_sort * return_type
  | AndR of resource_type * return_type
  | AndL of logical_constraint * return_type
  | Done

(* for currying *)
let existsC (id : id) (bt : base_type) (rt : return_type) : return_type = 
  ExistsC (id, bt, rt)
let existsL (id : id) (ls : logical_sort) (rt : return_type) : return_type = 
  ExistsL (id, ls, rt)
let andR (r : resource_type) (rt : return_type) : return_type = 
  AndR (r, rt)
let andL (ls : logical_constraint) (rt : return_type) : return_type = 
  AndL (ls, rt)



let rec pp_list_return_type = function
  | ExistsC (id, typ, rtyp) -> 
     sprintf "EC (%s : %s) . %s" 
       id 
       (pp_base_type typ)
       (pp_list_return_type rtyp)
  | ExistsL (id, ls, rtyp) ->
     sprintf "EL (%s : %s) %s" 
       id
       (pp_logical_sort ls)
       (pp_list_return_type rtyp)
  | AndR (rt, rtyp) ->
     sprintf "%s * %s" 
       (pp_resource_type rt)
       (pp_list_return_type rtyp)
  | AndL (lc, rtyp) ->
     sprintf "%s & %s"
       (pp_logical_constraint lc)
       (pp_list_return_type rtyp)
  | Done ->
     "I"

and pp_return_type rt = 
  sprintf "(%s)" (pp_list_return_type rt)


let rec list_sexp_to_return_type sx = 
  let open Sexp in 
  match sx with
  | Atom "EC" :: List [Atom id; Atom ":"; t] :: Atom "." :: rtyp ->
     ExistsC (id, sexp_to_base_type t, list_sexp_to_return_type rtyp)
  | Atom "EL" :: List [Atom id; Atom ":"; ls] :: Atom "." :: rtyp ->
     ExistsL (id, sexp_to_logical_sort ls, list_sexp_to_return_type rtyp)
  | rt :: Atom "*" :: rtyp ->
     AndR (sexp_to_resource_type rt, list_sexp_to_return_type rtyp)
  | lc :: Atom "&" :: rtyp ->
     AndL (sexp_to_logical_constraint lc, list_sexp_to_return_type rtyp)
  | Atom "I" :: [] -> Done
  | rt -> parse_error "return type" (List rt)

and sexp_to_return_type rt = 
  let open Sexp in
  match rt with
  | List rt -> list_sexp_to_return_type rt
  | Atom _ -> list_sexp_to_return_type [rt]


type function_type = 
  | ForallC of id * base_type * function_type
  | ForallL of id * logical_sort * function_type
  | ImpR of resource_type * function_type
  | ImpL of logical_constraint * function_type
  | Return of return_type

let forallC (id : id) (bt : base_type) (ft : function_type) : function_type = 
  ForallC (id, bt, ft)
let forallL (id : id) (ls : logical_sort) (ft : function_type) : function_type = 
  ForallL (id, ls, ft)
let impR (r : resource_type) (ft : function_type) : function_type = 
  ImpR (r, ft)
let impL (ls : logical_constraint) (ft : function_type) : function_type = 
  ImpL (ls, ft)


let rec pp_list_function_type = function
  | ForallC (id, bt, ftyp) -> 
     sprintf "A (%s : %s) . %s" 
       id 
       (pp_base_type bt)
       (pp_list_function_type ftyp)
  | ForallL (id, ls, ftyp) -> 
     sprintf "ForallL (%s : %s) . %s"
       id 
       (pp_logical_sort ls)
       (pp_list_function_type ftyp)
  | ImpR (rt,ftyp) ->
     sprintf "%s =* %s"
       (pp_resource_type rt)
       (pp_list_function_type ftyp)
  | ImpL (lc,ftyp) ->
     sprintf "%s => %s"
       (pp_logical_constraint lc)
       (pp_list_function_type ftyp)
  | Return rt ->
     pp_list_return_type rt

let pp_function_type ftyp = 
  sprintf "(%s)" (pp_list_function_type ftyp)
  

let rec list_sexp_to_function_type sx = 
  let open Sexp in
  match sx with
  | Atom "A" :: List [Atom id; Atom ":"; bt] :: Atom "." :: ftyp ->
     ForallC (id, sexp_to_base_type bt, list_sexp_to_function_type ftyp)
  | Atom "ForallL":: List [Atom id; Atom ":"; ls] :: Atom "." :: ftyp ->
     ForallL (id, sexp_to_logical_sort ls, list_sexp_to_function_type ftyp)
  | rt :: Atom "=*" :: ftyp ->
     ImpR (sexp_to_resource_type rt, list_sexp_to_function_type ftyp)
  | lc :: Atom "=>" :: ftyp ->
     ImpL (sexp_to_logical_constraint lc, list_sexp_to_function_type ftyp)
  | rt -> Return (list_sexp_to_return_type rt)


let sexp_to_function_type ftyp = 
  let open Sexp in
  match ftyp with
  | List ftyp -> list_sexp_to_function_type ftyp
  | Atom a -> list_sexp_to_function_type [ftyp]


(* Programs and terms *)

type 'a variable_context = (id * 'a) list

type cv_context = base_type variable_context
type lv_context = logical_sort variable_context
type rv_context = resource_type variable_context
type lc_context = logical_constraint list

let empty_context = []



(* Typing rules *)

(* value type inference *)

module ID : sig
  type id = string
  type id_state
  val init : id_state
  val fresh : id_state -> id * id_state
end = struct 
  type id = string
  type id_state = int
  let init = 0
  let fresh ids = (sprintf "%s%d" "_tv_" ids, ids + 1)
end

module ID_M = struct
  include ID
  type 'a m = id_state -> ('a * id_state)
  let return (a : 'a) : 'a m = 
    fun s -> (a,s)
  let bind (m : 'a m) (f : 'a -> 'b m) : 'b m = 
    fun s -> let a, s' = m s in f a s'
  let (>>=) = bind
  let rec doM (ms : ('a m) list) : ('a list) m = 
    match ms with
    | [] -> return []
    | m :: ms -> 
       m >>= fun x -> 
       doM ms >>= fun xs ->
       return (x :: xs)
end



open Core
open ID_M

let var_equal_to (id : id) (it : index_term) = 
  Pred (EQ (Var id, it))

let var_null (id : id) = 
  Pred (Null (Var id))


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

let infer_type__value v : return_type m = 

  let rec loaded_value_aux lv : (return_type -> return_type) m = 
    match lv with
    | LVspecified ov -> object_aux ov
    | LVunspecified _ -> failwith "LVunspecified not implemented"

  and object_aux ov : (return_type -> return_type) m = 
    match ov with
    | OVinteger i -> 
       fresh >>= fun n ->
       let i = option_get (eval_integer_value i) in
       return (nest [existsC n Int; andL (var_equal_to n (Int i))])
    | OVfloating _ -> 
       failwith "floats not supported"
    | OVpointer p -> 
       fresh >>= fun n ->
       case_ptrval p 
         (fun _ctype ->  (* case null *)
           return (nest [existsC n Loc; andL (var_null n)]))
         (fun _sym ->    (* case function pointer *)
           failwith "function pointers not supported")
         (fun _prov i -> (* case concrete pointer *)
          return (nest [existsC n Loc; andL (var_equal_to n (Int i))]))
         (fun _ ->       (* case unspecified_value *)
           unreachable ())
    | OVarray os -> failwith "not implemented yet"
       (* let n = List.length os in
        * fresh >>= fun pointer ->
        * fresh >>= fun f ->
        * return (nest [existsC pointer Loc;
        *               existsL size (Base Loc);
        *               existsL f (Fun (Base Loc, Base Loc));
        *               (\* do we have to specify f's index to location mapping *\)
        *               andR (Array (Var pointer, Var n, f));
        *               ]) *)
    | OVstruct _ -> 
       failwith "OVstruct not implemented"
    | OVunion _ -> 
       failwith "OVunion not implemented"
  in
    
  let rec value_aux rt : (return_type -> return_type) m =
    match rt with
    | Vobject ov -> object_aux ov
    | Vloaded lv -> loaded_value_aux lv
    | Vunit -> 
       fresh >>= fun n ->
       return (existsC n Unit)
    | Vtrue -> 
       fresh >>= fun n ->
       return (nest [existsC n Bool; andL (var_equal_to n (Bool true))])
    | Vfalse ->
       fresh >>= fun n ->
       return (nest [existsC n Bool; andL (var_equal_to n (Bool false))])
    | Vctype _ -> failwith "Vctype not supported"
    | Vlist _ ->  failwith "infer_type_value Vlist"
    | Vtuple vs -> 
       doM (List.map value_aux vs) >>= fun vs ->
       return (nest vs)
  in

  value_aux v >>= fun f -> 
  return (f Done)



let test_parse () = 
  let s = "(not ((1 + (x * 3)) < (2 + (x * 3))))" in
  print_endline (pp_logical_constraint (sexp_to_logical_constraint (Sexp.of_string s)));
  let s = "(array x (1 + (5 * y)) (fn i (i + 10)))" in
  print_endline (pp_resource_type (sexp_to_resource_type (Sexp.of_string s)));
  let s = "((list int) -> loc)" in
  print_endline (pp_logical_sort (sexp_to_logical_sort (Sexp.of_string s)));
  let s = "(EC (r : int) . (r = (f i)) & (array x n f) * I)" in
  print_endline (pp_return_type (sexp_to_return_type (Sexp.of_string s)));
  let s = "(A (x : loc) . A (i : int) . ForallL (n : int) . ForallL (f : (int -> int)) . ((0 <= i) & (i < n)) => (array x n f) =* EL (r : int) . (r = (f i)) & (array x n f) * I)" in
  print_endline (pp_function_type (sexp_to_function_type (Sexp.of_string s)));
  print_endline "\n";
  ()


let test_value_infer () = 
  let infer v = fst (infer_type__value v ID.init) in
  let t = Vtrue in
  let () = print_endline (pp_return_type (infer t)) in
  let t = 
    Vtuple 
      [Vtrue; 
       Vtuple [Vfalse; 
               Vobject (OVinteger (integer_ival (of_int 123)))]; 
       Vunit]
  in
  let () = print_endline (pp_return_type (infer t)) in
  ()


let pp_fun_map_decl f = 
  let pp = Pp_core.All.pp_funinfo_with_attributes f in
  print_string (Pp_utils.to_plain_string pp)

let check (core_file : unit Core.file) =
  let () = Tags.set_tagDefs core_file.tagDefs in
  let () = pp_fun_map_decl core_file.funinfo in
  test_parse ();
  test_value_infer ()

