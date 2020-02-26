(* open Lem_pervasives  *)
open Core
open Impl_mem
open Nat_big_num
open Sexplib
open Printf


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

type index_term =
  | Var of id
  | Num of num
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
  | Num num -> 
     Nat_big_num.to_string num
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
     begin try Num (Nat_big_num.of_string str) with
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




type logical_constraint =
  | LC_Pred of logical_predicate
  | LC_And of logical_constraint * logical_constraint
  | LC_Not of logical_constraint


let rec pp_logical_constraint = function
  | LC_And (o1,o2) -> 
     sprintf "(%s & %s)" 
       (pp_logical_constraint o1)
       (pp_logical_constraint o2)
  | LC_Not (o1) -> 
     sprintf "(not %s)" 
       (pp_logical_constraint o1)
  | LC_Pred p -> 
     pp_logical_predicate p


let rec sexp_to_logical_constraint sx =
  let open Sexp in
  match sx with
  | List [Atom "not";op] -> 
     LC_Not (sexp_to_logical_constraint op)
  | List [o1; Atom "&"; o2] ->
     LC_And (sexp_to_logical_constraint o1, sexp_to_logical_constraint o2)
  | l -> LC_Pred (sexp_to_logical_predicate l)


type base_type = 
  | BT_Unit
  | BT_Bool
  | BT_Int
  | BT_Loc

let pp_base_type = function
  | BT_Unit -> "unit"
  | BT_Bool -> "bool"
  | BT_Int -> "int"
  | BT_Loc -> "loc"

let sexp_to_base_type sx = 
  let open Sexp in
  match sx with
  | Atom "unit" -> BT_Unit
  | Atom "bool" -> BT_Bool
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

let rec sexp_to_resource_type sx = 
  let open Sexp in
  match sx with 
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

let rec sexp_to_logical_sort sx =
  let open Sexp in
  match sx with
  | List [Atom "list"; a] ->
     LS_List (sexp_to_base_type a)
  | List [o1; Atom "->"; o2] ->
     LS_Fun (sexp_to_logical_sort o1, sexp_to_logical_sort o2)
  | ((Atom _) as a) -> LS_Base (sexp_to_base_type a)
  | ls -> parse_error "logical sort" ls



type return_type = 
  | RT_EC of (id * (base_type,return_type) either) * return_type
  | RT_EL of (id * logical_sort) * return_type
  | RT_AndR of resource_type * return_type
  | RT_AndL of logical_constraint * return_type
  | RT_Done

let rec pp_list_return_type = function
  | RT_EC ((id, typ), rtyp) -> 
     sprintf "E (%s : %s) . %s" 
       id 
       (begin match typ with 
        | Left typ -> pp_base_type typ
        | Right typ -> pp_return_type typ
        end)
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

and pp_return_type rt = 
  sprintf "(%s)" (pp_list_return_type rt)


let rec list_sexp_to_return_type sx = 
  let open Sexp in 
  match sx with
  | Atom "E" :: List [Atom id; Atom ":"; t] :: Atom "." :: rtyp ->
     let t = try Left (sexp_to_base_type t) with 
             | _ -> Right (sexp_to_return_type t)
     in
     RT_EC ((id, t), list_sexp_to_return_type rtyp)
  | Atom "EL" :: List [Atom id; Atom ":"; ls] :: Atom "." :: rtyp ->
     RT_EL ((id, sexp_to_logical_sort ls), list_sexp_to_return_type rtyp)
  | rt :: Atom "*" :: rtyp ->
     RT_AndR (sexp_to_resource_type rt, list_sexp_to_return_type rtyp)
  | lc :: Atom "&" :: rtyp ->
     RT_AndL (sexp_to_logical_constraint lc, list_sexp_to_return_type rtyp)
  | Atom "I" :: [] -> RT_Done
  | rt -> parse_error "return type" (List rt)

and sexp_to_return_type rt = 
  let open Sexp in
  begin match rt with
  | List rt -> list_sexp_to_return_type rt
  | Atom _ -> list_sexp_to_return_type [rt]
  end


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
  

let rec list_sexp_to_function_type sx = 
  let open Sexp in
  match sx with
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
  let open Sexp in
  begin match ftyp with
  | List ftyp -> list_sexp_to_function_type ftyp
  | Atom a -> list_sexp_to_function_type [ftyp]
  end


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
end = 
struct 
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
end



open Core
open ID_M

let var_equal_to (id : id) (it : index_term) = 
  LC_Pred (EQ (Var id, it))

let var_null (id : id) = 
  LC_Pred (Null (Var id))


let option_get = function
  | Some a -> a
  | None -> failwith "get None"



  let rec object_aux (cv,lv,lc) ov inner_rt : return_type m = 
    fresh >>= fun n ->
    begin match ov with

    | OVinteger i -> 
       let i = option_get (eval_integer_value i) in
       return (RT_EC ((n, Left BT_Int), 
                      RT_AndL (var_equal_to n (Num i), inner_rt)))

    | OVfloating _ -> failwith "floats not supported"

    | OVpointer p -> 

       let case_null _ctype =
         return (RT_EC ((n, Left BT_Loc), RT_AndL (var_null n, inner_rt))) in
       let case_function_pointer _sym = 
         failwith "function pointers not supported" in
       let case_concrete_pointer _prov i = 
         return (RT_EC ((n, Left BT_Loc), 
                        RT_AndL (var_equal_to n (Num i), inner_rt))) in
       let case_unspecified_value _ = unreachable () in

       case_ptrval 
         p
         case_null 
         case_function_pointer 
         case_concrete_pointer 
         case_unspecified_value

    | OVarray _ -> failwith "OVarray not implemented"
    | OVstruct _ -> failwith "OVstruct not implemented"
    end


let infer_type__value (cv,lv,lc) v : return_type m = 
    
  let rec value_aux (cv,lv,lc) outer_rt inner_rt : return_type m =
    begin match outer_rt with
    | Vobject ov -> object_aux (cv,lv,lc) ov inner_rt
    | Vloaded lv -> failwith "infer_type_value Vloaded"
    | Vunit -> 
       fresh >>= fun n ->
       return (RT_EC ((n, Left BT_Unit), inner_rt))
    | Vtrue -> 
       fresh >>= fun n ->
       return (RT_EC ((n, Left BT_Bool), 
                      RT_AndL (var_equal_to n (Bool true), inner_rt)))
    | Vfalse ->
       fresh >>= fun n ->
       return (RT_EC ((n, Left BT_Bool), 
                      RT_AndL (var_equal_to n (Bool false), inner_rt)))
    | Vctype _ -> failwith "Vctype not supported"
    | Vlist _ ->  failwith "infer_type_value Vlist"
    | Vtuple vs -> 
       fresh >>= fun n ->
       value_aux_list (cv,lv,lc) vs >>= fun ts ->
       return (RT_EC ((n, Right ts), inner_rt))
    end

  and value_aux_list (cv,lv,lc) vs : return_type m = 
    begin match vs with
    | [] -> 
       return RT_Done
    | v :: vs -> 
       value_aux_list (cv,lv,lc) vs >>= fun vts ->
       value_aux (cv,lv,lc) v vts
    end
  in

  value_aux (cv,lv,lc) v RT_Done



let test_parse () = 
  let s = "(not ((1 + (x * 3)) < (2 + (x * 3))))" in
  print_endline (pp_logical_constraint (sexp_to_logical_constraint (Sexp.of_string s)));
  let s = "(array x (1 + (5 * y)) (fn i (i + 10)))" in
  print_endline (pp_resource_type (sexp_to_resource_type (Sexp.of_string s)));
  let s = "((list int) -> loc)" in
  print_endline (pp_logical_sort (sexp_to_logical_sort (Sexp.of_string s)));
  let s = "(E (r : int) . (r = (f i)) & (array x n f) * I)" in
  print_endline (pp_return_type (sexp_to_return_type (Sexp.of_string s)));
  let s = "(A (x : loc) . A (i : int) . AL (n : int) . AL (f : (int -> int)) . ((0 <= i) & (i < n)) => (array x n f) =* EL (r : int) . (r = (f i)) & (array x n f) * I)" in
  print_endline (pp_function_type (sexp_to_function_type (Sexp.of_string s)));
  print_endline "\n\n";
  ()


let test_value_infer () = 
  let infer v = 
    fst (infer_type__value (empty_context, empty_context, empty_context) v init) in
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
  test_value_infer ()

