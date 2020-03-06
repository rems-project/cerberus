(* open Lem_pervasives  *)
open Core
open Impl_mem
open Nat_big_num
open Sexplib
open Sexp
open Printf


type id = string
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
    | Var of id
    | Num of num
    | Bool of bool
    | Add of index_term * index_term
    | Sub of index_term * index_term
    | Mul of index_term * index_term
    | Div of index_term * index_term
    | Exp of index_term * index_term
    | App of index_term * index_term
    | List of index_term list

  let var id = Var id

  let rec pp = function
    | Var id -> id
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


  let rec parse_sexp sx = 
    match sx with
    | Atom "true" -> Bool true
    | Atom "false" -> Bool false
    | Atom str when Str.string_match (Str.regexp "[0-9]+") str 0 ->
       Num (Nat_big_num.of_string str)
    | Atom str -> Var str
    | List [o1;Atom "+";o2] -> Add (parse_sexp o1, parse_sexp o2)
    | List [o1;Atom "-";o2] -> Sub (parse_sexp o1, parse_sexp o2)
    | List [o1;Atom "*";o2] -> Mul (parse_sexp o1, parse_sexp o2)
    | List [o1;Atom "/";o2] -> Div (parse_sexp o1, parse_sexp o2)
    | List [o1;Atom "^";o2] -> Exp (parse_sexp o1, parse_sexp o2)
    | List [Atom "list"; its] -> List (parse_sexp_list parse_sexp its)
    | List [o1;o2] -> App (parse_sexp o1, parse_sexp o2)
    | t -> parse_error "index term" t

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

  let parse_sexp sx =
    match sx with 
    | List [o1;Atom "=";o2]  -> EQ (IT.parse_sexp o1, IT.parse_sexp o2)
    | List [o1;Atom "<>";o2] -> NE (IT.parse_sexp o1, IT.parse_sexp o2)
    | List [o1;Atom "<";o2]  -> LT (IT.parse_sexp o1, IT.parse_sexp o2)
    | List [o1;Atom ">";o2]  -> GT (IT.parse_sexp o1, IT.parse_sexp o2)
    | List [o1;Atom "<=";o2] -> LE (IT.parse_sexp o1, IT.parse_sexp o2)
    | List [o1;Atom ">=";o2] -> GE (IT.parse_sexp o1, IT.parse_sexp o2)
    | t -> parse_error "logical predicate" t
end


module LC = struct

  type logical_constraint =
    | Pred of LP.logical_predicate
    | And of logical_constraint * logical_constraint
    | Not of logical_constraint

  let rec pp = function
    | And (o1,o2) -> sprintf "(%s & %s)" (pp o1) (pp o2)
    | Not (o1) -> sprintf "(not %s)" (pp o1)
    | Pred p -> LP.pp p

  let rec parse_sexp sx =
    match sx with
    | List [Atom "not";op] -> Not (parse_sexp op)
    | List [o1; Atom "&"; o2] -> And (parse_sexp o1, parse_sexp o2)
    | l -> Pred (LP.parse_sexp l)

end


module BT = struct

  type base_type = 
    | Unit
    | Bool
    | Int
    | Loc
    | Struct of id

  let rec pp = function
    | Unit -> "unit"
    | Bool -> "bool"
    | Int -> "int"
    | Loc -> "loc"
    | Struct id -> sprintf "(struct %s)" id

  let rec parse_sexp sx = 
    match sx with
    | Atom "unit" -> Unit
    | Atom "bool" -> Bool
    | Atom "int" -> Int
    | Atom "loc" -> Loc
    | List [Atom "struct"; Atom id] -> Struct id
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

  let rec parse_sexp sx = 
    match sx with 
    | List [Atom "block";it1;it2] -> 
       Block (IT.parse_sexp it1,
              IT.parse_sexp it2)
    | List [Atom "int"; it1; it2] ->
       Int (IT.parse_sexp it1, 
            IT.parse_sexp it2)
    | List [Atom "array"; it1; it2] ->
       Array (IT.parse_sexp it1, 
              IT.parse_sexp it2)
    | List [Atom "points"; it1; it2] ->
       Points (IT.parse_sexp it1, 
               IT.parse_sexp it2)
    | List [Atom "uninit"; it1; it2; rt] ->
       Uninit (IT.parse_sexp it1, 
               IT.parse_sexp it2, 
               parse_sexp rt)
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

  let rec parse_sexp sx =
    match sx with
    | Sexp.List [Atom "list"; a] ->
       List (BT.parse_sexp a)
    | Sexp.List [o1; Atom "->"; o2] ->
       Fun (parse_sexp o1, parse_sexp o2)
    | ((Sexp.Atom _) as a) -> Base (BT.parse_sexp a)
    | ls -> parse_error "logical sort" ls

end


module RT = struct

  type return_item = 
    | A of id * BT.base_type
    | L of id * LS.logical_sort
    | R of RE.resource
    | C of LC.logical_constraint

  type return_type = return_item list


  let rec pp = function
    | A (id, typ) :: ret -> 
       sprintf "EC (%s : %s) . %s" id (BT.pp typ) (pp ret)
    | L (id, ls) :: ret  -> 
       sprintf "EL (%s : %s) . %s" id (LS.pp ls) (pp ret)
    | R rt :: ret -> 
       sprintf "%s * %s" (RE.pp rt) (pp ret)
    | C lc :: ret -> 
       sprintf "%s & %s" (LC.pp lc) (pp ret)
    | [] -> 
       "I"

  let rec parse_sexp = function
    | Atom "EC" :: List [Atom id; Atom ":"; t] :: Atom "." :: ret ->
       A (id, BT.parse_sexp t) :: parse_sexp ret
    | Atom "EL" :: List [Atom id; Atom ":"; ls] :: Atom "." :: ret ->
       L (id, LS.parse_sexp ls) :: parse_sexp ret
    | rt :: Atom "*" :: ret ->
       R (RE.parse_sexp rt) :: parse_sexp ret
    | lc :: Atom "&" :: ret ->
       C (LC.parse_sexp lc) :: parse_sexp ret
    | Atom "I" :: [] -> 
       []
    | rt -> 
       parse_error "return type" (List rt)

end


module FT = struct

  
  (* basically the same as return_item, so could unify if it stays
     like this? *)
  type argument = 
    | A of id * BT.base_type
    | L of id * LS.logical_sort
    | R of RE.resource
    | C of LC.logical_constraint

  type arguments = argument list

  type function_type = Fn of arguments * RT.return_type

  let rec pp_arguments = function
    | A (id, bt) :: args -> 
       sprintf "AC (%s : %s) . %s" id (BT.pp bt) (pp_arguments args)
    | L (id, ls) :: args -> 
       sprintf "AL (%s : %s) . %s" id (LS.pp ls) (pp_arguments args)
    | R (rt) :: args ->
       sprintf "%s =* %s" (RE.pp rt) (pp_arguments args)
    | C (lc) :: args ->
       sprintf "%s => %s" (LC.pp lc) (pp_arguments args)
    | [] -> 
       ""

  let pp (Fn (args, rt)) = 
    sprintf "%s%s" (pp_arguments args) (RT.pp rt)

  let rec parse_sexp_aux acc = function
    | Atom "AC" :: List [Atom id; Atom ":"; bt] :: Atom "." :: args ->
       parse_sexp_aux (A (id, BT.parse_sexp bt) :: acc) args
    | Atom "AL":: List [Atom id; Atom ":"; ls] :: Atom "." :: args ->
       parse_sexp_aux (L (id, LS.parse_sexp ls) :: acc) args
    | rt :: Atom "=*" :: args ->
       parse_sexp_aux (R (RE.parse_sexp rt) :: acc) args
    | lc :: Atom "=>" :: args ->
       parse_sexp_aux (C (LC.parse_sexp lc) :: acc) args
    | rt -> 
       Fn (List.rev acc, RT.parse_sexp rt)

  let parse_sexp = function
    | List ft -> parse_sexp_aux [] ft
    | t -> parse_error "function type" t
         
end
  





(* Programs and terms *)

type 'a variable_context = (id * 'a) list

type cv_context = BT.base_type variable_context
type lv_context = LS.logical_sort variable_context
type rv_context = RE.resource variable_context
type lc_context = LC.logical_constraint list

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
  let foreach (f : 'a -> 'b m) (xs : 'a list) : ('b list) m = 
    doM (List.map f xs)
    
  let liftM (f : 'a -> 'b) (x : 'a) : 'b m =
    return (f x)
end



open Core
open ID_M





let var_equal_to (id : id) (it : IT.index_term) = 
  LC.Pred (EQ (Var id, it))

let var_null (id : id) = 
  LC.Pred (Null (Var id))


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



let rec infer_lv lv : (id * RT.return_type) m = 
  match lv with
  | LVspecified ov -> infer_ov ov
  | LVunspecified _ -> failwith "LVunspecified not implemented"

and infer_ov ov : (id * RT.return_type) m = 
  match ov with
  | OVinteger i -> 
     fresh >>= fun n ->
     let i = option_get (eval_integer_value i) in
     return (n, [RT.A (n,BT.Int); RT.C (var_equal_to n (Num i))])
  | OVfloating _ -> 
     failwith "floats not supported"
  | OVpointer p -> 
     fresh >>= fun n ->
     case_ptrval p 
       (fun _ctype ->  (* case null *)
         return (n, [RT.A (n,BT.Loc); RT.C (var_null n)]))
       (fun _sym ->    (* case function pointer *)
         failwith "function pointers not supported")
       (fun _prov i -> (* case concrete pointer *)
        return (n, [RT.A (n,BT.Loc); RT.C (var_equal_to n (Num i))]))
       (fun _ ->       (* case unspecified_value *)
         unreachable ())
  | OVarray os -> 
     (* let n = of_int (List.length os) in *)
     fresh >>= fun pointer ->
     foreach infer_lv os >>= fun os ->
     let names, items = List.split os in
     let ts = 
       (RT.A (pointer, BT.Loc) :: List.concat items) @
       [RT.R (Array (IT.Var pointer, IT.List (List.map IT.var names)))]
     in
     return (pointer, ts)
  | OVstruct (sym,flds) -> 
     failwith "OVstruct not implemented"
  | OVunion _ -> 
     failwith "OVunion not implemented"

let rec infer_v rt : (id * RT.return_type) m =
  match rt with
  | Vobject ov -> infer_ov ov
  | Vloaded lv -> infer_lv lv
  | Vunit -> 
     fresh >>= fun n ->
     return (n, [RT.A (n, BT.Unit)])
  | Vtrue -> 
     fresh >>= fun n ->
     return (n, [RT.A (n,BT.Bool); RT.C (var_equal_to n (Bool true))])
  | Vfalse ->
     fresh >>= fun n ->
     return (n, [RT.A (n,BT.Bool); RT.C (var_equal_to n (Bool false))])
  | Vctype _ -> 
     unreachable ()
  | Vlist _ ->  
     unreachable ()
  | Vtuple vs -> 
     unreachable ()


type fenv = (Symbol.sym, FT.function_type) Pmap.map
type aenv = (Symbol.sym, BT.base_type) Pmap.map
type lenv = (Symbol.sym, LS.logical_sort) Pmap.map
type cenv = LC.logical_constraint list
type renv = (Symbol.sym, RE.resource) Pmap.map

let rec infer_p fenv aenv lenv renv c = ()




let test_parse () = 
  let s = "(not ((1 + (x * 3)) < (2 + (x * 3))))" in
  print_endline (LC.pp (LC.parse_sexp (of_string s)));
  let s = "(array x (4 10))" in
  print_endline (RE.pp (RE.parse_sexp (of_string s)));
  let s = "((list int) -> loc)" in
  print_endline (LS.pp (LS.parse_sexp (of_string s)));
  let s = "(A (x : loc) . A (i : int) . ForallL (n : int) . ForallL (f : (int -> int)) . ((0 <= i) & (i < n)) => (array x n f) =* EL (r : int) . (r = (f i)) & (array x n f) * I)" in
  print_endline (FT.pp (FT.parse_sexp (of_string s)));
  print_endline "\n";
  ()


let test_value_infer () = 
  let infer v = snd (fst (infer_v v ID.init)) in
  let t = Vtrue in
  let () = print_endline (RT.pp (infer t)) in
  let t = 
    Vtuple 
      [Vtrue; 
       Vtuple [Vfalse; 
               Vobject (OVinteger (integer_ival (of_int 123)))]; 
       Vunit]
  in
  let () = print_endline (RT.pp (infer t)) in
  ()


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
  let normalised_core_file = Core_anormalise.normalise_file core_file in
  print_core_file core_file "out1";
  Tags.set_tagDefs core_file.tagDefs;
  pp_fun_map_decl core_file.funinfo;
  print_core_file normalised_core_file "out2";
  let _mu_file = Mucore.core_to_mu__file normalised_core_file in
  (* test_parse (); *)
  test_value_infer ();

