module CF = Cerb_frontend
module Loc = Locations
module BT = BaseTypes
open Pp


module Terms = struct

  type term = 
    | Addr of string
    | Var of string
    | Pointee of term
    | Member of term * Id.t
    | StructUpdate of (term * Id.t) * term
    | ArraySet of (term * term) * term
    | Bool of bool
    | Integer of Z.t
    | Addition of term * term
    | Subtraction of term * term
    | Multiplication of term * term
    | Division of term * term
    | Exponentiation of term * term
    | Remainder of term * term
    | Modulus of term * term
    | Equality of term * term
    | Inequality of term * term
    | ITE of term * term * term
    | Or of term * term
    | And of term * term
    | Not of term
    | LessThan of term * term
    | LessOrEqual of term * term
    | GreaterThan of term * term
    | GreaterOrEqual of term * term
    | IntegerToPointerCast of term
    | PointerToIntegerCast of term
    (* | PredEqRegulator of string list * term *)
    | Null
    | OffsetOf of {tag:string; member:string}
    | MemberShift of {pointer:term; member:string}
    (* | ArrayShift of {pointer:term; index:term} *)
    | CellPointer of (term * term) * (term * term) * term
    | DatatypeCons of (string * (string * term) list)
    | App of term * term
    | Env of term * string
    | Unchanged of term
    | For of (Z.t * string * Z.t) * term
    | Pred of string * term list
  [@@deriving eq, ord]



  let equal = equal_term
  let compare = compare_term



  let mparens atomic pp = 
    if atomic then parens pp else pp

  let rec pp atomic = function
    | Addr b -> 
       ampersand ^^ !^b
    | Var b -> 
       !^b
    | Pointee p -> 
       star ^^ (pp true p)
    | Member (p, m) -> 
       pp true p ^^ dot ^^ Id.pp m
    | StructUpdate ((t, m), v) ->
       mparens atomic (pp true t ^^ braces (dot ^^ Id.pp m ^^^ equals ^^^ pp true v))
    | ArraySet ((t, i), v) ->
       mparens atomic (pp true t ^^ brackets (pp true i ^^^ equals ^^^ pp true v))
    | Bool b -> 
       !^(if b then "true" else "false")
    | Integer z -> 
       !^(Z.to_string z)
    | Addition (t1, t2) -> 
       mparens atomic (pp true t1 ^^^ plus ^^^ pp true t2)
    | Subtraction (t1, t2) -> 
       mparens atomic (pp true t1 ^^^ minus ^^^ pp true t2)
    | Multiplication (t1, t2) -> 
       mparens atomic (pp true t1 ^^^ star ^^^ pp true t2)
    | Division (t1, t2) -> 
       mparens atomic (pp true t1 ^^^ !^"/" ^^^ pp true t2)
    | Exponentiation (t1, t2) -> 
       c_app !^"power" [pp false t1; pp false t2]
    | Remainder (t1, t2) -> 
       c_app !^"rem" [pp false t1; pp false t2]
    | Modulus (t1, t2) -> 
       c_app !^"mod" [pp false t1; pp false t2]
    | Equality (t1, t2) -> 
       mparens atomic (pp true t1 ^^^ !^"==" ^^^ pp true t2)
    (* | PredEqRegulator ([], t) -> *)
    (*    mparens atomic (!^"{}" ^^^ pp true t) *)
    (* | PredEqRegulator (ss, t) -> *)
    (*    mparens atomic (!^"{/" ^^^ flow comma (List.map (format []) ss) ^^ !^"}" ^^ pp true t) *)
    | Inequality (t1, t2) -> 
       mparens atomic (pp true t1 ^^^ !^"!=" ^^^ pp true t2)
    | ITE (t1, t2, t3) ->
       mparens atomic (pp true t1 ^^^ !^"?" ^^^ pp true t2
                       ^^^ !^":" ^^^ pp true t3)
    | Or (t1, t2) ->
       mparens atomic (pp true t1 ^^^ !^"||" ^^^ pp true t2)
    | And (t1, t2) ->
       mparens atomic (pp true t1 ^^^ !^"&&" ^^^ pp true t2)
    | Not t ->
       mparens atomic (!^"!" ^^ parens (pp false t))
    | LessThan (t1, t2) -> 
       mparens atomic (pp true t1 ^^^ !^"<" ^^^ pp true t2)
    | LessOrEqual (t1, t2) -> 
       mparens atomic (pp true t1 ^^^ !^"<=" ^^^ pp true t2)
    | GreaterThan (t1, t2) -> 
          mparens atomic (pp true t1 ^^^ !^">" ^^^ pp true t2)
    | GreaterOrEqual (t1, t2) -> 
       mparens atomic (pp true t1 ^^^ !^">=" ^^^ pp true t2)
    | IntegerToPointerCast t1 ->
       mparens atomic (parens !^"pointer" ^^ (pp true t1))
    | PointerToIntegerCast t1 ->
       mparens atomic (parens !^"integer" ^^ (pp true t1))
    | Null ->
       !^"NULL"
    | OffsetOf {tag; member} ->
       mparens atomic (c_app !^"offsetof" [!^tag; !^member])
    | MemberShift {pointer; member} ->
       mparens atomic (!^"&" ^^ parens ((pp true pointer) ^^ !^"->" ^^ !^member))
    (* | ArrayShift {pointer; index} -> *)
    (*    mparens atomic (!^"&" ^^ parens ((pp true pointer) ^^ brackets (pp false index))) *)
    | CellPointer ((base, step), (from_index, to_index), pointer) ->
       mparens atomic 
         (c_app !^"cellPointer" 
            [pp false base; pp false step; 
             pp false from_index; pp false to_index; 
             pp false pointer])
    | DatatypeCons (nm, eqs) ->
       mparens atomic (!^ nm ^^^ braces (flow comma (List.map
            (fun (nm, t) -> !^ nm ^^^ equals ^^^ pp true t) eqs)))
    | App (t1, t2) ->
       mparens atomic (pp true t1 ^^ brackets (pp false t2))
    | Env (t, e) ->
       parens (pp false t) ^^ at ^^ !^e
    | Unchanged t ->
       parens (pp false t) ^^^ !^"unchanged"
    | For ((i, name, j), body) ->
       mparens atomic
         (!^"for" ^^ parens(!^(Z.to_string i) ^^ comma ^^^ !^name ^^ comma ^^^ !^(Z.to_string j)) ^^^
            braces (pp false body))
    | Pred (name, args) ->
       mparens atomic
         (c_app !^name (List.map (pp false) args))
       



  let addr bn = 
    Addr bn

  let var bn = 
    Var bn


  let pointee = function
    | Addr var -> Var var
    | t -> Pointee t

  (* let predarg pr a = *)
  (*   PredOutput (pr,a) *)

  let contains_env_or_unchanged_expression t = 
    let rec aux = function
      | Addr bn -> 
         false
      | Var bn -> 
         false
      | Pointee p -> 
         false
      | Member (p, m) -> 
         aux p
      | StructUpdate ((t, m), v) ->
         aux t || aux v
      | ArraySet ((t, i), v) ->
         aux t || aux i || aux v
      | Bool b -> 
         false
      | Integer i -> 
         false
      | Addition (t1, t2) -> 
         aux t1 || aux t2
      | Subtraction (t1, t2) -> 
         aux t1 || aux t2
      | Multiplication (t1, t2) -> 
         aux t1 || aux t2
      | Division (t1, t2) -> 
         aux t1 || aux t2
      | Exponentiation (t1, t2) -> 
         aux t1 || aux t2
      | Remainder (t1, t2) -> 
         aux t1 || aux t2
      | Modulus (t1, t2) -> 
         aux t1 || aux t2
      | Equality (t1, t2) -> 
         aux t1 || aux t2
      (* | PredEqRegulator (_, t) -> aux t *)
      | Inequality (t1, t2) -> 
         aux t1 || aux t2
      | ITE (t1, t2, t3) ->
         aux t1 || aux t2 || aux t3
      | Or (t1, t2) ->
         aux t1 || aux t2
      | And (t1, t2) ->
         aux t1 || aux t2
      | Not t ->
         aux t
      | LessThan (t1, t2) -> 
         aux t1 || aux t2
      | LessOrEqual (t1, t2) -> 
         aux t1 || aux t2
      | GreaterThan (t1, t2) -> 
         aux t1 || aux t2
      | GreaterOrEqual (t1, t2) -> 
         aux t1 || aux t2
      | IntegerToPointerCast t ->
         aux t
      | PointerToIntegerCast t ->
         aux t
      | Null ->
         false
      | OffsetOf {tag; member} ->
         false
      | MemberShift {pointer; member} ->
         aux pointer
      (* | ArrayShift {pointer; index} -> *)
      (*    aux pointer || aux index *)
      | CellPointer ((t1, t2), (t3, t4), t5) ->
         aux t1 || aux t2 || aux t3 || aux t4 || aux t5
      | DatatypeCons (nm, eqs) ->
         List.exists (fun (_, t) -> aux t) eqs
      | App (t1, t2) ->
         aux t1 || aux t2
      | Env (t, _) ->
         true
      | Unchanged _ ->
         true
      | For (_, body) ->
         aux body
      | Pred (name, args) ->
         List.exists aux args
    in
    aux t
  



end

include Terms





type typ = 
  | Typeof of term
  | Struct of string
  | Pointer of typ


type predicate = {
    oq : (string * BT.t * term) option;
    predicate : string;
    arguments : term list;
    o_permission: term option;
    typ: typ option;
  }

type condition = 
  | Constraint of (string * BT.t * term) option * term
  | Resource of string * predicate
  | Define of string * term




type keyword_condition = 
  | Accesses of Id.t list
  | Trusted
  | Requires of (Loc.t * condition) list
  | Ensures of (Loc.t * condition) list
  | Inv of (Loc.t * condition) list
  | Make_Function of Id.t



(* arguments with values *)
type varg = { vsym : Sym.t; typ : Sctypes.t }
(* arguments with addresses *)
type aarg = { asym : Sym.t; typ : Sctypes.t }
(* arguments with either addresses or values *)
type earg = { esym : Sym.t; typ : Sctypes.t }
(* global arguments *)
type garg = { asym : Sym.t; lsym : Sym.t; typ : Sctypes.t; accessed : Loc.t option }


type function_spec = { 
    trusted: CF.Mucore.trusted;
    global_arguments : garg list;
    function_arguments : earg list;
    function_return : varg;
    pre_condition : (Loc.t * condition) list;
    post_condition : (Loc.t * condition) list;
    defines_log_funs : Id.t list;
  }


type label_spec = {
    global_arguments : garg list;
    label_arguments: aarg list;
    invariant : (Loc.t * condition) list
  }
