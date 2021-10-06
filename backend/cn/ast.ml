module Loc = Locations
module BT = BaseTypes
open Pp


module Terms = struct

  type term = 
    | Addr of string
    | Var of string
    | Pointee of term
    | PredOutput of string * string
    | Member of term * Id.t
    | Integer of Z.t
    | Addition of term * term
    | Subtraction of term * term
    | Multiplication of term * term
    | Division of term * term
    | Exponentiation of term * term
    | Remainder of term * term
    | Equality of term * term
    | Inequality of term * term
    | ITE of term * term * term
    | Or of term * term
    | And of term * term
    | LessThan of term * term
    | LessOrEqual of term * term
    | GreaterThan of term * term
    | GreaterOrEqual of term * term
    | IntegerToPointerCast of term
    | PointerToIntegerCast of term
    | Null
    | OffsetOf of {tag:string; member:string}
    | App of term * term
    | Env of term * string



  let rec term_equal t1 t2 =
    match t1, t2 with
    | Addr b1, Addr b2 ->
       String.equal b1 b2
    | Var b1, Var b2 -> 
       String.equal b1 b2
    | Pointee p1, Pointee p2 ->
       term_equal p1 p2
    | PredOutput (p1, a1), PredOutput (p2, a2) ->
       String.equal p1 p2 && String.equal a1 a2
    | Member (t1, m1), Member (t2, m2) ->
       term_equal t1 t2 && Id.equal m1 m2
    | Integer i1, Integer i2 -> 
       Z.equal i1 i2
    | Addition (a11,a12), Addition (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | Subtraction (a11,a12), Subtraction (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | Multiplication (a11,a12), Multiplication (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | Division (a11,a12), Division (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | Exponentiation (a11,a12), Exponentiation (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | Remainder (a11,a12), Remainder (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | Equality (a11,a12), Equality (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | Inequality (a11,a12), Inequality (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | LessThan (a11,a12), LessThan (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | ITE (a11,a12,a13), ITE (a21,a22,a23) ->
       term_equal a11 a21 && term_equal a12 a22 && term_equal a13 a23
    | Or (a11,a12), Or (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | And (a11,a12), And (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | LessOrEqual (a11,a12), LessOrEqual (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | GreaterThan (a11,a12), GreaterThan (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | GreaterOrEqual (a11,a12), GreaterOrEqual (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | IntegerToPointerCast t1, IntegerToPointerCast t2 ->
       term_equal t1 t2
    | PointerToIntegerCast t1, PointerToIntegerCast t2 ->
       term_equal t1 t2
    | Null, Null ->
       true
    | OffsetOf {tag; member}, OffsetOf {tag=tag'; member=member'} ->
       String.equal tag tag' && String.equal member member'
    | App (t11, t12), App (t21, t22) ->
       term_equal t11 t21 && term_equal t12 t22
    | Env (t1, e1), Env (t2, e2) ->
       term_equal t1 t2 && String.equal e1 e2
    | Addr _, _ -> 
       false
    | Var _, _ ->
       false
    | Pointee _, _ ->
       false
    | PredOutput _, _ ->
       false
    | Member _, _ ->
       false
    | Integer _, _ -> 
       false
    | Addition _, _ -> 
       false
    | Subtraction _, _ -> 
       false
    | Multiplication _, _ -> 
       false
    | Division _, _ -> 
       false
    | Exponentiation _, _ -> 
       false
    | Remainder _, _ -> 
       false
    | Equality _, _ ->
       false
    | Inequality _, _ ->
       false
    | ITE _, _ ->
       false
    | Or _, _ ->
       false
    | And _, _ ->
       false
    | LessThan _, _ ->
       false
    | LessOrEqual _, _ ->
       false
    | GreaterThan _, _ ->
       false
    | GreaterOrEqual _, _ ->
       false
    | IntegerToPointerCast _, _ ->
       false
    | PointerToIntegerCast _, _ -> 
       false
    | Null, _ ->
       false
    | OffsetOf _, _ ->
       false
    | App _, _ ->
       false
    | Env _, _ ->
       false



  let mparens atomic pp = 
    if atomic then parens pp else pp

  let rec pp atomic = function
    | Addr b -> 
       ampersand ^^ !^b
    | Var b -> 
       !^b
    | Pointee p -> 
       star ^^ (pp true p)
    | PredOutput (p,a) -> 
       !^p ^^ dot ^^ dot ^^ !^a
    | Member (p, m) -> 
       pp true p ^^ dot ^^ Id.pp m
    | Integer z -> !^(Z.to_string z)
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
       mparens atomic (pp true t1 ^^^ !^"%" ^^^ pp true t2)
    | Equality (t1, t2) -> 
       mparens atomic (pp true t1 ^^^ !^"==" ^^^ pp true t2)
    | Inequality (t1, t2) -> 
       mparens atomic (pp true t1 ^^^ !^"!=" ^^^ pp true t2)
    | ITE (t1, t2, t3) ->
       mparens atomic (pp true t1 ^^^ !^"?" ^^^ pp true t2
                       ^^^ !^":" ^^^ pp true t3)
    | Or (t1, t2) ->
       mparens atomic (pp true t1 ^^^ !^"||" ^^^ pp true t2)
    | And (t1, t2) ->
       mparens atomic (pp true t1 ^^^ !^"&&" ^^^ pp true t2)
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
    | App (t1, t2) ->
       mparens atomic (pp true t1 ^^ brackets (pp false t2))
    | Env (t, e) ->
       parens (pp false t) ^^ at ^^ !^e
       



  let addr bn = 
    Addr bn

  let var bn = 
    Var bn


  let pointee = function
    | Addr var -> Var var
    | t -> Pointee t

  let predarg pr a =
    PredOutput (pr,a)

  let rec remove_labels t = 
    let rec aux = function
      | Addr bn -> 
         Addr bn
      | Var bn -> 
         Var bn
      | Pointee p -> 
         Pointee (remove_labels p)
      | PredOutput (pr,a) -> 
         PredOutput (pr, a)
      | Member (p, m) -> 
         Member (remove_labels p, m)
      | Integer i -> 
         Integer i
      | Addition (t1, t2) -> 
         Addition (aux t1, aux t2)
      | Subtraction (t1, t2) -> 
         Subtraction (aux t1, aux t2)
      | Multiplication (t1, t2) -> 
         Multiplication (aux t1, aux t2)
      | Division (t1, t2) -> 
         Division (aux t1, aux t2)
      | Exponentiation (t1, t2) -> 
         Exponentiation (aux t1, aux t2)
      | Remainder (t1, t2) -> 
         Remainder (aux t1, aux t2)
      | Equality (t1, t2) -> 
         Equality (aux t1, aux t2)
      | Inequality (t1, t2) -> 
         Inequality (aux t1, aux t2) 
      | ITE (t1, t2, t3) ->
         ITE (aux t1, aux t2, aux t3)
      | Or (t1, t2) ->
         Or (aux t1, aux t2)
      | And (t1, t2) ->
         And (aux t1, aux t2)
      | LessThan (t1, t2) -> 
         LessThan (aux t1, aux t2)
      | LessOrEqual (t1, t2) -> 
         LessOrEqual (aux t1, aux t2)
      | GreaterThan (t1, t2) -> 
         GreaterThan (aux t1, aux t2)
      | GreaterOrEqual (t1, t2) -> 
         GreaterOrEqual (aux t1, aux t2)
      | IntegerToPointerCast t ->
         IntegerToPointerCast (aux t)
      | PointerToIntegerCast t ->
         PointerToIntegerCast (aux t)
      | Null ->
         Null
      | OffsetOf {tag; member} ->
         OffsetOf {tag; member}
      | App (t1, t2) ->
         App (aux t1, aux t2)
      | Env (t, _) ->
         t
    in
    aux t
  



end

include Terms





type predicate = {
    oq : (string * BT.t * term) option;
    predicate : string;
    arguments : term list;
    oname : string option;
  }

type condition = 
  | Term of term
  | Predicate of predicate


let remove_labels = function
  | Term t -> 
     Term (remove_labels t)
  | Predicate {oq; predicate; arguments; oname} ->
     let oq = match oq with
       | None -> None
       | Some (name, bt, condition) -> Some (name, bt, remove_labels condition)
     in
     let arguments = List.map remove_labels arguments in
     Predicate { oq; predicate; arguments; oname }
    

type varg = { vsym : Sym.t; typ : Sctypes.t }
type aarg = { asym : Sym.t; typ : Sctypes.t }
type garg = { asym : Sym.t; lsym : Sym.t; typ : Sctypes.t; accessed : Loc.t option }


type function_spec = { 
    global_arguments : garg list;
    function_arguments : aarg list;
    function_return : varg;
    pre_condition : (Loc.t * condition) list;
    post_condition : (Loc.t * condition) list;
  }


type label_spec = {
    global_arguments : garg list;
    function_arguments: aarg list;
    label_arguments: aarg list;
    invariant : (Loc.t * condition) list
  }
