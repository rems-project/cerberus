open Pp

type 'var obj_ = 
  | Id of 'var
  | PredicateArg of 'var obj_ * string
  | StructMember of 'var obj_ * string
  | Pointee of 'var obj_

type 'var obj = 
  | VariableLocation of 'var
  | Obj_ of 'var obj_



type obj_map = (string obj * Sym.t) list





let pointee = function
  | VariableLocation v -> Obj_ (Id v)
  | Obj_ o -> Obj_ (Pointee o)


let rec pp_obj_ = function
  | Id s -> !^s
  | PredicateArg (o, s) -> pp_obj_ o ^^ dot ^^ dot ^^ !^s
  | StructMember (o, s) -> pp_obj_ o ^^ dot ^^ !^s
  | Pointee o -> star ^^ pp_obj_ o

let pp_obj = function
  | VariableLocation s -> ampersand ^^ !^s
  | Obj_ obj_ -> pp_obj_ obj_



type 'var index_term_ = 
  | Object of 'var obj
  | Bool of bool
  | Num of Z.t
  | EQ of 'var index_term * 'var index_term
  | NE of 'var index_term * 'var index_term
  | LT of 'var index_term * 'var index_term
  | GT of 'var index_term * 'var index_term
  | LE of 'var index_term * 'var index_term
  | GE of 'var index_term * 'var index_term
  | Add of 'var index_term * 'var index_term
  | Sub of 'var index_term * 'var index_term
  | Mul of 'var index_term * 'var index_term
  | Div of 'var index_term * 'var index_term
  | Min of 'var index_term * 'var index_term
  | Max of 'var index_term * 'var index_term

  (* maybe remove *)
  | MIN_U32
  | MIN_U64
  | MAX_U32
  | MAX_U64
  | MIN_I32
  | MIN_I64
  | MAX_I32
  | MAX_I64

and 'var index_term = 
  | IndexTerm of Locations.t * 'var index_term_



type ownership = 
  | Unowned
  | Uninit

type 'var condition = 
  | Constraint of 'var index_term
  | Ownership of 'var obj * ownership
  (* | Define of string * 'var index_term *)


type 'var definition = 
  | Definition of string * 'var obj



let compare_obj_ varcompare o1 o2 =
  let rec aux o1 o2 = 
  match o1, o2 with
  | Id v1, Id v2 ->
     varcompare v1 v2
  | Id _, _ -> -1
  | _, Id _ -> 1

  | PredicateArg (o1,a1), PredicateArg (o2,a2) ->
     let compared = aux o1 o2 in
     if compared = 0 then String.compare a1 a2 else compared
  | PredicateArg _, _ -> -1
  | _, PredicateArg _ -> 1

  | StructMember (o1,a1), StructMember (o2,a2) ->
     let compared = aux o1 o2 in
     if compared = 0 then String.compare a1 a2 else compared
  | StructMember _, _ -> -1
  | _, StructMember _ -> 1

  | Pointee o1, Pointee o2 -> aux o1 o2
  in
  aux o1 o2


let compare_obj varcompare o1 o2 =
  match o1, o2 with
  | VariableLocation v1, VariableLocation v2 ->
     varcompare v1 v2
  | VariableLocation _, _ -> -1
  | _, VariableLocation _ -> 1

  | Obj_ o1, Obj_ o2 -> compare_obj_ varcompare o1 o2





  

