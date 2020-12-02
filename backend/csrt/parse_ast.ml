open Pp

module O = struct 

  type 'var t = 
    | Id of 'var
    | PredicateArg of 'var t * string
    | StructMember of 'var t * string
    | Pointee of 'var t

  type 'var obj = 'var t


  let rec pp = function
    | Id s -> !^s
    | PredicateArg (o, s) -> pp o ^^ dot ^^ dot ^^ !^s
    | StructMember (o, s) -> pp o ^^ dot ^^ !^s
    | Pointee o -> star ^^ pp o

  let prefix = function
    | Id v -> None
    | PredicateArg (o, _) -> Some o
    | StructMember (o, _) -> Some o
    | Pointee o -> Some o


  let compare varcompare o1 o2 =
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

  let equal_or_in_prefix varcompare obj obj' = 
    let rec aux obj =
      if compare varcompare obj' obj = 0 then true 
      else 
        match prefix obj with
        | None -> false
        | Some prefix -> aux prefix
    in 
    aux obj'



end


module OOA = struct

  type 'var t = 
    | Addr of 'var
    | Obj of 'var O.t


  type 'var obj_or_addr = 'var t

  type obj_map = (string t * Sym.t) list


  let compare varcompare o1 o2 =
    match o1, o2 with
    | Addr v1, Addr v2 ->
       varcompare v1 v2
    | Addr _, _ -> -1
    | _, Addr _ -> 1

    | Obj o1, Obj o2 -> O.compare varcompare o1 o2


  let pointee_obj_ = function
    | Addr v -> O.Id v
    | Obj o -> O.Pointee o

  let pointee pointer =
    Obj (pointee_obj_ pointer)
  

  let pp = function
    | Addr s -> ampersand ^^ !^s
    | Obj obj -> O.pp obj

end



module IndexTerms = struct

  type 'var t_ = 
    | Object of 'var OOA.t
    | Bool of bool
    | Num of Z.t
    | EQ of 'var t * 'var t
    | NE of 'var t * 'var t
    | LT of 'var t * 'var t
    | GT of 'var t * 'var t
    | LE of 'var t * 'var t
    | GE of 'var t * 'var t
    | Add of 'var t * 'var t
    | Sub of 'var t * 'var t
    | Mul of 'var t * 'var t
    | Div of 'var t * 'var t
    | Min of 'var t * 'var t
    | Max of 'var t * 'var t

    (* maybe remove *)
    | MIN_U32
    | MIN_U64
    | MAX_U32
    | MAX_U64
    | MIN_I32
    | MIN_I64
    | MAX_I32
    | MAX_I64

  and 'var t = 
    | IndexTerm of Locations.t * 'var t_

  type 'var index_term = 'var t

end



type ownership = 
  | Unowned
  | Block

type 'var condition = 
  | Constraint of 'var IndexTerms.t
  | Ownership of 'var O.t * ownership
  (* | Define of string * 'var index_term *)


type 'var definition = 
  | Definition of string * 'var OOA.t



