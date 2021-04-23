open Pp

module LabeledName = struct

  type t = 
    {label : string option; v : string}

  let equal b1 b2 = 
    Option.equal String.equal b1.label b2.label && 
      String.equal b1.v b2.v

  let pp {label; v} = 
    let open Pp in
    match label with
    | Some label -> !^v ^^ at ^^ !^label
    | None -> !^v

  let map_label f {v; label} = 
    {v; label = f label}

  let remove_label = map_label (fun _ -> None)

end



type path = 
  | Addr of string
  | Var of LabeledName.t
  | Pointee of path
  | PredArg of string * predarg list * string

and predarg = 
  | PathArg of path
  | Add of predarg * predarg
  | Sub of predarg * predarg
  | AddPointer of predarg * predarg
  | SubPointer of predarg * predarg
  | MulPointer of predarg * predarg
  | IntegerToPointerCast of predarg
  | NumArg of Z.t

type t = path


let rec equal p1 p2 =
  match p1, p2 with
  | Addr b1, Addr b2 ->
     String.equal b1 b2
  | Var b1, Var b2 -> 
     LabeledName.equal b1 b2
  | Pointee p1, Pointee p2 ->
     equal p1 p2
  | PredArg (p1, t1, a1), PredArg (p2, t2, a2) ->
     String.equal p1 p2 && List.equal predarg_equal t1 t2 && String.equal a1 a2
  | Addr _, _ -> 
     false
  | Var _, _ ->
     false
  | Pointee _, _ ->
     false
  | PredArg _, _ ->
     false

and predarg_equal pa1 pa2 = 
  match pa1, pa2 with
  | PathArg p1, PathArg p2 -> equal p1 p2
  | Add (p1,i1), Add (p2,i2) -> predarg_equal p1 p2 && predarg_equal i1 i2
  | Sub (p1,i1), Sub (p2,i2) -> predarg_equal p1 p2 && predarg_equal i1 i2
  | AddPointer (p1,i1), AddPointer (p2,i2) -> predarg_equal p1 p2 && predarg_equal i1 i2
  | SubPointer (p1,i1), SubPointer (p2,i2) -> predarg_equal p1 p2 && predarg_equal i1 i2
  | MulPointer (p1,i1), MulPointer (p2,i2) -> predarg_equal p1 p2 && predarg_equal i1 i2
  | IntegerToPointerCast p1, IntegerToPointerCast p2 -> predarg_equal p1 p2
  | NumArg z1, NumArg z2 -> Z.equal z1 z2
  | PathArg _, _ -> false
  | Add _, _ -> false
  | Sub _, _ -> false
  | AddPointer _, _ -> false
  | SubPointer _, _ -> false
  | MulPointer _, _ -> false
  | IntegerToPointerCast _, _ -> false
  | NumArg _, _ -> false


let rec pp = function
  | Addr b -> ampersand ^^ !^b
  | Var b -> LabeledName.pp b
  | Pointee p -> star ^^ (pp p)
  | PredArg (p,t,a) -> !^p ^^ parens (separate_map comma pp_predarg t) ^^ dot ^^ !^a

and pp_predarg = function
  | PathArg t -> pp t
  | Add (p,t) -> pp_predarg p ^^^ plus ^^^ pp_predarg t
  | Sub (p,t) -> pp_predarg p ^^^ minus ^^^ pp_predarg t
  | AddPointer (p,t) -> pp_predarg p ^^^ plus ^^ dot ^^^ pp_predarg t
  | SubPointer (p,t) -> pp_predarg p ^^^ minus ^^ dot ^^^ pp_predarg t
  | MulPointer (p,t) -> pp_predarg p ^^^ star ^^ dot ^^^ pp_predarg t
  | IntegerToPointerCast p -> parens !^"pointer" ^^ pp_predarg p
  | NumArg z -> Z.pp z

let addr bn = 
  Addr bn

let var bn = 
  Var bn


let pointee olabel = function
  | Addr bn -> Var {label = olabel; v = bn}
  | Var bn -> Pointee (Var bn)
  | Pointee p -> Pointee (Pointee p)
  | PredArg (pr,p,a) -> Pointee (PredArg (pr,p,a))

let predarg pr p a =
  PredArg (pr,p,a)

let rec deref_path = function
  | Addr _ -> 
     None
  | Var bn -> 
     Some (bn, 0)
  | Pointee p -> 
     Option.bind (deref_path p) (fun (bn, pp) -> Some (bn, pp+1))
  | PredArg _ -> 
     None

let rec map_labels f = function
  | Addr bn -> Addr bn
  | Var bn -> Var (LabeledName.map_label f bn)
  | Pointee p -> Pointee (map_labels f p)
  | PredArg (pr,p,a) -> PredArg (pr, List.map (map_labels_predarg f) p, a)

and map_labels_predarg f pa = 
  let aux = map_labels_predarg f in
  match pa with
  | PathArg p -> PathArg (map_labels f p)
  | Add(p,p') -> Add (aux p, aux p')
  | Sub(p,p') -> Sub (aux p, aux p')
  | AddPointer(p,p') -> AddPointer (aux p, aux p')
  | SubPointer(p,p') -> SubPointer (aux p, aux p')
  | MulPointer(p,p') -> MulPointer (aux p, aux p')
  | IntegerToPointerCast p -> IntegerToPointerCast (aux p)
  | NumArg z -> NumArg z

let remove_labels = map_labels (fun _ -> None)
let remove_labels_predarg = map_labels_predarg (fun _ -> None)
