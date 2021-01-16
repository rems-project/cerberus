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

  let remove_label {v; _} = 
    {v; label = None}

end



type path = 
  | Addr of string
  | Var of LabeledName.t
  | Pointee of path
  | PredArg of string * predarg list * string

and predarg = 
  | PathArg of path
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
  | NumArg z1, NumArg z2 -> Z.equal z1 z2
  | PathArg _, _ -> false
  | NumArg _, _ -> false


let rec pp = function
  | Addr b -> ampersand ^^ !^b
  | Var b -> LabeledName.pp b
  | Pointee p -> star ^^ (pp p)
  | PredArg (p,t,a) -> !^p ^^ parens (separate_map comma pp_predarg t) ^^ dot ^^ !^a

and pp_predarg = function
  | PathArg t -> pp t
  | NumArg z -> Z.pp z

let addr bn = 
  Addr bn

let var bn = 
  Var bn


let pointee olabel = function
  | Addr bn -> Var {label = olabel; v = bn}
  | Var bn -> Pointee (Var bn)
  | Pointee p -> Pointee p
  | PredArg (pr,p,a) -> Pointee (PredArg (pr,p,a))

let predarg pr p a =
  PredArg (pr,p,a)

let rec deref_path = function
  | Var bn -> 
     Some (bn, 0)
  | Pointee p -> 
     Option.bind (deref_path p) 
       (fun (bn, pp) -> Some (bn, pp+1))
  | Addr _ -> 
     None
  | PredArg _ -> 
     None

let rec remove_labels = function
  | Addr bn -> Addr bn
  | Var bn -> Var (LabeledName.remove_label bn)
  | Pointee p -> Pointee (remove_labels p)
  | PredArg (pr,p,a) -> PredArg (pr, List.map remove_labels_predarg p, a)

and remove_labels_predarg = function
  | PathArg p -> PathArg (remove_labels p)
  | NumArg z -> NumArg z

