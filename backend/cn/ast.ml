module Loc = Locations
open Pp


module LabeledName = struct

  type t = 
    {label : string option; v : string}

  let equal b1 b2 = 
    Option.equal String.equal b1.label b2.label && 
      String.equal b1.v b2.v

  let pp {label; v} = 
    match label with
    | Some label -> !^v ^^ at ^^ !^label
    | None -> !^v

  let map_label f {v; label} = 
    {v; label = f label}

  let remove_label = map_label (fun _ -> None)

end



module Terms = struct

  type path = 
    | Addr of string
    | Var of LabeledName.t
    | Pointee of path
    | PredArg of string * pred_arg list * string

  and pred_arg = 
    | PathArg of path
    | Term of term

  and term = 
    | Integer of Z.t
    | Path of path
    | Addition of term * term
    | Subtraction of term * term
    | Multiplication of term * term
    | Division of term * term
    | Exponentiation of term * term
    | Equality of term * term
    | Inequality of term * term
    | ITE of term * term * term
    | LessThan of term * term
    | LessOrEqual of term * term
    | GreaterThan of term * term
    | GreaterOrEqual of term * term
    | StructMember of term * Id.t
    | IntegerToPointerCast of term



  let rec path_equal p1 p2 =
    match p1, p2 with
    | Addr b1, Addr b2 ->
       String.equal b1 b2
    | Var b1, Var b2 -> 
       LabeledName.equal b1 b2
    | Pointee p1, Pointee p2 ->
       path_equal p1 p2
    | PredArg (p1, t1, a1), PredArg (p2, t2, a2) ->
       String.equal p1 p2 && List.equal pred_arg_equal t1 t2 && String.equal a1 a2
    | Addr _, _ -> 
       false
    | Var _, _ ->
       false
    | Pointee _, _ ->
       false
    | PredArg _, _ ->
       false

  and pred_arg_equal a1 a2 =
    match a1, a2 with
    | PathArg p1, PathArg p2 -> path_equal p1 p2
    | Term t1, Term t2 -> term_equal t1 t2
    | PathArg _, _ -> false
    | Term _, _ -> false
  

  and term_equal t1 t2 =
    match t1, t2 with
    | Integer i1, Integer i2 -> Z.equal i1 i2
    | Path p1, Path p2 -> path_equal p1 p2
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
    | Equality (a11,a12), Equality (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | Inequality (a11,a12), Inequality (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | LessThan (a11,a12), LessThan (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | ITE (a11,a12,a13), ITE (a21,a22,a23) ->
       term_equal a11 a21 && term_equal a12 a22 && term_equal a13 a23
    | LessOrEqual (a11,a12), LessOrEqual (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | GreaterThan (a11,a12), GreaterThan (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | GreaterOrEqual (a11,a12), GreaterOrEqual (a21,a22) ->
       term_equal a11 a21 && term_equal a12 a22
    | StructMember (t1, m1), StructMember (t2, m2) ->
       term_equal t1 t2 && Id.equal m1 m2
    | IntegerToPointerCast t1, IntegerToPointerCast t2 ->
       term_equal t1 t2
    | Integer _, _ -> 
       false
    | Path _, _ -> 
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
    | Equality _, _ ->
       false
    | Inequality _, _ ->
       false
    | ITE _, _ ->
       false
    | LessThan _, _ ->
       false
    | LessOrEqual _, _ ->
       false
    | GreaterThan _, _ ->
       false
    | GreaterOrEqual _, _ ->
       false
    | StructMember _, _ -> 
       false
    | IntegerToPointerCast _, _ ->
       false


  let mparens atomic pp = 
    if atomic then parens pp else pp

  let rec pp_path _atomic = function
    | Addr b -> ampersand ^^ !^b
    | Var b -> LabeledName.pp b
    | Pointee p -> star ^^ (pp_path true p)
    | PredArg (p,t,a) -> !^p ^^ parens (separate_map comma (pp_pred_arg false) t) ^^ dot ^^ !^a

  and pp_pred_arg atomic = function
    | PathArg p -> pp_path atomic p
    | Term t  -> pp_term atomic t


  and pp_term atomic = function
    | Integer z -> 
       Z.pp z
    | Path p -> 
       pp_path atomic p
    | Addition (t1, t2) -> 
       mparens atomic (pp_term true t1 ^^^ plus ^^^ pp_term true t2)
    | Subtraction (t1, t2) -> 
       mparens atomic (pp_term true t1 ^^^ minus ^^^ pp_term true t2)
    | Multiplication (t1, t2) -> 
       mparens atomic (pp_term true t1 ^^^ star ^^^ pp_term true t2)
    | Division (t1, t2) -> 
       mparens atomic (pp_term true t1 ^^^ !^"/" ^^^ pp_term true t2)
    | Exponentiation (t1, t2) -> 
       c_app !^"power" [pp_term false t1; pp_term false t2]
    | Equality (t1, t2) -> 
       mparens atomic (pp_term true t1 ^^^ !^"==" ^^^ pp_term true t2)
    | Inequality (t1, t2) -> 
       mparens atomic (pp_term true t1 ^^^ !^"!=" ^^^ pp_term true t2)
    | ITE (t1, t2, t3) ->
       mparens atomic (pp_term true t1 ^^^ !^"?" ^^^ pp_term true t2
                       ^^^ !^":" ^^^ pp_term true t3)
    | LessThan (t1, t2) -> 
       mparens atomic (pp_term true t1 ^^^ !^"<" ^^^ pp_term true t2)
    | LessOrEqual (t1, t2) -> 
       mparens atomic (pp_term true t1 ^^^ !^"<=" ^^^ pp_term true t2)
    | GreaterThan (t1, t2) -> 
          mparens atomic (pp_term true t1 ^^^ !^">" ^^^ pp_term true t2)
    | GreaterOrEqual (t1, t2) -> 
       mparens atomic (pp_term true t1 ^^^ !^">=" ^^^ pp_term true t2)
    | StructMember (t1, m1) -> 
       pp_term true t1 ^^ dot ^^ Id.pp m1
    | IntegerToPointerCast t1 ->
       mparens atomic (parens !^"pointer" ^^ (pp_term true t1))


  let addr bn = 
    Addr bn

  let var bn = 
    Var bn


  let pointee olabel = function
    | Addr bn -> Var {label = olabel; v = bn}
    | Var bn -> Pointee (Var bn)
    | Pointee p -> Pointee (Pointee p)
    | PredArg (pr,p,a) -> Pointee (PredArg (pr,p,a))

  let predarg pr (ps : pred_arg list) a =
    PredArg (pr,ps,a)

  let rec deref_path = function
    | Addr _ -> 
       None
    | Var bn -> 
       Some (bn, 0)
    | Pointee p -> 
       Option.bind (deref_path p) (fun (bn, pp) -> Some (bn, pp+1))
    | PredArg _ -> 
       None




  let rec map_labels_path f = function
    | Addr bn -> Addr bn
    | Var bn -> Var (LabeledName.map_label f bn)
    | Pointee p -> Pointee (map_labels_path f p)
    | PredArg (pr,p,a) -> PredArg (pr, List.map (map_labels_pred_arg f) p, a)

  and map_labels_pred_arg f t = 
    match t with
    | PathArg p -> PathArg (map_labels_path f p)
    | Term t -> Term (map_labels_term f t)

  and map_labels_term f t = 
    let rec aux = function
      | Integer i -> 
         Integer i
      | Path path -> 
         Path (map_labels_path f path)
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
      | Equality (t1, t2) -> 
         Equality (aux t1, aux t2)
      | Inequality (t1, t2) -> 
         Inequality (aux t1, aux t2) 
      | ITE (t1, t2, t3) ->
         ITE (aux t1, aux t2, aux t3)
      | LessThan (t1, t2) -> 
         LessThan (aux t1, aux t2)
      | LessOrEqual (t1, t2) -> 
         LessOrEqual (aux t1, aux t2)
      | GreaterThan (t1, t2) -> 
         GreaterThan (aux t1, aux t2)
      | GreaterOrEqual (t1, t2) -> 
         GreaterOrEqual (aux t1, aux t2)
      | StructMember (t, member) ->
         StructMember (aux t, member)
      | IntegerToPointerCast t ->
         IntegerToPointerCast (aux t)
    in
    aux t
  

  let remove_labels_path = map_labels_path (fun _ -> None)




end

include Terms



type resource_condition = {
    predicate : string;
    arguments : pred_arg list;
  }

type logical_condition = term

type condition = 
  | Logical of logical_condition
  | Resource of resource_condition


let map_labels f = function
  | Logical cond -> 
     Logical (map_labels_term f cond)
  | Resource resource ->
     let arguments = 
       List.map (map_labels_pred_arg f) 
         resource.arguments 
     in
     Resource { resource with arguments }
    

type varg = { name : string; vsym : Sym.t; typ : Sctypes.t }
type aarg = { name : string; asym : Sym.t; typ : Sctypes.t }
type garg = { name : string; asym : Sym.t; lsym : Sym.t; typ : Sctypes.t; accessed : Loc.t option }


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
