module Loc = Locations

module Terms = struct


  type lit = 
    | Integer of Z.t


  type arith_op = 
    | Addition of term * term
    | Subtraction of term * term
    | Multiplication of term * term
    | Division of term * term
    | Exponentiation of term * term

  and cmp_op =
    | Equality of term * term
    | Inequality of term * term
    | LessThan of term * term
    | LessOrEqual of term * term
    | GreaterThan of term * term
    | GreaterOrEqual of term * term

  and term = 
    | Lit of lit
    | Path of Path.t
    | ArithOp of arith_op
    | CmpOp of cmp_op



  let map_labels f t = 
    let rec aux = function
      | Lit lit -> Lit lit
      | Path path -> Path (Path.map_labels f path)
      | ArithOp arithop ->
         ArithOp 
           begin match arithop with
           | Addition (t1, t2) -> Addition (aux t1, aux t2)
           | Subtraction (t1, t2) -> Subtraction (aux t1, aux t2)
           | Multiplication (t1, t2) -> Multiplication (aux t1, aux t2)
           | Division (t1, t2) -> Division (aux t1, aux t2)
           | Exponentiation (t1, t2) -> Exponentiation (aux t1, aux t2)
           end
      | CmpOp cmpop ->
         CmpOp 
           begin match cmpop with
           | Equality (t1, t2) -> Equality (aux t1, aux t2)
           | Inequality (t1, t2) -> Inequality (aux t1, aux t2) 
           | LessThan (t1, t2) -> LessThan (aux t1, aux t2)
           | LessOrEqual (t1, t2) -> LessOrEqual (aux t1, aux t2)
           | GreaterThan (t1, t2) -> GreaterThan (aux t1, aux t2)
           | GreaterOrEqual (t1, t2) -> GreaterOrEqual (aux t1, aux t2)
           end in
    aux t

end

include Terms



type resource_condition = {
    predicate : string;
    arguments : Path.predarg list;
  }

type logical_condition = term

type condition = 
  | Logical of logical_condition
  | Resource of resource_condition


let map_labels f = function
  | Logical cond -> 
     Logical (Terms.map_labels f cond)
  | Resource resource ->
     let arguments = 
       List.map (Path.map_labels_predarg f) 
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
