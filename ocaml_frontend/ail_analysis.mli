open AilSyntax

type 'a memory_access =
  | Load of
      { loc: Cerb_location.t
      ; lvalue: 'a expression }
  | Store of
      { loc: Cerb_location.t
      ; lvalue: 'a expression
      ; expr: 'a expression }
  | StoreOp of
      { loc: Cerb_location.t
      ; aop: arithmeticOperator
      ; lvalue: 'a expression
      ; expr: 'a expression }
  | Postfix of
      { loc: Cerb_location.t
      ; op: [ `Incr | `Decr ]
      ; lvalue: 'a expression }

(* Collect the location and operands of all syntactic occurence of
   memory accesses, regardless of their accessibility in the control-flow. *)
val collect_memory_accesses: 'a ail_program -> 'a memory_access list
