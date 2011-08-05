open CpPervasives

module A  = CpAil
module AT = CpAilTypes
module AR = CpAilRewrite
module AA = CpAilAnnotate

exception E_Invalid
exception E_Undefined
exception E_Implementation of CpAilConstraint.constr list

let empty = BatSet.empty

let report msg e =
  let module AP = CpAilPrint in
  let module D = CpDocument in
  let t = AA.type_of e in
  let p = AA.pos_of e in
  CpLogger.info (
    (^) msg
    -| (^) (" " ^ Position.lines_to_string p ^ ":\n")
    -| (fun s -> s ^ " : " ^ D.to_string (AP.pp_type_class t))
    -| D.to_string
    -| AP.pp_exp
  ) e
let invalid msg exp = report msg exp; raise E_Invalid
let report' msg (l, _) =
  CpLogger.info (CpPrint.pp_program msg) l
let invalid' msg exp = report' msg exp; raise E_Invalid
let require p result msg t e = if p t then result else invalid msg e

let lvalue_convert t e =
  try
    AT.lvalue_convert t
  with Invalid_argument _ ->
    let msg = "Undefined behaviour according to 6.3.2.1#2 Lvalues, arrays, and \
               function designators: \"If the value has an incomplete \
               type and does not have array type, the behaviour is undefined. \
               [...]\" in" in
    report msg e; raise E_Undefined

let int = A.BASE (empty, A.INTEGER (A.SIGNED A.INT))

let rec is_null_pointer (_, e) =
  match e with
  | A.CONSTANT (Cabs.CONST_INT (n, _)) ->
      let open BatBig_int in
      n = zero
  | A.CAST (A.POINTER (_, A.BASE (_, A.VOID)), e') ->
      is_null_pointer e'
  | _ -> false

let rt e = AA.type_of e

(* TODO Could improve specificity of error messages: Currently, we stop when we
   know that a constraint is violated but do not check whether it is partially
   satisfied. *)
(* Implementation note: [check_exp] returns the type of a given expression but
   we (eventually) want to annotate each expression in the abstract syntax tree
   with a type. To avoid redundant type computation, we use open
   recursion. [annotate_exp] complements the process. *)
let rec check_exp omega env l e_head =
  let invalid_head msg = invalid' msg (l, e_head) in
  let f e =
    let t = match AA.type_of e with
      | A.Exp    t -> t
      | A.Lvalue t -> AT.lvalue_convert t in
    AT.pointer_convert t in
  let f_lvalue msg e =
    match AA.type_of e with
    | A.Exp    _ -> invalid msg e
    | A.Lvalue t -> AT.pointer_convert t in
  match e_head with
  | A.VARIABLE id ->
      let t, _ = BatMap.find id env.A.id_map in
      if BatMap.mem id env.A.function_map then
        A.Exp t
      else A.Lvalue t
  | A.CONSTANT (Cabs.CONST_INT (i, None)) ->
      let module BI = BatBig_int in
      let module M = CpRange in
      if M.in_range M.int i then
        A.Exp (A.BASE (empty, A.INTEGER (A.SIGNED A.INT)))
      else
        let module AC = CpAilConstraint in
        let module ATC = CpAilTypeConstraint in
        let const = AC.const i in
        let is_int   = ATC.in_range_int (A.SIGNED A.INT) const in
        let is_long  = ATC.in_range_int (A.SIGNED A.LONG) const in
        let is_llong = ATC.in_range_int (A.SIGNED A.LONG_LONG) const in
        if M.in_range M.long i then begin
          if AC.mem is_int omega then
            A.Exp (A.BASE (empty, A.INTEGER (A.SIGNED A.INT)))
          else if AC.mem (AC.neg is_int) omega then
            A.Exp (A.BASE (empty, A.INTEGER (A.SIGNED A.LONG)))
          else raise (E_Implementation [is_int; AC.neg is_int])
        end else
          if AC.mem is_int omega then
            A.Exp (A.BASE (empty, A.INTEGER (A.SIGNED A.INT)))
          else if AC.mem (AC.neg is_int) omega then begin
            if AC.mem is_long omega then
              A.Exp (A.BASE (empty, A.INTEGER (A.SIGNED A.LONG)))
            else if AC.mem (AC.neg is_long) omega then begin
              if AC.mem is_llong omega then
                A.Exp (A.BASE (empty, A.INTEGER (A.SIGNED A.LONG_LONG)))
              else raise (E_Implementation [is_llong])
            end else raise (E_Implementation [is_long; AC.neg is_long])
          end else raise (E_Implementation [is_int; AC.neg is_int])
(*
        raise_error "Integer constant expression outside the minimal range \
                     of signed integers are currently not supported."
*)
  | A.CONSTANT (Cabs.CONST_INT (_, Some _)) ->
      raise_error "Suffixes in integer constant expressions are not supported."
  | A.CALL (e, es) ->
      let msg_r = "Violation of constraint 6.5.2.2#1 Function calls, \
                   Constraints: \"The expression that denotes the function \
                   shall have type pointer to function returning void or \
                   returning a complete object type other than an array \
                   type.\" (The return type doesn't seem to be valid.) in" in
      let msg_arg = "Violation of constraint 6.5.2.2#1 Function calls, \
                     Constraints: \"Each argument shall have a type such that \
                     its value may be assigned to an object [...] of the type \
                     corresponding to its parameter.\" in" in
      let msg_l = "Violation of constraint 6.5.2.2#1 Function calls, \
                   Constraints: \"[T]he number of arguments shall agree with \
                   the number of parameters.\" in" in
      let msg_f = "Violation of constraint 6.5.2.2#1 Function calls, \
                   Constraints: \"The expression that denotes the function \
                   shall have type pointer to function [...].\" in" in
      let t = f e in
      if AT.is_pointer_to_function t then
        let t_f = AT.base_of_pointer t in
        let t_r = AT.function_return t_f in
        let t_p = AT.function_parameters t_f in
        if AT.is_void t_r
          || (AT.is_complete_object t_r && not (AT.is_array t_r)) then
          if List.length t_p = List.length es then
            let f = fun t e ->
              (* TODO Horrible, horrible hack! Get rid of it! (Only works
                 because we never look at the expression.) *)
              let dummy = A.CONSTANT (Cabs.CONST_INT (BatBig_int.one, None)) in
              let exp = A.ASSIGN (None, (AA.a_type l (A.Lvalue t), dummy), e) in
              let (_ : A.type_class) = check_exp omega env l exp in
              true in
            if List.for_all2 f t_p es then
              A.Exp t_r
            else invalid_head msg_arg
          else invalid_head msg_l
        else invalid msg_r e
      else invalid msg_f e
  | A.UNARY (A.POSTFIX_INCR, e) ->
      let msg_l = "Violation of constraint 6.5.2.4#1 Postfix increment and \
                   decrement operators, Constraints: \"The operand of the \
                   postfix [...] decrement operator [...] shall be a \
                   modifiable lvalue.\" in" in
      let msg_r = "Violation of constraint 6.5.2.4#1 Postfix increment and \
                   decrement operators, Constraints: \"The operand of the \
                   postfix [...] decrement operator [...] shall have [...] \
                   real or pointer type [...].\" in" in
      let t = f_lvalue msg_l e in
      if AT.is_modifiable t then
        if AT.is_real t || AT.is_pointer t then
          let one = l, A.CONSTANT (Cabs.CONST_INT (BatBig_int.one, None)) in
          check_exp omega env l
            (A.ASSIGN (Some Cabs.ADD, e, annotate_exp omega env one))
        else invalid msg_r e
      else invalid msg_l e
  | A.UNARY (A.POSTFIX_DECR, e) ->
      let msg_l = "Violation of constraint 6.5.2.4#1 Postfix increment and \
                   decrement operators, Constraints: \"The operand of the \
                   postfix increment [...] operator [...] shall be a \
                   modifiable lvalue.\" in" in
      let msg_r = "Violation of constraint 6.5.2.4#1 Postfix increment and \
                   decrement operators, Constraints: \"The operand of the \
                   postfix increment [...] operator [...] shall have [...] \
                   real or pointer type [...].\" in" in
      let t = f_lvalue msg_l e in
      if AT.is_modifiable t then
        if AT.is_real t || AT.is_pointer t then
          let one = l, A.CONSTANT (Cabs.CONST_INT (BatBig_int.one, None)) in
          check_exp omega env l
            (A.ASSIGN (Some Cabs.SUB, e, annotate_exp omega env one))
        else invalid msg_r e
      else invalid msg_l e
  | A.UNARY (A.ADDRESS, e) ->
      let msg_f = "Violation of constraint 6.5.3.2#1 Address and indirection \
                   operators, Constraints: \"The operand of the & operator \
                   shall be either a function designator [...] or an lvalue \
                   that designates an object [...].\" in" in
      let t = match rt e with
      | A.Exp ((A.FUNCTION _) as t) -> t
      | A.Exp _ -> invalid msg_f e
      | A.Lvalue t ->
          if AT.is_object t then
            t
          else invalid msg_f e in
      A.Exp (A.POINTER (empty, t))
  | A.UNARY (A.INDIRECTION, e) ->
      let msg_p = "Violation of constraint 6.5.3.2#2 Address and indirection \
                   operators, Constraints: \"The operand of the unary * \
                   operator shall have pointer type.\" in" in
      let t = f e in
      if AT.is_pointer t then
        if AT.is_pointer_to_object t then
          A.Lvalue (AT.base_of_pointer t)
        else A.Exp (AT.base_of_pointer t)
      else invalid_head msg_p
  | A.UNARY (A.MINUS, e) ->
      let msg = "Violation of constraint 6.5.3.3#1 Unary arithmetic operators, \
                 Constraints: \"The operand of the unary [...] - operator \
                 shall have arithmetic type [...].\" in" in
      let t = f e in
      if AT.is_arithmetic t then
        A.Exp (AT.promote t)
      else invalid msg e
  | A.UNARY (A.PLUS, e) ->
      let msg = "Violation of constraint 6.5.3.3#1 Unary arithmetic operators, \
                 Constraints: \"The operand of the unary + [...] operator \
                 shall have arithmetic type [...].\" in" in
      let t = f e in
      if AT.is_arithmetic t then
        A.Exp (AT.promote t)
      else invalid msg e
  | A.UNARY (A.BNOT, e) ->
      let msg = "Violation of constraint 6.5.3.3#1 Unary arithmetic operators, \
                 Constraints: \"The operand [...] of the ~ operator [shall \
                 have] integer type [...].\" in" in
      let t = f e in
      if AT.is_integer t then
        A.Exp (AT.promote t)
      else invalid msg e
  | A.SIZEOF t ->
      let msg_i = "Violation of constraint 6.5.3.4#1 The sizeof and alignof \
                   operators, Constraints: \"The sizeof operator shall not be \
                   applied to an [...] incomplete type[...].\" in" in
      let msg_f = "Violation of constraint 6.5.3.4#1 The sizeof and alignof \
                   operators, Constraints: \"The sizeof operator shall not be \
                   applied to [a] [...] function type [...].\" in" in
      if not (AT.is_function t) then    
        if not (AT.is_incomplete t) then
          A.Exp (A.BASE (empty, A.INTEGER (A.SIGNED A.INT)))
        else invalid_head msg_i
      else invalid_head msg_f
  | A.ALIGNOF t ->
      let msg_i = "Violation of constraint 6.5.3.4#1 The sizeof and alignof \
                   operators, Constraints: \"The alignof operator shall not be \
                   applied to [...] an incomplete type.\" in" in
      let msg_f = "Violation of constraint 6.5.3.4#1 The sizeof and alignof \
                   operators, Constraints: \"The alignof operator shall not be \
                   applied to a function type [...].\" in" in
      if not (AT.is_function t) then    
        if not (AT.is_incomplete t) then
          A.Exp (A.BASE (empty, A.INTEGER (A.SIGNED A.INT)))
        else invalid_head msg_i
      else invalid_head msg_f
  | A.CAST (A.BASE (q, A.VOID), e) ->
      let (_ : A.ctype) = f e in
      A.Exp (A.BASE (q, A.VOID))
  | A.CAST (t, e) ->
      let msg_n = "Violation of constraint 6.5.4#1 Cast operators, \
                   Constraints: \"[T]he type name shall specify [...] \
                   scalar type [...].\" in" in
      let msg_s = "Violation of constraint 6.5.4#1 Cast operators, \
                   Constraints: \"[T]he operand shall have scalar type.\" \
                   in" in
      if AT.is_scalar t then
        if AT.is_scalar (f e) then
          A.Exp t
        else invalid msg_s e
      else invalid_head msg_n
  | A.BINARY (Cabs.ARITHMETIC Cabs.MUL, e1, e2)
  | A.BINARY (Cabs.ARITHMETIC Cabs.DIV, e1, e2) ->
      let msg = "Violation of constraint 6.5.5#2 Multiplicative operators, \
                 Contraints: \"Each operand shall have arithmetic type.\" \
                 in" in
      let t1 = f e1 in
      let t2 = f e2 in
      if AT.is_arithmetic t1 then
        if AT.is_arithmetic t2 then
          A.Exp (AT.usual_arithmetic t1 t2)
        else invalid msg e2
      else invalid_head msg
  | A.BINARY (Cabs.ARITHMETIC Cabs.MOD, e1, e2) ->
      let msg = "Violation of constraint 6.5.5#2 Multiplicative operators, \
                 Contraints: \"The operands of the % operator shall have \
                 integer type.\" in" in
      let t1 = f e1 in
      let t2 = f e2 in
      if AT.is_integer t1 then
        if AT.is_integer t2 then
          A.Exp (AT.usual_arithmetic t1 t2)
        else invalid msg e2
      else invalid_head msg
  | A.BINARY (Cabs.ARITHMETIC Cabs.ADD, e1, e2) ->
      let msg_a = "Violation of constraint 6.5.6#2 Additive operators, \
                   Constraints: \"[B]oth operands shall have arithmetic type \
                   [...].\" in" in
      let msg_i = "Violation of constraint 6.5.6#2 Additive operators, \
                   Constraints: \"[O]ne operand shall be a pointer to a \
                   complete object type and the other shall have integer \
                   type.\" (We were expecting an integer type.) in" in
      let msg_n = "Violation of constraint 6.5.6#2 Additive operators, \
                   Constraints: \"[E] both operands shall have arithmetic \
                   type, or one operand shall be a pointer to a complete \
                   object type and the other shall have integer type.\" in" in
      let t1 = f e1 in
      let t2 = f e2 in
      (* Case: ptr + int. *)
      if AT.is_pointer_to_complete_object t1 then
        if AT.is_integer t2 then
          A.Exp t1
        else invalid msg_i e2
      (* Case: int + ptr. *)
      else if AT.is_pointer_to_object t2 then
        if AT.is_integer t1 then
          A.Exp t2
        else invalid msg_i e1
      (* Case: arith + arith. *)
      else if AT.is_arithmetic t1 then
        if AT.is_arithmetic t2 then
          A.Exp (AT.usual_arithmetic t1 t2)
        else invalid msg_a e2
      else invalid_head msg_n
  | A.BINARY (Cabs.ARITHMETIC Cabs.SUB, e1, e2) ->
      let msg_c = "Violation of constraint 6.5.6#3 Additive operators, \
                   Constraint: \"[B]oth operands [shall be] pointers to [...] \
                   compatible complete object types [...].\" (Operands are \
                   pointers to incompatible types.) in" in
      let msg_i = "Violation of constraint 6.5.6#3 Additive operators, \
                   Constraints: \"[B]oth operands [shall either be] pointers \
                   to [...] compatible complete object types[,] or the left \
                   operand [shall be] a pointer to a complete object type and \
                   the right operand [shall have] integer type.\" (We expected \
                   either a pointer or an integer type.) in" in
      let msg_a = "Violation of contraint 6.5.6#3 Additive operators, \
                   Constraints: \"[B]oth operands have arithmetic type [...].\"
                   in" in
      let msg_n = "Violation of constraint 6.5.6#3 Additive operators, \
                   Constraints: \"[B]oth operands [shall] have arithmetic \
                   type[, or shall be] pointers to [...] compatible complete
                   object types[,] or the left operand [shall be] a pointer to \
                   a complete object type and the right operand [shall have]
                   integer type.\" in" in
      let t1 = f e1 in
      let t2 = f e2 in
      if AT.is_pointer_to_complete_object t1 then
        (* Case: ptr - ptr. *)
        if AT.is_pointer_to_complete_object t2 then
          if AT.compatible t1 t2 then
            raise_error "Computing the difference of two pointers is not yet \
                         supported.\n"
          else invalid_head msg_c
        else
          (* Case: ptr - int. *)
          if AT.is_integer t2 then
            A.Exp t1
          else invalid msg_i e2
      (* Case: arith - arith. *)
      else if AT.is_arithmetic t1 then
        if AT.is_arithmetic t2 then
          A.Exp (AT.usual_arithmetic t1 t2)
        else invalid msg_a e2
      else invalid_head msg_n
  | A.BINARY (Cabs.ARITHMETIC Cabs.SHL, e1, e2)
  | A.BINARY (Cabs.ARITHMETIC Cabs.SHR, e1, e2)  ->
      let msg = "Violation of constraint 6.5.7#2 Bitwise shift operators, \
                 Constraints: \"Each of the operands shall have integer \
                 type.\" in" in
      let t1 = f e1 in
      let t2 = f e2 in
      if AT.is_integer t1 then
        if AT.is_integer t2 then
          A.Exp (AT.promote t1)
        else invalid msg e2
      else invalid_head msg
  | A.BINARY (Cabs.RELATIONAL Cabs.LT, e1, e2)
  | A.BINARY (Cabs.RELATIONAL Cabs.GT, e1, e2)
  | A.BINARY (Cabs.RELATIONAL Cabs.LE, e1, e2)
  | A.BINARY (Cabs.RELATIONAL Cabs.GE, e1, e2) ->
      let msg_c = "Violation of constraint 6.5.8#2 Relational operators, \
                   Constraints: \"[B]oth operands [shall be] pointers to [...] \
                   compatible object types.\" (Operands don't seem to be
                   compatible.) in" in
      let msg_p = "Violation of constraint 6.5.8#2 Relational operators, \
                   Constraints: \"[B]oth operands [shall be] pointers to [...] \
                   compatible object types.\" (Operand doesn't seem to be a \
                   pointer.) in" in
      let msg_r = "Violation of constraint 6.5.8#2 Relational operators, \
                   Constraints: \"[B]oth operands [shall] have real type \
                   [...].\" in" in
      let msg_n = "Violation of constraint 6.5.8#2 Relational operators, \
                   Constraints: \"One of the following shall hold: both \
                   operands have real type or both operands are pointers to \
                   [...] compatible types.\" in" in
      let t1 = f e1 in
      let t2 = f e2 in      
      if AT.is_pointer_to_object t1 then
        if AT.is_pointer_to_object t2 then
          if AT.compatible t1 t2 then
            A.Exp int
          else invalid_head msg_c
        else invalid msg_p e2
      else if AT.is_real t1 then
        if AT.is_real t2 then
          A.Exp int
        else invalid msg_r e2
      else invalid_head msg_n
  | A.BINARY (Cabs.RELATIONAL Cabs.EQ, e1, e2)
  | A.BINARY (Cabs.RELATIONAL Cabs.NE, e1, e2) ->
      let msg_v = "Constraint 6.5.9#2 Equality operators, Constraints: \"[O]ne \
                   operand is a pointer to an object type and the other is a \
                   pointer to [...] void [...].\" (Operand doesn't seem to be \
                   a pointer.) in" in
      let msg_p = "Constraint 6.5.9#2 Equality operators, Constraints: \"[O]ne \
                   operand [shall be] a pointer and the other [shall be] a \
                   null pointer constant.\" (Operand doesn't seem to be a \
                   pointer.) in" in
      let msg_c = "Constraint 6.5.9#2 Equality operators, Constraints: \"[O]ne \
                   operand [shall be] a pointer and the other [shall be] a \
                   null pointer constant.\" (Operands don't seem to point to \
                   compatible types.) in" in
      let msg_a = "Constraint 6.5.9#2 Equality operators, Constraints: \
                   \"[B]oth operands [shall] have arithmetic type.\" in" in
      let msg_n = "Constraint 6.5.9#2 Equality operators, Constraints: \
                   \"One of the following shall hold: both operands have \
                   arithmetic type[, or] both operands are pointers to [...] \
                   compatible types[, or] one operand is a pointer to an \
                   object type and the other is a pointer to [...] void[, or] \
                   one operand is a pointer and the other is a null pointer \
                   constant.\" in" in
      let t1 = f e1 in
      let t2 = f e2 in
      let req_obj_ptr = require AT.is_pointer_to_object (A.Exp int) in
      (* Case: void ptr == ptr. *)
      if AT.is_pointer_to_void t1 then
        req_obj_ptr msg_v t2 e2
      (* Case: ptr == void ptr. *)
      else if AT.is_pointer_to_void t2 then
        req_obj_ptr msg_v t1 e1
      (* Case: null ptr == ptr. *)
      else if is_null_pointer e1 && AT.is_pointer t2 then
        A.Exp int
      (* Case: ptr == null ptr. *)
      else if AT.is_pointer t1 && is_null_pointer e2 then
        A.Exp int
      (* Case: ptr == ptr. *)
      else if AT.is_pointer t1 then
        if AT.is_pointer t2 then
          if AT.compatible t1 t2 then
            A.Exp int
          else invalid_head msg_c
        else invalid msg_p e2
      (* Case: arith + arith. *)
      else if AT.is_arithmetic t1 then
        if AT.is_arithmetic t2 then
          A.Exp int
        else invalid msg_a e2
      else invalid_head msg_n
  |  A.BINARY (Cabs.ARITHMETIC Cabs.BAND, e1, e2) ->
      let msg = "Violation of constraint 6.5.10#2 Bitwise AND operator, \
                 Contraints: \"Each of the operands shall have integer type.\" \
                 in" in
      let t1 = f e1 in
      let t2 = f e2 in
      if AT.is_integer t1 then
        if AT.is_integer t2 then
          A.Exp (AT.usual_arithmetic t1 t2)
        else invalid msg e1
      else invalid_head msg
  |  A.BINARY (Cabs.ARITHMETIC Cabs.XOR, e1, e2) ->
      let msg = "Violation of constraint 6.5.11#2 Bitwise exclusive OR \
                 operator, Contraints: \"Each of the operands shall have \
                 integer type.\" in" in
      let t1 = f e1 in
      let t2 = f e2 in
      if AT.is_integer t1 then
        if AT.is_integer t2 then
          A.Exp (AT.usual_arithmetic t1 t2)
        else invalid msg e1
      else invalid_head msg
  |  A.BINARY (Cabs.ARITHMETIC Cabs.BOR, e1, e2) ->
      let msg = "Violation of constraint 6.5.12#2 Bitwise inclusive OR \
                 operator, Contraints: \"Each of the operands shall have \
                 integer type.\" in" in
      let t1 = f e1 in
      let t2 = f e2 in
      if AT.is_integer t1 then
        if AT.is_integer t2 then
          A.Exp (AT.usual_arithmetic t1 t2)
        else invalid msg e1
      else invalid_head msg
  |  A.BINARY (Cabs.SEQUENTIAL Cabs.AND, e1, e2) ->
      let msg = "Violation of constraint 6.5.13#2 Logical AND operator, \
                 Constraints: \"Each of the operands shall have scalar type.\" \
                 in" in
      let t1 = f e1 in
      let t2 = f e2 in
      if AT.is_scalar t1 then
        if AT.is_scalar t2 then
          A.Exp int
        else invalid msg e1
      else invalid_head msg
  |  A.BINARY (Cabs.SEQUENTIAL Cabs.OR, e1, e2) ->
      let msg = "Violation of constraint 6.5.14#2 Logical OR operator, \
                 Contraints: \"Each of the operands shall have scalar type.\" \
                 in" in
      let t1 = f e1 in
      let t2 = f e2 in
      if AT.is_scalar t1 then
        if AT.is_scalar t2 then
          A.Exp int
        else invalid msg e1
      else invalid_head msg
  |  A.QUESTION (e1, e2, e3) ->
      let msg_s = "Violation of constraint 6.5.15#2 Conditional operator, \
                  Constraints: \"The first operand shall have scalar type.\" \
                  in" in
      let msg_np = "Violation of constraint 6.5.15#3 Conditional operator, \
                    Constraints: \"[T]he following shall hold for the \
                    second and third operands: [...] one is a pointer and the \
                    other is a null pointer constant [...].\" (Operand doesn't \
                    seem to be a pointer.) in" in
      let msg_vp = "Violation of constraint 6.5.15#3 Conditional operator, \
                    Constraints: \"[T]he following shall hold for the second \
                    and third operands: [...] one operand is a pointer to an \
                    object type and the other is a pointer to [...] void.\" \
                    (Operand doesn't seem to be a pointer to an object type.)
                    in" in
      let msg_p = "Violation of constraint 6.5.15#3 Conditional operator, \
                   Constraints: \"[T]he following shall hold for the second \
                   and third operands: [...] both operands are pointers to \
                   compatible types [...].\" (Operand doesn't seem to be a \
                   pointer.) in" in
      let msg_c = "Violation of constraint 6.5.15#3 Conditional operator, \
                   Constraints: \"[T]he following shall hold for the second \
                   and third operands: [...] both operands are pointers to \
                   compatible types [...].\" (Operands don't seem to point to \
                   compatible types.) in" in
      let msg_v = "Violation of constraint 6.5.15#3 Conditional operator, \
                   Constraints: \"[T]he following shall hold for the second \
                   and third operands: [...] both operands have void type \
                   [...].\" in" in
      let msg_a = "Violation of constraint 6.5.15#3 Conditional operator, \
                   Constraints: \"[T]he following shall hold for the second \
                   and third operands: [...] both operands have arithmetic \
                   type [...].\" in" in
      let msg_u = "Violation of constraint 6.5.15#3 Conditional operator, \
                   Constraints: \"[T]he following shall hold for the second \
                   and third operands: [...] both operands have the same \
                   structure or union type [...].\" in" in
      let msg_n = "Violation of constraint 6.5.15#3 Conditional operator, \
                   Constraints: \"One of the following shall hold for the \
                   second and third operands: [Either] both operands have \
                   arithmetic type[, or] both operands have the same structure \
                   or union type[, or] both operands have void type[, or] both \
                   operands are pointers to [...] compatible types[, or] one \
                   operand is a pointer and the other is a null pointer \
                   constant[, or] one operand is a pointer to an object type \
                   and the other is a pointer [...] to void.\" in" in
      let t1 = f e1 in
      let t2 = f e2 in
      let t3 = f e3 in
      (* First operand must be scalar. *)
      if AT.is_scalar t1 then
        (* Case: null ptr : ptr. *)
        if is_null_pointer e2 && AT.is_pointer t3 then
          A.Exp (AT.include_qualifiers t3 (AT.qualifiers t2))
        (* Case: ptr : null ptr. *)
        else if AT.is_pointer t2 && is_null_pointer e3 then
          A.Exp (AT.include_qualifiers t2 (AT.qualifiers t3))
        (* Case: void ptr : ptr.
           Note that, since void is also an object, there is no need to deal
           with the case ptr : void ptr separately. *)
        else if AT.is_pointer_to_void t2 then
          if AT.is_pointer_to_object t3 then
            let q = AT.merge_qualifiers t2 t3 in
            A.Exp (A.POINTER (q, A.BASE (empty, A.VOID)))
          else invalid msg_vp e3
        (* Case: ptr : ptr. *)
        else if AT.is_pointer t2 then
          if AT.is_pointer t3 then
            if AT.compatible t2 t3 then
              let q = AT.merge_qualifiers t2 t3 in
              A.Exp (AT.include_qualifiers (AT.composite t2 t3) q)
            else invalid_head msg_c
          else invalid msg_p e3
        (* Case: arith : arith. *)
        else if AT.is_arithmetic t2 then
          if AT.is_arithmetic t3 then
            A.Exp (AT.common (AT.promote t2) (AT.promote t3))
          else invalid msg_a e3
        (* Case: void : void. *)
        else if AT.is_void t2 then
          if AT.is_void t3 then
            A.Exp (A.BASE (empty, A.VOID))
          else invalid msg_v e3
        (* Case: struct : struct, enum : enum. *)
        else if AT.is_structure t2 || AT.is_union t2 then
          if t2 = t3 then
            A.Exp t2
          else invalid msg_u e3
        else invalid_head msg_n
      else invalid msg_s e1
  | A.ASSIGN (None, e1, e2) ->
      let msg_l = "Violation of constraint 6.5.16#1 Assignment operators, \
                   Constraints: \"An assignment operator shall have a \
                   modifiable lvalue as its left operand.\" in" in
      let msg_b = "Violation of constraint 6.5.16.1#1 Simple assignment, \
                   Constraints: \"[T]he left operand has type [...] _Bool, and \
                   the right is a pointer.\" (Operand doesn't seem to be a \
                   pointer.) in" in
      let msg_sc = "Violation of constraint 6.5.16.1#1 Simple assignment, \
                    Constraints: \"[T]he left operand has [...] structure or \
                    union type compatible with the type of the right [...]\" ( \
                    Operands don't seem to have compatible types.) in" in
      let msg_a = "Violation of constraint 6.5.16.1#1 Simple assignment, \
                   Constraints: \"[T]he left operand [shall have] arithmetic \
                   [...] type, and the right [shall have] arithmetic type \
                   [...]..\" in" in
      let msg_vq = "Violation of constraint 6.5.16.1#1 Simple assignment, \
                    Constraints: \"[T]he left operand [shall have] [...] \
                    pointer type, and [...] one operand [shall be] a pointer \
                    to an object type, and the other [shall be] a pointer to \
                    [...] void, and the type pointed to by the left has all \
                    the qualifiers of type pointed to by the right [...].\" \
                    (Left operand doesn't seem to have all the qualifiers of \
                    the right operand.) in" in
      let msg_v = "Violation of constraint 6.5.16.1#1 Simple assignment, \
                   Constraints: \"[T]he left operand [shall have] [...] \
                   pointer type, and [...] one operand [shall be] a pointer to \
                   an object type, and the other [shall be] a pointer to [...] \
                   void [...].\" (Operand doesn't seem to be a pointer to an \
                   object type.) in" in
      let msg_cq = "Violation of constraint 6.5.16.1#1 Simple assignment, \
                    Constraints: \"[T]he left operand [shall have] [...] \
                    pointer type and [...] both operands [shall be] pointers \
                    to [...] compatible types, and the type pointed to by the \
                    left [shall have] all the qualifiers of the type pointed \
                    to by the right [...].\" (Left operand doesn't seem to \
                    have all the qualifiers of the right operand.) in" in
      let msg_c = "Violation of constraint 6.5.16.1#1 Simple assignment, \
                   Constraints: \"[T]he left operand [shall have] [...] \
                   pointer type and [...] both operands [shall be] pointers to \
                   [...] compatible types [...].\" (Operands don't seem to \
                   point to compatible types.) in" in
      let msg_n = "Violation of constraint 6.5.16.1#1 Simple assignment, \
                   Constraints: \"One of the following shall hold: the left \
                   operand has [...] arithmetic type, and the right has \
                   arithmetic type[, or] the left operand has [...] structure \
                   or union type compatible with the type of the right[, or] \
                   the left operand has [...] pointer type, and [...] both \
                   operands are pointer to [...] compatible types, and the \
                   type pointed to by the left has all the qualifiers of the \
                   type pointed to by the right[, or] the left operand has \
                   [...] pointer type, and [...] one operand is a pointer to \
                   an object type, and the other is a pointer to [...] void, \
                   and the type pointed to by the left has all the qualifiers \
                   of the type pointed to by the right[, or] the left operand \
                   is [a] [...] pointer, and the right is a null pointer \
                   constant[, or] the left operand has type [...] _Bool, and \
                   the right is a pointer.\" in" in
      let t1 = f_lvalue msg_l e1 in
      let t2 = f e2 in   
      let t_head = lvalue_convert t1 e1 in
      let base_has_all_qualifiers t1 t2 =
        let b1 = AT.base_of_pointer t1 in
        let b2 = AT.base_of_pointer t2 in
        BatSet.subset (AT.qualifiers b2) (AT.qualifiers b1) in
      if AT.is_modifiable t1 then
        (* Case: bool = ptr. *)
        if AT.is_bool t1 then
          if AT.is_pointer t2 then
            A.Exp t_head
          else invalid msg_b e2
        (* Case struct = struct or enum = enum. *)
        else if AT.is_structure t1 || AT.is_enum t1 then
          if AT.compatible t1 t2 then
            A.Exp t_head
          else invalid msg_sc e2
        (* Case: arith = arith. *)
        else if AT.is_arithmetic t1 then
          if AT.is_arithmetic t2 then
            A.Exp t_head
          else invalid msg_a e2
        (* Cases of the form ptr = _. *)
        else if AT.is_pointer t1 then
          (* Case ptr = null ptr. *)
          if is_null_pointer e2 then
            A.Exp t_head
          (* Case: void ptr = ptr. *)
          else if AT.is_pointer_to_void t1 then
            if AT.is_pointer_to_object t2 then
              if base_has_all_qualifiers t1 t2 then
                A.Exp t_head
              else invalid_head msg_vq
            else invalid msg_v e2
          (* Case: ptr = void ptr. *)
          else if AT.is_pointer_to_void t2 then
            if AT.is_pointer_to_object t1 then
              if base_has_all_qualifiers t1 t2 then
                A.Exp t_head
              else invalid_head msg_vq
            else invalid msg_v e1
          (* Case: ptr = ptr. *)
          else if AT.is_pointer t2 then
            if AT.compatible t1 t2 then
              if base_has_all_qualifiers t1 t2 then
                A.Exp t_head
              else invalid_head msg_cq
            else invalid_head msg_c
          else invalid_head msg_n
        else invalid_head msg_n
      else invalid msg_l e1
  | A.ASSIGN (Some Cabs.ADD, e1, e2)
  | A.ASSIGN (Some Cabs.SUB, e1, e2) ->
      let msg_l = "Violation of constraint 6.5.16#2 Assignment operators, \
                   Constraints: \"An assignment operator shall have a \
                   modifiable lvalue as its left operand.\" in" in
      let msg_i = "Violation of constraint 6.5.16.2#1 Compound assignment,
                   Constraints: \"[T]he left operand shall be [a] [...] \
                   pointer to a complete object type, and the right shall have \
                   integer type [...].\" (Operand doesn't seem to have integer \
                   type.) in" in
      let msg_a = "Violation of constraint 6.5.16.2#1 Compound assignment,
                   Constraints: \"[T]he left operand shall have [...] \
                   arithmetic type, and the right shall have arithmetic \
                   type.\" (Operand doesn't seem to have  arithmetic type.)\" \
                   in" in
      let msg_n = "Violation of constraint 6.5.16.2#1 Compound assignment,
                   Constraints: \"For the operators += and -= only, either the \
                   left operand shall be [a] [...] pointer to a complete \
                   object type, and the right shall have integer type[, or] \
                   the left operand shall have [...] arithmetic type and the \
                   right shall have arithmetic type.\" in" in
      let t1 = f_lvalue msg_l e1 in
      let t2 = f e2 in
      let t_head = lvalue_convert t1 e1 in
      if AT.is_modifiable t1 then
        if AT.is_pointer_to_complete_object t1 then
          if AT.is_integer t2 then
            A.Exp t_head
          else invalid msg_i e2
        else if AT.is_arithmetic t1 then
          if AT.is_arithmetic t2 then
            A.Exp t_head
          else invalid msg_a e2
        else invalid_head msg_n
      else invalid msg_l e1
  | A.ASSIGN (Some o, e1, e2) ->
      let msg_l = "Violation of constraint 6.5.16#2 Assignment operators, \
                   Constraints: \"An assignment operator shall have a \
                   modifiable lvalue as its left operand.\" in" in
      let msg_a = "Violation of constraint 6.5.16.2#2 Compound assignment, \
                   Constraints: \"[T]he left operand shall have [...] \
                   arithmetic type [...].\" in" in
      let t1 = f_lvalue msg_l e1 in
      let t_head = lvalue_convert t1 e1 in
      if AT.is_modifiable t1 then
        if AT.is_arithmetic t1 then
          let bexp = A.BINARY (Cabs.ARITHMETIC o, e1, e2) in
          let (_ : A.type_class) = check_exp omega env l bexp in
          A.Exp t_head
        else invalid msg_a e1
      else invalid msg_l e1
  | A.BINARY (Cabs.SEQUENTIAL Cabs.COMMA, e1, e2) ->
      let (_ : A.ctype) = f e1 in
      A.Exp (f e2)

and annotate_exp omega env (l, e) =
  let a_type e = AA.a_type l (check_exp omega env l e) in
  match e with
  | A.VARIABLE v ->
      let e' = A.VARIABLE v in
      a_type e', e'
  | A.CONSTANT c ->
      let e' = A.CONSTANT c in
      a_type e', e'
  | A.SIZEOF t ->
      let e' = A.SIZEOF t in
      a_type e', e'
  | A.ALIGNOF t ->
      let e' = A.ALIGNOF t in
      a_type e', e'
  | _ ->
      let e' = AR.map_exp (annotate_exp omega env) (fun x -> x) e in
      a_type e', e'


let rec annotate_stmt omega env (l, stmt) =
  let f_e = annotate_exp  omega env in
  let f_s = annotate_stmt omega env in
  let type_of = AA.exp_type_of in
  AA.a_pos l, match stmt with
  | A.IF (e, s1, s2) ->
      let msg_s = "Violation of constraint 6.8.4.1 The if statement, \
                   Constraints: \"The controlling expression of an if \
                   statement shall have scalar type.\" in" in
      let e' = f_e e in
      if AT.is_scalar (type_of e') then
        A.IF (e', f_s s1, f_s s2)
      else invalid msg_s e'
  | A.SWITCH _ -> raise_error "No support for switch statements yet."
  | A.WHILE (e, s) ->
      let msg_s = "Violation of constraint 6.8.4.1 Iteration statements, \
                   Constraints: \"The controlling expression of an iteration \
                   statement shall have scalar type.\" in" in
      let e' = f_e e in
      if AT.is_scalar (type_of e') then
        A.WHILE (e', f_s s)
      else invalid msg_s e'
  | A.DO (e, s) ->
      let msg_s = "Violation of constraint 6.8.4.1 Iteration statements, \
                   Constraints: \"The controlling expression of an iteration \
                   statement shall have scalar type.\" in" in
      let e' = f_e e in
      if AT.is_scalar (type_of e') then
        A.DO (e', f_s s)
      else invalid msg_s e'
  | _ -> AR.map_stmt f_s f_e (fun x -> x) stmt

let annotate_program omega ({A.id_map = ids; globals; function_map; _} as p) =
  let () =
    if not (List.for_all AT.well_formed (BatMap.values ids)) then
      raise_error "Found an ill-formed type!" in
  let gs = List.map 
    (fun (id,  e) -> id,  annotate_exp  omega p e) globals in
  let fs = BatMap.map
    (fun (ids, s) -> ids, annotate_stmt omega p s) function_map in
  {p with A.globals = gs; function_map = fs}

let annotate_program_e f =
  let module AC = CpAilConstraint in
  let rec loop omega =
    try
      [omega, A.Program (annotate_program omega f)]
    with
    | E_Implementation cs ->
        List.fold_left (fun l c -> loop (AC.union (AC.make c) omega) @ l) [] cs
    | E_Undefined -> [omega, A.Undefined]
    | E_Invalid -> [omega, A.Invalid]
  in
  loop AC.empty

let annotate p =
  let module AC = CpAilConstraint in
  match p with
  | A.Program file -> annotate_program_e file
  | A.Undefined -> [AC.empty, A.Undefined]
  | A.Invalid   -> [AC.empty, A.Invalid]
