module A = CpAil
module AT = CpAilTypes
module AA = CpAilAnnotate

module AM = CpAilMeaning
module AC = CpAilConstraint

module AIC = CpAilIntegerConstraint
module ATC = CpAilTypeConstraint

module Action = CpAilAction

module M = BatMap

let symbol = ref (CpSymbol.make ())

let update_env env ids =
  List.fold_left (fun e id -> M.add id (AC.fresh_address ()) e) env ids

let conv t t' (c, m) =
  let open AM.Operators in
  let a, constr = ATC.conv t t' c in
  a, m <&- constr

let conv_int t (c, m) =
  let open AM.Operators in
  let a, constr = ATC.conv_int t c in
  a, m <&- constr

let rec reduce_lvalue n b env file exp =
  let open AM.Operators in
  let f = reduce_exp n b env file in
  let f_lvalue = reduce_lvalue n b env file in
  match AA.exp_of exp with
  | A.VARIABLE id -> M.find id env, AM.empty
  | A.UNARY (A.INDIRECTION, e) ->
      let t = AT.pointer_convert (AA.exp_type_of e) in
      let a, m = f e in
      let null = AC.eq a AC.null in
      let ill_aligned = AC.neg (ATC.align (AT.base_of_pointer t) a) in
      let c = AC.implies (AC.disj null ill_aligned) AC.undef in
      a, m <&- c

  and reduce_exp n b env file exp =
  let open AM.Operators in
      let f = reduce_exp n b env file in
  let f_lvalue e =
    let a, m = reduce_lvalue n b env file e in
    a, m &>> (AM.empty <@- Action.id a) in
  let lookup_type id = fst (M.find id file.A.id_map) in
  let conv_exp e = conv_int (AA.exp_type_of exp) (f e) in
  let usual_arithmetic e1 e2 =
    AT.usual_arithmetic (AA.exp_type_of e1) (AA.exp_type_of e2) in
  let overflow t c = AC.implies (AC.neg (ATC.in_range t c)) AC.undef in
  match AA.exp_of exp with
  | A.VARIABLE id when AT.is_array (lookup_type id) ->
      M.find id env, AM.empty
  | _ when AT.is_lvalue (AA.type_of exp)
      && not (AT.is_array (AA.exp_type_of exp)) ->
      let a, m = f_lvalue exp in
      let v = AC.fresh_name () in
      let load = Action.load (AA.lvalue_type_of exp) a v in
      v, m &>> (AM.empty <@- load)
  | A.CONSTANT (Cabs.CONST_INT (i, _)) -> AC.const i, AM.empty
  | A.UNARY (A.POSTFIX_INCR, e) ->
      let a, m = f_lvalue e in
      let v = AC.fresh_name () in
      let incr = AC.plus v AC.one in
      let v', m' = conv_int (AA.exp_type_of e) (incr, AM.empty) in
      let modify = Action.modify (AA.lvalue_type_of e) a v v' in
      v, (m <&> m') &>> (AM.empty <@- modify)
  | A.UNARY (A.POSTFIX_DECR, e) ->
      let a, m = f_lvalue e in
      let v = AC.fresh_name () in
      let decr = AC.minus v AC.one in
      let a', m' = conv_int (AA.exp_type_of e) (decr, AM.empty) in
      let modify = Action.modify (AA.lvalue_type_of e) a v a' in
      v, (m <&> m') &>> (AM.empty <@- modify)
  | A.UNARY (A.ADDRESS, (_, A.UNARY (A.INDIRECTION, e))) -> f e
  | A.UNARY (A.ADDRESS, e) -> f_lvalue e
  | A.CAST (t, e) -> conv t (AA.exp_type_of e) (f e)
  | A.BINARY (Cabs.ARITHMETIC Cabs.ADD, e1, e2)
      when AT.is_arithmetic (AA.exp_type_of e1)
        && AT.is_arithmetic (AA.exp_type_of e2)
        && AT.is_signed_integer(AA.exp_type_of exp) ->
      let a1, m1 = conv_exp e1 in
      let a2, m2 = conv_exp e2 in
      let sum = AC.plus a1 a2 in
      let c = overflow (AA.exp_type_of exp) sum in
      sum, m1 <&> m2 <&- c
  | A.BINARY (Cabs.ARITHMETIC Cabs.ADD, e1, e2)
      when AT.is_arithmetic (AA.exp_type_of e1)
        && AT.is_arithmetic (AA.exp_type_of e2) ->
      let a1, m1 = conv_exp e1 in
      let a2, m2 = conv_exp e2 in
      let a, m = conv_int (AA.exp_type_of exp) (AC.plus a1 a2, AM.empty) in
      a, m1 <&> m2 <&> m
  | A.BINARY (Cabs.ARITHMETIC Cabs.ADD, e1, e2)
      when AT.is_pointer (AA.exp_type_of e1) ->
      (* Pointer arithmetic. *)
      let a1, m1 = f e1 in
      let a2, m2 = f e2 in
      let size = ATC.size (AT.base_of_pointer (AA.exp_type_of e1)) in
      let a = AC.offset a1 a2 size in
      a, (m1 <&> m2) &>> (AM.empty <@- Action.same a1 a)
  | A.BINARY (Cabs.ARITHMETIC Cabs.SUB, e1, e2)
      when AT.is_pointer (AA.exp_type_of e1) ->
      (* Pointer arithmetic. *)
      let a1, m1 = f e1 in
      let a2, m2 = f e2 in
      let size = ATC.size (AT.base_of_pointer (AA.exp_type_of e1)) in
      let a = AC.offset a1 (AC.minus AC.zero a2) size in
      a, (m1 <&> m2) &>> (AM.empty <@- Action.same a1 a)
  | A.BINARY(Cabs.ARITHMETIC Cabs.SUB, e1, e2)
      when AT.is_arithmetic (AA.exp_type_of e1)
        && AT.is_arithmetic (AA.exp_type_of e2)
        && AT.is_signed_integer(AA.exp_type_of exp) ->
      let a1, m1 = conv_exp e1 in
      let a2, m2 = conv_exp e2 in
      let diff = AC.minus a1 a2 in
      let c = overflow (AA.exp_type_of exp) diff in
      diff, (m1 <&> m2) <&- c
  | A.BINARY(Cabs.ARITHMETIC Cabs.SUB, e1, e2)
      when AT.is_arithmetic (AA.exp_type_of e1)
        && AT.is_arithmetic (AA.exp_type_of e2) ->
      let a1, m1 = conv_exp e1 in
      let a2, m2 = conv_exp e2 in
      let a, m = conv_int (AA.exp_type_of exp) (AC.minus a1 a2, AM.empty) in
      a, m1 <&> m2 <&> m
  | A.BINARY(Cabs.ARITHMETIC Cabs.MOD, e1, e2)
      when AT.is_arithmetic (AA.exp_type_of e1)
        && AT.is_arithmetic (AA.exp_type_of e2)
        && AT.is_signed_integer(AA.exp_type_of exp) ->
      let a1, m1 = conv_exp e1 in
      let a2, m2 = conv_exp e2 in
      let modulo = AC.modulo a1 a2 in
      let div_zero = AC.implies (AC.eq a2 AC.zero) AC.undef in
      let c = overflow (AA.exp_type_of exp) (AC.div a1 a2) in
      modulo, (m1 <&> m2) <&- div_zero <&- c
  | A.BINARY(Cabs.ARITHMETIC Cabs.MOD, e1, e2)
      when AT.is_arithmetic (AA.exp_type_of e1)
        && AT.is_arithmetic (AA.exp_type_of e2) ->
      let a1, m1 = conv_exp e1 in
      let a2, m2 = conv_exp e2 in
      let modulo = AC.modulo a1 a2 in
      let a, m = conv_int (AA.exp_type_of exp) (modulo, AM.empty) in
      let div_zero = AC.implies (AC.eq a2 AC.zero) AC.undef in
      a, (m1 <&> m2 <&> m) <&- div_zero
  | A.BINARY (Cabs.SEQUENTIAL Cabs.COMMA, e1, e2) ->
      let _,  m1 = f e1 in
      let a2, m2 = f e2 in
      a2, m1 &>> m2
  | A.BINARY (Cabs.SEQUENTIAL Cabs.OR, e1, e2) ->
      let a1, m1 = f e1 in
      let a2, m2 = f e2 in
      let a = AC.fresh_name () in
      let first_only = AC.conj (AC.neq a1 AC.zero) (AC.eq a AC.one) in
      let both = AC.conj
        (AC.eq a1 AC.zero)
        (AC.case (AC.eq a2 AC.zero) (AC.eq a AC.zero) (AC.eq a AC.one)) in
      a, (m1 <&- first_only) <|> ((m1 &>> m2) <&- both)
  | A.BINARY (Cabs.SEQUENTIAL Cabs.AND, e1, e2) ->
      let a1, m1 = f e1 in
      let a2, m2 = f e2 in
      let a = AC.fresh_name () in
      let first_only = AC.conj (AC.eq a1 AC.zero) (AC.eq a AC.zero) in
      let both = AC.conj
        (AC.neq a1 AC.zero)
        (AC.case (AC.neq a2 AC.zero) (AC.eq a AC.one) (AC.eq a AC.zero)) in
      a, (m1 <&- first_only) <|> ((m1 &>> m2) <&- both)
  | A.BINARY (Cabs.ARITHMETIC Cabs.SHL, e1, e2) ->
      let a1, m1 = conv_exp e1 in
      let a2, m2 = conv_int (AT.promote (AA.exp_type_of e1)) (f e2) in
      let shifted = AC.mult a1 (AC.pow a2) in
      if AT.is_signed_integer (AA.exp_type_of exp) then
        let not_repr = AC.neg (ATC.in_range (AA.exp_type_of exp) shifted) in
        let neg = AC.lt shifted AC.zero in
        let c = AC.implies (AC.disj neg not_repr) AC.undef in
        shifted, (m1 <&> m2) <&- c
      else
        let a, m = conv_int (AA.exp_type_of exp) (shifted, AM.empty) in
        a, m1 <&> m2 <&> m
  | A.BINARY (Cabs.ARITHMETIC Cabs.SHR, e1, e2) ->
      let a1, m1 = conv_exp e1 in
      let a2, m2 = conv_int (AT.promote (AA.exp_type_of e1)) (f e2) in
      let shifted = AC.div a1 (AC.pow a2) in
      if AT.is_signed_integer (AA.exp_type_of exp) then
        let a = AC.fresh_name () in
        let negative = AC.lt shifted AC.zero in
        let c = AC.case negative
          (AC.eq a (AC.fn "impl_right_shift" [shifted]))
          (AC.eq a shifted) in
        shifted, (m1 <&> m2) <&- c
      else
        shifted, m1 <&> m2
  | A.BINARY (Cabs.RELATIONAL Cabs.EQ, e1, e2)
      when AT.is_arithmetic (AA.exp_type_of e1)
        && AT.is_arithmetic (AA.exp_type_of e2) ->
      let t = usual_arithmetic e1 e2 in
      let a1, m1 = conv_int t (f e1) in
      let a2, m2 = conv_int t (f e2) in
      let a = AC.fresh_name () in
      let c = AC.case (AC.eq a1 a2) (AC.eq a AC.one) (AC.eq a AC.zero) in
      a, (m1 <&> m2) <&- c
  | A.BINARY (Cabs.RELATIONAL Cabs.NE, e1, e2)
      when AT.is_arithmetic (AA.exp_type_of e1)
        && AT.is_arithmetic (AA.exp_type_of e2) ->
      let t = usual_arithmetic e1 e2 in
      let a1, m1 = conv_int t (f e1) in
      let a2, m2 = conv_int t (f e2) in
      let a = AC.fresh_name () in
      let c = AC.case (AC.neg (AC.eq a1 a2))
        (AC.eq a AC.one)
        (AC.eq a AC.zero) in
      a, (m1 <&> m2) <&- c
  | A.BINARY (Cabs.RELATIONAL Cabs.LT, e1, e2)
      when AT.is_arithmetic (AA.exp_type_of e1)
        && AT.is_arithmetic (AA.exp_type_of e2) ->
      let t = usual_arithmetic e1 e2 in
      let a1, m1 = conv_int t (f e1) in
      let a2, m2 = conv_int t (f e2) in
      let a = AC.fresh_name () in
      let c = AC.case (AC.lt a1 a2) (AC.eq a AC.one) (AC.eq a AC.zero) in
      a, (m1 <&> m2) <&- c
  | A.BINARY (Cabs.RELATIONAL Cabs.LE, e1, e2)
      when AT.is_arithmetic (AA.exp_type_of e1)
        && AT.is_arithmetic (AA.exp_type_of e2) ->
      let t = usual_arithmetic e1 e2 in
      let a1, m1 = conv_int t (f e1) in
      let a2, m2 = conv_int t (f e2) in
      let a = AC.fresh_name () in
      let c = AC.case (AC.le a1 a2) (AC.eq a AC.one) (AC.eq a AC.zero) in
      a, (m1 <&> m2) <&- c
  | A.BINARY (Cabs.RELATIONAL Cabs.GT, e1, e2)
      when AT.is_arithmetic (AA.exp_type_of e1)
        && AT.is_arithmetic (AA.exp_type_of e2) ->
      let t = usual_arithmetic e1 e2 in
      let a1, m1 = conv_int t (f e1) in
      let a2, m2 = conv_int t (f e2) in
      let a = AC.fresh_name () in
      let c = AC.case (AC.gt a1 a2) (AC.eq a AC.one) (AC.eq a AC.zero) in
      a, (m1 <&> m2) <&- c
  | A.BINARY (Cabs.RELATIONAL Cabs.GT, e1, e2)
      when AT.is_pointer (AA.exp_type_of e1) ->
      (* TODO Comparing two pointers to different object is
	 undefined. *)
      let a1, m1 = f e1 in
      let a2, m2 = f e2 in
      let a = AC.fresh_name () in
      let c = AC.case (AC.gt a1 a2) (AC.eq a AC.one) (AC.eq a AC.zero) in
      a, (m1 <&> m2) <&- c
  | A.BINARY (Cabs.RELATIONAL Cabs.GE, e1, e2)
      when AT.is_arithmetic (AA.exp_type_of e1)
        && AT.is_arithmetic (AA.exp_type_of e2) ->
      let t = usual_arithmetic e1 e2 in
      let a1, m1 = conv_int t (f e1) in
      let a2, m2 = conv_int t (f e2) in
      let a = AC.fresh_name () in
      let c = AC.case (AC.ge a1 a2) (AC.eq a AC.one) (AC.eq a AC.zero) in
      a, (m1 <&> m2) <&- c
  | A.BINARY (Cabs.ARITHMETIC Cabs.BAND, e1, e2) ->
      let a1, m1 = conv_exp e1 in
      let a2, m2 = conv_exp e2 in
      let a = AC.fresh_name () in
      a, (m1 <&> m2) <&- (AC.eq a (AC.bit_and a1 a2))
  | A.BINARY (Cabs.ARITHMETIC Cabs.BOR, e1, e2) ->
      let a1, m1 = conv_exp e1 in
      let a2, m2 = conv_exp e2 in
      let a = AC.fresh_name () in
      a, (m1 <&> m2) <&- (AC.eq a (AC.bit_or a1 a2))
  | A.BINARY (Cabs.ARITHMETIC Cabs.XOR, e1, e2) ->
      let a1, m1 = conv_exp e1 in
      let a2, m2 = conv_exp e2 in
      let a = AC.fresh_name () in
      a, (m1 <&> m2) <&- (AC.eq a (AC.bit_xor a1 a2))
  | A.ASSIGN (None, e1, e2) ->
      let a1, m1 = f_lvalue e1 in
      let a2, m2 = f e2 in
      let a, m =
        conv (AA.exp_type_of e1) (AA.exp_type_of e2) (a2, AM.empty) in
      let write = Action.store (AA.lvalue_type_of e1) a1 a in
      a,  (m1 <&> m2) &>> (m <@- write)
  | A.QUESTION (e1, e2, e3)
      when AT.is_arithmetic (AA.exp_type_of e1)
        && AT.is_arithmetic (AA.exp_type_of e2) ->
      let a1, m1 = f e1 in
      let a2, m2 = conv_exp e2 in
      let a3, m3 = conv_exp e3 in
      let a = AC.fresh_name () in
      let pos = m2 <&- (AC.eq a a2) <&- (AC.eq  a1 AC.zero) in
      let neg = m3 <&- (AC.eq a a3) <&- (AC.neq a1 AC.zero) in
      a, m1 &>> (pos <|> neg)
  | A.CALL ((_, A.VARIABLE fid), es) 
      when M.mem fid file.A.function_map
        && M.find fid b > 0 ->
      let depth = M.find fid b in
      let b' = M.add fid (depth - 1) b in
      let ids, s = M.find fid file.A.function_map in
      let env' = update_env env ids in
      let ids_t = List.map (fun id -> M.find id env', lookup_type id) ids in
      let m_args = List.fold_left2
        (fun m' (l, t) e ->
          let a, m = conv (AT.unqualify t) (AA.exp_type_of e) (f e) in
          let create = Action.create t l in
          let store = Action.fn_store t l a in
          m' <&> ((m <@- create) &>> (AM.empty <@- store))
        ) AM.empty ids_t es in
      let kill_ids m (l, _) = m <@- Action.kill l in
      let m_kill = List.fold_left kill_ids AM.empty ids_t in
      let a = AC.fresh_name () in
      let m_body = AM.flatten_func (reduce_stmt n b' fid a env' file s) in
      a, m_args &>> m_body &>> m_kill
  | A.CALL ((_, A.VARIABLE _), _) ->
      AC.fresh_name (), AM.none

and reduce_stmt n b fid return env file (d, stmt) =
  let open AM.StatementOperators in
  let f_s = reduce_stmt n b fid return env file in
  let f_e = reduce_exp n b env file in
  let lift (a, m) = a, AM.normal m in
  let lookup_type id = fst (M.find id file.A.id_map) in
  match stmt with
  | A.SKIP -> AM.empty_func
  | A.IF (e, s1, s2) ->
      let a, m = lift (f_e e) in
      let pos = f_s s1 <&- (AC.neq  a AC.zero) in
      let neg = f_s s2 <&- (AC.eq a AC.zero) in
      m &>> (pos <|> neg)
  | A.BLOCK (ids, ss) ->
      let module S = BatSet in
      let create_ids m (l, t) = m <@- Action.create t l in
      let kill_ids   m (l, _) = S.add (Action.kill l) m in
      let env' = update_env env ids in
      let ids_t = List.map (fun i -> M.find i env', lookup_type i) ids in
      let m_create = List.fold_left create_ids AM.empty_func ids_t in
      let m_kill   = List.fold_left kill_ids S.empty ids_t in
      let m =
        List.fold_left
          (fun m s -> m &>> (reduce_stmt n b fid return env' file s))
          AM.empty_func ss in
      AM.add_actions_entire_func_sb (m_create &>> m) m_kill
  | A.DECLARATION defns ->
      let define (id, e) =
        let t = lookup_type id in
        let a, m = lift (conv t (AA.exp_type_of e) (f_e e)) in
        m &>> (AM.empty_func <@- Action.store t (M.find id env) a) in
      List.fold_left (fun m p -> m &>> define p) AM.empty_func defns
  | A.RETURN_EXPRESSION e ->
      let t_return = match lookup_type fid with
        | A.FUNCTION (t, _) -> t
        | _ -> invalid_arg "Not a function type." in
      let a, m = conv t_return (AA.exp_type_of e) (f_e e) in
      AM.return (AM.add_constraint m (AC.eq a return))
  | A.RETURN_VOID -> AM.return AM.empty
  | A.EXPRESSION e -> snd (lift (f_e e))
  | A.WHILE (e, s) ->
      let m_neg (a, m) = AM.add_constraint m (AC.eq  a AC.zero) in
      let m_pos (a, m) = AM.add_constraint m (AC.neq a AC.zero) in
      let rec iterate m = function
        | 0 -> AM.exit_loop (m_neg (f_e e)) m
        | n ->
            let test = f_e e in
            let m' = AM.enter_loop (m_pos test) (m_neg test) m in
            iterate (m' &>> f_s s) (n-1) in
      iterate AM.empty_func n
  | A.BREAK -> AM.break AM.empty
  | A.CONTINUE -> AM.continue AM.empty

let reduce_file n omega ({A.function_map; A.main; _} as file) =
  let b =
    List.fold_left (fun m fid -> M.add fid n m) M.empty (List.map fst (M.bindings function_map)) in
  let _, s = M.find main function_map in
  let m = reduce_stmt n b main (AC.fresh_named "return") M.empty file s in
  AM.add_constraint_set (AM.flatten_func m) omega
(*
  List.map rd (List.map snd (M.values function_map))
*)

let reduce n (omega, result) =
  match result with
  | A.Program file -> A.Program (reduce_file n omega file)
  | A.Invalid -> A.Invalid
  | A.Undefined -> A.Undefined

module Print = struct

  let pp = ()

end
