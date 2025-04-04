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

let collect_memory_accesses (_, sigm) =
  let acc = ref [] in
  let rec aux_expr (AnnotatedExpression (_, _, loc, expr_)) =
    match expr_ with
      | AilErvalue lvalue ->
          acc := Load {loc; lvalue } :: !acc;
          aux_expr lvalue
      | AilEassign (lvalue, expr) ->
          acc := Store {loc; lvalue; expr} :: !acc;
          aux_expr lvalue;
          aux_expr expr
      | AilEcompoundAssign (lvalue, aop, expr) ->
          acc := StoreOp {loc; lvalue; aop; expr} :: !acc;
          aux_expr lvalue;
          aux_expr expr
      | AilEunary (PostfixIncr, lvalue) ->
          acc := Postfix {loc; op= `Incr; lvalue } :: !acc;
          aux_expr lvalue
      | AilEunary (PostfixDecr, lvalue) ->
          acc := Postfix {loc; op= `Decr; lvalue } :: !acc;
          aux_expr lvalue
      | AilEunion (_, _, None)
      | AilEoffsetof _
      | AilEbuiltin _
      | AilEstr _
      | AilEconst _
      | AilEident _
        (* TODO(vla): if the type is a VLA, the size expression is evaluated *)
      | AilEsizeof _
        (* the sub-expr is not evaluated; TODO(vla): except if it is possible
           to have an expression with VLA type here (?) *)
      | AilEsizeof_expr _
      | AilEalignof _
      | AilEreg_load _ ->
          ()
      | AilEunary (_, e)
      | AilEcast (_, _, e)
      | AilEassert e
      | AilEunion (_, _, Some e)
      | AilEcompound (_, _, e)
      | AilEmemberof (e, _)
      | AilEmemberofptr (e, _)
      | AilEannot (_, e)
      | AilEva_start (e, _)
      | AilEva_arg (e, _)
      | AilEva_end e
      | AilEprint_type e
      | AilEbmc_assume e
      | AilEarray_decay e
      | AilEfunction_decay e
      | AilEatomic e ->
          aux_expr e
      | AilEbinary (e1, _, e2)
      | AilEcond (e1, None, e2)
      | AilEva_copy (e1, e2) ->
          aux_expr e1;
          aux_expr e2
      | AilEcond (e1, Some e2, e3) ->
          aux_expr e1;
          aux_expr e2;
          aux_expr e3
      | AilEcall (e, es) ->
          aux_expr e;
          List.iter aux_expr es
      | AilEgeneric (e, gas) ->
          aux_expr e;
          List.iter (function
            | AilGAtype (_, e)
            | AilGAdefault e -> aux_expr e
          ) gas
      | AilEarray (_ , _, xs) ->
          List.iter (function
            | None -> ()
            | Some e -> aux_expr e
          ) xs
      | AilEstruct (_, xs) ->
          List.iter (function
            | (_, None) -> ()
            | (_, Some e) -> aux_expr e
          ) xs
      | AilEgcc_statement (_, ss) ->
          List.iter aux_stmt ss
  and aux_stmt stmt =
    match stmt.node with
      | AilSskip
      | AilSbreak
      | AilScontinue
      | AilSreturnVoid
      | AilSgoto _ ->
          ()
      | AilSexpr e
      | AilSreturn e
      | AilSreg_store (_, e) ->
          aux_expr e
      | AilSblock (_, ss)
      | AilSpar ss ->
          List.iter aux_stmt ss
      | AilSif (e, s1, s2) ->
          aux_expr e;
          aux_stmt s1;
          aux_stmt s2
      | AilSwhile (e, s, _)
      | AilSdo (s, e, _)
      | AilSswitch (e, s) ->
          aux_expr e;
          aux_stmt s
      | AilScase (_, s)
      | AilScase_rangeGNU (_, _, s)
      | AilSdefault s
      | AilSlabel (_, s, _)
      | AilSmarker (_, s) ->
          aux_stmt s
      | AilSdeclaration xs ->
          List.iter (function
            | (_, None) -> ()
            | (_, Some e) -> aux_expr e
          ) xs in
  List.iter (fun (_, (_, _, _, _, stmt)) ->
    aux_stmt stmt
  ) sigm.function_definitions;
  !acc
