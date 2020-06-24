open Cerb_frontend
open AilSyntax

module Scopes = struct
  module C2A_eff = Cabs_to_ail_effect
  type scope = C2A_eff.scope
  
  let scopeEqual =
    C2A_eff.scopeEqual
  
  let string_of_scope =
    C2A_eff.string_of_scope
  
  type table = (scope, Symbol.sym, unit) Scope_table.t3
  
  let dict: Symbol.sym Lem_pervasives.mapKeyType_class = {
    mapKeyCompare_method=  Symbol.instance_Basic_classes_Ord_Symbol_sym_dict.compare_method
  }
  
  let empty: table =
    []
  
  let register sym (tbl: table) =
    Scope_table.register dict sym () tbl
  
  let create_scope scope (tbl: table) =
    Scope_table.create_scope dict scope tbl
  
  let resolve sym (tbl: table) =
    Scope_table.resolve dict sym tbl
  
  let current_scope_is tbl =
    Scope_table.current_scope_is tbl
end




type env = {
  counter: int;
  block_depth: int;
  scopes: (Cabs_to_ail_effect.scope, Symbol.sym, unit) Scope_table.t3;
}



let show_sym sym =
  Pp_utils.to_plain_string (Pp_ail.pp_id sym)
(*  Symbol.instance_Show_Show_Symbol_sym_dict.show_method *)


type pointsto =
  [ `Current of ail_identifier
  | `Local of Cabs_to_ail_effect.scope * ail_identifier
  | `Funptr of ail_identifier
  | `Global of ail_identifier
  | `Wild ]

(* returns [[true]] iff pt1 extends (strictly) further than pt2 *)
let gt_pointsto (pt1: pointsto) (pt2: pointsto) =
  let open Cabs_to_ail_effect in
  match pt1, pt2 with
  | `Current _, _ ->
      false
  | `Local (Scope_block n1, _), `Local (Scope_block n2, _) ->
      n1 < n2
  | `Local _, `Local _ ->
      (* TODO: remove the scopes and only have block id *)
      assert false
  | `Funptr _, _
  | _, `Funptr _ ->
      (* TODO: this doesn't match the spec, but does correspond to no escape *)
      false
  | `Global _, (`Current _ | `Local _) ->
      true
  | `Local _, `Current _ ->
      true
  | _, `Wild ->
      false (* TODO: check *)
  | `Wild, _ ->
      true
  | _ ->
      false
(*
  | _ ->
      if pt1 <> pt2 then
        assert false
      else
        false
*)




let classify sigm env sym =
  match List.assoc_opt sym sigm.declarations with
    | Some (_, _, Decl_object _) ->
        `Global sym
    | Some (_, _, Decl_function _) ->
        `Funptr sym
    | None ->
        begin match Scopes.resolve sym env.scopes with
          | None ->
              Printf.printf "None ==> %s\n" (show_sym sym);
              assert false
          | Some (scope, ()) ->
              if Scopes.(scopeEqual scope (current_scope_is env.scopes)) then
                `Current sym
              else
                `Local (scope, sym)
        end


let get_ctype (AnnotatedExpression(gtc,_,_,_)) : Ctype.ctype =
  (* TODO: these are taken from ail_to_coq.ml (should we just export them in the .mli ?) *)
  let c_type_of_type_cat = function
    | GenTypes.LValueType(_,c_ty,_) -> c_ty
    | GenTypes.RValueType(c_ty)     -> c_ty in
  let to_type_cat tc =
    let loc = Location_ocaml.unknown in
    let impl = Ocaml_implementation.hafniumIntImpl in
    let m_tc = GenTypesAux.interpret_genTypeCategory loc impl tc in
    match ErrorMonad.runErrorMonad m_tc with
      | Either.Right(tc) -> tc
      | Either.Left(_,_) -> assert false (* FIXME possible here? *) in
  c_type_of_type_cat (to_type_cat gtc)


let points_to classify expr =
  let is_lvalue =
    match expr with
      | AnnotatedExpression (GenTypes.GenLValueType _, _, _, _) ->
          true
      | AnnotatedExpression (GenTypes.GenRValueType _, _, _, _) ->
          false in
  
  let rec aux (AnnotatedExpression (_, _, _, expr_)) =
    match expr_ with
      | AilEbuiltin _
      | AilEstr _
      | AilEconst _
      | AilEsizeof _
      | AilEalignof _
      | AilEreg_load _
      | AilEsizeof_expr _
      | AilEoffsetof _
      | AilEassert _ ->
          []
      | AilEident sym ->
          [classify sym]
      | AilEunary (Address, e) ->
          (* TODO: need to distinguish lvalue from rvalue *)
(*
          if is_lvalue then
            print_endline "Address LVALUE"
          else
            print_endline "Address RVALUE";
*)
          aux e
      
      | AilEunary (Indirection, e) ->
          begin match AilTypesAux.referenced_type (get_ctype e) with
            | Some ref_ty when AilTypesAux.is_pointer ref_ty ->
                [ `Wild ]
            | _ ->
                if is_lvalue then
                  [`Wild]
                else
                  [] (* TODO ???? *)
          end
      | AilEunary (_, e) ->
          aux e (* TODO: failwith "AilEunary" *)
      | AilEcast (_, _, e) ->
          aux e
      | AilEcompound (_, _, e) ->
          failwith "AilEcompound"
      | AilEmemberof (e, _) ->
(*          Printf.printf "==> %s\n" (Pp_utils.to_plain_string (Pp_ail.pp_expression expr)); *)
          [] (* TODO: failwith "AilEmemberof" *)
      | AilEmemberofptr (e, _) ->
          [] (* `UNKNOWN ? *)
      | AilEannot (_, e) ->
          aux e
      
      | AilEva_start _
      | AilEva_arg _
      | AilEva_end _
      | AilEva_copy _ ->
          []
      
      | AilEprint_type e
      | AilEbmc_assume e ->
          aux e
      
      | AilErvalue e ->
          [] (* TODO: failwith "AilErvalue" *)
      | AilEarray_decay e ->
          [] (* TODO: failwith "AilEarray_decay" *)
      | AilEfunction_decay e ->
          failwith "AilEfunction_decay"
      | AilEbinary (e1, _, e2) ->
          if AilTypesAux.is_pointer (get_ctype e1) then
            aux e1
          else if AilTypesAux.is_pointer (get_ctype e2) then
            aux e2
          else
            [] (* TODO: what if the integers came from casting a pointer? *)
      | AilEassign (e1, e2) ->
          aux e2 (* TODO: the pointsto of e1 can't escape? *)
      | AilEcompoundAssign (e1, _, e2) ->
          failwith "AilEcompoundAssign"
      | AilEcond (_, e2, e3) ->
          aux e2 @ aux e3
      
      | AilEcall (e, es) ->
          []
      
      | AilEgeneric (e ,gas) ->
          failwith "AilEgeneric"
      | AilEarray (_, _, xs) ->
          failwith "AilEarray"
      | AilEstruct (_, xs) ->
          failwith "AilEstruct"
      | AilEunion (_, _, e_opt) ->
          failwith "AilEunion"
  in
  aux expr


let str_points_to classify expr =
  Lem_show.stringFromList
    begin function
      | `Global sym ->
          "global: " ^ show_sym sym
      | `Funptr sym ->
          "funptr: " ^ show_sym sym
      | `Current sym ->
          "current: " ^ show_sym sym
      | `Local (scope, sym) ->
          "local(scope: " ^ Scopes.string_of_scope scope ^ "): " ^ show_sym sym
      | `Wild ->
          "wild"
    end
    (points_to classify expr)


let foo z =
  Lem_show.stringFromList
    begin function
      | `Global sym ->
          "global: " ^ show_sym sym
      | `Funptr sym ->
          "funptr: " ^ show_sym sym
      | `Current sym ->
          "current: " ^ show_sym sym
      | `Local (scope, sym) ->
          "local(scope: " ^ Scopes.string_of_scope scope ^ "): " ^ show_sym sym
      | `Wild ->
          "wild"
    end z


let scope_of_lvalue classify expr =
  let _xs = points_to classify expr in
  failwith "wip"


let warn_file (_, sigm) =
  let rec aux_expr env (AnnotatedExpression (_, _, loc, expr_)) =
    let self = aux_expr env in
    match expr_ with
      | AilEbuiltin _
      | AilEstr _
      | AilEconst _
      | AilEident _
      | AilEsizeof _
      | AilEalignof _
      | AilEreg_load _ ->
          ()
(*
      | AilEunary (Address, e) when env.block_depth > 1 ->
          Panic.wrn (Some loc)
            "an address is taken inside an inner block ==> %s <==> pointsto: %s"
            (Pp_utils.to_plain_string (Pp_ail.pp_expression e))
            (str_points_to (classify sigm env) e)
*)
      | AilEassign (e1, e2)
      | AilEcompoundAssign (e1, _, e2) ->
          (* Warn if [[e2]] points to objects whose scope is smaller than the scope of
             the object referred by the lvalue [[e1]] *)
          let xs1 = points_to (classify sigm env) e1 in
          let xs2 = points_to (classify sigm env) e2 in
          if xs2 <> [] && List.exists (fun (x, y) -> gt_pointsto x y) (Utils.product_list xs1 xs2) then
            Printf.printf "%sASSIGN[%s] ==> lvalue: %s -- e2: %s\x1b[0m\n"
             (if List.exists (fun (x, y) -> gt_pointsto x y) (Utils.product_list xs1 xs2) then "\x1b[31m" else "")
             (Location_ocaml.location_to_string loc)
              (foo xs1)
              (foo xs2);
          () (* exit 1 *)

(*
          let _scope1 = scope_of_lvalue (classify sigm env) e1 in
          failwith "WIP: assignments"
*)
      | AilEunary (_, e)
      | AilEcast (_, _, e)
      | AilEassert e
      | AilEcompound (_, _, e)
      | AilEmemberof (e, _)
      | AilEmemberofptr (e, _)
      | AilEsizeof_expr e
      | AilEannot (_, e)
      | AilEva_start (e, _)
      | AilEva_arg (e, _)
      | AilEva_end e
      | AilEprint_type e
      | AilEbmc_assume e
      | AilErvalue e
      | AilEarray_decay e
      | AilEfunction_decay e ->
          self e
      | AilEbinary (e1, _, e2)
      | AilEva_copy (e1, e2) ->
          self e1;
          self e2
      | AilEcond (e1, e2, e3) ->
          self e1;
          self e2;
          self e3
      | AilEcall (e, es) ->
          let xss = List.map (fun e -> points_to (classify sigm env) e) es in
          if List.exists (fun xs -> xs <> []) xss then
            Printf.printf "AilEcall[%s] ==> warn ==> %s\n"
              (Location_ocaml.location_to_string loc)
              (String.concat " -- " (List.map foo xss));
          self e;
          List.iter self es
      | AilEoffsetof _ ->
          ()
      | AilEgeneric (e ,gas) ->
          self e;
          List.iter (function
            | AilGAtype (_, e)
            | AilGAdefault e ->
                self e
          ) gas
      | AilEarray (_, _, xs) ->
          List.iter (function
            | Some e ->
                self e
            | None ->
                ()
          ) xs
      | AilEstruct (_, xs) ->
          List.iter (function
            | (_, Some e) ->
                self e
            | (_, None) ->
                ()
          ) xs
      | AilEunion (_, _, e_opt) ->
          begin match e_opt with
            | Some e ->
                self e
            | None ->
                ()
          end in
  let rec aux env (AnnotatedStatement (loc, _, stmt_)) =
    let self = aux env in
    match stmt_ with
      | AilSskip ->
          ()
      | AilSexpr e
      | AilSreturn e ->
          aux_expr env e
      | AilSblock (bs, ss) ->
          let new_scopes =
            List.fold_left (fun acc (sym, _) ->
              Scopes.register sym acc
            ) (Scopes.create_scope (Cabs_to_ail_effect.Scope_block env.counter) env.scopes) bs in
          let env' = {
            counter= env.counter + 1;
            block_depth= env.block_depth + 1;
            scopes = new_scopes;
          } in
(*          Printf.printf "AilSblock => counter: %d\n" env'.counter; *)
          List.iter (aux env') ss
      | AilSif (e, s1, s2) ->
          aux_expr env e;
          self s1;
          self s2
      | AilSwhile (e, s) ->
          self s;
          aux_expr env e
      | AilSdo (s, e) ->
          aux_expr env e;
          self s
      | AilSbreak
      | AilScontinue
      | AilSreturnVoid ->
          ()
      | AilSswitch (e, s) ->
          aux_expr env e;
          self s
      | AilScase (_, s)
      | AilSdefault s
      | AilSlabel (_, s) ->
          self s
      | AilSgoto _ ->
          ()
      | AilSdeclaration xs ->
          List.iter (fun (_, e) ->
            aux_expr env e
          ) xs
      | AilSpar ss ->
          List.iter (aux { env with block_depth= 0 }) ss
      | AilSreg_store (_, e) ->
          aux_expr env e in
  List.iter (fun (_, (_, _, params, stmt)) ->
    (* NOTE: following (§6.2.1#4), the function parameters are placed in a block scope *)
    let fun_scopes =
      List.fold_left (fun acc sym ->
        Scopes.register sym acc
      ) (Scopes.(create_scope (Cabs_to_ail_effect.Scope_block 0) empty)) params in
    aux { counter= 1; block_depth= 0; scopes= fun_scopes } stmt;
    flush_all ()
  ) sigm.function_definitions
