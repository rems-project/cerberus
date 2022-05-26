module CF = Cerb_frontend

module RP = ResourcePredicates

module IT = IndexTerms

open CF.Cn

type cn_predicate =
  (CF.Symbol.sym, CF.Ctype.ctype) CF.Cn.cn_predicate

type cn_function =
  (CF.Symbol.sym, CF.Ctype.ctype) CF.Cn.cn_function


let rec translate_cn_base_type (bTy: CF.Symbol.sym cn_base_type) =
  let open BaseTypes in
  match bTy with
    | CN_unit ->
        Unit
    | CN_bool ->
        Bool
    | CN_integer ->
        Integer
    | CN_real ->
        Real
    | CN_loc ->
        Loc
    | CN_struct tag_sym ->
        Struct tag_sym
    | CN_map (bTy1, bTy2) ->
        Map ( translate_cn_base_type bTy1
            , translate_cn_base_type bTy2 )
    | CN_list bTy' -> 
        List (translate_cn_base_type bTy')
    | CN_tuple bTys ->
        Tuple (List.map translate_cn_base_type bTys)
    | CN_set bTy' ->
        Set (translate_cn_base_type bTy')


let mk_translate_binop bop bTy =
  let open IndexTerms in
  match bop, bTy with
    | CN_add, (BT.Integer | BT.Real) ->
        add_
    | CN_sub, (BT.Integer | BT.Real) ->
        sub_
    | CN_mul, (BT.Integer | BT.Real) ->
        mul_
    | CN_div, (BT.Integer | BT.Real) ->
        div_
    | CN_equal, _ ->
        eq_
    | CN_inequal, _ ->
        ne_
    | CN_lt, (BT.Integer | BT.Real) ->
        lt_
    | CN_lt, BT.Loc ->
        ltPointer_
    | CN_le, (BT.Integer | BT.Real) ->
        le_
    | CN_le, BT.Loc ->
        lePointer_
    | CN_gt, (BT.Integer | BT.Real) ->
        gt_
    | CN_gt, BT.Loc ->
        gtPointer_
    | CN_ge, (BT.Integer | BT.Real) ->
        ge_
    | CN_ge, BT.Loc ->
        gePointer_
    | CN_or, BT.Bool ->
        fun (x, y) -> or_ [x; y]
    | CN_and, BT.Bool ->
        fun (x, y) -> and_ [x; y]
    | _ ->
        failwith "CompilePredicates.mk_translate_binop"

open Resultat
open Effectful.Make(Resultat)

type message =
  | First_iarg_missing of { pred_name: Sym.t }
  | First_iarg_not_pointer of { pred_name: Sym.t; found_bty: BaseTypes.t }
  | Invalid_oarg_owned of { invalid_ident: Id.t }
  | Invalid_oarg of { res_name: Sym.t; invalid_ident: Id.t }
  | Invalid_struct_member of { struct_name: Sym.t; invalid_ident: Id.t }
  | TypeMismatchBinary of { bTy1: BaseTypes.t; bTy2: BaseTypes.t }
  | TODO_error of string

type error = {
  loc: Locations.t;
  msg: message
}

let pp_message = let open Pp in function
  | First_iarg_missing { pred_name } ->
      !^ "a predicate definition must have at least one iarg (missing from: " ^^ Sym.pp pred_name ^^ !^ ")"
  | First_iarg_not_pointer { pred_name; found_bty } ->
      !^ "the first iarg of predicate" ^^^ Pp.squotes (Sym.pp pred_name) ^^^
      !^ "must have type" ^^^ Pp.squotes (BaseTypes.(pp Loc)) ^^^ !^ "but was found with type" ^^^
      Pp.squotes (BaseTypes.(pp found_bty))
  | Invalid_oarg_owned { invalid_ident } ->
      Pp.squotes (Pp.dot ^^ Id.pp invalid_ident) ^^^ !^ "is not an oarg of 'Owned()' (expecting '.value')"
  | Invalid_oarg { res_name; invalid_ident } ->
      Pp.squotes (Pp.dot ^^ Id.pp invalid_ident) ^^^ !^ "is not an oarg of" ^^^
      Pp.squotes(Sym.pp res_name)
  | Invalid_struct_member { struct_name; invalid_ident } ->
      Pp.squotes (Pp.dot ^^ Id.pp invalid_ident) ^^^ !^ "is not a member of" ^^^
      Pp.squotes(!^ "struct" ^^^ Sym.pp struct_name)
  | TypeMismatchBinary { bTy1; bTy2 } ->
      !^ "type mismatch in a binary operator" ^^^ Pp.parens (
        Pp.squotes (BaseTypes.pp bTy1) ^^^ !^ " <-> " ^^^ Pp.squotes (BaseTypes.pp bTy2)
      )
  | TODO_error str ->
      !^ ("TODO(msg): " ^ str)


let report_error {loc; msg} =
  let doc = pp_message msg in
  Pp.error loc doc []

module Env = struct
  module X = Map.Make(Sym)
  module Y = Map.Make(String)

  type function_sig = {
      args: (Sym.t * BaseTypes.t) list;
      return_bty: BaseTypes.t;
    }

  type predicate_sig = {
    pred_iargs: (Sym.t * BaseTypes.t) list;
    pred_oargs: (Sym.t * BaseTypes.t) list;
  }
  
  type resource_def =
    | RPred_owned of BaseTypes.t * Sym.t (* value member *)
    | RPred_block
    | RPred_named of Sym.t * Sym.t list

  type t = {
    logicals: BaseTypes.t X.t;
    pred_names: Sym.t Y.t;
    functions: function_sig X.t;
    predicates: predicate_sig X.t;
    resources: resource_def X.t;
    tagDefs: CF.Core_anormalise.Mu.mu_tag_definitions;
  }

  let empty tagDefs =
    { logicals= X.empty; pred_names= Y.empty; functions = X.empty; predicates= X.empty; resources= X.empty; tagDefs }
  
  let add_logical sym bTy env =
    {env with logicals= X.add sym bTy env.logicals }
  
  let add_pred_name str sym env =
    {env with pred_names= Y.add str sym env.pred_names }
  
  let add_function sym func_sig env =
    {env with functions= X.add sym func_sig env.functions }

  let add_predicate sym pred_sig env =
    {env with predicates= X.add sym pred_sig env.predicates }
  
  let add_resource sym res_def env =
    { env with resources= X.add sym res_def env.resources }
  
  let lookup_logical sym env =
    X.find_opt sym env.logicals

  let lookup_pred_name str env =
    Y.find_opt str env.pred_names

  let lookup_predicate sym env =
    X.find_opt sym env.predicates

  let lookup_resource sym env =
    X.find_opt sym env.resources
  
  let lookup_struct sym env =
    match Pmap.lookup sym env.tagDefs with
      | Some (M_StructDef xs) ->
          Some xs
      | Some (M_UnionDef _)| None ->
          None
end


let todo_string_of_sym (CF.Symbol.Symbol (_, _, sd)) =
  match sd with
    | SD_Id str | SD_ObjectAddress str ->
        str
    | _ ->
        assert false

let translate_member_accesses loc env res_def xs =
  let mk_kind = function
    | BaseTypes.Struct tag_sym ->
        `STRUCT tag_sym
    | _ ->
        `LOGICAL in
  let rec aux acc kind = function
    | [] ->
        begin match acc with
          | None ->
              assert false
          | Some z ->
              return z
        end
    | ident :: xs ->
        let open IndexTerms in
        begin match kind with
          | `RES (Env.RPred_owned (bTy, value_sym)) ->
              if String.equal "value" (Id.pp_string ident) then
                let acc' = Some (sym_ (value_sym, bTy)) in
                aux acc' (mk_kind bTy) xs
              else
                fail {loc; msg= Invalid_oarg_owned {invalid_ident= ident}}
          | `RES Env.RPred_block ->
              failwith "TODO: member access on a resource bound to a Block() predicate"
          | `RES (Env.RPred_named (pred_sym, res_oargs)) ->
              begin match Env.lookup_predicate pred_sym env with
                | None ->
                    assert false
                | Some pred_sig ->
                    let oargs =
                      List.map2 (fun (sym, bTy) sym' ->
                        (todo_string_of_sym sym, (sym', bTy))
                      )  pred_sig.pred_oargs res_oargs in
                    begin match List.assoc_opt (String.equal) (Id.pp_string ident) oargs with
                      | None ->
                          fail {loc; msg= Invalid_oarg {res_name= pred_sym; invalid_ident= ident}}
                      | Some memb ->
                        let acc' = Some (sym_ memb) in
                        aux acc' (mk_kind (snd memb)) xs
                    end
              end
          | `STRUCT tag_sym ->
              begin match Env.lookup_struct tag_sym env with
                | None ->
                    (* TODO: make the desugaring catch this *)
                    fail {loc; msg= TODO_error ("unknown struct: " ^ Sym.pp_string tag_sym)}
                | Some (defs_, _) (* TODO flexible *) ->
                    let defs =
                      List.map (fun (membr_ident, (_, _, ty)) ->
                        match Sctypes.of_ctype ty with
                          | None ->
                              assert false
                          | Some ty' ->
                              begin match acc with
                                | None ->
                                    assert false
                                | Some z ->
                                    let member_bt = BaseTypes.of_sct ty' in
                                    ( Id.pp_string membr_ident
                                    , member_ ~member_bt (tag_sym, z, membr_ident) )
                              end
                      ) defs_ in
                begin match List.assoc_opt (String.equal) (Id.pp_string ident) defs with
                  | None ->
                      fail {loc; msg= Invalid_struct_member {struct_name= tag_sym; invalid_ident= ident}}
                  | Some x ->
                      aux (Some x) (mk_kind (basetype x)) xs
                end
              end
          | `LOGICAL ->
              fail {loc; msg= TODO_error "member access on a scalar"}
        end in
  aux None (`RES res_def) xs


let translate_cn_expr (env: Env.t) expr =
  let open IndexTerms in
  let module BT = BaseTypes in
  let rec self (CNExpr (loc, expr_)) =
    match expr_ with
      | CNExpr_const CNConst_NULL ->
          return null_
      | CNExpr_const (CNConst_integer n) ->
          return (z_ n)
      | CNExpr_const (CNConst_bool b) ->
          return (bool_ b)
      | CNExpr_var sym ->
          begin match Env.lookup_logical sym env with
            | None ->
                fail {loc; msg= TODO_error ("TODO(msg) CNExpr_var lookup failed ==> " ^ todo_string_of_sym sym)}
            | Some bTy ->
                return (IT (Lit (Sym sym), bTy))
          end
      | CNExpr_nil bTy_ ->
          return (nil_ ~item_bt:(translate_cn_base_type bTy_))
      | CNExpr_cons (e1_, e2_) ->
          let@ e1 = self e1_ in
          let@ e2 = self e2_ in
          return (cons_ (e1, e2))
      | CNExpr_list es_ ->
          let@ es = ListM.mapM self es_ in
          let item_bt = basetype (List.hd es) in
          return (list_ ~item_bt es)
      | CNExpr_memberof (sym, xs) ->
          begin match Env.lookup_resource sym env with
            | None ->
                (* TODO: (could the case where sym is a C struct) is this allowed? *)
                failwith ("TODO: CNExpr_memberof ==> " ^ Sym.pp_string sym)
            | Some res_def ->
                translate_member_accesses loc env res_def xs
          end
      | CNExpr_binop (bop, e1_, e2_) ->
          let@ e1 = self e1_ in
          let@ e2 = self e2_ in
          let bTy1 = basetype e1 in
          let bTy2 = basetype e2 in
          if BT.equal bTy1 bTy2 then
            return (mk_translate_binop bop (basetype e1) (e1, e2))
          else
            fail {loc; msg= TypeMismatchBinary { bTy1; bTy2 }}
  in self expr


let translate_cn_clause env clause =
  let rec translate_cn_clause_aux env acc clause =
    let module AT = ArgumentTypes in
    match clause with
      | CN_letResource (res_loc, sym, res, cl) ->
          let open Resources in
          begin match res with
            | CN_pred (pred_loc, CN_owned ty, [expr_]) ->
                begin match Sctypes.of_ctype ty with
                  | None ->
                      fail {loc= Locations.unknown; msg= TODO_error "CN_owned -- of_ctype failed"}
                  | Some scty ->
                      let@ expr = translate_cn_expr env expr_ in
                      let bTy = BaseTypes.of_sct scty in
                      let value_sym, value_sym_expr = IT.fresh bTy in
                      let acc' =
                        fun z -> acc begin
                          let pt =
                            (ResourceTypes.P { name = Owned scty
                                ; pointer= expr
                                ; permission= IT.bool_ true
                                ; iargs = []},
                             [(Resources.value_sym, value_sym_expr); 
                              (Resources.init_sym, IT.bool_ true)]) 
                          in
                          AT.mLogical (value_sym, bTy, (res_loc, None))
                          (AT.mResource (pt, (pred_loc, None)) z)
                        end in
                      let env' = Env.(add_resource sym (RPred_owned (bTy, value_sym)) env) in
                      translate_cn_clause_aux env' acc' cl
                end
            | CN_pred (_, CN_owned _, _) ->
                fail {loc= Locations.unknown; msg= TODO_error "Owned applied to more/less than 1 argument"}
            | CN_pred (pred_loc, CN_block ty, [expr_]) ->
                begin match Sctypes.of_ctype ty with
                  | None ->
                      fail {loc= Locations.unknown; msg= TODO_error "CN_owned -- of_ctype failed"}
                  | Some scty ->
                      let@ expr = translate_cn_expr env expr_ in
                      let bTy = BaseTypes.of_sct scty in
                      let value_sym, value_sym_expr = IT.fresh bTy in
                      let init_sym, init_sym_expr = IT.fresh BaseTypes.Bool in
                      let acc' =
                        fun z -> acc begin
                          let pt =
                            (ResourceTypes.P { name = Owned scty
                                ; pointer= expr
                                ; permission= IT.bool_ true
                                ; iargs = []},
                             [(Resources.value_sym, value_sym_expr); 
                              (Resources.init_sym, init_sym_expr)]) 
                          in
                          AT.mLogical (value_sym, bTy, (res_loc, None))
                          (AT.mLogical (init_sym, BaseTypes.Bool, (res_loc, None))
                          (AT.mResource (pt, (pred_loc, None)) z))
                        end in
                      translate_cn_clause_aux env acc' cl
                end
            | CN_pred (_, CN_block _, _) ->
                fail {loc= Locations.unknown; msg= TODO_error "Block applied to more/less than 1 argument"}
            | CN_pred (pred_loc, CN_named pred_sym, es_) ->
                begin match Env.lookup_predicate pred_sym env with
                  | None ->
                      fail {loc= Locations.unknown; msg= TODO_error ("unknown predicate name ==> " ^ Sym.pp_string pred_sym)}
                  | Some pred_sig ->
                      let nargs = List.length es_ in
                      let nexpected = List.length pred_sig.pred_iargs in
                      if nargs <> nexpected then
                        fail {loc= Locations.unknown; msg= TODO_error (Printf.sprintf "predicate %s expecting %d arguments, found %d\n"
                          (Sym.pp_string pred_sym) nexpected nargs)}
                      else
                        let@ es =
                          ListM.mapM (fun ((_, bTy), e_) ->
                            let@ e = translate_cn_expr env e_ in
                            if not (BaseTypes.equal (IT.basetype e) bTy) then
                              fail {loc= Locations.unknown; msg= TODO_error (Printf.sprintf "illtyped argument for predicate %s\n" (Sym.pp_string pred_sym))}
                            else
                              return e
                          ) (List.combine pred_sig.pred_iargs es_) in
                        let (o_syms, o_sym_bTys, o_sym_exprs) =
                          List.fold_left (fun (acc1, acc2, acc3) (oarg_name, o_bTy) ->
                            let o_sym, o_sym_expr = IT.fresh o_bTy in
                            (o_sym :: acc1, (o_sym, o_bTy, (res_loc, None)) :: acc2, (oarg_name, o_sym_expr) :: acc3)
                          ) ([], [], []) (List.rev pred_sig.pred_oargs) in
                        let acc' =
                          fun z -> acc begin
                            let pred =
                              (ResourceTypes.P { name= (*TODO*) PName (todo_string_of_sym pred_sym)
                                  ; pointer= List.hd es
                                  ; permission= IT.bool_ true
                                  ; iargs= List.tl es
                              },
                               o_sym_exprs)  (* TODO: Christopher please check this *)
                            in
                              AT.mLogicals o_sym_bTys
                              (AT.mResource (pred, (pred_loc, None)) z)
                          end in
                        let env' = Env.(add_resource sym (RPred_named (pred_sym, o_syms)) (* { res_pred= pred_sym; res_oargs= o_syms}*) env) in
                        translate_cn_clause_aux env' acc' cl
                end
            | CN_each _ ->
                failwith "TODO: CN_each"
          end
      | CN_letExpr (loc, sym, e_, cl) ->
          let@ e = translate_cn_expr env e_ in
          let acc' =
            fun z -> acc begin
              AT.mDefine (sym, e, (loc, None)) z
            end in
            translate_cn_clause_aux (Env.add_logical sym (IT.basetype e) env) acc' cl
      | CN_assert (loc, e_, cl) ->
          let@ e = translate_cn_expr env e_ in
          let acc' =
            fun z -> acc begin
              AT.mConstraint ( LogicalConstraints.T e
                             , (loc, None) ) z
            end in
            translate_cn_clause_aux env acc' cl
      | CN_return (loc, xs_) ->
          let@ xs =
            ListM.mapM (fun (sym, e_) ->
              let@ e = translate_cn_expr env e_ in
              return (OutputDef.{loc= loc; name= sym; value= e})
            ) xs_ in
          acc (AT.I xs) in
  translate_cn_clause_aux env (fun z -> return z) clause


let translate_cn_clauses env clauses =
  let rec self acc = function
    | CN_clause (loc, cl_) ->
        let@ cl = translate_cn_clause env cl_ in
        return (RP.{loc= loc; guard= IT.bool_ true; packing_ft= cl} :: acc)
    | CN_if (loc, e_, cl_, clauses') ->
      let@ e  = translate_cn_expr env e_ in
      let@ cl = translate_cn_clause env cl_ in
      self begin
        RP.{loc= loc; guard= e; packing_ft= cl} :: acc
      end clauses'
  in
  let@ xs = self [] clauses in
  return (List.rev xs)


let translate_cn_func_body env body =
  let rec translate_cn_func_body_aux env acc body =
    match body with
      | CN_fb_letExpr (loc, sym, e_, cl) ->
          let@ e = translate_cn_expr env e_ in
          let acc' =
            fun z -> acc begin
              IT.let_ sym e z
            end in
            translate_cn_func_body_aux (Env.add_logical sym (IT.basetype e) env) acc' cl
      | CN_fb_return (loc, x) ->
         let@ x = translate_cn_expr env x in
         acc x
  in
  translate_cn_func_body_aux env (fun z -> return z) body



let register_cn_predicates tagDefs (defs: cn_predicate list) =
  let aux env def =
    let translate_args xs =
      List.map (fun (bTy, sym) ->
        (sym, translate_cn_base_type bTy)
      ) xs in
    let iargs = translate_args def.cn_pred_iargs in
    let oargs = translate_args def.cn_pred_oargs in
    Env.add_predicate def.cn_pred_name { pred_iargs= iargs; pred_oargs= oargs } env in
  List.fold_left aux (Env.empty tagDefs) defs




let translate_and_register_cn_function env (def: cn_function) =
  let open LogicalPredicates in
  let args = 
    List.map (fun (bTy, sym) -> (sym, translate_cn_base_type bTy)
      ) def.cn_func_args in
  let env' =
    List.fold_left (fun acc (sym, bt) -> Env.add_logical sym bt acc
      ) env args in
  let@ definition = match def.cn_func_body with
    | Some body -> 
       let@ body = translate_cn_func_body env' body in
       return (Def body)
    | None -> return Uninterp in
  let return_bt = translate_cn_base_type def.cn_func_return_bty in
  return {loc = def.cn_func_loc; args; return_bt; definition; infer_arguments = failwith "asd"}


let translate_cn_predicate env (def: cn_predicate) =
  let open RP in
  let (iargs, oargs) =
    match Env.lookup_predicate def.cn_pred_name env with
      | None ->
          assert false
      | Some pred_sig ->
          (pred_sig.pred_iargs, pred_sig.pred_oargs) in
  let env' =
    List.fold_left (fun acc (sym, bTy) ->
      Env.add_logical sym bTy acc
    ) env iargs in
  let@ clauses = translate_cn_clauses env' def.cn_pred_clauses in
  match iargs with
    | (iarg0, BaseTypes.Loc) :: iargs' ->
        return 
          ( todo_string_of_sym (* TODO *)def.cn_pred_name
          , { loc= def.cn_pred_loc
            ; pointer= iarg0
            ; iargs= iargs'
            ; oargs= oargs
            ; clauses= clauses
            } )
    | (_, found_bty) :: _ ->
        fail { loc= def.cn_pred_loc; msg= First_iarg_not_pointer { pred_name= def.cn_pred_name; found_bty } }
    | [] ->
        fail { loc= def.cn_pred_loc; msg= First_iarg_missing { pred_name= def.cn_pred_name} }

let translate tagDefs (defs: cn_predicate list) =
  let env_with_preds = register_cn_predicates tagDefs defs in
  ListM.mapM (translate_cn_predicate env_with_preds) defs

