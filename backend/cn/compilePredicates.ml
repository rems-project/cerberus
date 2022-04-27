module CF = Cerb_frontend

module RP = ResourcePredicates

module IT = IndexTerms

open CF.Cn

type cn_predicate =
  (CF.Symbol.sym, CF.Ctype.ctype) CF.Cn.cn_predicate

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

module Env = struct
  module X = Map.Make(Sym)

  type predicate_sig = {
    pred_iargs: (Sym.t * BaseTypes.t) list;
    pred_oargs: (Sym.t * BaseTypes.t) list;
  }
  
  type ressource_def =
    | RPred_owned of BaseTypes.t * Sym.t (* value member *)
    | RPred_block
    | RPred_named of Sym.t * Sym.t list

  (* type ressource_def = {
    res_pred: Sym.t;
    res_oargs: Sym.t list;
  } *)

  type t = {
    logicals: BaseTypes.t X.t;
    predicates: predicate_sig X.t;
    ressources: ressource_def X.t;
    tagDefs: CF.Core_anormalise.Mu.mu_tag_definitions;
  }

  let empty tagDefs =
    { logicals= X.empty; predicates= X.empty; ressources= X.empty; tagDefs }
  
  let add_logical sym bTy env =
    {env with logicals= X.add sym bTy env.logicals }
  
  let add_predicate sym pred_sig env =
    {env with predicates= X.add sym pred_sig env.predicates }
  
  let add_ressource sym res_def env =
    { env with ressources= X.add sym res_def env.ressources }
  
  let lookup_logical sym env =
    X.find_opt sym env.logicals

  let lookup_predicate sym env =
    X.find_opt sym env.predicates

  let lookup_ressource sym env =
    X.find_opt sym env.ressources
  
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

let translate_member_accesses env res_def xs =
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
                fail "TODO(msg): only .value is valid for a Owned()"
          | `RES Env.RPred_block ->
              failwith "TODO: member access on a ressource bound to a Block() predicate"
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
                          let msg =
                            Printf.sprintf "TODO(msg): .%s is not an oarg of ressource %s"
                              (Id.pp_string ident) (Sym.pp_string pred_sym) in
                          fail msg
                      | Some memb ->
                        let acc' = Some (sym_ memb) in
                        aux acc' (mk_kind (snd memb)) xs
                    end
              end
          | `STRUCT tag_sym ->
              begin match Env.lookup_struct tag_sym env with
                | None ->
                    (* TODO: make the desugaring catch this *)
                    fail ("TODO(msg): unknown struct: " ^ Sym.pp_string tag_sym)
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
                      fail "TODO(msg): invalid struct member"
                  | Some x ->
                      aux (Some x) (mk_kind (basetype x)) xs
                end
              end
          | `LOGICAL ->
              fail "TODO(msg): member access on a scalar"
        end in
  aux None (`RES res_def) xs


let translate_cn_expr (env: Env.t) expr =
  let open IndexTerms in
  let module BT = BaseTypes in
  let rec self = function
    | CNExpr_const CNConst_NULL ->
        return null_
    | CNExpr_const (CNConst_integer n) ->
        return (z_ n)
    | CNExpr_const (CNConst_bool b) ->
        return (bool_ b)
    | CNExpr_var sym ->
        begin match Env.lookup_logical sym env with
          | None ->
              fail ("TODO(msg) CNExpr_var lookup failed ==> " ^ todo_string_of_sym sym)
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
        begin match Env.lookup_ressource sym env with
          | None ->
              (* TODO: (could the case where sym is a C struct) is this allowed? *)
              failwith ("TODO: CNExpr_memberof ==> " ^ Sym.pp_string sym)
          | Some res_def ->
              translate_member_accesses env res_def xs
        end
    | CNExpr_binop (bop, e1_, e2_) ->
        let@ e1 = self e1_ in
        let@ e2 = self e2_ in
        if BT.equal (basetype e1) (basetype e2) then
          return (mk_translate_binop bop (basetype e1) (e1, e2))
        else
          fail "CNExpr_binop -- type mismatch"
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
                      fail "CN_owned -- of_ctype failed"
                  | Some scty ->
                      let@ expr = translate_cn_expr env expr_ in
                      let bTy = BaseTypes.of_sct scty in
                      let value_sym, value_sym_expr = IT.fresh bTy in
                      let acc' =
                        fun z -> acc begin
                          let pt =
                            RE.({ ct= scty
                                ; pointer= expr
                                ; permission= IT.bool_ true
                                ; value= value_sym_expr
                                ; init= IT.bool_ true }) in
                          AT.mLogical (value_sym, bTy, (res_loc, None))
                          (AT.mResource (Point pt, (pred_loc, None)) z)
                        end in
                      (* translate_cn_clause_aux env acc' cl *)
                      let env' = Env.(add_ressource sym (RPred_owned (bTy, value_sym)) env) in
                      translate_cn_clause_aux env' acc' cl
                end
            | CN_pred (_, CN_owned _, _) ->
                fail "Owned applied to more/less than 1 argument"
            | CN_pred (pred_loc, CN_block ty, [expr_]) ->
                begin match Sctypes.of_ctype ty with
                  | None ->
                      fail "CN_owned -- of_ctype failed"
                  | Some scty ->
                      let@ expr = translate_cn_expr env expr_ in
                      let bTy = BaseTypes.of_sct scty in
                      let value_sym, value_sym_expr = IT.fresh bTy in
                      let init_sym, init_sym_expr = IT.fresh BaseTypes.Bool in
                      let acc' =
                        fun z -> acc begin
                          let pt =
                            RE.({ ct= scty
                                ; pointer= expr
                                ; permission= IT.bool_ true
                                ; value= value_sym_expr
                                ; init= init_sym_expr }) in
                          AT.mLogical (value_sym, bTy, (res_loc, None))
                          (AT.mLogical (init_sym, BaseTypes.Bool, (res_loc, None))
                          (AT.mResource (Point pt, (pred_loc, None)) z))
                        end in
                      translate_cn_clause_aux env acc' cl
                end
            | CN_pred (_, CN_block _, _) ->
                fail "Block applied to more/less than 1 argument"  
            | CN_pred (pred_loc, CN_named pred_sym, es_) ->
                begin match Env.lookup_predicate pred_sym env with
                  | None ->
                      fail ("TODO(msg): unknown predicate name ==> " ^ Sym.pp_string pred_sym)
                  | Some pred_sig ->
                      let nargs = List.length es_ in
                      let nexpected = List.length pred_sig.pred_iargs in
                      if nargs <> nexpected then
                        fail (Printf.sprintf "TODO(msg): predicate %s expecting %d arguments, found %d\n"
                          (Sym.pp_string pred_sym) nexpected nargs)
                      else
                        let@ es =
                          ListM.mapM (fun ((_, bTy), e_) ->
                            let@ e = translate_cn_expr env e_ in
                            if not (BaseTypes.equal (IT.basetype e) bTy) then
                              fail (Printf.sprintf "TODO(msg): illtyped argument for predicate %s\n" (Sym.pp_string pred_sym))
                            else
                              return e
                          ) (List.combine pred_sig.pred_iargs es_) in
                        let (o_syms, o_sym_bTys, o_sym_exprs) =
                          List.fold_left (fun (acc1, acc2, acc3) (_, o_bTy) ->
                            let o_sym, o_sym_expr = IT.fresh o_bTy in
                            (o_sym :: acc1, (o_sym, o_bTy, (res_loc, None)) :: acc2, o_sym_expr :: acc3)
                          ) ([], [], []) (List.rev pred_sig.pred_oargs) in
                        let acc' =
                          fun z -> acc begin
                            let pred =
                              RE.({ name= (*TODO*) todo_string_of_sym pred_sym
                                  ; pointer= List.hd es
                                  ; permission= IT.bool_ true
                                  ; iargs= List.tl es
                                  ; oargs= o_sym_exprs (* TODO: Christopher please check this *)
                              }) in
                              AT.mLogicals o_sym_bTys
                              (AT.mResource (Predicate pred, (pred_loc, None)) z)
                          end in
                        let env' = Env.(add_ressource sym (RPred_named (pred_sym, o_syms)) (* { res_pred= pred_sym; res_oargs= o_syms}*) env) in
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

(*

type OutputDef.entry = {
    loc : Locations.t;
    name : string;
    value : IndexTerms.t;
  }

type OutputDef.t = entry list


type clause = {
    loc : Locations.t;
    guard : IndexTerms.t;
    packing_ft : ArgumentTypes.packing_ft
  }

*)


(*

type 'i ArgumentTypes.t = 
  | Computational of (Sym.t * BT.t) * info * 'i at
  | Logical of (Sym.t * LS.t) * info * 'i at
  | Define of (Sym.t * IT.t) * info * 'i at
  | Resource of RE.t * info * 'i at
  | Constraint of LC.t * info * 'i at
  | I of 'i

type ArgumentTypes.packing_ft = OutputDef.t t

*)



let translate_cn_predicate env (def: cn_predicate) = (*: CF.Symbol.sym * RP.definition = *)
  let open RP in
  let translate_args xs =
    List.map (fun (bTy, sym) ->
      (sym, translate_cn_base_type bTy)
    ) xs in
  let iargs = translate_args def.cn_pred_iargs in
  let oargs = translate_args def.cn_pred_oargs in
  let env_with_pred = Env.add_predicate def.cn_pred_name { pred_iargs= iargs; pred_oargs= oargs } env in
  let env' =
    List.fold_left (fun acc (sym, bTy) ->
      Env.add_logical sym bTy acc
    ) env_with_pred iargs in
  let@ clauses = translate_cn_clauses env' def.cn_pred_clauses in
  match iargs with
    | (iarg0, BaseTypes.Loc) :: iargs' ->
        return 
          ( env_with_pred
          , ( todo_string_of_sym (* TODO *)def.cn_pred_name
            , { loc= def.cn_pred_loc
              ; pointer= iarg0
              ; iargs= iargs'
              ; oargs= oargs
              ; clauses= clauses
              } ) )
    | (_, _) :: _ ->
        fail "TODO(msg): error first iarg must be a pointer"
    | [] ->
        fail "TODO(msg): error missing a first iarg"

let translate tagDefs (defs: cn_predicate list) =
  let@ (_, xs) =
    ListM.fold_leftM (fun (env, acc) def ->
      let@ (env', pred_def) = translate_cn_predicate env def in
      return (env', pred_def :: acc)
    ) (Env.empty tagDefs, []) defs in
  return (List.rev xs)
