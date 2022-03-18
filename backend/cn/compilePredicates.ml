module CF = Cerb_frontend

module RP = ResourcePredicates

module IT = IndexTerms

open CF.Cn

type cn_predicate =
  (CF.Symbol.sym, CF.Ctype.ctype) CF.Cn.cn_predicate

let loc_todo =
  Locations.unknown

let info_todo : Locations.info =
  (loc_todo, None)

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

  type ressource_def = {
    res_pred: Sym.t;
    res_oargs: Sym.t list;
  }

  type t = {
    logicals: BaseTypes.t X.t;
    predicates: predicate_sig X.t;
    ressources: ressource_def X.t;
  }

  let empty =
    { logicals= X.empty; predicates= X.empty; ressources= X.empty }
  
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
end



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
              fail ("TODO(msg) CNExpr_var lookup failed ==> " ^ Sym.pp_string sym)
          | Some bTy ->
              return (IT (Lit (Sym sym), bTy))
        end
    | CNExpr_memberof (sym, ident) ->
        begin match Env.lookup_ressource sym env with
          | None ->
              (* TODO: could a C struct *)
              failwith "TODO: CNExpr_memberof"
          | Some res_def ->
              begin match Env.lookup_predicate res_def.res_pred env with
                | None ->
                    assert false
                | Some pred_sig ->
                    let xs =
                      List.map2 (fun (sym, bTy) sym' ->
                        (Sym.pp_string sym, (sym', bTy))
                      )  pred_sig.pred_oargs res_def.res_oargs in
                  begin match List.assoc_opt (String.equal) (Id.pp_string ident) xs with
                    | None ->
                        fail "TODO: unknown member"
                    | Some memb ->
                      return (sym_ memb)
                  end
              end
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
      | CN_letResource (sym, res, cl) ->
          let open Resources in
          begin match res with
            | CN_pred (CN_owned ty, [expr_]) ->
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
                          AT.mLogical (value_sym, bTy, (loc_todo, None))
                          (AT.mResource (Point pt, (loc_todo, None)) z)
                        end in
                      translate_cn_clause_aux env acc' cl
                end
            | CN_pred (CN_owned _, _) ->
                fail "Owned applied to more/less than 1 argument"
            | CN_pred (CN_block ty, [expr_]) ->
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
                          AT.mLogical (value_sym, bTy, (loc_todo, None))
                          (AT.mLogical (init_sym, BaseTypes.Bool, (loc_todo, None))
                          (AT.mResource (Point pt, (loc_todo, None)) z))
                        end in
                      translate_cn_clause_aux env acc' cl
                end
            | CN_pred (CN_block _, _) ->
                fail "Block applied to more/less than 1 argument"  
            | CN_pred (CN_named pred_sym, es_) ->
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
                            (o_sym :: acc1, (o_sym, o_bTy, (loc_todo, None)) :: acc2, o_sym_expr :: acc3)
                          ) ([], [], []) (List.rev pred_sig.pred_oargs) in
                        let acc' =
                          fun z -> acc begin
                            let pred =
                              RE.({ name= (*TODO*) Sym.pp_string pred_sym
                                  ; pointer= List.hd es
                                  ; permission= IT.bool_ true
                                  ; iargs= List.tl es
                                  ; oargs= o_sym_exprs (* TODO: Christopher please check this *)
                              }) in
                              AT.mLogicals o_sym_bTys
                              (AT.mResource (Predicate pred, (loc_todo, None)) z)
                          end in
                        let env' = Env.add_ressource sym { res_pred= pred_sym; res_oargs= o_syms} env in
                        translate_cn_clause_aux env' acc' cl
                end
            | CN_each _ ->
                failwith "TODO: CN_each"
          end
      | CN_letExpr (sym, e_, cl) ->
          let@ e = translate_cn_expr env e_ in
          let acc' =
            fun z -> acc begin
              AT.mDefine (sym, e, (loc_todo, None)) z
            end in
            translate_cn_clause_aux (Env.add_logical sym (IT.basetype e) env) acc' cl
      | CN_assert (e_, cl) ->
          let@ e = translate_cn_expr env e_ in
          let acc' =
            fun z -> acc begin
              AT.mConstraint ( LogicalConstraints.T e
                             , (loc_todo, None) ) z
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
    | CN_clause cl_ ->
        let@ cl = translate_cn_clause env cl_ in
        return (RP.{loc= loc_todo; guard= IT.bool_ true; packing_ft= cl} :: acc)
    | CN_if (e_, cl_, clauses') ->
      let@ e  = translate_cn_expr env e_ in
      let@ cl = translate_cn_clause env cl_ in
      self begin
        RP.{loc= loc_todo; guard= e; packing_ft= cl} :: acc
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



let translate (def: cn_predicate) = (*: CF.Symbol.sym * RP.definition = *)
  let open RP in
  let translate_args xs =
    List.map (fun (bTy, sym) ->
      (sym, translate_cn_base_type bTy)
    ) xs in
  let iargs = translate_args def.cn_pred_iargs in
  let oargs = translate_args def.cn_pred_oargs in
  let env =
    List.fold_left (fun acc (sym, bTy) ->
      Env.add_logical sym bTy acc
    ) Env.empty iargs in
  let env' =
    Env.add_predicate def.cn_pred_name
      { pred_iargs= iargs; pred_oargs= oargs } env in
  let@ clauses = translate_cn_clauses env' def.cn_pred_clauses in
  match iargs with
    | (iarg0, BaseTypes.Loc) :: iargs' ->
        return 
          ( Sym.pp_string (* TODO *)def.cn_pred_name
          , { loc= def.cn_pred_loc
            ; pointer= iarg0
            ; iargs= iargs'
            ; oargs= oargs
            ; clauses= clauses
            } )
    | (_, _) :: _ ->
        fail "TODO(msg): error first iarg must be a pointer"
    | [] ->
        fail "TODO(msg): error missing a first iarg"
