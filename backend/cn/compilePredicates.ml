module CF = Cerb_frontend

module BT = BaseTypes
module RP = ResourcePredicates

module IT = IndexTerms

open CF.Cn
open TypeErrors
open Conversions


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

(* type message = *)
(*   | Invalid_oarg_owned of { invalid_ident: Id.t } *)
(*   | Invalid_oarg of { res_name: Sym.t; invalid_ident: Id.t } *)
(*   | Invalid_struct_member of { struct_name: Sym.t; invalid_ident: Id.t } *)
(*   | TypeMismatchBinary of { bTy1: BaseTypes.t; bTy2: BaseTypes.t } *)
(*   | TODO_error of string *)

(* type error = { *)
(*   loc: Locations.t; *)
(*   msg: message *)
(* } *)

(* let pp_message = let open Pp in function *)
(*   | Invalid_oarg_owned { invalid_ident } -> *)
(*       Pp.squotes (Pp.dot ^^ Id.pp invalid_ident) ^^^ !^ "is not an oarg of 'Owned()' (expecting '.value')" *)
(*   | Invalid_oarg { res_name; invalid_ident } -> *)
(*       Pp.squotes (Pp.dot ^^ Id.pp invalid_ident) ^^^ !^ "is not an oarg of" ^^^ *)
(*       Pp.squotes(Sym.pp res_name) *)
(*   | Invalid_struct_member { struct_name; invalid_ident } -> *)
(*       Pp.squotes (Pp.dot ^^ Id.pp invalid_ident) ^^^ !^ "is not a member of" ^^^ *)
(*       Pp.squotes(!^ "struct" ^^^ Sym.pp struct_name) *)
(*   | TypeMismatchBinary { bTy1; bTy2 } -> *)
(*       !^ "type mismatch in a binary operator" ^^^ Pp.parens ( *)
(*         Pp.squotes (BaseTypes.pp bTy1) ^^^ !^ " <-> " ^^^ Pp.squotes (BaseTypes.pp bTy2) *)
(*       ) *)
(*   | TODO_error str -> *)
(*       !^ ("TODO(msg): " ^ str) *)


(* let report_error {loc; msg} = *)
(*   let doc = pp_message msg in *)
(*   Pp.error loc doc [] *)

module Env = CompileEnv
open Env







(* just copy-pasting and adapting Kayvan's older version of this code *)
let translate_member_access loc env t member =
  match IT.bt t with
  | Record members ->
     let member' = Id.s member in
     let members' = List.map (fun (s, bt) -> (todo_string_of_sym s, (s, bt))) members in
     let@ (member, member_bt) = match List.assoc_opt String.equal member' members' with
       | Some (member, member_bt) -> return (member, member_bt)
       | None -> fail {loc; msg = Unknown_record_member (members, member)}
     in
     return (IT.recordMember_ ~member_bt (t, member))
  | Struct tag ->
     let@ members = match lookup_struct tag env with
       | None -> fail {loc; msg= Unknown_struct tag}
       | Some (defs_, _) (* TODO flexible *) -> return defs_
     in
     let@ ty = match List.assoc_opt Id.equal member members with
       | None -> fail {loc; msg = Unknown_member (tag, member)}
       | Some (_, _, ty) -> return ty
     in
     let ty' = Retype.ct_of_ct loc ty in
     let member_bt = BaseTypes.of_sct ty' in
     return ( IT.member_ ~member_bt (tag, t, member) )
  | has -> 
     fail {loc; msg = Illtyped_it' {it = t; has; expected = "struct"}}

let translate_member_accesses loc env t xs = 
  ListM.fold_leftM (translate_member_access loc env) t xs



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
            | None -> fail {loc; msg= Unknown_variable sym}
            | Some bTy -> return (IT (Lit (Sym sym), bTy))
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
         let@ bt = match Env.lookup_resource sym env with
           | None ->
              (* TODO: (could the case where sym is a C struct) is this allowed? *)
              fail {loc; msg= Unknown_variable sym}
           | Some RPred_owned ct ->
              return (Resources.owned_oargs ct)
           | Some RPred_block ct ->
              return (Resources.owned_oargs ct)
           | Some RPred_named s ->
              let@ pred_sig = match Env.lookup_predicate s env with
                | None -> fail {loc; msg = Unknown_resource_predicate {id = s; logical = false}}
                | Some pred_sig -> return pred_sig 
              in
              return (BT.Record pred_sig.pred_oargs)
           | Some RPred_I_owned ct ->
              return (Resources.q_owned_oargs ct)
           | Some RPred_I_block ct ->
              return (Resources.q_owned_oargs ct)
           | Some RPred_I_named s ->
              let@ pred_sig = match Env.lookup_predicate s env with
                | None -> fail {loc; msg = Unknown_resource_predicate {id = s; logical = false}}
                | Some pred_sig -> return pred_sig 
              in
              return (BT.Record (List.map_snd (BT.make_map_bt Integer) pred_sig.pred_oargs))
         in
         let t = sym_ (sym, bt) in
         translate_member_accesses loc env t xs
      | CNExpr_binop (bop, e1_, e2_) ->
          let@ e1 = self e1_ in
          let@ e2 = self e2_ in
          let bt1 = basetype e1 in
          begin match bt1 with
          | Loc -> 
             let err = "pointer addition not allowed in specifications: "^
                         "please instead use pointer/integer casts"
             in
             fail {loc; msg = Generic (Pp.string err)}
          | _ ->
             return (mk_translate_binop bop (basetype e1) (e1, e2))
          end
  in self expr


let at_least_one_argument loc pname = function
  | [] -> 
     (* owned vs block mismatch *)
     fail {loc; msg= First_iarg_missing {pname}}
  | expr :: iargs -> 
     return (expr, iargs)






let translate_cn_clause env clause =
  let rec translate_cn_clause_aux env acc clause =
    let module LAT = LogicalArgumentTypes in
    match clause with
      | CN_letResource (res_loc, sym, res, cl) ->
          let open Resources in
          begin match res with
            | CN_pred (pred_loc, CN_owned ty, args) ->
               let scty = Retype.ct_of_ct res_loc ty in
               let@ args = ListM.mapM (translate_cn_expr env) args in
               let@ expr, iargs = at_least_one_argument pred_loc (Owned scty) args in
               let oargs_ty = owned_oargs scty in
               let acc' =
                 fun z -> acc begin
                   let pt =
                     (ResourceTypes.P { name = Owned scty
                         ; pointer= expr
                         ; permission= IT.bool_ true
                         ; iargs = []},
                      oargs_ty) 
                   in
                   (LAT.mResource ((sym, pt), (pred_loc, None)) z)
                 end in
               let env' = Env.(add_resource sym (RPred_owned scty) env) in
               translate_cn_clause_aux env' acc' cl
            | CN_pred (pred_loc, CN_block ty, args) ->
               let scty = Retype.ct_of_ct pred_loc ty in
               let@ args = ListM.mapM (translate_cn_expr env) args in
               (* owned vs block mismatch *)
               let@ expr, iargs = at_least_one_argument pred_loc (Owned scty) args in
               let acc' =
                 fun z -> acc begin
                   let pt =
                     (ResourceTypes.P { name = Block scty
                         ; pointer= expr
                         ; permission= IT.bool_ true
                         ; iargs = []},
                      owned_oargs scty) 
                   in
                   (LAT.mResource ((sym, pt), (pred_loc, None)) z)
                 end in
               translate_cn_clause_aux env acc' cl
            | CN_pred (pred_loc, CN_named pred_sym, es_) ->
               let@ args = ListM.mapM (translate_cn_expr env) es_ in
               let@ expr, iargs = at_least_one_argument pred_loc (PName pred_sym) args in
               let@ pred_sig = match Env.lookup_predicate pred_sym env with
                 | None -> fail {loc = pred_loc; msg = Unknown_resource_predicate {id = pred_sym; logical = false}}
                 | Some pred_sig -> return pred_sig 
               in
               let acc' =
                 fun z -> acc begin
                   let pred =
                     (ResourceTypes.P { name= PName pred_sym
                         ; pointer= expr
                         ; permission= IT.bool_ true
                         ; iargs= iargs
                     },
                      BT.Record pred_sig.pred_oargs)
                   in
                   (LAT.mResource ((sym, pred), (pred_loc, None)) z)
                 end 
               in
               let env' = Env.(add_resource sym (RPred_named pred_sym) env) in
               translate_cn_clause_aux env' acc' cl
            | CN_each _ ->
                failwith "TODO: CN_each"
          end
      | CN_letExpr (loc, sym, e_, cl) ->
          let@ e = translate_cn_expr env e_ in
          let acc' =
            fun z -> acc begin
              LAT.mDefine (sym, e, (loc, None)) z
            end in
            translate_cn_clause_aux (Env.add_logical sym (IT.basetype e) env) acc' cl
      | CN_assert (loc, e_, cl) ->
          let@ e = translate_cn_expr env e_ in
          let acc' =
            fun z -> acc begin
              LAT.mConstraint ( LogicalConstraints.T e
                             , (loc, None) ) z
            end in
            translate_cn_clause_aux env acc' cl
      | CN_return (loc, xs_) ->
          let@ xs =
            ListM.mapM (fun (sym, e_) ->
              let@ e = translate_cn_expr env e_ in
              return (OutputDef.{loc= loc; name= sym; value= e})
            ) xs_ in
          acc (LAT.I xs) in
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



let register_cn_predicates env tagDefs (defs: cn_predicate list) =
  let aux env def =
    let translate_args xs =
      List.map (fun (bTy, sym) ->
        (sym, translate_cn_base_type bTy)
      ) xs in
    let iargs = translate_args def.cn_pred_iargs in
    let oargs = translate_args def.cn_pred_oargs in
    Env.add_predicate def.cn_pred_name { pred_iargs= iargs; pred_oargs= oargs } env in
  List.fold_left aux env defs




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
  let def2 = {loc = def.cn_func_loc; args; return_bt; definition} in
  return (env', (def.cn_func_name, def2))

let translate_and_register_cn_functions (env : Env.t) (to_translate: cn_function list) = 
  let@ (env, defs) = 
    ListM.fold_leftM (fun (env, defs) def ->
        let@ (env, def) = translate_and_register_cn_function env def in
        return (env, def :: defs)
      ) (env,[]) to_translate
  in
  return (env, List.rev defs)


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
          ( def.cn_pred_name
          , { loc= def.cn_pred_loc
            ; pointer= iarg0
            ; iargs= iargs'
            ; oargs= oargs
            ; clauses= clauses
            } )
    | (_, found_bty) :: _ ->
        fail { loc= def.cn_pred_loc; msg= First_iarg_not_pointer { pname= PName def.cn_pred_name; found_bty } }
    | [] ->
        fail { loc= def.cn_pred_loc; msg= First_iarg_missing { pname= PName def.cn_pred_name} }

let translate tagDefs (f_defs: cn_function list) (pred_defs: cn_predicate list) =
  let env = Env.empty tagDefs in
  let@ (env, log_defs) = translate_and_register_cn_functions env f_defs in
  let env = register_cn_predicates env tagDefs pred_defs in
  let@ pred_defs = ListM.mapM (translate_cn_predicate env) pred_defs in
  return (log_defs, pred_defs)

