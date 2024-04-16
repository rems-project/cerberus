module CF = Cerb_frontend
module SBT = SurfaceBaseTypes
module BT = BaseTypes
module RP = ResourcePredicates
module IT = IndexTerms
module LAT = LogicalArgumentTypes
module LRT = LogicalReturnTypes
module LC = LogicalConstraints
module RET = ResourceTypes
module Mu = Mucore
module RT = ReturnTypes


open Pp

open CF.Cn
open TypeErrors

module SymSet = Set.Make(Sym)
module SymMap = Map.Make(Sym)
module STermMap = Map.Make(struct type t = IndexTerms.sterm let compare = Terms.compare SBT.compare end)
module StringMap = Map.Make(String)

module StringSet = Set.Make(String)


type function_sig = {
    args: (Sym.t * BaseTypes.t) list;
    return_bty: BaseTypes.t;
  }



type predicate_sig = {
  pred_iargs: (Sym.t * BaseTypes.t) list;
  pred_output: BaseTypes.t;
}


type env = {
  computationals: (SBT.t * Sym.t option) SymMap.t;
  logicals: SBT.t SymMap.t;
  predicates: predicate_sig SymMap.t;
  functions: function_sig SymMap.t;
  datatypes : BaseTypes.datatype_info SymMap.t;
  datatype_constrs : BaseTypes.constr_info SymMap.t;
  tagDefs: Mu.mu_tag_definitions;
  fetch_enum_expr: Locations.t -> Sym.t -> (unit CF.AilSyntax.expression) Resultat.t;
  fetch_typedef: Locations.t -> Sym.t -> CF.Ctype.ctype Resultat.t;
}

let init_env tagDefs fetch_enum_expr fetch_typedef =
  { computationals = SymMap.empty;
    logicals= SymMap.empty;
    predicates= SymMap.empty;
    functions = SymMap.empty;
    datatypes = SymMap.empty;
    datatype_constrs = SymMap.empty;
    tagDefs;
    fetch_enum_expr;
    fetch_typedef;
  }


let pointer_eq_warned = ref false


(* TODO: ugly hack to get started *)
module SymTable = Hashtbl.Make(Sym)
let symtable = SymTable.create 10000

let add_computational sym bTy env =
  SymTable.add symtable sym bTy;
  {env with computationals= SymMap.add sym (bTy, None) env.computationals }

let add_renamed_computational sym sym2 bTy env =
  SymTable.add symtable sym bTy;
  {env with computationals= SymMap.add sym (bTy, Some sym2) env.computationals }

let add_logical sym bTy env =
  SymTable.add symtable sym bTy;
  {env with logicals= SymMap.add sym bTy env.logicals }

let add_predicate sym pred_sig env =
  {env with predicates= SymMap.add sym pred_sig env.predicates }


let lookup_computational_or_logical sym env =
  match SymMap.find_opt sym env.logicals with
  | Some bt -> Some (bt, None)
  | None ->
     SymMap.find_opt sym env.computationals


let lookup_predicate sym env =
  SymMap.find_opt sym env.predicates

let lookup_function sym env =
  SymMap.find_opt sym env.functions



let lookup_struct_opt sym env =
  match Pmap.lookup sym env.tagDefs with
    | Some (M_StructDef xs) ->
        Some xs
    | Some (M_UnionDef _)| None ->
        None


let add_datatype sym info env =
  let datatypes = SymMap.add sym info env.datatypes in
  {env with datatypes}



let add_datatype_constr sym info env =
  let datatype_constrs = SymMap.add sym info env.datatype_constrs in
  {env with datatype_constrs}

let get_datatype_maps env =
  (SymMap.bindings env.datatypes,
   SymMap.bindings env.datatype_constrs)





type cn_predicate =
  (CF.Symbol.sym, CF.Ctype.ctype) CF.Cn.cn_predicate

type cn_function =
  (CF.Symbol.sym, CF.Ctype.ctype) CF.Cn.cn_function

type cn_lemma =
  (CF.Symbol.sym, CF.Ctype.ctype) CF.Cn.cn_lemma

type cn_datatype =
  (CF.Symbol.sym) CF.Cn.cn_datatype


(* let pp_cnexpr_kind expr_ = *)
(*   let open Pp in *)
(*   match expr_ with *)
(*   | CNExpr_const CNConst_NULL -> !^ "NULL" *)
(*   | CNExpr_const (CNConst_integer n) -> Pp.string (Z.to_string n) *)
(*   | CNExpr_const (CNConst_bits ((sign,n),v)) -> *)
(*     Pp.string (Z.to_string v ^ (match sign with CN_unsigned -> "u" | CN_signed -> "i") ^ string_of_int n) *)
(*   | CNExpr_const (CNConst_bool b) -> !^ (if b then "true" else "false") *)
(*   | CNExpr_const CNConst_unit -> !^"void" *)
(*   | CNExpr_var sym -> parens (typ (!^ "var") (Sym.pp sym)) *)
(*   | CNExpr_deref e -> !^ "(deref ...)" *)
(*   | CNExpr_value_of_c_atom (sym, kind) -> parens (typ *)
(*         (CF.Cn_ocaml.PpAil.pp_cn_c_kind kind) (Sym.pp sym)) *)
(*   | CNExpr_list es_ -> !^ "[...]" *)
(*   | CNExpr_memberof (e, xs) -> !^ "_." ^^ Id.pp xs *)
(*   | CNExpr_record members -> !^"{ ... }" *)
(*   | CNExpr_memberupdates (e, _updates) -> !^ "{_ with ...}" *)
(*   | CNExpr_arrayindexupdates (e, _updates) -> !^ "_ [ _ = _ ...]" *)
(*   | CNExpr_binop (bop, x, y) -> !^ "(binop (_, _, _))" *)
(*   | CNExpr_sizeof ct -> !^ "(sizeof _)" *)
(*   | CNExpr_offsetof (tag, member) -> !^ "(offsetof (_, _))" *)
(*   | CNExpr_array_shift (e1, ct, e2) -> !^"(array_shift<_>(_, _)" *)
(*   | CNExpr_membershift (e1, opt_tag, member) -> !^ "&(_ -> _)" *)
(*   | CNExpr_addr nm -> !^ "&_" *)
(*   | CNExpr_cast (bt, expr) -> !^ "(cast (_, _))" *)
(*   | CNExpr_call (sym, exprs) -> !^ "(" ^^ Sym.pp sym ^^^ !^ "(...))" *)
(*   | CNExpr_cons (c_nm, exprs) -> !^ "(" ^^ Sym.pp c_nm ^^^ !^ "{...})" *)
(*   | CNExpr_each (sym, bt, r, e) -> !^ "(each ...)" *)
(*   | CNExpr_match (x, ms) -> !^ "match ... {...}" *)
(*   | CNExpr_let (s, e, body) -> !^ "let ...; ..." *)
(*   | CNExpr_ite (e1, e2, e3) -> !^ "(if ... then ...)" *)
(*   | CNExpr_good (ty, e) -> !^ "(good (_, _))" *)
(*   | CNExpr_unchanged e -> !^"(unchanged (_))" *)
(*   | CNExpr_at_env (e, es) -> !^"{_}@_" *)
(*   | CNExpr_not e -> !^"!_" *)
(*   | CNExpr_default bt -> !^"default" *)


let rec symset_bigunion = function
  | [] -> SymSet.empty
  | syms::symses -> SymSet.union syms (symset_bigunion symses)


let rec bound_by_pattern (CNPat (_loc, pat_)) =
  match pat_ with
  | CNPat_sym s -> SymSet.singleton s
  | CNPat_wild -> SymSet.empty
  | CNPat_constructor (_, args) ->
     symset_bigunion (List.map (fun (_,p) -> bound_by_pattern p) args)

let rec free_in_expr (CNExpr (_loc, expr_)) =
  match expr_ with
  | CNExpr_const _ ->
     SymSet.empty
  | CNExpr_var v ->
     SymSet.singleton v
  | CNExpr_list es ->
     free_in_exprs es
  | CNExpr_memberof (e, _id) ->
     free_in_expr e
  | CNExpr_record members ->
     free_in_exprs (List.map snd members)
  | CNExpr_memberupdates (e, updates) ->
     free_in_exprs (e :: List.map snd updates)
  | CNExpr_arrayindexupdates (e, updates) ->
     free_in_exprs (e :: List.concat_map (fun (e1, e2) -> [e1; e2]) updates)
  | CNExpr_binop (_binop, e1, e2) ->
     free_in_exprs [e1; e2]
  | CNExpr_sizeof _ ->
     SymSet.empty
  | CNExpr_offsetof _ ->
     SymSet.empty
  | CNExpr_array_shift (e1, _ct, e2) ->
     free_in_exprs [e1; e2]
  | CNExpr_membershift (e, _opt_tag, _id) ->
     free_in_expr e
  | CNExpr_addr _ ->
     SymSet.empty
  | CNExpr_cast (_bt, e) ->
     free_in_expr e
  | CNExpr_call (_id, es) ->
     free_in_exprs es
  | CNExpr_cons (_c, args) ->
     free_in_exprs (List.map snd args)
  | CNExpr_each (s, bt, range, e) ->
     SymSet.remove s (free_in_expr e)
  | CNExpr_match (x, ms) ->
     let free_per_case =
       List.map (fun (pat, body) ->
           SymSet.diff (free_in_expr body) (bound_by_pattern pat)
         ) ms
     in
     SymSet.union (free_in_expr x) (symset_bigunion free_per_case)
  | CNExpr_let (s, e, body) ->
     SymSet.union (free_in_expr e)
      (SymSet.remove s (free_in_expr body))
  | CNExpr_ite (e1, e2, e3) ->
     free_in_exprs [e1; e2; e3]
  | CNExpr_good (typ, e) ->
     free_in_expr e
  | CNExpr_deref e ->
     free_in_expr e
  | CNExpr_value_of_c_atom (s, _) ->
     SymSet.singleton s
  | CNExpr_unchanged e ->
     free_in_expr e
  | CNExpr_at_env (e, _evaluation_scope) ->
     free_in_expr e
  | CNExpr_not e ->
     free_in_expr e
  | CNExpr_default _bt ->
     SymSet.empty
     

and free_in_exprs = function
  | [] -> SymSet.empty
  | e :: es -> SymSet.union (free_in_expr e) (free_in_exprs es)


let rec translate_cn_base_type env (bTy: CF.Symbol.sym cn_base_type) =
  let open SurfaceBaseTypes in
  let self bTy = translate_cn_base_type env bTy in
  match bTy with
    | CN_unit ->
        Unit
    | CN_bool ->
        Bool
    | CN_integer ->
        Integer
    | CN_bits (CN_unsigned, n) ->
        Bits (Unsigned, n)
    | CN_bits (CN_signed, n) ->
        Bits (Signed, n)
    | CN_real ->
        Real
    | CN_loc ->
        Loc None
    | CN_alloc_id ->
        Alloc_id
    | CN_struct tag_sym ->
        Struct tag_sym
    | CN_record members ->
        SBT.Record (List.map (fun (m,bt) -> (m, self bt)) members)
    | CN_datatype dt_sym ->
        Datatype dt_sym
    | CN_map (bTy1, bTy2) ->
        Map ( self bTy1, self bTy2 )
    | CN_list bTy' ->
        List (self bTy')
    | CN_tuple bTys ->
        Tuple (List.map self bTys)
    | CN_set bTy' ->
        Set (self bTy')
    | CN_user_type_name _ ->
        failwith "user type-abbreviation not removed by cabs->ail elaboration"
    | CN_c_typedef_name sym ->
        (* FIXME handle errors here properly *)
        let loc = Locations.unknown in
        match env.fetch_typedef loc sym with
          | Result.Ok r -> Memory.sbt_of_sct (Sctypes.of_ctype_unsafe loc r)
          | Result.Error e -> failwith (Pp.plain (TypeErrors.((pp_message e.msg).short)))


let register_cn_predicates env (defs: cn_predicate list) =
  let aux env def =
    let translate_args xs =
      List.map (fun (id_or_sym, bTy) ->
        (id_or_sym, SBT.to_basetype (translate_cn_base_type env bTy))
      ) xs in
    let iargs = translate_args def.cn_pred_iargs in
    let output =
      (SBT.to_basetype (translate_cn_base_type env (snd def.cn_pred_output)))
    in
    add_predicate def.cn_pred_name {
        pred_iargs= iargs;
        pred_output= output
      } env
  in
  List.fold_left aux env defs


open Resultat
open Effectful.Make(Resultat)


(* TODO: handle more kinds of constant expression *)
let convert_enum_expr =
  let open CF.AilSyntax in
  let conv_const loc = function
    | ConstantInteger (IConstant (z, _, _)) ->
      let@ bt = match BT.pick_integer_encoding_type z with
      | Some bt -> return bt
      | None -> fail {loc; msg = Generic (Pp.item "no standard encoding type for constant"
            (Pp.z z))}
      in
      return (IT.sterm_of_term (IT.num_lit_ z bt loc))
    | c -> fail {loc; msg = Generic (Pp.item "enum conversion: unhandled constant"
        (CF.Pp_ail_ast.pp_constant c))}
  in
  let rec conv_expr_ e1 loc = function
    | AilEconst const -> conv_const loc const
    | AilEannot (cty, expr) -> conv_expr expr
    | _ -> fail {loc; msg = Generic (Pp.item "enum conversion: unhandled expression kind"
        (CF.Pp_ast.doc_tree_toplevel (CF.Pp_ail_ast.dtree_of_expression (fun _ -> (!^ "()")) e1)))}
  and conv_expr e = match e with
    | AnnotatedExpression (_, _, loc, expr) -> conv_expr_ e loc expr
  in
  conv_expr

let do_decode_enum env loc sym =
  let@ expr = env.fetch_enum_expr loc sym in
  convert_enum_expr expr



let add_function loc sym func_sig env =
  return {env with functions= SymMap.add sym func_sig env.functions }


let register_cn_functions env (defs: cn_function list) =
  let aux env def =
    let args =
      List.map (fun (sym, bTy) ->
          (sym, SBT.to_basetype (translate_cn_base_type env bTy))
      ) def.cn_func_args
    in
    let return_bt =
      SBT.to_basetype (translate_cn_base_type env def.cn_func_return_bty)
    in
    let fsig = {args; return_bty = return_bt} in
    add_function def.cn_func_loc def.cn_func_name fsig env
  in
  ListM.fold_leftM aux env defs


let add_datatype_info env (dt : cn_datatype) =
  Pp.debug 2 (lazy (Pp.item "translating datatype declaration" (Sym.pp dt.cn_dt_name)));
  (* This seems to require that variables aren't simply unique to the
    constructor, but to the entire datatype declaration.  
    This is weird, and is probably an arbitrary restriction that should be
    lifted, but it will require effort. *)
  let add_param m (nm, ty) =
    match StringMap.find_opt (Id.s nm) m with
    | None ->
      return (StringMap.add (Id.s nm) (nm, SBT.to_basetype (translate_cn_base_type env ty)) m)
    | Some _ ->
        fail {loc = Id.loc nm;
              msg = Generic (!^"Re-using member name" ^^^ Id.pp nm
                             ^^^ !^"within datatype definition.")}
  in
  let@ all_params = ListM.fold_leftM add_param StringMap.empty
    (List.concat_map snd dt.cn_dt_cases) in
  let add_constr env (cname, params) =
    let c_params =
      List.map (fun (nm, ty) ->
        (nm, SBT.to_basetype (translate_cn_base_type env ty))
        ) params
    in
    let info = BT.{c_params; c_datatype_tag = dt.cn_dt_name} in
    add_datatype_constr cname info env
  in
  let env = List.fold_left add_constr env dt.cn_dt_cases in
  let dt_all_params = List.map snd (StringMap.bindings all_params) in
  let dt_constrs = List.map fst dt.cn_dt_cases in
  return (add_datatype dt.cn_dt_name
    BT.{dt_constrs; dt_all_params} env)

let add_datatype_infos env dts =
  ListM.fold_leftM add_datatype_info env dts


module E = struct

  type evaluation_scope = string

  type ('a) m =
    | Done of 'a
    | Error of TypeErrors.t
    | ScopeExists of Loc.t * evaluation_scope * (bool -> 'a m)
    | Value_of_c_variable of Loc.t * Sym.t * evaluation_scope option * (IT.sterm option -> ('a) m)
    | Deref of Loc.t * IT.sterm * evaluation_scope option * (IT.sterm option -> ('a) m)

  let return x = Done x

  let rec bind (m : ('a) m) (f : 'a -> ('b) m) : ('b) m =
    match m with
    | Done x ->
       f x
    | Error err ->
       Error err
    | ScopeExists (loc, scope, k) ->
       ScopeExists (loc, scope, fun b -> bind (k b) f)
    | Value_of_c_variable (loc, s, scope, k) ->
       Value_of_c_variable (loc, s, scope, fun it_o -> bind (k it_o) f)
    | Deref (loc, it, scope, k) ->
       Deref (loc, it, scope, fun it_o -> bind (k it_o) f)

  let fail e =
    Error e

  let scope_exists loc scope =
    ScopeExists (loc, scope, fun b -> Done b)

  let deref loc it scope =
    Deref (loc, it, scope, fun o_v_it -> Done o_v_it)

  let value_of_c_variable loc sym scope =
    Value_of_c_variable (loc, sym, scope, fun o_v_it -> Done o_v_it)

  let liftResultat = function
    | Result.Ok a -> Done a
    | Result.Error e -> Error e

end

let start_evaluation_scope = "start"


module EffectfulTranslation = struct

  open Effectful.Make(E)
  open E





  let pp_in_scope = function
    | Some scope -> !^"in evaluation scope" ^^^ squotes !^scope
    | None -> !^"in current scope"




  let lookup_struct loc tag env =
    match lookup_struct_opt tag env with
    | Some def -> return def
    | None -> fail {loc; msg = Unknown_struct tag}



  let lookup_member loc (tag, def) member =
    let member_types = Memory.member_types def in
    match List.assoc_opt Id.equal member member_types with
    | Some ty -> return ty
    | None -> fail {loc; msg = Unexpected_member (List.map fst member_types, member)}

  let lookup_datatype loc sym env = match SymMap.find_opt sym env.datatypes with
    | Some info -> return info
    | None -> fail (TypeErrors.{loc; msg = TypeErrors.Unknown_datatype sym})

  let lookup_constr loc sym env = match SymMap.find_opt sym env.datatype_constrs with
    | Some info -> return info
    | None -> fail (TypeErrors.{loc; msg = TypeErrors.Unknown_datatype_constr sym})

  let cannot_tell_pointee_ctype loc e =
    let msg =
      !^"Cannot tell pointee C-type of"
      ^^^ squotes (IT.pp e) ^^ dot
    in
    fail {loc; msg = Generic msg}

  let mk_translate_binop loc' bop (e1, e2) =
    let open IndexTerms in
    let loc = loc' in
    match bop, IT.bt e1 with
    | CN_add, (SBT.Integer | SBT.Real | SBT.Bits _) ->
        return (IT (Binop (Add, e1, e2), IT.bt e1, loc))
    | CN_add, (SBT.Loc oct) ->
       begin match oct with
       | Some ct ->
          let (IT (it_, _, _)) =
            sterm_of_term (arrayShift_ ~base:(term_of_sterm e1) ct ~index:(term_of_sterm e2) loc) in
          return (IT (it_, Loc oct, loc))
       | None ->
          cannot_tell_pointee_ctype loc e1
       end
    | CN_sub, (SBT.Integer | SBT.Real | SBT.Bits _ ) ->
        return (IT (Binop (Sub, e1, e2), IT.bt e1, loc))
    | CN_sub, (SBT.Loc oct) ->
       begin match oct with
       | Some ct ->
          let here = Locations.other __FUNCTION__ in
          let (IT (it_, _, _)) =
            sterm_of_term (arrayShift_ ~base:(term_of_sterm e1) ct ~index:(sub_ (int_ 0 here, term_of_sterm e2) here) loc) in
          return (IT (it_, Loc oct, loc))
       | None ->
          cannot_tell_pointee_ctype loc e1
       end
    | CN_mul, _ ->
        return (IT (Binop (Mul, e1, e2), IT.bt e1, loc))
    | CN_div, _ ->
        return (IT (Binop (Div, e1, e2), IT.bt e1, loc))
    | CN_equal, _ ->
      (match IT.bt e1, IT.bt e2, !pointer_eq_warned with
       | Loc _, Loc _, false ->
         pointer_eq_warned := true;
         Pp.warn loc !^"CN pointer equality is not the same as C's (will not warn again)"
       | _, _, _ -> ());
        return (IT (Binop (EQ, e1, e2), SBT.Bool, loc))
    | CN_inequal, _ ->
      (match IT.bt e1, IT.bt e2, !pointer_eq_warned with
       | Loc _, Loc _, false ->
         pointer_eq_warned := true;
         Pp.warn loc !^"CN pointer equality is not the same as C's (will not warn again)"
       | _, _, _ -> ());
        return (not_ (IT (Binop (EQ, e1, e2), SBT.Bool, loc)) loc)
    | CN_lt, (SBT.Integer | SBT.Real | SBT.Bits _) ->
        return (IT (Binop (LT, e1, e2), SBT.Bool, loc))
    | CN_lt, SBT.Loc _ ->
        return (IT (Binop (LTPointer, e1, e2), SBT.Bool, loc))
    | CN_le, (SBT.Integer | SBT.Real | SBT.Bits _) ->
        return (IT (Binop (LE, e1, e2), SBT.Bool, loc))
    | CN_le, SBT.Loc _ ->
        return (IT (Binop (LEPointer, e1, e2), SBT.Bool, loc))
    | CN_gt, (SBT.Integer | SBT.Real | SBT.Bits _) ->
        return (IT (Binop (LT, e2, e1), SBT.Bool, loc))
    | CN_gt, SBT.Loc _ ->
        return (IT (Binop (LTPointer, e2, e1), SBT.Bool, loc))
    | CN_ge, (SBT.Integer | SBT.Real | SBT.Bits _) ->
        return (IT (Binop (LE, e2, e1), SBT.Bool, loc))
    | CN_ge, SBT.Loc _ ->
        return (IT (Binop (LEPointer, e2, e1), SBT.Bool, loc))
    | CN_or, SBT.Bool ->
        return (IT (Binop (Or, e1, e2), SBT.Bool, loc))
    | CN_and, SBT.Bool ->
        return (IT (Binop (And, e1, e2), SBT.Bool, loc))
    | CN_map_get, _ ->
       let@ rbt = match IT.bt e1 with
         | Map (_, rbt) -> return rbt
         | has ->
            let expected = "map/array" in
            let reason = "map/array index" in
            fail {loc; msg = Illtyped_it {it = Terms.pp e1; has = SBT.pp has; expected; reason; o_ctxt = None}}
       in
       return (IT ((MapGet (e1, e2)), rbt, loc))
    | _ ->
        let open Pp in
        let msg =
          !^"Ill-typed application of binary operation"
          ^^^ squotes (CF.Cn_ocaml.PpAil.pp_cn_binop bop) ^^^ dot
          ^/^ !^"Left-hand-side:" ^^^ squotes (IT.pp e1) ^^^ !^"of type" ^^^ squotes (SBT.pp (IT.bt e1)) ^^ comma
          ^/^ !^"right-hand-side:" ^^^ squotes (IT.pp e2) ^^^ !^"of type" ^^^ squotes (SBT.pp (IT.bt e2)) ^^ dot
        in
        fail {loc; msg = Generic msg}


  (* just copy-pasting and adapting Kayvan's older version of this code *)
  let translate_member_access loc env (t : IT.sterm) member =
    match IT.bt t with
    | SBT.Record members ->
       let@ member_bt = match List.assoc_opt Id.equal member members with
         | Some member_bt -> return member_bt
         | None -> fail {loc; msg = Unexpected_member (List.map fst members, member)}
       in
       return (IT.recordMember_ ~member_bt (t, member) loc)
    | Struct tag ->
       let@ defs_ = lookup_struct loc tag env in
       let@ ty = lookup_member loc (tag, defs_) member in
       let member_bt = Memory.sbt_of_sct ty in
       return ( IT.IT ((StructMember (t, member)), member_bt, loc))
    (* | Datatype tag -> *)
    (*    let@ dt_info = lookup_datatype loc tag env in *)
    (*    let@ bt = match List.assoc_opt Id.equal member dt_info.dt_all_params with *)
    (*      | None ->  *)
    (*          let msg = !^"Unknown member" ^^^ squotes (Id.pp member) *)
    (*                    ^^^ !^"of datatype" ^^^ squotes (Sym.pp tag) *)
    (*          in *)
    (*          fail {loc; msg = Generic msg} *)
    (*      | Some bt -> return (SurfaceBaseTypes.of_basetype bt) *)
    (*    in *)
    (*    return (IT.IT ((IT.DatatypeMember (t, member)), bt)) *)
    | has ->
       let expected = "struct" in
       let reason = "struct member access" in
       fail {loc; msg = Illtyped_it {it = Terms.pp t; has = SurfaceBaseTypes.pp has; expected; reason; o_ctxt = None}}








  let rec translate_cn_pat env locally_bound (CNPat (loc, pat_), bt) =
    match pat_ with
    | CNPat_wild ->
       return (env, locally_bound, IT.Pat (PWild, bt, loc))
    | CNPat_sym s ->
       let env' = add_logical s bt env in
       let locally_bound' = SymSet.add s locally_bound in
       return (env', locally_bound', IT.Pat (PSym s, bt, loc))
    | CNPat_constructor (cons, args) ->
       let@ cons_info = lookup_constr loc cons env in
       let@ env', locally_bound', args =
         ListM.fold_leftM (fun (env, locally_bound, acc) (m, pat') ->
             match List.assoc_opt Id.equal m cons_info.c_params with
             | None ->
                fail {loc; msg= Unexpected_member (List.map fst cons_info.c_params,m)}
             | Some mbt ->
                let@ env', locally_bound', pat' =
                  translate_cn_pat env locally_bound (pat', SBT.of_basetype mbt) in
                return (env', locally_bound', acc @ [(m, pat')])
           ) (env, locally_bound, []) args
       in
       return (env', locally_bound', IT.Pat (PConstructor (cons, args), bt, loc))


  let check_quantified_base_type env loc bt =
    let bt = translate_cn_base_type env bt in
    if SBT.equal bt SBT.Integer then return bt
    else if Option.is_some (SBT.is_bits_bt bt) then return bt
    else fail {loc; msg = let open Pp in
        Generic (!^ "quantified v must be integer or bitvector:" ^^^ SBT.pp bt)}


  let translate_cn_expr =
    let open IndexTerms in
    let module BT = BaseTypes in
    let rec trans (evaluation_scope : string option) locally_bound env (CNExpr (loc, expr_)) =
      let self = trans evaluation_scope locally_bound env in
      match expr_ with
        | CNExpr_const CNConst_NULL ->
            return (IT (Const Null, SBT.Loc None, loc))
        | CNExpr_const (CNConst_integer n) ->
            return (IT (Const (Z n), SBT.Integer, loc))
        | CNExpr_const (CNConst_bits ((sign,n),v)) ->
            let sign = match sign with
              | CN_unsigned -> BT.Unsigned
              | CN_signed -> BT.Signed
            in
            return (IT (Const (Bits ((sign,n), v)), SBT.Bits (sign,n), loc))
        | CNExpr_const (CNConst_bool b) ->
            return (IT (Const (Bool b), SBT.Bool, loc))
        | CNExpr_const CNConst_unit ->
            return (IT (Const Unit, SBT.Unit, loc))
        | CNExpr_var sym ->
            let@ (sym, bTy) = match lookup_computational_or_logical sym env with
              | None ->
                 Pp.debug 2 (lazy (Pp.item ("failed lookup of CNExpr_var " ^ Sym.pp_string sym)
                                     (Pp.list (fun (nm, _) -> Sym.pp nm) (SymMap.bindings env.computationals))));
                 fail {loc; msg= Unknown_variable sym}
              | Some (bt, None) ->
                 return (sym, bt)
              | Some (bt, Some renamed_sym) ->
                 return (renamed_sym, bt)
            in
            return (IT ((Sym sym), bTy, loc))
        | CNExpr_list es ->
            let@ es = ListM.mapM self es in
            let item_bt = basetype (List.hd es) in
            let  (_, nil_pos, _) =
              (* parser should ensure loc is a region *)
              Option.get @@ Locations.get_region loc in
            let cons hd tl =
              let hd_pos = Option.get @@ Locations.start_pos @@ IT.loc hd in
              let loc = Locations.(region (hd_pos, nil_pos) NoCursor) in
               IT (Cons (hd, tl), SBT.List item_bt, loc) in
            let nil =
              let nil_loc = Cerb_location.point nil_pos in
              IT (Nil (SBT.to_basetype item_bt), SBT.List item_bt, nil_loc) in
            return (List.fold_right cons es nil)
        | CNExpr_memberof (e, xs) ->
           let@ e = self e in
           translate_member_access loc env e xs
        | CNExpr_record members ->
           let@ members = ListM.mapsndM self members in
           let bts = List.map_snd IT.bt members in
           return (IT (IT.Record members, SBT.Record bts, loc))
        | CNExpr_memberupdates (e, updates) ->
           let@ e = self e in
           let bt = IT.bt e in
           let end_pos = Option.get @@ Locations.end_pos loc in
           begin match IT.bt e with
           | Struct _ ->
              let@ expr =
                ListM.fold_rightM (fun (id, v) expr ->
                   let@ v = self v in
                   let start_pos = Option.get @@ Locations.start_pos @@ Id.loc id in
                   let cursor = Cerb_location.PointCursor start_pos in
                   let loc = Locations.region (start_pos, end_pos) cursor in
                   return (IT ((StructUpdate ((expr, id), v)), bt, loc))
                ) updates e
              in
              return expr
           | _ ->
              fail {
                loc = IT.loc e;
                msg = Illtyped_it {
                    it = Terms.pp e;
                    has = SBT.pp bt;
                    expected = "struct";
                    reason = (let (head, pos) = Locations.head_pos_of_location loc in head ^ "\n" ^ pos);
                    o_ctxt = None
                  }
              }
           end
        | CNExpr_arrayindexupdates (e, updates) ->
           let@ e = self e in
           let bt = IT.bt e in
           (* start_pos points to start_pos of e
              ignored cursor points to '['
              end_pos points to ']' *)
           let (start_pos, end_pos, _) =
             (* parser should ensure loc is a region *)
             Option.get @@ Locations.get_region loc in
           let@ IT (e, bt, loc) =
             ListM.fold_leftM (fun acc (i, v) ->
                 let@ i = self i in
                 let@ v = self v in
                 let end_pos = Option.get @@ Locations.end_pos @@ IT.loc v in
                 (* cursor for the first update doesn't point to '[' - oh well *)
                 let cursor = Cerb_location.PointCursor (Option.get @@ Locations.start_pos @@ IT.loc i) in
                 return (IT ((MapSet (acc, i, v)), bt, Cerb_location.region (start_pos, end_pos) cursor))
               ) e updates in
           (* cursor points to start of last index
              ignored start_pos is just start_pos as above
              ignored end_pos points to the end last value
              we want to restore it to point to ']' *)
            let (_, _, cursor) = Option.get @@ Locations.get_region loc in
            return (IT (e, bt, Locations.region (start_pos, end_pos) cursor))
        | CNExpr_binop (bop, e1_, e2_) ->
            let@ e1 = self e1_ in
            let@ e2 = self e2_ in
            mk_translate_binop loc bop (e1, e2)
        | CNExpr_sizeof ct ->
            let scty = Sctypes.of_ctype_unsafe loc ct in
            return (IT (SizeOf scty, Memory.size_sbt, loc))
        | CNExpr_offsetof (tag, member) ->
            let@ _ = lookup_struct loc tag env in
            return (IT ((OffsetOf (tag, member)), Memory.sint_sbt, loc))
        | CNExpr_array_shift (base, ty_annot, index) ->
           let@ base = self base in
           let@ ct = match ty_annot, IT.bt base with
           | Some ty, _ ->
             (* this does not check whether the annotation and pointer type agree
                and just defers to what the user wrote, because pointer
                arithmetic can happen at any size/type *)
             return (Sctypes.of_ctype_unsafe loc ty)
           | None, Loc (Some bt) -> return bt
           | _ -> fail {loc; msg = Generic
               (!^ "type of array not specified (e.g. array_shift<int>) or known from pointer")}
           in
           begin match IT.bt base with
           | Loc _ ->
              let@ index = self index in
              begin match IT.bt index with
              | Integer | Bits _ ->
                return (IT (ArrayShift { base; ct; index }, Loc (Some ct), loc))
              | has ->
                 let expected = "integer or bits" in
                 let reason = "pointer arithmetic" in
                 fail {loc; msg = Illtyped_it {it = Terms.pp index; has = SBT.pp has; expected; reason; o_ctxt = None}}
              end
           | has ->
             let expected = "pointer" in
             let reason = "pointer arithmetic" in
             fail {loc; msg = Illtyped_it {it = Terms.pp base; has = SBT.pp has; expected; reason; o_ctxt = None}}
           end
        | CNExpr_membershift (e, opt_tag, member) ->
           let@ e = self e in
           let with_tag tag =
              let@ struct_def = lookup_struct loc tag env in
              let@ member_ty = lookup_member loc (tag, struct_def) member in
              let (IT (it_, _, _)) = IT.sterm_of_term (memberShift_ (term_of_sterm e, tag, member) loc) in
              (* sterm_of_term will not have produced a C-type-annotated bt. So stick that on now. *)
              return (IT (it_, Loc (Some member_ty), loc))
           in
           begin match opt_tag, IT.bt e with
           | Some tag, Loc (Some (Struct tag')) ->
             if Sym.equal tag tag' then
               with_tag tag
             else
               let expected = Pp.plain @@ SBT.pp (Struct tag) in
               let reason = "struct member offset" in
               fail {loc; msg = Illtyped_it {it = Terms.pp e; has = SBT.pp (Struct tag'); expected; reason; o_ctxt = None}}
           | Some tag, Loc None
           | None, Loc (Some (Struct tag)) ->
              with_tag tag
           | None, Loc None ->
              cannot_tell_pointee_ctype loc e
           | _ , has ->
              let expected = "struct pointer" in
              let reason = "struct member offset" in
              fail {loc; msg = Illtyped_it {it = Terms.pp e; has = SBT.pp has; expected; reason; o_ctxt = None}}
           end
        | CNExpr_addr nm ->
            return (sym_ (nm, SBT.Loc None, loc))
        | CNExpr_cast (bt, expr) ->
            let@ expr = self expr in
            let bt = translate_cn_base_type env bt in
            return (IT (Cast (SBT.to_basetype bt, expr), bt, loc))
        | CNExpr_call (fsym, exprs) ->
            let@ args = ListM.mapM self exprs in
            let@ b = liftResultat (Builtins.apply_builtin_funs fsym args loc) in
            begin match b with
              | Some t -> return t
              | None ->
                let@ bt = match lookup_function fsym env with
                  | Some fsig -> return fsig.return_bty
                  | None ->
                      fail {loc; msg = Unknown_logical_function
                          {id = fsym; resource = false}}
                in
                return (pred_ fsym args (SurfaceBaseTypes.of_basetype bt) loc)
            end
        | CNExpr_cons (c_nm, exprs) ->
            let@ cons_info = lookup_constr loc c_nm env in
            let@ exprs =
              ListM.mapM (fun (nm, expr) ->
                  let@ expr = self expr in
                  return (nm, expr)
                ) exprs
            in
            return (IT (Constructor (c_nm, exprs), SBT.Datatype cons_info.c_datatype_tag, loc))
        | CNExpr_each (sym, bt, r, e) ->
            let@ expr =
              trans
                evaluation_scope
                (SymSet.add sym locally_bound)
                (add_logical sym SBT.Integer env)
                e
            in
            let@ bt = check_quantified_base_type env loc bt in
            return (IT ((EachI ((Z.to_int (fst r), (sym, SBT.to_basetype bt), Z.to_int (snd r)), expr)), SBT.Bool, loc))
        | CNExpr_match (x, ms) ->
           let@ x = self x in
           let@ ms =
             ListM.mapM (fun (pat, body) ->
                 let@ env', locally_bound', pat =
                   translate_cn_pat env locally_bound (pat, IT.bt x) in
                 let@ body = trans evaluation_scope locally_bound' env' body in
                 return (pat, body)
               ) ms
           in
           let rbt = IT.basetype (snd (List.hd ms)) in
           return (IT (Match (x, ms), rbt, loc))
        | CNExpr_let (s, e, body) ->
            let@ e = self e in
            let@ body =
              trans evaluation_scope (SymSet.add s locally_bound)
                (add_logical s (IT.bt e) env) body
            in
            return (IT (Let ((s, e), body), IT.bt body, loc))
        | CNExpr_ite (e1, e2, e3) ->
            let@ e1 = self e1 in
            let@ e2 = self e2 in
            let@ e3 = self e3 in
            return (ite_ (e1, e2, e3) loc)
        | CNExpr_good (ty, e) ->
           let scty = Sctypes.of_ctype_unsafe loc ty in
           let@ e = self e in
           return (IT ((Good (scty, e)), SBT.Bool, loc))
        | CNExpr_not e ->
           let@ e = self e in
           return (not_ e loc)
        | CNExpr_default bt ->
           let bt = translate_cn_base_type env bt in
           return (IT (Const (Default (SBT.to_basetype bt)), bt, loc))
        | CNExpr_unchanged e ->
           let@ cur_e = self e in
           let@ old_e = self (CNExpr (loc, CNExpr_at_env (e, start_evaluation_scope))) in
           (* want to bypass the warning for (Loc, Loc) equality *)
           (* mk_translate_binop loc CN_equal (cur_e, old_e) *)
           return (IT (Binop (EQ, cur_e, old_e), SBT.Bool, loc))
        | CNExpr_at_env (e, scope) ->
           let@ () = match evaluation_scope with
             | None -> return ()
             | Some _ -> fail {loc; msg = Generic !^"Cannot nest evaluation scopes."}
           in
           let@ scope_exists = scope_exists loc scope in
           (* let@ () = match StringMap.mem scope env.old_states with *)
           let@ () = match scope_exists with
             | true -> return ()
             | false -> fail { loc; msg = Generic !^("Unknown evaluation scope '"^scope^"'.") }
           in
           trans (Some scope) locally_bound env e
        | CNExpr_deref e ->
           let@ () =
             let locally_bound_in_e = SymSet.inter (free_in_expr e) locally_bound in
             match SymSet.elements locally_bound_in_e with
             | [] ->
                return ()
             | s :: _ ->
                let msg =
                  Sym.pp s ^^^ !^"is locally bound in this expression."
                  ^/^ !^"Cannot dereference a pointer expression containing a locally bound variable."
                in
                fail {loc; msg = Generic msg}
           in
           let@ expr = self e in
           let@ o_v = deref loc expr evaluation_scope in
           (* let@ o_v = match evaluation_scope with *)
           (*   | Some scope -> *)
           (*      let state = StringMap.find scope env.old_states in *)
           (*      return (STermMap.find_opt expr state.pointee_values) *)
           (*   | None -> *)
           (*      deref loc expr *)
           (* in *)
           begin match o_v with
           | Some v -> return v
           | None ->
              let msg =
                !^"Cannot dereference" ^^^ squotes (Terms.pp expr)
                ^^^ pp_in_scope evaluation_scope ^^ dot
                ^^^ !^"Is the necessary ownership missing?"
              in
              fail {loc; msg = Generic msg}
           end
        | CNExpr_value_of_c_atom (sym, C_kind_var) ->
           assert (not (SymSet.mem sym locally_bound));
           (* let@ o_v = match evaluation_scope with *)
           (*   | Some scope -> *)
           (*      let state = StringMap.find scope env.old_states in *)
           (*      let o_v =  *)
           (*        Option.map (function *)
           (*            | CVS_Value x -> x *)
           (*            | CVS_Pointer_pointing_to x -> x *)
           (*          ) (SymMap.find_opt sym state.c_variable_state) *)
           (*      in *)
           (*      return o_v *)
           (*   | None -> *)
           (*      value_of_c_variable loc sym *)
           (* in *)
           let@ o_v = value_of_c_variable loc sym evaluation_scope in
           begin match o_v with
           | None ->
              let msg =
                !^"Cannot resolve the value of" ^^^ Sym.pp sym
                ^^^ pp_in_scope evaluation_scope ^^ dot
                ^^^ !^"Is the ownership for accessing" ^^^ Sym.pp sym ^^^ !^"missing?"
              in
              fail {loc; msg = Generic msg}
           | Some v ->
              return v
           end
        | CNExpr_value_of_c_atom (sym, C_kind_enum) ->
           assert (not (SymSet.mem sym locally_bound));
           liftResultat (do_decode_enum env loc sym)
    in
    trans None




  let translate_cn_res_info res_loc loc env res args =
    let open RET in
    let@ (ptr_expr, iargs) = match args with
      | [] -> fail {loc; msg = First_iarg_missing}
      | (x :: xs) -> return (x, xs)
    in
    let@ (pname, oargs_ty) = match res with
      | CN_owned oty ->
         let@ scty = match oty with
           | Some ty -> return (Sctypes.of_ctype_unsafe res_loc ty)
           | None ->
              match IT.bt ptr_expr with
              | SBT.Loc (Some ty) -> return ty
              | Loc None ->
                 fail {loc; msg = Generic !^"Cannot tell C-type of pointer. Please use Owned with an annotation: \'Owned<CTYPE>'."}
              | has ->
                 let expected = "pointer" in
                 let reason = "Owned<_> predicate" in
                 fail {loc; msg = Illtyped_it {it = Terms.pp ptr_expr; has = SBT.pp has; expected; reason; o_ctxt = None}}
         in
         (* we don't take Resources.owned_oargs here because we want to
            maintain the C-type information *)
         let oargs_ty = Memory.sbt_of_sct scty in
         return (Owned (scty, Init), oargs_ty)
      | CN_block ty ->
        let scty = Sctypes.of_ctype_unsafe res_loc ty in
        return (Owned (scty, Uninit), Memory.sbt_of_sct scty)
      | CN_named pred ->
        let@ pred_sig = match lookup_predicate pred env with
          | None -> fail {loc; msg = Unknown_resource_predicate {id = pred; logical = false}}
          | Some pred_sig -> return pred_sig
        in
        let output_bt = pred_sig.pred_output in
        return (PName pred, SBT.of_basetype output_bt)
    in
    return (pname, ptr_expr, iargs, oargs_ty)



  let split_pointer_linear_step loc ((q, bt, _) as sym_args) (ptr_expr : IT.sterm) =
    let open Pp in
    let qs = IT.sym_ sym_args in
    let msg_s = "Iterated predicate pointer must be array_shift<ctype>(ptr, q_var):" in
    begin match IT.term ptr_expr with
      | ArrayShift { base=p; ct; index=x } when Terms.equal SBT.equal x qs ->
        let here = Locations.other __FUNCTION__ in
        return (p, IT.cast_ (SBT.to_basetype bt) (IT.sizeOf_ ct here) here)
      | _ ->
      fail { loc; msg= Generic (!^msg_s ^^^ IT.pp ptr_expr)}
    end



  let owned_good loc sym (res_t, oargs_ty) =
    match res_t with
    | RET.P { name = Owned (scty, Init); _} ->
       (* TODO revisit these locations *)
       let v = IT.sym_ (sym, SBT.to_basetype oargs_ty, loc) in
       [(LC.T ((IT.good_ (scty, v) loc)),
         (loc, Some "default value constraint"))]
    | RET.Q { name = Owned (scty, Init); q = (q_sym, q_bt); q_loc; permission; _} ->
       (* TODO revisit these locations *)
       let v = IT.sym_ (sym, SBT.to_basetype oargs_ty, loc) in
       let v_el = IT.map_get_ v (IT.sym_ (q_sym, q_bt, q_loc)) loc in
       [(LC.forall_ (q_sym, q_bt) (IT.impl_ (permission, IT.good_ (scty, v_el) loc) loc),
          (loc, Some "default value constraint"))]
     | _ ->
        []


  let translate_cn_let_resource__pred env res_loc sym (pred_loc, res, args) =
    let@ args = ListM.mapM (translate_cn_expr SymSet.empty env) args in
    let@ (pname, ptr_expr, iargs, oargs_ty) =
           translate_cn_res_info res_loc pred_loc env res args in
    let pt = (RET.P { name = pname
              ; pointer= IT.term_of_sterm ptr_expr
              ; iargs = List.map IT.term_of_sterm iargs},
           oargs_ty)
    in
    let pointee_value = match pname with
      | Owned (_, Init) ->
        (* TODO revisit this location *)
        [(ptr_expr, (IT.sym_ (sym, oargs_ty, res_loc)))]
      | _ -> []
    in
    return (pt, pointee_value)

  let translate_cn_let_resource__each env res_loc (q, bt, guard, pred_loc, res, args) =
    let@ bt' = check_quantified_base_type env pred_loc bt in
    let env_with_q = add_logical q bt' env in
    let@ guard_expr = translate_cn_expr (SymSet.singleton q) env_with_q guard in
    let@ args = ListM.mapM (translate_cn_expr (SymSet.singleton q) env_with_q) args in
    let@ (pname, ptr_expr, iargs, oargs_ty) =
           translate_cn_res_info res_loc pred_loc env_with_q res args in
    (* TODO revisit this location *)
    let@ (ptr_base, step) = split_pointer_linear_step pred_loc (q, bt', res_loc) ptr_expr in
    let m_oargs_ty = SBT.make_map_bt bt' oargs_ty in
    let pt = (RET.Q { name = pname
              ; q= (q, SBT.to_basetype bt')
              (* TODO revisit this location *)
              ; q_loc = res_loc
              ; pointer= IT.term_of_sterm ptr_base
              ; step = step
              ; permission= IT.term_of_sterm guard_expr
              ; iargs = List.map IT.term_of_sterm iargs},
           m_oargs_ty)
    in
    return (pt, [])

  let translate_cn_let_resource env (res_loc, sym, the_res) =
    let@ pt, pointee_values = match the_res with
      | CN_pred (pred_loc, res, args) ->
         translate_cn_let_resource__pred env res_loc sym
           (pred_loc, res, args)
      | CN_each (q, bt, guard, pred_loc, res, args) ->
         translate_cn_let_resource__each env res_loc
           (q, bt, guard, pred_loc, res, args)
    in
    return (pt,
            owned_good res_loc sym pt,
            pointee_values)


  let translate_cn_assrt env (loc, assrt) =
    match assrt with
    | CN_assert_exp e_ ->
       let@ e = translate_cn_expr SymSet.empty env e_ in
       return (LC.T (IT.term_of_sterm e))
    | CN_assert_qexp (sym, bTy, e1_, e2_) ->
       let bt = translate_cn_base_type env bTy in
       let env_with_q = add_logical sym bt env in
       let@ e1 = translate_cn_expr (SymSet.singleton sym) env_with_q e1_ in
       let@ e2 = translate_cn_expr (SymSet.singleton sym) env_with_q e2_ in
       return (LC.Forall ((sym, SBT.to_basetype bt),
                          IT.impl_ (IT.term_of_sterm e1,
                                    IT.term_of_sterm e2) loc))


end


module ET = EffectfulTranslation

module Pure = struct

  let handle what = function
    | E.Done x ->
       Resultat.return x
    | E.Error e ->
       Resultat.fail e
    | E.Value_of_c_variable (loc, _, _, _) ->
       let msg = !^what ^^^ !^"are not allowed to refer to (the state of) C variables." in
       fail {loc; msg = Generic msg}
    | E.Deref (loc, _, _, _) ->
       let msg = !^what ^^^ !^"are not allowed to dereference pointers." in
       fail {loc; msg = Generic msg}
    | E.ScopeExists (loc, _, _) ->
       let msg = !^what ^^^ !^"are not allowed to use evaluation scopes." in
       fail {loc; msg = Generic msg}

end


let translate_cn_func_body env body =
  let handle = Pure.handle "Function definitions" in
  let@ body = handle (ET.translate_cn_expr SymSet.empty env body) in
  return ((IT.term_of_sterm body))


let known_attrs = ["rec"; "coq_unfold"]

let translate_cn_function env (def: cn_function) =
  let open LogicalFunctions in
  Pp.debug 2 (lazy (Pp.item "translating function defn" (Sym.pp def.cn_func_name)));
  let args =
    List.map (fun (sym, bTy) -> (sym, translate_cn_base_type env bTy)
      ) def.cn_func_args in
  let env' =
    List.fold_left (fun acc (sym, bt) -> add_logical sym bt acc
      ) env args in
  let is_rec = List.exists (fun id -> String.equal (Id.s id) "rec") def.cn_func_attrs in
  let coq_unfold = List.exists (fun id -> String.equal (Id.s id) "coq_unfold") def.cn_func_attrs in
  let@ () = ListM.iterM (fun id -> if List.exists (String.equal (Id.s id)) known_attrs
    then return ()
    else fail {loc = def.cn_func_loc; msg = Generic (Pp.item "Unknown attribute" (Id.pp id))}
  ) def.cn_func_attrs in
  let@ definition = match def.cn_func_body with
    | Some body ->
       let@ body = translate_cn_func_body env' body in
       return (if is_rec then Rec_Def body else Def body)
    | None -> return Uninterp in
  let return_bt = translate_cn_base_type env def.cn_func_return_bty in
  let def2 = {
      loc = def.cn_func_loc;
      args = List.map_snd SBT.to_basetype args;
      return_bt = SBT.to_basetype return_bt;
      emit_coq = not coq_unfold;
      definition
    }
  in
  return (def.cn_func_name, def2)



let ownership (loc, (addr_s, ct)) env =
  let name = match Sym.description addr_s with
    | SD_ObjectAddress obj_name ->
       Sym.fresh_make_uniq ("O_"^obj_name)
    | _ -> assert false
  in
  let resource = CN_pred (loc, CN_owned (Some ct), [CNExpr (loc, CNExpr_var addr_s)]) in

  let@ (pt_ret, oa_bt), lcs, _ =
    Pure.handle "'Accesses'"
      (ET.translate_cn_let_resource env (loc, name, resource)) in
  let value = IT.sym_ (name, oa_bt, loc) in
  return (name, ((pt_ret, oa_bt), lcs), value)

let allocation_token loc addr_s =
  let name = match Sym.description addr_s with
    | SD_ObjectAddress obj_name ->
       Sym.fresh_make_uniq ("A_"^obj_name)
    | _ -> assert false in
  let alloc_ret = Global.mk_alloc (IT.sym_ (addr_s, BT.Loc, loc)) in
  ((name, (ResourceTypes.P alloc_ret, BT.Unit)), (loc, None))



module LocalState = struct

  (* the expression that encodes the current value of this c variable *)
  type c_variable_state =
    | CVS_Value of IT.sterm           (* currently the variable is a pure value, this one *)
    | CVS_Pointer_pointing_to of IT.sterm         (* currently the variable is a pointer to memory holding this value *)



  type state = {
      c_variable_state : c_variable_state SymMap.t;
      pointee_values : IT.sterm STermMap.t
    }

  let empty_state = {
      c_variable_state= SymMap.empty;
      pointee_values= STermMap.empty
    }

  type states = {
      state : state;
      old_states : state StringMap.t
    }

  let init_st = {state = empty_state; old_states = StringMap.empty}

  let make_state_old {state; old_states} old_name =
    { state = empty_state;
      old_states = StringMap.add old_name state old_states }

  let add_c_variable_state c_sym cvs {state; old_states} =
    { state = { state with c_variable_state = SymMap.add c_sym cvs state.c_variable_state };
      old_states }

  let add_pointee_value p v {state; old_states} =
    { state = { state with pointee_values = STermMap.add p v state.pointee_values };
      old_states }


  let add_c_variable_states cvss st =
    List.fold_left (fun st (sym, cvs) ->
        add_c_variable_state sym cvs st
      ) st cvss

  let add_pointee_values pvs st =
    List.fold_left (fun st (p, v) ->
        add_pointee_value p v st
      ) st pvs



  let handle {state;old_states} : 'a E.m -> 'a Resultat.m =
    let state_for_scope = function
      | None -> state
      | Some s -> StringMap.find s old_states
    in
    let rec aux = function
      | E.Done x ->
         Resultat.return x
      | E.Error e ->
         Resultat.fail e
      | E.Value_of_c_variable (loc, sym, scope, k) ->
         let variable_state = (state_for_scope scope).c_variable_state in
         let o_v =
           Option.map (function
               | CVS_Value x -> x
               | CVS_Pointer_pointing_to x -> x
             ) (SymMap.find_opt sym variable_state)
         in
         aux (k o_v)
      | E.Deref (loc, it, scope, k) ->
         let pointee_values = (state_for_scope scope).pointee_values in
         let o_v = STermMap.find_opt it pointee_values in
         aux (k o_v)
      | E.ScopeExists (loc, scope, k) ->
         aux (k (StringMap.mem scope old_states))
    in
    aux

end


let translate_cn_clause env clause =
  let open Resources in
  let open LocalState in
  let rec translate_cn_clause_aux env st acc clause =
    let module LAT = LogicalArgumentTypes in
    match clause with
      | CN_letResource (res_loc, sym, the_res, cl) ->
         let@ (pt_ret, oa_bt), lcs, pointee_vals =
           handle st (ET.translate_cn_let_resource env (res_loc, sym, the_res)) in
         let acc' z =
           acc (LAT.mResource ((sym, (pt_ret, SBT.to_basetype oa_bt)), (res_loc, None))
               (LAT.mConstraints lcs z))
         in
         let env' = add_logical sym oa_bt env in
         let st' = add_pointee_values pointee_vals st in
         translate_cn_clause_aux env' st' acc' cl
      | CN_letExpr (loc, sym, e_, cl) ->
          let@ e = handle st (ET.translate_cn_expr SymSet.empty env e_) in
          let acc' =
            fun z -> acc begin
              LAT.mDefine (sym, IT.term_of_sterm e, (loc, None)) z
            end in
          translate_cn_clause_aux (add_logical sym (IT.basetype e) env) st acc' cl
      | CN_assert (loc, assrt, cl) ->
         let@ lc = handle st (ET.translate_cn_assrt env (loc, assrt)) in
         let acc' z = acc (LAT.mConstraint ( lc, (loc, None) ) z) in
         translate_cn_clause_aux env st acc' cl
      | CN_return (loc, e_) ->
          let@ e = handle st (ET.translate_cn_expr SymSet.empty env e_) in
          let e = IT.term_of_sterm e in
          acc (LAT.I e)
  in
  translate_cn_clause_aux env init_st (fun z -> return z) clause



let translate_cn_clauses env clauses =
  let rec self acc = function
    | CN_clause (loc, cl_) ->
        let@ cl = translate_cn_clause env cl_ in
        let here = Locations.other __FUNCTION__ in
        return (RP.{loc= loc; guard= IT.bool_ true here; packing_ft= cl} :: acc)
    | CN_if (loc, e_, cl_, clauses') ->
      let@ e  = Pure.handle "Predicate guards" (ET.translate_cn_expr SymSet.empty env e_) in
      let@ cl = translate_cn_clause env cl_ in
      self begin
        RP.{loc= loc; guard= IT.term_of_sterm e; packing_ft= cl} :: acc
      end clauses'
  in
  let@ xs = self [] clauses in
  return (List.rev xs)

let translate_option_cn_clauses env = function
  | Some clauses ->
     let@ clauses = translate_cn_clauses env clauses in
     return (Some clauses)
  | None ->
     return None

let translate_cn_predicate env (def: cn_predicate) =
  let open RP in
  Pp.debug 2 (lazy (Pp.item "translating predicate defn" (Sym.pp def.cn_pred_name)));
  let (iargs, output_bt) =
    match lookup_predicate def.cn_pred_name env with
      | None ->
          assert false
      | Some pred_sig ->
          (pred_sig.pred_iargs, pred_sig.pred_output) in
  let env' =
    List.fold_left (fun acc (sym, bTy) ->
      add_logical sym (SBT.of_basetype bTy) acc
    ) env iargs in
  let@ clauses = translate_option_cn_clauses env' def.cn_pred_clauses in
  match iargs with
    | (iarg0, BaseTypes.Loc) :: iargs' ->
        return
          ( def.cn_pred_name
          , { loc= def.cn_pred_loc
            ; pointer= iarg0
            ; iargs= iargs'
            ; oarg_bt= output_bt
            ; clauses= clauses
            } )
    | (_, found_bty) :: _ ->
        fail { loc= def.cn_pred_loc; msg= First_iarg_not_pointer { pname= PName def.cn_pred_name; found_bty } }
    | [] ->
        fail { loc= def.cn_pred_loc; msg= First_iarg_missing }


let rec make_lrt_generic env st =
  let open LocalState in
  function
  | (CN_cletResource (loc, name, resource) :: ensures) ->
     let@ (pt_ret, oa_bt), lcs, pointee_values =
       handle st (ET.translate_cn_let_resource env (loc, name, resource)) in
     let env = add_logical name oa_bt env in
     let st = add_pointee_values pointee_values st in
     let@ lrt, env, st = make_lrt_generic env st (ensures) in
     return ((LRT.mResource ((name, (pt_ret, SBT.to_basetype oa_bt)), (loc, None))
             (LRT.mConstraints lcs lrt)),
             env, st)
  | (CN_cletExpr (loc, name, expr) :: ensures) ->
     let@ expr = handle st (ET.translate_cn_expr SymSet.empty env expr) in
     let@ lrt, env, st = make_lrt_generic (add_logical name (IT.bt expr) env) st (ensures) in
     return ((LRT.mDefine (name, IT.term_of_sterm expr, (loc, None)) lrt), env, st)
  | (CN_cconstr (loc, constr) :: ensures) ->
     let@ lc = handle st (ET.translate_cn_assrt env (loc, constr)) in
     let@ lrt, env, st = make_lrt_generic env st (ensures) in
     return ((LRT.mConstraint (lc, (loc, None)) lrt), env, st)
  | [] ->
     return (LRT.I, env, st)

  let make_lrt env st conds =
    let@ lrt, _env, _st = make_lrt_generic env st conds in
    return lrt

  let make_lat env st (requires, ensures) =
    let@ args_lrt, env, st = make_lrt_generic env st requires in
    let st = LocalState.make_state_old st start_evaluation_scope in
    let@ ret_lrt, env, st = make_lrt_generic env st ensures in
    return (LAT.of_lrt args_lrt (LAT.I ret_lrt))


  let rec make_lrt_with_accesses env st (accesses, ensures) =
    match accesses with
    | (loc, (addr_s, ct)) :: accesses ->
       let@ (name, ((pt_ret, oa_bt), lcs), value) = ownership (loc, (addr_s, ct)) env in
       let env = add_logical name oa_bt env in
       let st = LocalState.add_c_variable_state addr_s (CVS_Pointer_pointing_to value) st in
       let@ lrt = make_lrt_with_accesses env st (accesses, ensures) in
       return (LRT.mResource ((name, (pt_ret, SBT.to_basetype oa_bt)), (loc, None))
              (LRT.mConstraints lcs lrt))
    | [] ->
       make_lrt env st ensures

  let make_rt loc (env : env) st (s, ct) (accesses, ensures) =
    let ct = Sctypes.of_ctype_unsafe loc ct in
    let sbt = Memory.sbt_of_sct ct in
    let bt = SBT.to_basetype sbt in
    let@ lrt = make_lrt_with_accesses (add_computational s sbt env) st (accesses, ensures) in
    let info = (loc, Some "return value good") in
    let here = Locations.other __FUNCTION__ in
    let lrt = LRT.mConstraint (LC.t_ (IT.good_ (ct, IT.sym_ (s, bt, loc)) here), info) lrt in
    return (RT.mComputational ((s, bt), (loc, None)) lrt)



  (* copied and adjusted from translate_cn_function *)
  let translate_cn_lemma env (def: cn_lemma) =
    Pp.debug 2 (lazy (Pp.item "translating lemma defn" (Sym.pp def.cn_lemma_name)));
    let rec aux env = function
      | (sym, bTy) :: args' ->
         let bTy = translate_cn_base_type env bTy in
         let env = add_computational sym bTy env in
         let@ at = aux env args' in
         let info = (def.cn_lemma_loc, None) in
         return (ArgumentTypes.Computational ((sym, SBT.to_basetype bTy), info, at))
      | [] ->
         let@ lat = make_lat env LocalState.init_st (def.cn_lemma_requires, def.cn_lemma_ensures) in
         return (ArgumentTypes.L lat)
    in
    let@ at = aux env def.cn_lemma_args in
    return (def.cn_lemma_name, (def.cn_lemma_loc, at))





module UsingLoads = struct

  let pointee_ct loc it =
    match IT.bt it with
    | SBT.Loc (Some ct) ->
       return ct
    | SBT.Loc None ->
       let msg =
         !^"Cannot tell pointee C-type of"
         ^^^ squotes (IT.pp it) ^^ dot
       in
       fail {loc; msg = Generic msg}
    | has ->
       let expected = "pointer" in
       let reason = "dereferencing" in
       let msg = Illtyped_it {it= IT.pp it; has= SBT.pp has; expected; reason; o_ctxt = None} in
       fail {loc; msg}


  open Cnprog

  let handle allocations old_states : cn_prog E.m -> cn_prog Resultat.m =

    let rec aux = function
      | E.Done x ->
         return x
      | E.Error e ->
         fail e
      | E.Value_of_c_variable (loc,sym,scope,k) ->
         begin match scope with
         | Some scope ->
            let variable_state = LocalState.((StringMap.find scope old_states).c_variable_state) in
            let o_v =
              Option.map (function
                  | LocalState.CVS_Value x -> x
                  | LocalState.CVS_Pointer_pointing_to x -> x
                ) (SymMap.find_opt sym variable_state)
            in
            aux (k o_v)
         | None ->
            let ct = Sctypes.of_ctype_unsafe loc (allocations sym) in
            let pointer = IT.sym_ (sym, SBT.Loc (Some ct), loc) in
            load loc "read" pointer k
         end
      | Deref (loc, pointer, scope, k) ->
         begin match scope with
         | Some scope ->
            let pointee_values = (StringMap.find scope old_states).pointee_values in
            let o_v = STermMap.find_opt pointer pointee_values in
            aux (k o_v)
         | None ->
            load loc "deref" pointer k
         end
      | ScopeExists (loc, scope, k) ->
         aux (k (StringMap.mem scope old_states))

    and load loc action_pp pointer k =
      let@ pointee_ct = pointee_ct loc pointer in
      let value_loc = Locations.other __FUNCTION__ in
      let value_s = Sym.fresh_make_uniq (action_pp ^ "_" ^ Pp.plain (IT.pp pointer)) in
      let value_bt = Memory.sbt_of_sct pointee_ct in
      let value = IT.sym_ (value_s, value_bt, value_loc) in
      let@ prog = aux (k (Some value)) in
      let load = {ct = pointee_ct; pointer = IT.term_of_sterm pointer} in
      return (M_CN_let (loc, (value_s, load), prog))

    in

    aux

end


let translate_cn_statement
      (allocations : Sym.t -> CF.Ctype.ctype)
      old_states
      env
      (CN_statement (loc, stmt_))
  =

  let open Cnprog in

  UsingLoads.handle allocations old_states (
      let open E in
      let open Effectful.Make(E) in
      match stmt_ with
      | CN_pack_unpack (pack_unpack, pred, args) ->
         let@ args = ListM.mapM (ET.translate_cn_expr SymSet.empty env) args in
         let@ name, pointer, iargs, oargs_ty =
           ET.translate_cn_res_info loc loc env pred args in
         let stmt =
           M_CN_pack_unpack
             (pack_unpack, {
               name = name;
               pointer = IT.term_of_sterm pointer;
               iargs = List.map IT.term_of_sterm iargs;
             })
         in
         return (M_CN_statement (loc, stmt))
      | CN_have assrt ->
         let@ assrt = ET.translate_cn_assrt env (loc, assrt) in
         return (M_CN_statement (loc, M_CN_have assrt))
      | CN_instantiate (to_instantiate, expr) ->
         let@ expr = ET.translate_cn_expr SymSet.empty env expr in
         let expr = IT.term_of_sterm expr in
         let to_instantiate = match to_instantiate with
           | I_Everything -> I_Everything
           | I_Function f -> I_Function f
           | I_Good ct -> I_Good (Sctypes.of_ctype_unsafe loc ct)
         in
         return (M_CN_statement (loc, M_CN_instantiate (to_instantiate, expr)))
      | CN_split_case e ->
         let@ e = ET.translate_cn_assrt env (loc, e) in
         return (M_CN_statement (loc, M_CN_split_case e))
      | CN_extract (attrs, to_extract, expr) ->
          let@ expr = ET.translate_cn_expr SymSet.empty env expr in
          let expr = IT.term_of_sterm expr in
          let to_extract = match to_extract with
           | E_Everything -> E_Everything
           | E_Pred (CN_owned oty) -> E_Pred (CN_owned (Option.map (Sctypes.of_ctype_unsafe loc) oty))
           | E_Pred (CN_block ty) -> E_Pred (CN_block (Sctypes.of_ctype_unsafe loc ty))
           | E_Pred (CN_named pn) -> E_Pred (CN_named pn)
          in
          return (M_CN_statement (loc, M_CN_extract (attrs, to_extract, expr)))
      | CN_unfold (s, args) ->
         let@ args = ListM.mapM (ET.translate_cn_expr SymSet.empty env) args in
         let args = List.map IT.term_of_sterm args in
         return (M_CN_statement (loc, M_CN_unfold (s, args)))
      | CN_assert_stmt e ->
         let@ e = ET.translate_cn_assrt env (loc, e) in
         return (M_CN_statement (loc, M_CN_assert e))
      | CN_apply (s, args) ->
         let@ args = ListM.mapM (ET.translate_cn_expr SymSet.empty env) args in
         let args = List.map IT.term_of_sterm args in
         return (M_CN_statement (loc, M_CN_apply (s, args)))
      | CN_inline nms ->
         return (M_CN_statement (loc, M_CN_inline nms))
      | CN_print expr ->
         let@ expr = ET.translate_cn_expr SymSet.empty env expr in
         let expr = IT.term_of_sterm expr in
         return (M_CN_statement (loc, M_CN_print expr))

    )



