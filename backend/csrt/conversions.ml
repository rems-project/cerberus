module CF=Cerb_frontend
module CB=Cerb_backend
open List
open Sym
open Resultat
open Pp
(* open Tools *)
module BT = BaseTypes
module RT = ReturnTypes
module FT = ArgumentTypes.Make(ReturnTypes)
module LT = ArgumentTypes.Make(False)
open TypeErrors
open IndexTerms
open BaseTypes
open LogicalConstraints
open Resources


module SymSet = Set.Make(Sym)
module StringMap = Map.Make(String)






(* convert from other types *)

let bt_of_core_object_type loc ot =
  let open CF.Core in
  match ot with
  | OTy_integer -> return BT.Integer
  | OTy_pointer -> return BT.Loc
  | OTy_array cbt -> return BT.Array
  | OTy_struct sym -> return (BT.Struct (Tag sym))
  | OTy_union _sym -> fail loc (Unsupported !^"todo: unions")
  | OTy_floating -> fail loc (Unsupported !^"todo: float")

let rec bt_of_core_base_type loc cbt =
  let open CF.Core in
  match cbt with
  | BTy_unit -> return BT.Unit
  | BTy_boolean -> return BT.Bool
  | BTy_object ot -> bt_of_core_object_type loc ot
  | BTy_loaded ot -> bt_of_core_object_type loc ot
  | BTy_list bt -> 
     let* bt = bt_of_core_base_type loc bt in
     return (BT.List bt)
  | BTy_tuple bts -> 
     let* bts = ListM.mapM (bt_of_core_base_type loc) bts in
     return (BT.Tuple bts)
  | BTy_storable -> fail loc (Unsupported !^"BTy_storable")
  | BTy_ctype -> fail loc (Unsupported !^"ctype")



let integerType_constraint loc about it =
  let* (min,max) = Memory.integer_range loc it in
  return (LC (And [IT.LE (Num min, about); IT.LE (about, Num max)]))


(* let integerType loc name it =
 *   let* (min,max) = Memory.integer_range loc it in
 *   let* constr = integerType_constraint loc (S name) it in
 *   return (Integer, constr) *)

let floatingType loc =
  fail loc (Unsupported !^"floats")



let rec ctype_aux owned loc (name: Sym.t) (CF.Ctype.Ctype (annots, ct_)) =
  let open RT in
  let loc = Loc.update loc annots in
  match ct_ with
  | Void -> 
     return ((name, BT.Unit), I)
  | Basic (Integer it) -> 
     let* constr = integerType_constraint loc (S name) it in
     return ((name, Integer), Constraint (constr, I))
  | Array (ct, _maybe_integer) -> 
     return ((name,BT.Array), I)
  | Pointer (_qualifiers, ct) ->
     if owned then
       let* ((pointee_name,bt),t) = ctype_aux owned loc (fresh ()) ct in
       let* size = Memory.size_of_ctype loc ct in
       let points = Points {pointer = S name; pointee = S pointee_name; size} in
       let t = Logical ((pointee_name, Base bt), Resource (points, t)) in
       return ((name,Loc),t)
     else
       return ((name,Loc),I)
  (* fix *)
  | Atomic ct -> ctype_aux owned loc name ct
  | Struct sym -> return ((name, Struct (Tag sym)),I)
  | Basic (Floating _) -> floatingType loc 
  | Union sym -> fail loc (Unsupported !^"todo: union types")
  | Function _ -> fail loc (Unsupported !^"function pointers")


let ctype owned loc (name : Sym.t) (ct : CF.Ctype.ctype) =
  let* ((name,bt),t) = ctype_aux owned loc name ct in
  return (RT.Computational ((name,bt),t))

let bt_of_ctype loc ct = 
  let* ((_,bt),_) = ctype_aux false loc (Sym.fresh ()) ct in
  return bt



let make_pointer_ctype ct = 
  let open CF.Ctype in
  (* fix *)
  let q = {const = false; restrict = false; volatile = false} in
  Ctype ([], Pointer (q, ct))







(* let explode_struct_in_binding loc global (Tag tag) logical_struct binding = 
 *   let open RT in
 *   let rec explode_struct loc global (Tag tag) logical_struct = 
 *     let* decl = Global.get_struct_decl loc global (Tag tag) in
 *     let rec aux = function
 *       | (member,bt)::members ->
 *          let this = IT.Member (Tag tag, logical_struct, member) in
 *          let* substs = aux members in
 *          let* substs2 = match bt with
 *            | Struct tag2 -> explode_struct loc global tag2 this
 *            | _ -> return [(fresh (), bt, this)]
 *          in
 *          return (substs @ substs2)
 *       | [] -> return []
 *     in
 *     aux decl.Global.raw 
 *   in
 *   let* substs = explode_struct loc global (Tag tag) logical_struct in
 *   let binding' = 
 *     fold_right (fun (name,bt,it) binding -> 
 *         Logical ((name,Base bt), 
 *                  instantiate_struct_member_l {s=it;swith=S name} binding)
 *       ) substs binding
 *   in
 *   return binding' *)



let rec lrt_to_ft (lrt : RT.l) (rest : FT.t) : FT.t = 
  match lrt with
  | RT.I -> rest
  | RT.Logical ((name, t), args) -> FT.Logical ((name, t), lrt_to_ft args rest)
  | RT.Resource (t, args) -> FT.Resource (t, lrt_to_ft args rest)
  | RT.Constraint (t, args) -> FT.Constraint (t, lrt_to_ft args rest)

let rt_to_ft rt rest = 
  let (RT.Computational ((name, t), lrt)) = rt in
  FT.Computational ((name, t), lrt_to_ft lrt rest)


let rec lrt_to_lt (lrt : RT.l) : LT.t = 
  match lrt with
  | RT.I -> I False
  | RT.Logical ((name, t), args) -> LT.Logical ((name, t), lrt_to_lt args)
  | RT.Resource (t, args) -> LT.Resource (t, lrt_to_lt args)
  | RT.Constraint (t, args) -> LT.Constraint (t, lrt_to_lt args)

let rt_to_lt rt = 
  let (RT.Computational ((name, t), lrt)) = rt in
  LT.Computational ((name, t), lrt_to_lt lrt)



let struct_decl_raw loc fields = 
  let rec aux id ct = 
    let member = Member (Id.s id) in
    let (CF.Ctype.Ctype (annots, ct_)) = ct in
    let loc = Loc.update loc annots in
    match ct_ with
    | Void -> return (member,Unit)
    | Basic (Integer it) -> return (member,Integer)
    | Array (ct, _maybe_integer) -> return (member,Array)
    | Pointer (_qualifiers, ct) -> return (member,Loc)
    | Atomic ct -> aux id ct
    | Struct tag -> return (member, Struct (Tag tag))
    | Basic (Floating _) -> fail loc (Unsupported !^"todo: union types")
    | Union sym -> fail loc (Unsupported !^"todo: union types")
    | Function _ -> fail loc (Unsupported !^"function pointers")
  in
  ListM.mapM (fun (id, (_,_,ct)) -> aux id ct) fields


let struct_decl_sizes loc fields = 
  ListM.mapM (fun (id, (_, _, ct)) ->
      let member = Member (Id.s id) in
      let* size = Memory.size_of_ctype loc ct in
      return (member,size)
    ) fields


let struct_decl_closed loc tag fields struct_decls = 
  let open Sym in
  let rec aux loc acc the_struct member ct =
    let (CF.Ctype.Ctype (annots, ct_)) = ct in
    let loc = Loc.update loc annots in
    let this = IT.Member (tag, S the_struct, member) in
    match ct_ with
    | Void -> 
       return acc
    | Basic (Integer it) -> 
       let* lc1 = integerType_constraint loc this it in
       return (RT.Constraint (lc1,acc))
    | Array (ct, _maybe_integer) -> 
       return acc
    | Pointer (_qualifiers, ct) -> 
       return acc
    (* fix *)
    | Atomic ct -> 
       aux loc acc the_struct member ct
    | Struct tag2 -> 
       let open RT in
       let open Global in
       let* decl = Global.get_struct_decl loc struct_decls (Tag tag2) in
       let Computational ((s,_struct),tag2_bindings) = decl.closed in
       return (RT.subst_var_l (Subst.{before=s;after=this}) tag2_bindings @@ acc)
    | Basic (Floating _) -> fail loc (Unsupported !^"todo: union types")
    | Union sym -> fail loc (Unsupported !^"todo: union types")
    | Function _ -> fail loc (Unsupported !^"function pointers")
  in
  let thisstruct = fresh () in
  let* bindings = 
    ListM.fold_rightM (fun (id, (_attributes, _qualifier, ct)) acc ->
        aux loc acc thisstruct (BT.Member (Id.s id)) ct
      ) fields I
  in
  return (RT.Computational ((thisstruct, BT.Struct tag), bindings))






let struct_decl_closed_stored loc tag fields (struct_decls: Global.struct_decls) = 
  let open Sym in
  let rec aux loc (lbs,rbs) struct_p member ct =
    let open RT in
    let* size = Memory.size_of_ctype loc ct in
    let (CF.Ctype.Ctype (annots, ct_)) = ct in
    let loc = Loc.update loc annots in
    let this_p = IT.MemberOffset (tag,struct_p,member) in
    let this_v = Sym.fresh () in
    let points = RE.Points {pointer=this_p;pointee= S this_v; size} in
    let new_lbs bt = RT.Logical ((this_v, Base bt), I) in
    let new_rbs = RT.Resource (points, I) in
    match ct_ with
    | Void -> 
       fail loc (Generic !^"void member of struct")
    | Basic (Integer it) -> 
       let* lc = integerType_constraint loc (S this_v) it in
       return (new_lbs Integer @@ RT.Constraint (lc,lbs), new_rbs)
    | Array (ct, _maybe_integer) -> 
       return (new_lbs Array @@ lbs, new_rbs)
    | Pointer (_qualifiers, ct) -> 
       return (new_lbs Loc @@ lbs, new_rbs)
    | Atomic ct -> 
       (* fix *)
       aux loc (lbs,rbs) struct_p member ct
    | Struct tag2 -> 
       let open RT in
       let open Global in
       let* decl = Global.get_struct_decl loc struct_decls (Tag tag2) in
       let (RT.Computational ((s,_loc),tag2_bindings)) = 
         RT.freshify (decl.closed_stored) in
       let rbs = 
         RT.subst_var_l (Subst.{before=s; after=this_p}) tag2_bindings @@ rbs in
       return (lbs, rbs)
    | Basic (Floating _) -> fail loc (Unsupported !^"todo: union types")
    | Union sym -> fail loc (Unsupported !^"todo: union types")
    | Function _ -> fail loc (Unsupported !^"function pointers")
  in
  let struct_pointer = Sym.fresh () in
  let* (lbs,rbs) = 
    ListM.fold_rightM (fun (id, (_attributes, _qualifier, ct)) acc ->
        aux loc acc (S struct_pointer) (BT.Member (Id.s id)) ct
      ) fields (RT.I,RT.I)
  in
  return (RT.Computational ((struct_pointer, Loc), RT.(@@) lbs rbs))



let struct_decl loc tag fields struct_decls = 
  let* raw = struct_decl_raw loc fields in
  let* sizes = struct_decl_sizes loc fields in
  let* closed = struct_decl_closed loc tag fields struct_decls in
  let* closed_stored = struct_decl_closed_stored loc tag fields struct_decls in
  return Global.{ raw; sizes; closed; closed_stored }



(* revisit later *)
let make_fun_arg_type_rt loc struct_decls lift asym ct =
  let open RT in
  let ct = if lift then make_pointer_ctype ct else ct in
  let rec aux name (CF.Ctype.Ctype (annots, ct_)) =
    match ct_ with
    | Void -> return (BT.Unit, I)
    | Basic (Integer it) -> 
       let* constr = integerType_constraint loc (S name) it in
       return (Integer, Constraint (constr,I))
    | Array (ct, _maybe_integer) ->
       return (Array, I)
    | Pointer (_qualifiers, ct) ->
       begin match ct with
       | CF.Ctype.Ctype (_, Struct s) ->
          let* decl = Global.get_struct_decl loc struct_decls (Tag s) in
          let Computational ((s,bt), lrt) = RT.freshify decl.Global.closed_stored in
          return (bt, RT.subst_var_l {before=s; after=S name} lrt)
       | _ ->
          let name2 = Sym.fresh () in
          let* (bt,lrt) = aux name2 ct in
          (* fix *)
          let* size = try Memory.size_of_ctype loc ct with _ -> return Num.zero in
          let points = RE.Points {pointer = S name; pointee = S name2; size} in
          return (Loc, Logical ((name2, Base bt), Resource (points, lrt)))
       end
    (* fix *)
    | Atomic ct -> 
       aux name ct
    | Struct tag -> 
       let* decl = Global.get_struct_decl loc struct_decls (Tag tag) in
       let Computational ((s,bt),lrt) = RT.freshify decl.Global.closed in
       return (bt, RT.subst_var_l {before=s; after=S name} lrt)
    | Basic (Floating _) -> floatingType loc 
    | Union sym -> fail loc (Unsupported !^"todo: union types")
    | Function _ -> fail loc (Unsupported !^"function pointers")
  in
  let* (bt,lrt) = aux asym ct in
  return (Computational ((asym, bt), lrt))


let make_name = function
  | Some (Symbol (_,_,Some name)) -> Sym.fresh_pretty (name ^ "_l")
  | Some (Symbol (_,_,None)) -> Sym.fresh ()
  | None -> Sym.fresh ()




(* let rec logical_variables_lrt = function
 *   | RT.Logical ((s,ls),lrt) -> SymMap.add s ls (logical_variables_lrt lrt)
 *   | RT.Resource (_,lrt) -> logical_variables_lrt lrt
 *   | RT.Constraint (_,lrt) -> logical_variables_lrt lrt
 *   | RT.I -> SymMap.empty
 * 
 * let logical_variables_rt = function
 *   | RT.Computational (_,lrt) -> logical_variables_lrt lrt
 * 
 * 
 * let return_resources_lrt loc lvars lrt =
 *   let find_lvar lvar = 
 *     match SymMap.find_opt lvar lvars with
 *     | None -> fail loc (Unreachable (!^"unbound lvar" ^^^ Sym.pp lvar))
 *     | Some ls -> return ls
 *   in
 *   let rec aux = function
 *     | RT.Resource (re,lrt) -> 
 *        let* rt' = aux lrt in
 *        begin match re with
 *        | Points ({pointee=None;_} as p) -> (\* this is not very good *\)
 *           return (RT.Resource (Points p, rt'))
 *        | Points ({pointee=Some lvar;_} as p) ->
 *           let lvar' = Sym.fresh () in
 *           let* ls = find_lvar lvar in
 *           return (RT.Logical ((lvar', ls), 
 *                   RT.Resource (RE.Points {p with pointee = Some lvar'}, rt')))
 *        | StoredStruct s ->
 *           let* (members,rt') = 
 *             ListM.fold_rightM (fun (member,lvar) (members,rt') ->
 *                 (\* has to be Loc, though *\)
 *                 let* ls = find_lvar lvar in
 *                 let lvar' = Sym.fresh () in
 *                 return ((member,lvar') :: members, RT.Logical ((lvar',ls), rt'))
 *               ) s.members ([],rt')
 *           in
 *           return (RT.Resource (StoredStruct {s with members}, rt'))
 *        end
 *     | RT.Logical (_,lrt) -> aux lrt
 *     | RT.Constraint (_,lrt) -> aux lrt
 *     | RT.I -> return RT.I
 *   in
 *   aux lrt
 * 
 * let return_resources_rt loc lvars = function
 *   | RT.Computational (_,lrt) -> 
 *      return_resources_lrt loc lvars lrt *)


let make_return_from_argument_lrt lrt =
  let subst_non_pointer = RT.subst_var_l ~re_subst_var:RE.subst_non_pointer in
  let rec aux = function
    | RT.Logical ((s,ls),lrt) ->
       let s' = Sym.fresh () in
       let lrt' = subst_non_pointer {before=s;after=S s'} lrt in
       RT.Logical ((s',ls), aux lrt')
    | RT.Resource (re,lrt) -> RT.Resource (re,aux lrt)
    | RT.Constraint (lc,lrt) -> RT.Constraint (lc,aux lrt)
    | RT.I -> RT.I
  in
  aux lrt
     
     

let make_return_from_argument_rt = function
  | RT.Computational (_,lrt) -> make_return_from_argument_lrt lrt



let make_fun_arg_type loc genv lift name ct =
  let* arg_rt = make_fun_arg_type_rt loc genv lift name ct in
  return (rt_to_ft arg_rt)

let make_fun_arg_and_return_type loc genv lift name ct =
  let* arg_rt = make_fun_arg_type_rt loc genv lift name ct in
  let ret = make_return_from_argument_rt arg_rt in
  return (rt_to_ft arg_rt, ret)

let make_fun_spec loc genv args ret_ctype = 
  let open FT in
  let open RT in
  let* (arguments, returns) = 
    ListM.fold_leftM (fun (args,returns) (msym, ct) ->
        let name = make_name msym in
        let* (arg,ret) = make_fun_arg_and_return_type loc genv true name ct in
        let args = Tools.comp args arg in
        return (args, returns @@ ret)
      ) 
      ((fun ft -> ft), I) args
  in
  let* (Computational ((ret_name,bound),ret)) = 
    ctype true loc (Sym.fresh ()) ret_ctype in
  let ftyp = arguments (I (RT.Computational ((ret_name,bound), RT.(@@) ret returns))) in
  return ftyp


let make_esave_spec loc genv attrs args = 
  let open FT in
  let open RT in
  let* arguments = 
    ListM.fold_leftM (fun args (msym, (ct,by_pointer)) ->
        let name = make_name msym in
        let* arg = make_fun_arg_type loc genv by_pointer name ct in
        let args = Tools.comp args arg in
        return args
      ) 
      (fun ft -> ft) args
  in
  let ftyp = arguments (I (RT.Computational ((fresh (), BT.Unit), I))) in
  return ftyp

let make_return_esave_spec ftyp =
  rt_to_lt (FT.get_return ftyp)

















let make_fun_spec_annot loc genv attrs args ret_ctype = 
  let open Rc_annot in
  let module LC = LogicalConstraints in
  let module LS = LogicalSorts in

  let pp_list pp_item xs = 
    brackets (Pp.separate_map (semi ^^ space) pp_item xs) in

  let pp_tuple pped = parens (separate (comma ^^ space) pped) in

  let pp_pattern = pp_list (Pp.string) in

  let pp_option pp_item = function
    | Some x -> parens (!^"Some" ^^^ pp_item x)
    | None -> !^"None"
  in

  let pp_quot_elt pp_elt = function
    | Quot_plain s -> parens (!^"Quot_plain" ^^^ parens !^s)
    | Quot_anti a -> pp_elt a
  in

  let pp_quoted pp_elt = pp_list (pp_quot_elt pp_elt) in

  let rec pp_coq_term coq_term = pp_quoted pp_type_expr coq_term
  and pp_iris_term iris_term = pp_quoted pp_type_expr iris_term

  and pp_coq_expr coq_expr = 
    parens 
      begin match coq_expr with
      | Coq_ident s -> !^"Coq_ident" ^^^ !^s
      | Coq_all coq_term -> !^"Coq_all" ^^^ pp_coq_term coq_term
      end

  and pp_constr constr =
    parens
      begin match constr with
      | Constr_Iris iris_term -> 
         !^"Constr_Iris" ^^^ pp_iris_term iris_term
      | Constr_exist (string,o_coq_expr,constr) ->
         !^"Constr_exist" ^^^ 
           pp_tuple [!^string;
                     pp_option pp_coq_expr o_coq_expr;
                     pp_constr constr]
      | Constr_own (string,ptr_kind,type_expr) ->
         !^"Constr_own" ^^^
           pp_tuple [!^string;
                     pp_ptr_kind ptr_kind;
                     pp_type_expr type_expr]
      | Constr_Coq coq_expr ->
         !^"Constr_Coq" ^^^ pp_coq_expr coq_expr
      end

  and pp_ptr_kind = function
    | Own -> !^"Own"
    | Shr -> !^"Shr"
    | Frac coq_expr -> parens (!^"Frac" ^^^ pp_coq_expr coq_expr)

  and pp_type_expr type_expr = 
    parens
      begin match type_expr with
      | Ty_refine (coq_expr,type_expr) ->
         !^"Ty_refine" ^^^
           pp_tuple [pp_coq_expr coq_expr; pp_type_expr type_expr]
      | Ty_ptr (ptr_kind, type_expr) ->
         !^"Ty_ptr" ^^^ 
           pp_tuple [pp_ptr_kind ptr_kind; 
                     pp_type_expr type_expr]
      | Ty_dots ->
         !^"Ty_dots"
      | Ty_exists (pattern,o_coq_expr,type_expr) ->
         !^"Ty_exists" ^^^
           pp_tuple [pp_pattern pattern; 
                     pp_option pp_coq_expr o_coq_expr;
                     pp_type_expr type_expr]
      | Ty_constr (type_expr, constr) ->
         !^"Ty_constr" ^^^
           pp_tuple [pp_type_expr type_expr; 
                     pp_constr constr]
      | Ty_params (ident,type_expr_args) ->
         !^"Ty_params" ^^^
           pp_tuple [!^ident;
                     pp_list pp_type_expr_arg type_expr_args]
      | Ty_Coq coq_expr ->
         !^"Ty_Coq" ^^^ pp_coq_expr coq_expr
      end

  and pp_type_expr_arg type_expr_arg = 
    parens
      begin match type_expr_arg with
      | Ty_arg_expr type_expr ->
         !^"Ty_arg_expr" ^^^ pp_type_expr type_expr
      | Ty_arg_lambda (pattern, o_coq_expr, type_expr_arg) ->
         !^"Ty_arg_lambda" ^^^
           pp_tuple [pp_pattern pattern;
                     pp_option pp_coq_expr o_coq_expr;
                     pp_type_expr_arg type_expr_arg]
      end
  in


  let rec of_coq_expr_typ loc names newname coq_expr =
    match coq_expr with
    | Coq_ident ident ->
       begin match ident with
       | "Z" -> 
          return ((BT.Integer, None), [], [], [])
       | "nat" -> 
          return ((BT.Integer, None), [], [], [LC.LC (IT.GE (S newname, Num Num.zero))])
       | "loc" -> 
          return ((BT.Loc, None), [], [], [])
       | _ -> 
          fail loc (Unsupported (!^"cannot process coq type term:" ^/^ 
                                   pp_coq_expr coq_expr))
       end
    | Coq_all coq_term -> 
       begin match coq_term with
       | [Quot_plain "Z"] -> 
          return ((BT.Integer, None), [], [], [])
       | [Quot_plain "nat"] -> 
          return ((BT.Integer, None), [], [], [LC.LC (IT.GE (S newname, Num Num.zero))])
       | _ -> 
          fail loc (Unsupported (!^"cannot process coq type term:" ^/^ 
                                   pp_coq_expr coq_expr))
       end

  and of_coq_term loc names coq_term =
    match coq_term with
    | [Quot_plain s] ->
       begin match IndexTermParser.parse loc names s with
       | Ok r -> return ([],r)
       | Error (loc,msg) -> 
          let err = 
            !^"cannot process coq term" ^^^ 
            parens (!^"returned" ^^^ squotes !^msg) ^^ colon ^/^ 
            (pp_coq_term coq_term)
          in
          fail loc (Unsupported err)
       end
    | _ ->
       fail loc (Unsupported (!^"cannot process coq term:" ^/^ 
                                pp_coq_term coq_term))

  and of_coq_expr loc names coq_expr = 
    match coq_expr with
    | Coq_ident ident ->
       begin match StringMap.find_opt ident names with
       | Some sym -> return ([], IT.S sym)
       | None -> fail loc (Generic !^("unknown name" ^ ident))
       end
    | Coq_all coq_term -> 
       of_coq_term loc names coq_term


  and of_coq_expr_refinement loc names newname coq_expr = 
    let* (l,it) = of_coq_expr loc names coq_expr in
    return (l, LC.LC (IT.EQ (IT.S newname, it)))

  and of_coq_expr_constraint loc names coq_expr = 
    let* (l,it) = of_coq_expr loc names coq_expr in
    return (l, LC.LC it)

  and of_constr loc names constr : ((Sym.t * LS.t) list * RE.t list * LC.t list) m =
    match constr with
    | Constr_Iris _ ->
       fail loc (Unsupported !^"Constr_Iris")
    | Constr_exist _ ->
       fail loc (Unsupported !^"Constr_exist")
    | Constr_own (ident,ptr_kind,type_expr) ->
       let* sym = match StringMap.find_opt ident names with
       | Some sym -> return sym
       | None -> fail loc (Generic !^("unknown name" ^ ident))
       in
       make_owned_pointer loc names sym ptr_kind type_expr
    | Constr_Coq coq_expr ->
       let* (l, c) = of_coq_expr_constraint loc names coq_expr in
       return (l, [], [c])

  and is_uninit_type_expr = function
    | Ty_params ("uninit", [Ty_arg_expr arg]) -> Some arg
    | _ -> None

  and of_integer_type_expr loc te = 
    match te with
    | Ty_Coq (Coq_ident "u32") -> return (32, `Unsigned, 4)
    | Ty_params ("u32", []) -> return (32, `Unsigned, 4)
    | Ty_Coq (Coq_ident "i32") -> return (32, `Signed, 4)
    | Ty_params ("i32", []) -> return (32, `Signed, 4)
    | _ -> 
       fail loc (Generic (!^"This integer type is not supported yet:" ^/^
                            pp_type_expr te))

  and make_owned_pointer loc names existing_pointer ptr_kind type_expr =
    let newname' = Sym.fresh () in
    (* from impl_mem *)
    begin match ptr_kind, is_uninit_type_expr type_expr with
    | Own, Some integer_type_expr -> 
       let* (_, _, bytes) = of_integer_type_expr loc integer_type_expr in
       let size = Num.of_int bytes in
       let points = Uninit {pointer = S existing_pointer; size} in
       return ([], [points], [])
    | Own, None -> 
       let* ((bt,osize),l,r,c) = of_type_expr loc names newname' type_expr in
       let* points = match osize with
         | Some size ->
            return (Points {pointer = S existing_pointer; 
                            pointee = S newname'; size})
         | None -> fail loc (Generic !^"pointer to non-object")
       in
       return ((newname', LS.Base bt) :: l, r @ [points], c)
    | Shr, _ -> 
       fail loc (Generic !^"Shared pointers not supported yet")
    | Frac _, _ -> 
       fail loc (Generic !^"Fractional pointers not supported yet")
    end

  and of_type_expr loc names newname te =
    match te with
    | Ty_refine (coq_expr,type_expr) ->
       let* ((bt,size),l,r,c) = of_type_expr loc names newname type_expr in
       let* (l',constr) = of_coq_expr_refinement loc names newname coq_expr in
       return ((bt,size),l @ l', r, c @ [constr])
    | Ty_ptr (ptr_kind, type_expr) ->
         (* from impl_mem *)
       let* pointer_size = match (CF.Ocaml_implementation.get ()).sizeof_pointer with
         | Some n -> return (Num.of_int n)
         | None -> fail loc (Generic !^"sizeof_pointer returned None")
       in
       let* (l,r,c) = make_owned_pointer loc names newname ptr_kind type_expr in
       return ((BT.Loc, Some pointer_size), l, r, c)
    | Ty_dots ->
       fail loc (Generic !^"Recursive types not supported yet")
    | Ty_exists _ ->
       fail loc (Unsupported !^"existential types")
    | Ty_constr (type_expr,constr) ->
       let* ((bt,size),l,r,c) = of_type_expr loc names newname type_expr in
       let* (l',r',c') = of_constr loc names constr in
       return((bt,size), l @ l', r @ r', c @ c')
    | Ty_params (ident,args) ->
       let open IT in
       begin match ident, args with
       | "int", [Ty_arg_expr arg] -> 
          let* (bits,signedness,bytes) = of_integer_type_expr loc arg in
          begin match bits, signedness with
          | 32, `Signed ->
             let constr = LC.LC (in_range (S newname) (int 0) max_u32) in
             return ((BT.Integer, Some (Num.of_int bytes)), [], [], [constr])
          | 32, `Unsigned ->
             let constr = LC.LC (in_range (S newname) min_i32 max_i32) in
             return ((BT.Integer, Some (Num.of_int bytes)), [], [], [constr])
          | _ -> 
             fail loc (Generic (!^"This type application is not supported yet:" ^/^
                                  pp_type_expr te))
          end
       | "void", [] ->
          return ((BT.Unit, None), [], [], [])
       | _ -> 
          fail loc (Generic (!^"This type application is not supported yet:" ^/^
                               pp_type_expr te))
       end
    | Ty_Coq coq_expr ->
       of_coq_expr_typ loc names newname coq_expr

  in


  let (annot: function_annot) = function_annot attrs in
  let names = StringMap.empty in
  let a, l, r, c = [], [], [], [] in
  let rl, rr, rc = [], [], [] in
  let* (names, (a, l, r, c)) = 
    ListM.fold_leftM (fun (names, (a, l, r, c)) (ident, coq_expr) ->
        let s = Sym.fresh_pretty ident in
        let names = StringMap.add ident s names in
        let* ((bt,_),l',r',c') = of_coq_expr_typ loc names s coq_expr in
        return (names, (a, l @ [(s, LS.Base bt)] @ l', r @ r', c @ c'))
      ) (names, (a, l, r, c)) annot.fa_parameters
  in
  let* ((a, l, r, c), (rl, rr, rc)) =
    ListM.fold_leftM (fun ((a, l, r, c), (rl, rr, rc)) type_expr ->
        let s = Sym.fresh () in
        let sa, sr = Sym.fresh (), Sym.fresh () in
        let* ((bt, osize), l', r', c') = of_type_expr loc names sa type_expr in
        let* size = match osize with
          | Some size -> return size
          | None -> fail loc (Generic !^"argument type without size")
        in
        let pointsa = RE.Points {pointer = S s; pointee = S sa; size} in
        let pointsr = RE.Points {pointer = S s; pointee = S sr; size} in
        return ((a @ [(s,BT.Loc)], l @ [(sa, LS.Base bt)] @ l', r @ [pointsa] @ r', c @ c'),
                (rl @ [(sr, LS.Base bt)], rr @ [pointsr], rc))
      ) ((a, l, r, c), (rl, rr, rc)) annot.fa_args
  in
  let* (ra, rl, rr, rc) =
    let type_expr = annot.fa_returns in
    let s = Sym.fresh () in
    let* ((bt, size), rl', rr', rc') = of_type_expr loc names s type_expr in
    return ((s,bt), rl @ rl', rr @ rr', rc @ rc')
  in
  let* (names, (rl, rr, rc)) = 
    ListM.fold_leftM (fun (names, (rl, rr, rc)) (ident,coq_expr) ->
        let s = Sym.fresh_pretty ident in
        let names = StringMap.add ident s names in
        let* ((bt,_), rl', rr', rc') = of_coq_expr_typ loc names s coq_expr in
        return (names, (rl @ [(s, LS.Base bt)] @ rl', rr @ rr', rc @ rc'))
      ) (names, (rl, rr, rc)) annot.fa_exists
  in
  let* (a, l, r, c) = 
    ListM.fold_leftM (fun (a, l, r, c) constr ->
        let* (l',r',c') = of_constr loc names constr in
        return (a, l @ l', r @ r', c @ c')
      ) (a, l, r, c) annot.fa_requires
  in
  let* (rl, rr, rc) = 
    ListM.fold_leftM (fun (rl, rr, rc) constr ->
        let* (rl', rr', rc') = of_constr loc names constr in
        return (rl @ rl', rr @ rr', rc @ rc')
      ) (rl, rr, rc) annot.fa_ensures
  in
  
  let rt = 
    RT.mComputational ra
      (Tools.comps 
         (map RT.mLogical rl @ 
          map RT.mResource rr @ 
          map RT.mConstraint rc)
         RT.I)
  in
  
  let ft =
    Tools.comps 
      (map FT.mComputational a @
       map FT.mLogical l @ 
       map FT.mResource r @ 
       map FT.mConstraint c)
      (FT.I rt)
  in
  return ft



