module CF=Cerb_frontend
open List
open Sym
open Result
open Pp
(* open Tools *)
module BT = BaseTypes
module RT = ReturnTypes
module FT = ArgumentTypes.Make(RT)
module LT = ArgumentTypes.Make(NoReturn)
open TypeErrors
open IndexTerms
open BaseTypes
open LogicalConstraints
open Resources


module SymSet = Set.Make(Sym)






(* convert from other types *)

let bt_of_core_object_type loc ot =
  let open CF.Core in
  match ot with
  | OTy_integer -> return BT.Int
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


let integerType loc name it =
  let* (min,max) = Memory.integer_range loc it in
  let* constr = integerType_constraint loc (S name) it in
  return ((name,Int), constr)

let floatingType loc =
  fail loc (Unsupported !^"floats")



let rec ctype_aux owned loc name (CF.Ctype.Ctype (annots, ct_)) =
  let open RT in
  let loc = Loc.update loc annots in
  match ct_ with
  | Void -> 
     return ((name, BT.Unit), I)
  | Basic (Integer it) -> 
     let* ((name,bt), constr) = integerType loc name it in
     return ((name, bt), Constraint (constr, I))
  | Array (ct, _maybe_integer) -> 
     return ((name,BT.Array), I)
  | Pointer (_qualifiers, ct) ->
     if owned then
       let* ((pointee_name,bt),t) = ctype_aux owned loc (fresh ()) ct in
       let* size = Memory.size_of_ctype loc ct in
       let points = Points {pointer = S name; pointee = Some (S pointee_name); size} in
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







let explode_struct_in_binding loc global (Tag tag) logical_struct binding = 
  let open RT in
  let rec explode_struct loc global (Tag tag) logical_struct = 
    let* decl = Global.get_struct_decl loc global (Tag tag) in
    let rec aux = function
      | (member,bt)::members ->
         let this = IT.Member (Tag tag, logical_struct, member) in
         let* substs = aux members in
         let* substs2 = match bt with
           | Struct tag2 -> explode_struct loc global tag2 this
           | _ -> return [(fresh (), bt, this)]
         in
         return (substs @ substs2)
      | [] -> return []
    in
    aux decl.Global.raw 
  in
  let* substs = explode_struct loc global (Tag tag) logical_struct in
  let binding' = 
    fold_right (fun (name,bt,it) binding -> 
        Logical ((name,Base bt), 
                 instantiate_struct_member_l {s=it;swith=S name} binding)
      ) substs binding
  in
  return binding'



let rec lrt_to_at (lrt : RT.l) (rest : FT.t) : FT.t = 
  match lrt with
  | RT.I -> rest
  | RT.Logical ((name, t), args) -> FT.Logical ((name, t), lrt_to_at args rest)
  | RT.Resource (t, args) -> FT.Resource (t, lrt_to_at args rest)
  | RT.Constraint (t, args) -> FT.Constraint (t, lrt_to_at args rest)

let rt_to_at rt rest = 
  let (RT.Computational ((name, t), lrt)) = rt in
  FT.Computational ((name, t), lrt_to_at lrt rest)


let rec lrt_to_lt (lrt : RT.l) : LT.t = 
  match lrt with
  | RT.I -> I False
  | RT.Logical ((name, t), args) -> LT.Logical ((name, t), lrt_to_lt args)
  | RT.Resource (t, args) -> LT.Resource (t, lrt_to_lt args)
  | RT.Constraint (t, args) -> LT.Constraint (t, lrt_to_lt args)

let rt_to_lt rt = 
  let (RT.Computational ((name, t), lrt)) = rt in
  LT.Computational ((name, t), lrt_to_lt lrt)



let struct_decl loc tag fields struct_decls = 
  let open Sym in
  let open BaseTypes in
  let open RT in

  let rec aux thisstruct loc (acc_members,acc_sopen,acc_sclosed,acc_cts) member ct =
    let (CF.Ctype.Ctype (annots, ct_)) = ct in
    let loc = Loc.update loc annots in
    match ct_ with
    | Void -> 
       return ((member,Unit)::acc_members, 
               acc_sopen, 
               acc_sclosed, 
               (member,ct)::acc_cts)
    | Basic (Integer it) -> 
       let* lc1 = integerType_constraint loc (Member (tag, S thisstruct, member)) it in
       let spec_name = fresh () in
       let* lc2 = integerType_constraint loc (S spec_name) it in
       return ((member,Int)::acc_members, 
               Constraint (lc1,acc_sopen), 
               Constraint (lc1,acc_sclosed),
               (member,ct)::acc_cts)
    | Array (ct, _maybe_integer) -> 
       return ((member,Array)::acc_members, 
               acc_sopen, 
               acc_sclosed, 
               (member,ct):: acc_cts)
    | Pointer (_qualifiers, ct) -> 
       return ((member,Loc)::acc_members, 
               acc_sopen, 
               acc_sclosed, 
               (member,ct)::acc_cts)
    (* fix *)
    | Atomic ct -> 
       aux thisstruct loc (acc_members,acc_sopen,acc_sclosed,acc_cts) member ct
    | Struct tag2 -> 
       let* decl = Global.get_struct_decl loc struct_decls (Tag tag2) in
       let sopen = 
         let subst = Subst.{s=decl.Global.open_type.sbinder; 
                            swith=IT.Member (tag, S thisstruct, member)} in
         RT.subst_var_l subst decl.open_type.souter
       in
       let sclosed = 
         let subst = Subst.{s=decl.closed_type.sbinder; 
                            swith=IT.Member (tag, S thisstruct, member)} in
         RT.subst_var_l subst decl.closed_type.souter
       in
       return ((member, Struct (Tag tag2))::acc_members, 
               sopen@@acc_sopen, 
               sclosed@@acc_sclosed,
               (member, ct)::acc_cts)
    | Basic (Floating _) -> 
       fail loc (Unsupported !^"todo: union types")
    | Union sym -> 
       fail loc (Unsupported !^"todo: union types")
    | Function _ -> 
       fail loc (Unsupported !^"function pointers")
  in
  let thisstruct = fresh () in
  let* (raw,sopen,sclosed,ctypes) = 
    List.fold_right (fun (id, (_attributes, _qualifier, ct)) acc ->
        let* acc = acc in
        aux thisstruct loc acc (Member (Id.s id)) ct
      ) fields (return ([],I,I,[])) 
  in
  let open Global in
  let open_type = {sbinder = thisstruct; souter=sopen } in
  let closed_type = {sbinder = thisstruct; souter=sclosed } in
  return { raw; open_type; closed_type; ctypes }






(* brittle. revisit later *)
let make_fun_arg_type lift struct_decls asym loc ct =
  let open RT in
  let ct = if lift then make_pointer_ctype ct else ct in

  let rec aux pointed (aname,rname) (CF.Ctype.Ctype (annots, ct_)) =
    match ct_ with
    | Void -> 
       let arg = (BT.Unit, I) in
       let ret = (BT.Unit, I) in
       return (arg,ret)
    | Basic (Integer it) -> 
       let* ((_,abt), aconstr) = integerType loc aname it in
       let* ((_,rbt), rconstr) = integerType loc rname it in
       let arg = (abt, Constraint (aconstr,I)) in
       let ret = (rbt, Constraint (rconstr,I)) in
       return (arg, ret)
    | Array (ct, _maybe_integer) ->
       let arg = (Array, I) in
       let ret = (Array, I) in
       return (arg, ret)
    | Pointer (_qualifiers, ct) ->
       let aname2 = Sym.fresh () in
       let rname2 = Sym.fresh () in
       let* ((abt,ftt),(rbt,rtt)) = aux true (aname2,rname2) ct in
       let* size = try Memory.size_of_ctype loc ct with _ -> return Num.zero in
       begin match ct with
       | CF.Ctype.Ctype (_, Struct s) ->
          let* arg = 
            let* (stored,lbindings,rbindings) = 
              ResourceInference.store_struct loc struct_decls (Tag s) (S aname) (Some (S aname2)) in
            let* abindings = 
              explode_struct_in_binding loc struct_decls (Tag s) (S aname2)
                (lbindings @@ Resource (StoredStruct stored, I) @@ 
                 rbindings @@ ftt)
            in
            return (Loc, abindings)
          in
          let* ret = 
            let* (stored,lbindings,rbindings) = 
              ResourceInference.store_struct loc struct_decls (Tag s) (S aname) (Some (S rname2)) in
            let* abindings = 
              explode_struct_in_binding loc struct_decls (Tag s) (S rname2)
                (lbindings @@ Resource (StoredStruct stored, I) @@ 
                 rbindings @@ rtt)
            in
            return (Loc, abindings)
          in
          return (arg, ret)
       | _ ->
          let* arg = 
            let apoints = RE.Points {pointer = S aname; pointee = Some (S aname2); size}  in
            return (Loc, Logical ((aname2, Base abt), Resource (apoints, ftt)))
          in
          let* ret = 
            let rpoints = RE.Points {pointer = S aname; pointee = Some (S rname2); size} in
            return (Loc, Logical ((rname2, Base rbt), Resource (rpoints, rtt)))
          in
          return (arg, ret)
       end
    (* fix *)
    | Atomic ct -> 
       aux pointed (aname,rname) ct
    | Struct tag -> 
       let* decl = Global.get_struct_decl loc struct_decls (Tag tag) in
       let ftt = RT.subst_var_l {s=decl.closed_type.sbinder; swith=S aname }
                   decl.closed_type.souter in
       let rtt = RT.subst_var_l {s=decl.closed_type.sbinder; swith=S rname }
                   decl.closed_type.souter in
       let arg = (Struct (Tag tag), ftt) in
       let ret = (Struct (Tag tag), rtt) in
       return (arg, ret)
    | Basic (Floating _) -> floatingType loc 
    | Union sym -> fail loc (Unsupported !^"todo: union types")
    | Function _ -> fail loc (Unsupported !^"function pointers")
  in

  let* ((abt,arg),(_,ret)) = aux false (asym, Sym.fresh_pretty "return") ct in
  
  let ftt = lrt_to_at arg in
  let arg = Tools.comp (FT.mComputational asym abt) ftt in
  return ((arg : FT.t -> FT.t),(ret : RT.l))


let make_name = function
  | Some (Symbol (_,_,Some name)) -> Sym.fresh_pretty (name ^ "_l")
  | Some (Symbol (_,_,None)) -> Sym.fresh ()
  | None -> Sym.fresh ()

let make_fun_spec loc genv attrs args ret_ctype = 
  let open FT in
  let open RT in
  let* (arguments, returns) = 
    ListM.fold_leftM (fun (args,returns) (msym, ct) ->
        let name = make_name msym in
        let* (arg,ret) = make_fun_arg_type true genv name loc ct in
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
        let* (arg,_) = make_fun_arg_type by_pointer genv name loc ct in
        let args = Tools.comp args arg in
        return args
      ) 
      (fun ft -> ft) args
  in
  let ftyp = arguments (I (RT.Computational ((fresh (), BT.Unit), I))) in
  return ftyp

let make_return_esave_spec ftyp =
  rt_to_lt (FT.get_return ftyp)
