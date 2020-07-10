module CF=Cerb_frontend
open List
open Sym
open Except
open Pp
open Tools
module BT = BaseTypes
module RT = ReturnTypes
module FT = FunctionTypes
open TypeErrors
open IndexTerms
open BaseTypes
open LogicalConstraints
open Resources

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
     let* bts = mapM (bt_of_core_base_type loc) bts in
     return (BT.Tuple bts)
  | BTy_storable -> fail loc (Unsupported !^"BTy_storable")
  | BTy_ctype -> fail loc (Unsupported !^"ctype")




let integerType_constraint loc about it =
  let* min = Memory.integer_value_min loc it in
  let* max = Memory.integer_value_max loc it in
  return (LC ((Num min %<= about) %& (about %<= Num max)))

let integerType loc name it =
  let* constr = integerType_constraint loc (S name) it in
  return ((name,Int), constr)

let floatingType loc =
  fail loc (Unsupported !^"floats")



let rec ctype_aux owned loc name (CF.Ctype.Ctype (annots, ct_)) =
  let open RT in
  let loc = update_loc loc annots in
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
       let points = Points {pointer = S name; pointee = Some (S pointee_name); 
                            typ = ct; size} in
       let t = Logical (pointee_name, Base bt, Resource (points, t)) in
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
  return (RT.Computational (name,bt,t))

let make_pointer_ctype ct = 
  let open CF.Ctype in
  (* fix *)
  let q = {const = false; restrict = false; volatile = false} in
  Ctype ([], Pointer (q, ct))





let rec make_stored_struct loc genv (Tag tag) (spointer : IT.t) o_logical_struct =
  let open RT in
  let* decl = Environment.Global.get_struct_decl loc genv (Tag tag) in
  let rec aux = function
    | (member,bt)::members ->
       let pointer = fresh () in
       let pointer_constraint = 
         LC (IT.S pointer %= IT.MemberOffset (Tag tag,spointer,member)) in
       let this = match o_logical_struct with
         | Some logical_struct -> 
            Some (IT.Member (Tag tag, logical_struct, member))
         | None -> None
       in
       let* (mapping,lbindings,rbindings) = aux members in
       let* (lbindings',rbindings') = match bt with
         | Struct tag2 -> 
            let* (stored_struct,lbindings2,rbindings2) = 
              make_stored_struct loc genv tag2 (S pointer) this in
            return (Logical (pointer, Base Loc, 
                      Constraint (pointer_constraint, lbindings2@@lbindings)),
                    Resource (StoredStruct stored_struct, rbindings2@@rbindings))
         | _ -> 
            let* ct = assoc_err loc member decl.ctypes "make_stored_struct" in
            let* size = Memory.size_of_ctype loc ct in
            let points = {pointer = S pointer; pointee = this; typ = ct ; size} in
            return (Logical (pointer, Base Loc,
                      Constraint (pointer_constraint, I)),
                    Resource (Points points, I))
       in
       return ((member,S pointer)::mapping, lbindings', rbindings')
    | [] -> return ([],I,I)
  in  
  let* (members,lbindings,rbindings) = aux decl.raw in
  let ct = (CF.Ctype.Ctype ([], CF.Ctype.Struct tag)) in
  let* size = Memory.size_of_ctype loc ct in
  let stored = {pointer = spointer; tag = Tag tag; size; members} in
  return (stored, lbindings, rbindings)


let explode_struct_in_binding loc genv (Tag tag) logical_struct binding = 
  let open RT in
  let rec explode_struct loc genv (Tag tag) logical_struct = 
    let* decl = Environment.Global.get_struct_decl loc genv (Tag tag) in
    let rec aux = function
      | (member,bt)::members ->
         let this = IT.Member (Tag tag, logical_struct, member) in
         let* substs = aux members in
         let* substs2 = match bt with
           | Struct tag2 -> explode_struct loc genv tag2 this
           | _ -> return [(fresh (), bt, this)]
         in
         return (substs @ substs2)
      | [] -> return []
    in
    aux decl.raw 
  in
  let* substs = explode_struct loc genv (Tag tag) logical_struct in
  let binding' = 
    fold_right (fun (name,bt,it) binding -> 
        Logical (name,Base bt, instantiate_struct_member {substitute=it;swith=S name} binding)
      ) substs binding
  in
  return binding'



let rec returnType_to_argumentType args return = 
  match args with
  | RT.I -> 
     FT.Return return
  | RT.Computational (name, t, args) -> 
     FT.Computational (name, t, returnType_to_argumentType args return)
  | RT.Logical (name, t, args) -> 
     FT.Logical (name, t, returnType_to_argumentType args return)
  | RT.Resource (t, args) -> 
     FT.Resource (t, returnType_to_argumentType args return)
  | RT.Constraint (t, args) -> 
     FT.Constraint (t, returnType_to_argumentType args return)


(* brittle. revisit later *)
let make_fun_arg_type genv asym loc ct =
  let open RT in
  let ct = make_pointer_ctype ct in

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
       let aname2 = fresh () in
       let rname2 = fresh () in
       let* ((abt,ftt),(rbt,rtt)) = aux true (aname2,rname2) ct in
       let* size = Memory.size_of_ctype loc ct in
       begin match ct with
       | CF.Ctype.Ctype (_, Struct s) ->
          let* (stored,a_lbindings,a_rbindings) = 
            make_stored_struct loc genv (Tag s) (S aname) (Some (S aname2)) in
          let* arg = 
            let* abindings = 
              explode_struct_in_binding loc genv (Tag s) (S aname2)
                (a_lbindings @@ Resource (StoredStruct stored, I) @@ 
                 a_rbindings @@ ftt)
            in
            return (Loc, abindings)
          in
          let* ret = 
            let r_rbindings = RT.subst_var {substitute=aname2;swith=S rname2} a_rbindings in
            let rpoints = StoredStruct stored in
            let* rbindings = 
              explode_struct_in_binding loc genv (Tag s) (S rname2)
              (Resource (rpoints,I) @@ r_rbindings @@ rtt)
            in
            return (Loc, rbindings)
          in
          return (arg, ret)
       | _ ->
          let* arg = 
            let apoints = Points {pointer = S aname; pointee = Some (S aname2); 
                                  typ = ct; size}  in
            return (Loc, Logical (aname2, Base abt, Resource (apoints, ftt)))
          in
          let* ret = 
            let rpoints = Points {pointer = S aname; pointee = Some (S rname2); 
                                  typ = ct; size} in
            return (Loc, Logical (rname2, Base rbt, Resource (rpoints, rtt)))
          in
          return (arg, ret)
       end
    (* fix *)
    | Atomic ct -> 
       aux pointed (aname,rname) ct
    | Struct tag -> 
       let* decl = Environment.Global.get_struct_decl loc genv (Tag tag) in
       let ftt = RT.subst_var {substitute=decl.closed_type.sbinder; swith=S aname }
                   decl.closed_type.souter in
       let rtt = RT.subst_var {substitute=decl.closed_type.sbinder; swith=S rname }
                   decl.closed_type.souter in
       let arg = (Struct (Tag tag), ftt) in
       let ret = (Struct (Tag tag), rtt) in
       return (arg, ret)
    | Basic (Floating _) -> floatingType loc 
    | Union sym -> fail loc (Unsupported !^"todo: union types")
    | Function _ -> fail loc (Unsupported !^"function pointers")
  in

  let* ((abt,arg),(_,ret)) = aux false (asym, fresh_pretty "return") ct in
  
  (* let arg = fun rt -> returnType_to_argumentType rt 
   *                       (Computational (asym, abt, ftt)) in *)
  return (Computational (asym, abt, arg),ret)



let make_fun_spec loc genv attrs args ret_ctype = 
  let open FT in
  let open RT in
  let* (arguments, returns, names) = 
    fold_leftM (fun (args,returns,names) (msym, ct) ->
        let name = match msym with
          | Some sym -> sym
          | None -> Sym.fresh ()
        in
        let* (arg,ret) = make_fun_arg_type genv name loc ct in
        return (args @@ arg, returns @@ ret, name::names)
      ) (I, I, []) args
  in
  let* ret = ctype true loc (fresh ()) ret_ctype in
  let ftyp = returnType_to_argumentType arguments (ret @@ returns) in
  return ftyp

