module CF=Cerb_frontend
open List
open Sym
open Except
open Pp
(* open Tools *)
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
  let* (min,max) = Memory.integer_range loc it in
  return (LC ((Num min %<= about) %& (about %<= Num max)))


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
    aux decl.raw 
  in
  let* substs = explode_struct loc global (Tag tag) logical_struct in
  let binding' = 
    fold_right (fun (name,bt,it) binding -> 
        Logical (name,Base bt, 
                 instantiate_struct_member_l {s=it;swith=S name} binding)
      ) substs binding
  in
  return binding'



let rec logical_returnType_to_argumentType 
          (args : RT.l)
          (more_args : FT.t)
        : FT.t = 
  match args with
  | RT.I -> 
     more_args
  (* | RT.Computational (name, t, args) -> 
   *    FT.Computational (name, t, returnType_to_argumentType args return) *)
  | RT.Logical (name, t, args) -> 
     FT.Logical (name, t, logical_returnType_to_argumentType args more_args)
  | RT.Resource (t, args) -> 
     FT.Resource (t, logical_returnType_to_argumentType args more_args)
  | RT.Constraint (t, args) -> 
     FT.Constraint (t, logical_returnType_to_argumentType args more_args)


