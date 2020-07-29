module RE = Resources
module IT = IndexTerms
module BT = BaseTypes
module LC = LogicalConstraints

open Except
open Tools
open Pp


type 'a t_points = 
  { pointer: IT.t; 
    pointee: 'a option; 
    typ: CF.Ctype.ctype;
    size: Num.t 
  }

type 'a t_stored_struct =
  { pointer: IT.t;
    tag: BT.tag;
    size: Num.t;
    members: ((BT.member * IT.t) * ('a t) option) list 
  }

and 'a t = 
  | TPoints of 'a t_points
  | TStoredStruct of 'a t_stored_struct

type tree = IT.t t
type merge_tree = ((LC.t * IT.t) list) t


let trees_of_map loc global equality 
                 (rvars : RE.resource SymMap.t) 
    : ((Sym.t * tree) list) m =


  let find_struct_child tag (member,cpointer) = 
    let* decl = Global.get_struct_decl loc global tag in
    let* bt = assoc_err loc member decl.raw
                        (TypeErrors.Unreachable !^"remove_owned_subtree") in
    let* found = 
      symmap_foldM (fun sym' resource' found ->
          match bt, resource' with
          | BT.Struct tag, RE.StoredStruct s when tag = s.tag ->  
             let* equal = equality cpointer (RE.pointer resource') in
             if equal 
             then return ((sym',resource')::found)
             else return found
          | Struct tag, _ ->
             return found
          | _, _ ->
             let* equal = equality cpointer (RE.pointer resource') in
             if equal 
             then return ((sym',resource')::found)
             else return found
        ) rvars []
    in
    match found with
    | [] -> return None
    | [r] -> return (Some r)
    | _ -> fail loc (TypeErrors.Unreachable !^"pointer owned multiple times")
  in

  let children resource = 
    match resource with
    | RE.Points _ -> return []
    | RE.StoredStruct s ->
       let* children = mapM (find_struct_child s.tag) s.members in
       return (List.filter_map (Option.map fst) children)
  in

  let* roots = 
    let* m =
      symmap_filter (fun sym resource ->
          symmap_for_all (fun sym' resource' ->
              let* children = children resource' in
              return (not (List.mem sym children))
            ) rvars
        ) rvars
    in
    return (SymMap.bindings m)
  in

  let rec make_tree = function
    | RE.Points p -> 
       let t_points = 
         { pointer = p.pointer;
           pointee = p.pointee;
           typ = p.typ;
           size = p.size; }
       in
       return (TPoints t_points)
    | RE.StoredStruct s -> 
       let* members = 
         mapM (fun (member,cpointer) ->
             let* found = find_struct_child s.tag (member,cpointer) in
             match found with
               | None -> return ((member,cpointer),None)
               | Some (_,r) -> 
                  let* subtree = make_tree r in
                  return ((member,cpointer),Some subtree) 
           )
           s.members
       in
       let t_stored_struct = 
         { pointer = s.pointer;
           tag = s.tag;
           size = s.size;
           members} 
       in
       return (TStoredStruct t_stored_struct)
  in

  let make_trees roots = 
    mapM (fun (sym,root) -> 
        let* tree = make_tree root in
        return (sym,tree)
      ) roots 
  in

  make_trees roots



let rec merge_tree_of_tree cond (tree : tree) : merge_tree =
  match tree with
  | TPoints p ->
     TPoints
       { pointer = p.pointer;
         pointee = Option.map (fun it -> [(cond,it)]) p.pointee;
         typ = p.typ;
         size = p.size; }
  | TStoredStruct s ->
     let members = 
       List.map (fun ((m,it),t) ->
           ((m,it),Option.map (fun t -> merge_tree_of_tree cond t) t)
         ) s.members
     in
     TStoredStruct
       { pointer = s.pointer;
         tag = s.tag;
         size = s.size;
         members }
         

let merge_trees_of_map loc global equality (cond, m) 
    : ((Sym.t * merge_tree) list) m = 
  let* trees = trees_of_map loc global equality m in
  let merge_trees = 
    List.map (fun (sym,tree) -> (sym,merge_tree_of_tree cond tree)) trees in
  return merge_trees



let merge_trees_to_trees loc (trees : merge_tree list) = 
       
  let rec merge_tree_to_tree = function
    | TPoints tp ->
       let* (pointee,acc) = match tp.pointee with
         | Some p -> 
            let newname = Sym.fresh () in
            let* bt = Conversions.bt_of_ctype loc tp.typ in
            return (Some (IT.S newname), [(newname,bt,p)])
         | None -> 
            return (None, [])
       in
       return (TPoints {tp with pointee}, acc)
    | TStoredStruct s ->
       let* (members,acc) =
         fold_leftM (fun (members,acc) ((member,it),child) ->
             let* (child,acc') = match child with
               | Some c -> 
                  let* (child,acc') = merge_tree_to_tree c in
                  return (Some child, acc')
               | None -> 
                  return (None,[])
             in
             return (members@[((member,it),child)],acc@acc')
           ) ([],[]) s.members
       in
       return (TStoredStruct {s with members}, acc)
  in

  let rec merge_trees_to_trees = function
    | [] -> 
       return ([],[])
    | mtree::mtrees -> 
       let* (tree,acc) = merge_tree_to_tree mtree in
       let* (trees,acc') = merge_trees_to_trees mtrees in
       return (tree::trees,acc@acc')       
  in

  merge_trees_to_trees trees



let trees_to_map (trees : tree list) : RE.t SymMap.t = 

  let rec tree_to_map acc = function
    | TPoints tp ->
       let r = 
         RE.Points 
           { pointer = tp.pointer;
             pointee = tp.pointee;
             typ = tp.typ;
             size = tp.size }
       in
       SymMap.add (Sym.fresh ()) r acc
    | TStoredStruct s ->
       let (members,children) = List.split s.members in
       let r = 
         RE.StoredStruct 
           { pointer = s.pointer;
             members = members;
             tag = s.tag;
             size = s.size;
           }
       in
       let acc = 
         List.fold_left (fun acc mchild ->
             match mchild with
             | Some child -> tree_to_map acc child
             | None -> acc
           ) acc children
       in
       SymMap.add (Sym.fresh ()) r acc
  in

  let rec trees_to_map acc = function
    | [] -> acc
    | tree::trees -> trees_to_map (tree_to_map acc tree) trees
  in

  trees_to_map SymMap.empty trees




let rec merge_merge_trees loc mtree1 mtree2 = 
  match mtree1, mtree2 with
  | TPoints p1, TPoints p2 
       when CF.Ctype.ctypeEqual p1.typ p2.typ && Num.equal p1.size p2.size ->
     begin match p1.pointee, p2.pointee with
     | None, None -> 
        return (TPoints p1)
     | Some cp1, Some cp2 ->
        return (TPoints { p1 with pointee = Some (cp1@cp2) })
     | _ -> 
        fail loc (TypeErrors.Generic_error !^"incompatible resources")
     end
  | TStoredStruct s1, TStoredStruct s2
       when s1.tag = s2.tag && Num.equal s1.size s2.size ->
     let rec merge_members ms1 ms2 = 
       match ms1, ms2 with
       | ((m1,it1),None)::ms1, ((m2,it2),None)::ms2 when m1 = m2 ->
          let* ms = merge_members ms1 ms2 in
          return (((m1,it1),None)::ms)
       | ((m1,it1),Some t1)::ms1, ((m2,it2),Some t2)::ms2 when m1 = m2 ->
          let* t = merge_merge_trees loc t1 t2 in
          let* ms = merge_members ms1 ms2 in
          return (((m1,it1),Some t)::ms)
       | [], [] -> 
          return []
       | _ ->
          fail loc (TypeErrors.Generic_error !^"incompatible resources")
     in
     let* members = merge_members s1.members s2.members in
     return (TStoredStruct { s1 with members } )
  | _ ->
     fail loc (TypeErrors.Generic_error !^"incompatible resources")




