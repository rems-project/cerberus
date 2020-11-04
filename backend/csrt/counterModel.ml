open Pp
open Environment
open Resultat
open TypeErrors
module Loc = Locations
module L = Local
module RE = Resources
module LS = LogicalSorts

module SymSet = Set.Make(Sym)



let for_pointer (loc: Loc.t) {local;global} pointer_it
    : ((Sym.t * RE.t) option) m = 
  let* points = 
    Local.filterM (fun name vb ->
        match vb with 
        | VariableBinding.Resource re -> 
           let* holds = Solver.equal loc {local;global} pointer_it (RE.pointer re) in
           return (if holds then Some (name, re) else None)
        | _ -> 
           return None
      ) local
  in
  Tools.at_most_one loc !^"multiple points-to for same pointer" points


let equal_lvars loc {local;global} lname =
  L.filterM (fun name b ->
      match b with
      | VariableBinding.Logical ls -> 
         let* equal = Solver.equal loc {local; global} (S lname) (S name) in
         return (if equal then Some (name, ls) else None)
      | _ -> 
         return None
    ) local




type lvar_equivalence_classes = (Sym.t * LS.t * SymSet.t) list

let lvar_equivalence_classes loc {local; global} lvars : lvar_equivalence_classes m = 
  ListM.fold_leftM (fun classes (l, ls) ->
      let rec aux = function
        | (representative, ls', clss) :: classes ->
           if LS.equal ls ls' then
             let* equal = Solver.equal loc {local; global} (S l) (S representative) in
             if equal then
               let clss' = SymSet.add l clss in
               let representative' = 
                 if Sym.named representative 
                 then representative else l
               in
               return ((representative', ls', clss') :: classes)
             else 
               let* classes' = aux classes in
               return ((representative, ls', clss) :: classes')
           else
             let* classes' = aux classes in
             return ((representative, ls', clss) :: classes')
        | [] -> 
           return [(l, ls, SymSet.singleton l)]
      in
      aux classes
    ) [] lvars


let find_good_name_subst loc lvar_eq_classes l =
  let rec aux = function
    | (representative, _ls, clss) :: _ when SymSet.mem l clss ->
       return representative
    | _ :: rest -> aux rest
    | [] -> fail loc (Internal (!^"error finding equivalence class for" ^^^ Sym.pp l))
  in
  let* representative = aux lvar_eq_classes in
  return (Subst.{before = l; after = representative})


let dedup symlist = SymSet.elements (SymSet.of_list symlist)


let bigunion = List.fold_left SymSet.union SymSet.empty

let all_it_names_good it = 
  SymSet.for_all (fun s -> Sym.named s) (IT.vars_in it)





let make loc {local; global} oconsts : Pp.document m = 
  let cvars = L.all_computational local in
  let lvars = L.all_logical local in
  let resources = L.all_resources local in
  let* substs = 
    let* lvar_classes = lvar_equivalence_classes loc {local; global} lvars in
    let relevant_lvars = 
      let lvarses1 = List.map (fun (_,r) -> (RE.vars_in r)) resources in
      let lvarses2 = List.map (fun (_,(l,_)) -> SymSet.singleton l) cvars in
      bigunion (lvarses1 @ lvarses2)
    in
    ListM.mapM (find_good_name_subst loc lvar_classes)
      (SymSet.elements relevant_lvars) 
  in
  let resources = 
    List.map (fun (rname,r) -> (rname, RE.subst_vars substs r)) resources
  in
  let cvars = 
    List.map (fun (c,(l,bt)) -> (c, (Sym.substs substs l, bt))) cvars
  in
  let* cvars = 
    ListM.fold_rightM (fun (c,(l,bt)) vars ->
        if Sym.named c && bt = BT.Loc then
          let* o_re = for_pointer loc {local; global} (S l) in
          return ((c, (l, bt), o_re) :: vars)
        else return vars
      ) cvars []
  in
  let mentioned_resources = 
    List.fold_left (fun acc (c, _, o_r) ->
        match o_r with
        | None -> acc
        | Some (rname, _) ->
           let already_mentioned = Option.value [] (SymMap.find_opt rname acc) in
           SymMap.add rname (c :: already_mentioned) acc
      ) SymMap.empty cvars
  in

  let (pped_cvars, mentioned_lvars) = 
    List.fold_right (fun (s, (lname, bt), o_re) (acc_pp, acc_mentioned) ->
        begin match o_re with
        | Some (_, RE.Uninit u) -> 
           let pp = 
             Sym.pp s ^^^
               !^"at location" ^^^ IT.pp ~quote:false u.RE.pointer ^^^
                 !^"uninitialised" ^^^ Pp.c_comment (!^"of size" ^^^ Z.pp u.size)
           in
           let mentioned = 
             SymSet.union (IT.vars_in u.RE.pointer) 
               acc_mentioned 
           in
           (pp :: acc_pp, mentioned)
        | Some (_, RE.Points p) -> 
           let pp = 
             Sym.pp s ^^^
               !^"at location" ^^^ IT.pp ~quote:false p.RE.pointer ^^^
                 equals ^^^ Sym.pp p.pointee ^^^
                   Pp.c_comment (!^"size" ^^^ Z.pp p.size)
           in
           let mentioned = 
             SymSet.add p.pointee
               (SymSet.union (IT.vars_in p.RE.pointer) acc_mentioned)
           in
           (pp :: acc_pp, mentioned)
        | None ->
           let pp = 
             Sym.pp s ^^^
               !^"at location" ^^^ Sym.pp lname ^^^
                 parens (!^"no ownership of memory")
           in
           (pp :: acc_pp, acc_mentioned)
        end
      ) cvars ([], SymSet.empty)
  in

  let unmentioned_resources = 
    List.filter (fun (name,re) ->
        Option.is_none (SymMap.find_opt name mentioned_resources)
      ) 
      resources
  in

  let (pped_extra_memory, mentioned_lvars) = 
    List.fold_right (fun re (acc_pp, acc_mentioned) ->
        match re with
        | RE.Uninit u -> 
           let pp = 
             IT.pp ~quote:false u.RE.pointer ^^^ 
               !^"uninitialised" ^^^
                 Pp.c_comment (!^"size" ^^^ Z.pp u.size)
           in
           let mentioned = 
             SymSet.union (IT.vars_in u.RE.pointer) acc_mentioned 
           in
           (pp :: acc_pp, mentioned)
        | RE.Points p -> 
           let pp = 
             IT.pp ~quote:false p.RE.pointer ^^^ 
               equals ^^^ Sym.pp p.pointee ^^^
                 Pp.c_comment (!^"size" ^^^ Z.pp p.size)
           in
           let mentioned = 
             SymSet.add p.pointee
               (SymSet.union (IT.vars_in p.RE.pointer) acc_mentioned)
           in
           (pp :: acc_pp, mentioned)
      ) 
      (List.map snd unmentioned_resources) ([], mentioned_lvars)
  in



  let aliases = 
    List.filter_map (fun (_,vars) -> 
        if List.length vars > 1 then Some vars else None
      ) (SymMap.bindings mentioned_resources)
  in

  let* lvar_info = 
    let consts = Option.value [] oconsts in
    ListM.mapM (fun s ->
        let* ls = L.get_l loc s local in
        let ov = List.assoc_opt s consts in
        return (s, ls, ov)
      ) (SymSet.elements mentioned_lvars)
  in

  let pped_lvars = 
    List.map (fun (name,ls,ov) ->
        match ov with
        | None -> typ (Sym.pp name) (LogicalSorts.pp false ls)
        | Some v ->
           typ (Sym.pp name) (LogicalSorts.pp false ls) ^^^
             !^":=" ^^^ !^v
      ) lvar_info
  in

  let pped_aliases = match aliases with
    | []-> Pp.empty
    | _ ->
       flow_map (comma ^^ break 1) (fun l ->
             pp_list Sym.pp l ^^^ !^"alias"
         ) aliases
  in
  let pp = 
    flow (comma ^^ hardline) 
      (pped_cvars @ pped_extra_memory @ pped_lvars) ^^^
      pped_aliases
  in

  return pp
