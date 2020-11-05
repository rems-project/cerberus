open Pp
open Environment
open Resultat
open TypeErrors
module Loc = Locations
module L = Local
module RE = Resources
module LS = LogicalSorts

module SymSet = Set.Make(Sym)



module VarEquivalenceClass = struct

  let counter = ref 0

  type t = 
    { representative : Sym.t;
      sort: LS.t;
      lelements : SymSet.t;
      celements : SymSet.t;
    }


  let ls_prefix (LS.Base bt) = 
    match bt with
    | Unit -> "u"
    | Bool -> "b"
    | Integer -> "i"
    | Loc -> "l"
    | Array -> "a"
    | List _ -> "l"
    | Tuple _ -> "p"
    | Struct _ -> "s"
    | FunctionPointer _ -> "f"

  let name veclass = 
    match SymSet.find_first_opt Sym.named veclass.celements with
    | Some s -> s
    | None -> 
       match SymSet.find_first_opt Sym.named veclass.lelements with
       | Some s -> s
       | None -> veclass.representative

  let print_name veclass = 
    match SymSet.find_first_opt Sym.named veclass.celements with
    | Some s -> s
    | None -> 
       match SymSet.find_first_opt Sym.named veclass.lelements with
       | Some s -> s
       | None -> veclass.representative

  let new_class l ls = 
    counter := !counter + 1;
    { representative = l;
      sort = ls;
      lelements = SymSet.singleton l;
      celements = SymSet.empty;
    }

  let insert_l l veclass = 
    { veclass with lelements = SymSet.add l veclass.lelements }

  let insert_c c veclass = 
    { veclass with celements = SymSet.add c veclass.celements }

  let o_insert_c o_c veclass = 
    match o_c with
    | None -> veclass
    | Some c -> insert_c c veclass

  let classify loc {local; global} classes l ls o_c : t list m =
    let rec aux = function
      | veclass :: veclasses ->
         let* found_class = 
           if not (LS.equal veclass.sort ls) then return false else
             Solver.equal loc {local; global} 
               (S veclass.representative) (S l)
         in
         if found_class then 
           return (o_insert_c o_c (insert_l l veclass) :: veclasses) 
         else 
           let* veclasses' = aux veclasses in
           return (veclass :: veclasses')
      | [] -> 
         return [o_insert_c o_c (new_class l ls)]
    in
    aux classes

  

end
  


open VarEquivalenceClass



let all_it_names_good it = 
  SymSet.for_all (fun s -> Sym.named s) (IT.vars_in it)

let make loc {local; global} oconsts : Pp.document m = 
  let c = L.all_computational local in
  let l = L.all_logical local in
  let r = L.all_resources local in
  let* veclasses = 
    let* with_l = 
      ListM.fold_leftM (fun classes (l, ls) ->
          classify loc {local; global} classes l ls None
        ) [] l
    in
    let* with_c = 
      ListM.fold_leftM (fun classes (c, (l, bt)) ->
          classify loc {local; global} classes l (LS.Base bt) (Some c)
        ) with_l c
    in
    return with_c
  in
  let print_substs =
    List.fold_right (fun veclass substs ->
      let name = print_name veclass in
      let to_substitute = SymSet.union veclass.celements veclass.lelements in
      SymSet.fold (fun sym substs ->
          Subst.{ before = sym; after = name } :: substs
        ) to_substitute substs 
      ) veclasses []
  in
  
  let (pped_resources, mentioned_lvars) = 
    List.fold_right (fun (_,r) (acc_pp, acc_mentioned) ->
        let mentioned = SymSet.diff (RE.vars_in r) (IT.vars_in (RE.pointer r)) in
        let pp = match RE.subst_vars print_substs r with
          | RE.Uninit u -> 
             IT.pp ~quote:false u.RE.pointer ^^^ !^"uninitialised" ^^^
               Pp.c_comment (
                   !^"of size" ^^^ Z.pp u.size
                 )
          | RE.Points p -> 
             IT.pp ~quote:false p.RE.pointer ^^^
               equals ^^ equals ^^^ Sym.pp p.pointee ^^^
                 Pp.c_comment (
                     !^"of size" ^^^ Z.pp p.size
                   )
        in
        (pp :: acc_pp, SymSet.union acc_mentioned mentioned)
      ) r ([], SymSet.empty)
  in

  let* (lvar_info, _) = 
    let consts = Option.value [] oconsts in
    ListM.fold_rightM (fun s (acc_pp,acc_done) ->
        let print_name = Sym.substs print_substs s in
        if SymSet.mem print_name acc_done 
        then return (acc_pp, acc_done)
        else
          let* ls = L.get_l loc s local in
          let ov = List.assoc_opt s consts in
          let acc_pp = (print_name, ls, ov) :: acc_pp in
          let acc_done = SymSet.add print_name acc_done in
          return (acc_pp, acc_done)
      ) (SymSet.elements mentioned_lvars) ([], SymSet.empty)
  in

  let pped_lvars = 
    List.map (fun (name,ls,ov) ->
        let val_pp = match ov with
        | Some v (* when not (LS.equal ls (LS.Base (BT.Loc))) *) -> 
           space ^^ !^":=" ^^^ !^v
        | _ -> Pp.empty
        in
        typ (Sym.pp name) (LogicalSorts.pp false ls) ^^ val_pp
      ) lvar_info
  in

  let pp = 
    flow hardline (pped_resources @ pped_lvars)
  in
  
  return pp



