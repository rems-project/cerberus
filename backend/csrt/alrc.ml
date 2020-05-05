open Binders
open VarTypes

module Types = struct

  type alrc = {
      a : (BaseTypes.t Binders.t) list;
      l : (LogicalSorts.t Binders.t) list;
      r : (Resources.t Binders.t) list;
      c : (LogicalConstraints.t Binders.t) list
    }


  let empty = {a = []; l = []; r = []; c = []}


  let from_type (t : Types.t) = 
    List.fold_left (fun (alrc : alrc) (b : VarTypes.t Binders.t) ->
        match b.bound with
        | A bt -> {alrc with a = alrc.a@[{name = b.name; bound = bt}]}
        | L ls -> {alrc with l = alrc.l@[{name = b.name; bound = ls}]}
        | R re -> {alrc with r = alrc.r@[{name = b.name; bound = re}]}
        | C lc -> {alrc with c = alrc.c@[{name = b.name; bound = lc}]}
      ) empty t

  let to_type alrc = 
    (List.map (fun b -> {name = b.name; bound = A b.bound}) alrc.a) @
    (List.map (fun b -> {name = b.name; bound = L b.bound}) alrc.l) @
    (List.map (fun b -> {name = b.name; bound = R b.bound}) alrc.r) @
    (List.map (fun b -> {name = b.name; bound = C b.bound}) alrc.c)


  let pp alrc = Types.pp (to_type alrc)
  let subst sym with_it alrc = 
    { a = List.map (Binders.subst BaseTypes.subst sym with_it) alrc.a;
      l = List.map (Binders.subst LogicalSorts.subst sym with_it) alrc.l;
      r = List.map (Binders.subst Resources.subst sym with_it) alrc.r;
      c = List.map (Binders.subst LogicalConstraints.subst sym with_it) alrc.c; }  


end

module FunctionTypes = struct

  open Types


  type t = {arguments2 : alrc; return2 : alrc}

  let subst sym with_it ft = 
    { arguments2 = subst sym with_it ft.arguments2; 
      return2 = subst sym with_it ft.return2}

  let pp ft = 
    FunctionTypes.pp 
      (FunctionTypes.make (to_type ft.arguments2) (to_type ft.return2))

  let from_function_type ft = 
    let open FunctionTypes in
    let {arguments;return} = ft in
    { arguments2 = from_type arguments; 
      return2 = from_type return }

  let to_function_type ft = 
    let open FunctionTypes in
    let {arguments2;return2} = ft in
    { arguments = to_type arguments2; 
      return = to_type return2 }

  let updateAargs ft aargs = 
    { ft with arguments2 = { ft.arguments2 with a = aargs }}

  let updateLargs ft largs = 
    { ft with arguments2 = { ft.arguments2 with l = largs }}

  let updateRargs ft rargs = 
    { ft with arguments2 = { ft.arguments2 with r = rargs }}

  let updateCargs ft cargs = 
    { ft with arguments2 = { ft.arguments2 with c = cargs }}


end
