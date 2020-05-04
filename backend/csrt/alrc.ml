open Binders
open VarTypes

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
let subst alrc sym with_it = 
  { a = List.map (Binders.subst BaseTypes.subst sym with_it) alrc.a;
    l = List.map (Binders.subst LogicalSorts.subst sym with_it) alrc.l;
    r = List.map (Binders.subst Resources.subst sym with_it) alrc.r;
    c = List.map (Binders.subst LogicalConstraints.subst sym with_it) alrc.c; }
  



type ft = {args : alrc; ret : alrc}

let subst_ft sym with_it ft = 
  { args = subst ft.args sym with_it; 
    ret = subst ft.ret sym with_it }

let pp_ft ft = 
  FunctionTypes.pp (FunctionTypes.make (to_type ft.args) (to_type ft.ret))

let ft_from_function_type (FunctionTypes.F {arguments;return}) = 
  { args = from_type arguments; ret = from_type return }

