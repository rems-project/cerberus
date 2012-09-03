exception TODO of Ast.l * string

module Duplicate(S : Set.S) = struct

type dups = 
  | No_dups of S.t
  | Has_dups of S.elt

let duplicates (x : S.elt list) : dups =
  let rec f x acc = match x with
    | [] -> No_dups(acc)
    | s::rest ->
        if S.mem s acc then
          Has_dups(s)
        else
          f rest (S.add s acc)
  in
    f x S.empty
end

let rec compare_list f l1 l2 = 
  match (l1,l2) with
    | ([],[]) -> 0
    | (_,[]) -> 1
    | ([],_) -> -1
    | (x::l1,y::l2) ->
        let c = f x y in
          if c = 0 then
            compare_list f l1 l2
          else
            c
              
let map_changed f l =
  let rec g = function
    | [] -> ([],false)
    | x::y ->
        let (r,c) = g y in
          match f x with
            | None -> (x::r,c)
            | Some(x') -> (x'::r,true)
  in
  let (r,c) = g l in
    if c then
      Some(r)
    else
      None

let option_map f = function
  | None -> None
  | Some(o) -> Some(f o)

let changed2 f g x h y =
  match (g x, h y) with
    | (None,None) -> None
    | (Some(x'),None) -> Some(f x' y)
    | (None,Some(y')) -> Some(f x y')
    | (Some(x'),Some(y')) -> Some(f x' y')

