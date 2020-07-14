
module CF = Cerb_frontend
module CB = Cerb_backend

module StringMap = Map.Make(String)


let concat_map (f : 'a -> 'b list) (xs : 'a list) : 'b list = 
    List.concat (List.map f xs)


let id = fun x -> x

let comp (f : 'b -> 'c) (g : 'a -> 'b) (x : 'a) : 'c = f (g (x))
let rec comps (fs : ('a -> 'a) list) (a : 'a) : 'a =
  match fs with
  | [] -> a
  | f :: fs -> f (comps fs a)



let is_some = function
  | Some _ -> true
  | None -> false

let is_none = function
  | None -> true
  | Some _ -> false


let precise_loc loc mlock = 
  match mlock with
  | Some loc2 -> loc2
  | None -> loc


let update_loc loc annots =
  precise_loc loc (CF.Annot.get_loc annots)
  
let aunpack loc (CF.Mucore.Annotated (annots, _, x)) = 
  (x, update_loc loc annots)



let assoc_err loc entry list err =
  let open Pp in
  match List.assoc_opt entry list with
  | Some result -> Except.return result
  | None -> Except.fail loc (TypeErrors.Unreachable (!^"list assoc failed:" ^^^ !^err))

let rassoc_err loc entry list err =
  let open Pp in
  let rec aux = function
    | [] -> None
    | (a,entry') :: rest -> 
       if entry = entry' then Some a else aux rest
  in
  match aux list with
  | Some result -> Except.return result
  | None -> Except.fail loc (TypeErrors.Unreachable (!^"list assoc failed:" ^^^ !^err))
