include Result



let return (a: 'a) : ('a,'e) t = 
  Ok a

 let fail (loc: Locations.t) (e: 'e) : ('a, Locations.t * Tools.stacktrace option * 'e) t = 
  Error (loc, Tools.do_stack_trace (),  e)

let bind (m : ('a,'e) t) (f: 'a -> ('b,'e) t) : ('b,'e) t = 
  match m with
  | Ok a -> f a
  | Error e -> Error e

let (let*) = bind


type 'a m = ('a, Locations.t * Tools.stacktrace option * TypeErrors.t) t





let at_most_one loc err_str = function
  | [] -> return None
  | [x] -> return (Some x)
  | _ -> fail loc (TypeErrors.Generic err_str)

let assoc_err loc entry list err =
  match List.assoc_opt entry list with
  | Some result -> return result
  | None -> fail loc err




