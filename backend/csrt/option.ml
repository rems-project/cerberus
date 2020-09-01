type 'a m = 'a option

let map f = function
  | Some a -> Some (f a)
  | None -> None

let is_some = function
  | Some _ -> true
  | None -> false

let is_none = function
  | None -> true
  | Some _ -> false

let return (a: 'a): 'a m = Some a

let fail : 'a m = None

let bind (a: 'a m) (f: 'a -> 'b m) : 'b m = 
  match a with
  | Some a -> f a 
  | None -> None


let (let*) = bind
