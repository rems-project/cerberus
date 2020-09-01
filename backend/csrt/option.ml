type 'a m = 'a option

let return : 'a -> 'a m = 
  fun a -> Some a

let fail : 'a m = 
  None

let (>>=) : 'a m -> ('a -> 'b m) -> 'b m = 
  fun a f ->
  match a with
  | Some a -> f a 
  | None -> None


let (let*) = (>>=)


let map f = function
  | Some a -> Some (f a)
  | None -> None


let is_some = function
  | Some _ -> true
  | None -> false

let is_none = function
  | None -> true
  | Some _ -> false
