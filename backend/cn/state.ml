type ('a,'s) t = 's -> 'a * 's

let return (a : 'a) : ('a, 's) t =
  fun s -> (a, s)

let bind (x : ('a, 's) t) (f : 'a -> ('b, 's) t) : ('b, 's) t = 
  fun s -> 
  let (x, s') = x s in 
  f x s'

let (let@) = bind
    
let get () : ('s, 's) t = 
  fun s -> (s, s)

let set (s : 's) : (unit, 's) t = 
  fun _ -> ((), s)
