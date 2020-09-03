include Stdlib.Result



type ('a,'e) t = ('a,'e) result

let return : 'a -> ('a,'e) t = ok

let fail (loc: Locations.t) (e: 'e) : ('a, Locations.t * 'e) t = 
  error (loc,e)

let (let*) = bind

type 'a m = ('a, Locations.t * TypeErrors.t) t



let printM pp = let () = Pp.print pp in return ()
let warnM pp = let () = Pp.warn pp in return ()
let dprintM l pp = let () = Pp.dprint l pp in return ()
