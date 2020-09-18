include Result


let return (a: 'a) : ('a,'e) t = 
  Ok a

let fail (loc: Locations.t) (e: 'e) : ('a, Locations.t * 'e) t = 
  Error (loc,e)

let bind (m : ('a,'e) t) (f: 'a -> ('b,'e) t) : ('b,'e) t = 
  match m with
  | Ok a -> f a
  | Error e -> Error e

let (let*) = bind

type 'a m = ('a, Locations.t * TypeErrors.t) t



let printM pp = let () = Pp.print pp in return ()
let warnM pp = let () = Pp.warn pp in return ()
let dprintM l pp = let () = Pp.dprint l pp in return ()




let time f = 
  let t = Unix.gettimeofday () in
  let* res = Lazy.force f in
  let t' = Unix.gettimeofday () in
  let* () = printM (Pp.item "time" (Pp.string (Printf.sprintf "%f" (t' -. t)))) in
  return res
