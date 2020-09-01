module CF = Cerb_frontend
module CB = Cerb_backend

include Stdlib.Result



type ('a,'e) t = ('a, 'e) result

let return : 'a -> ('a,'e) t = ok

let fail (loc: Locations.t) (e: 'e) : ('a, Locations.t * 'e) t = 
  error (loc,e)

let (let*) = bind


let print pp = 
  let open Pp in
  let () = CB.Pipeline.run_pp None (pp ^^ hardline) in
  return ()

let warn pp = 
  let open Pp in
  print (blank 3 ^^ !^(yellowb "[!] Warning:") ^^^ pp)

let debug_print print_level pp =
  let open Pp in
  if !debug_level >= print_level then print pp else return ()





type 'a m = ('a, Locations.t * TypeErrors.t) t

let to_exception_type = function
  | Ok a -> CF.Exception.Result a
  | Error e -> CF.Exception.Exception e
