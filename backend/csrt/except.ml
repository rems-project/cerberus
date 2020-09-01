open Cerb_frontend.Exception
module CB = Cerb_backend



type ('a,'e) t = ('a, 'e) exceptM

let return : 'a -> ('a,'e) t = except_return

let fail : Locations.t -> 'e -> ('a, Locations.t * 'e) t = 
  fun loc e -> fail (loc,e)

let (let*) = except_bind



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
