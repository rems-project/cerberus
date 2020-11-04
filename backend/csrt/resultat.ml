include Result



type stacktrace = string


let do_stack_trace () = 
  let open Pp in
  if !Debug_ocaml.debug_level > 0 then 
    let backtrace = Printexc.get_callstack (!print_level * 10) in
    Some (Printexc.raw_backtrace_to_string backtrace)
  else 
    None


let return (a: 'a) : ('a,'e) t = 
  Ok a

 let fail (loc: Locations.t) (e: 'e) : ('a, Locations.t * stacktrace option * 'e) t = 
  Error (loc, do_stack_trace (),  e)

let bind (m : ('a,'e) t) (f: 'a -> ('b,'e) t) : ('b,'e) t = 
  match m with
  | Ok a -> f a
  | Error e -> Error e

let (let*) = bind

type 'a m = ('a, Locations.t * stacktrace option * TypeErrors.t) t


