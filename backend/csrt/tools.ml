module Loc = Locations



let id = fun x -> x

let comp (f : 'b -> 'c) (g : 'a -> 'b) (x : 'a) : 'c = f (g (x))
let rec comps (fs : ('a -> 'a) list) (a : 'a) : 'a =
  match fs with
  | [] -> a
  | f :: fs -> f (comps fs a)



let do_stack_trace () = 
  let open Pp in
  if !Debug_ocaml.debug_level > 0 then 
    let backtrace = Printexc.get_callstack (!print_level * 10) in
    Some (Printexc.raw_backtrace_to_string backtrace)
  else 
    None




type stacktrace = string


