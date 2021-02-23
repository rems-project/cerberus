let id = fun x -> x

let comp (f : 'b -> 'c) (g : 'a -> 'b) (x : 'a) : 'c = f (g (x))
let rec comps (fs : ('a -> 'a) list) (a : 'a) : 'a =
  match fs with
  | [] -> a
  | f :: fs -> f (comps fs a)



let do_stack_trace () = 
  let open Debug_ocaml in
  if !debug_level > 0 then 
    let backtrace = Printexc.get_callstack 200 in
    Some (Printexc.raw_backtrace_to_string backtrace)
  else 
    None



(* let at_most_one err_str = function
 *   | [] -> None
 *   | [x] -> (Some x)
 *   | _ -> Debug_ocaml.error err_str *)


type stacktrace = string




