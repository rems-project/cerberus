let id = fun x -> x

let starts_with pfx s = String.length s >= String.length pfx
    && String.equal (String.sub s 0 (String.length pfx)) pfx

let comp (f : 'b -> 'c) (g : 'a -> 'b) (x : 'a) : 'c = f (g (x))
let rec comps (fs : ('a -> 'a) list) (a : 'a) : 'a =
  match fs with
  | [] -> a
  | f :: fs -> f (comps fs a)


let curry f a b = f (a, b)
let uncurry f (a, b) = f a b

let do_stack_trace () =
  let open Cerb_debug in
  if !debug_level > 0 then
    let backtrace = Printexc.get_callstack 200 in
    Some (Printexc.raw_backtrace_to_string backtrace)
  else
    None



let pair_equal equalityA equalityB (a,b) (a',b') =
  equalityA a a' && equalityB b b'

(* let at_most_one err_str = function
 *   | [] -> None
 *   | [x] -> (Some x)
 *   | _ -> Cerb_debug.error err_str *)


let unsupported (loc : Locations.t) (err : Pp.document) : 'a =
  let trace = Option.map Pp.string (do_stack_trace ()) in
  Pp.error loc err (Option.to_list trace);
  exit 2

let skip swith lrt = if true then swith else lrt

