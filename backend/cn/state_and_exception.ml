module type S = sig
  type e
  type s
end


module Make(S : S) = struct

  open S

  type error = 
    Locations.loc * Tools.stacktrace option * e Lazy.t

  type 'a t = 
    { c : s -> ('a * s, error) Result.t }

  type 'a m = 
    'a t


  let return (a : 'a) : 'a t =
    { c = fun s -> Ok (a, s) }

  let bind (m : 'a t) (f : 'a -> 'b t) : 'b t = 
    let c s = match m.c s with
      | Error e -> Error e
      | Ok (x, s') -> (f x).c s'
    in
    { c }

  let get () : 'a t = 
    { c = fun s -> Ok (s, s) }

  let set (s : 's) : unit t = 
    { c = fun _ -> Ok ((), s) }


  let error loc e = 
    (loc, Tools.do_stack_trace (),  e)

  let fail (loc: Locations.loc) (e: 'e Lazy.t) : 'a t = 
    { c = fun _ -> Error (error loc e) }


  let rec attempt (fs : (('a t) Lazy.t) List1.t) : 'a t = 
    let c s = 
      let (hd, tl) = List1.dest fs in
      let hd_run = Lazy.force hd in
      match hd_run.c s, tl with
      | Ok (a, s'), _ -> 
         Ok (a, s')
      | Error _, hd' :: tl' -> 
         (attempt (List1.make (hd', tl'))).c s
      | Error err, _ -> 
         Error err
    in
    { c }


end
