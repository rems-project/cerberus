open Cerb_frontend.Exception
module CB = Cerb_backend



type ('a,'e) t = ('a, 'e) exceptM

let return : 'a -> ('a,'e) t = except_return

let fail : Locations.t -> 'e -> ('a, Locations.t * 'e) t = 
  fun loc e -> fail (loc,e)

let (>>=) = except_bind
let (let*) = except_bind

(* this is dangerous when combined with effects: ">>" does not enforce
   evluation order in the right way *)
(* let (>>) m m' = m >>= fun _ -> m' *)

let liftM = except_fmap

let seq = except_sequence

let of_maybe = of_maybe

let to_bool = to_bool

let mapM : ('a -> ('b,'e) t) -> 'a list -> ('b list, 'e) t = 
  except_mapM

let iterM : ('a -> (unit,'e) t) -> 'a list -> (unit, 'e) t = 
  fun f l -> mapM f l >>= fun _ -> return ()

let concat_mapM f l = 
  seq (List.map f l) >>= fun xs ->
  return (List.concat xs)

let rec filter_map (f : 'a -> 'b option) (xs : 'a list) : 'b list = 
  match xs with
  | [] -> []
  | x :: xs ->
     match f x with
     | None -> filter_map f xs
     | Some y -> y :: filter_map f xs

let filter_mapM f l = 
  seq (List.map f l) >>= fun xs ->
  return (filter_map (fun x -> x) xs)


let fold_leftM (f : 'a -> 'b -> ('c,'e) t) (a : 'a) (bs : 'b list) =
  List.fold_left (fun a b -> a >>= fun a -> f a b) (return a) bs


let pmap_foldM 
      (f : 'k -> 'x -> 'y -> ('y,'e) t)
      (map : ('k,'x) Pmap.map) (init: 'y) : ('y,'e) t =
  Pmap.fold (fun k v a -> a >>= f k v) map (return init)

let pmap_iterM f m = 
  Pmap.fold (fun k v a -> a >>= fun () -> f k v) 
    m (return ())

let tryM (m : ('a,'e1) exceptM) (m' : ('a,'e2) exceptM) =
  match m with
  | Result a -> Result a
  | Exception _ -> m'

let rec tryMs (m : ('a,'e1) exceptM) (ms : (('a,'e2) exceptM) list) =
  match m, ms with
  | Result a, _ -> Result a
  | Exception _, m' :: ms' -> tryMs m' ms'
  | Exception e, [] -> Exception e





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
