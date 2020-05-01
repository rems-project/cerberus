open Cerb_frontend
open Exception


type ('a,'e) m = ('a, 'e) exceptM

let return : 'a -> ('a,'e) m = except_return

let fail : Locations.t -> 'e -> ('a, Locations.t * 'e) m = 
  fun loc e -> Exception.fail (loc,e)

let fail_noloc e = Exception.fail e

let (>>=) = except_bind

let (>>) m m' = m >>= fun _ -> m'

let liftM = except_fmap

let seq = except_sequence

let of_maybe = of_maybe

let to_bool = to_bool

let mapM : ('a -> ('b,'e) m) -> 'a list -> ('b list, 'e) m = 
  except_mapM

let concatmapM f l = 
  seq (List.map f l) >>= fun xs ->
  return (List.concat xs)

let fold_leftM (f : 'a -> 'b -> ('c,'e) m) (a : 'a) (bs : 'b list) =
  List.fold_left (fun a b -> a >>= fun a -> f a b) (return a) bs

let pmap_foldM 
      (f : 'k -> 'x -> 'y -> ('y,'e) m)
      (map : ('k,'x) Pmap.map) (init: 'y) : ('y,'e) m =
  Pmap.fold (fun k v a -> a >>= f k v) map (return init)

let pmap_iterM f m = 
  Pmap.fold (fun k v a -> a >> f k v) 
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
