open Tools
open Pp
open Cerb_frontend.Exception



type ('a,'e) m = ('a, 'e) exceptM

let return : 'a -> ('a,'e) m = except_return

let fail : Locations.t -> 'e -> ('a, Locations.t * 'e) m = 
  fun loc e -> fail (loc,e)

let fail_noloc e = fail e

let (>>=) = except_bind
let (let*) = except_bind

(* this is dangerous when combined with effects: ">>" does not enforce
   evluation order in the right way *)
(* let (>>) m m' = m >>= fun _ -> m' *)

let liftM = except_fmap

let seq = except_sequence

let of_maybe = of_maybe

let to_bool = to_bool

let mapM : ('a -> ('b,'e) m) -> 'a list -> ('b list, 'e) m = 
  except_mapM

let iterM : ('a -> (unit,'e) m) -> 'a list -> (unit, 'e) m = 
  fun f l -> mapM f l >>= fun _ -> return ()

let concat_mapM f l = 
  seq (List.map f l) >>= fun xs ->
  return (List.concat xs)

let filter_mapM f l = 
  seq (List.map f l) >>= fun xs ->
  return (filter_map (fun x -> x) xs)


let fold_leftM (f : 'a -> 'b -> ('c,'e) m) (a : 'a) (bs : 'b list) =
  List.fold_left (fun a b -> a >>= fun a -> f a b) (return a) bs

let pmap_foldM 
      (f : 'k -> 'x -> 'y -> ('y,'e) m)
      (map : ('k,'x) Pmap.map) (init: 'y) : ('y,'e) m =
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




let print (pp : PPrint.document) : (unit,'e) m = unsafe_print pp; return ()
let debug_print l pp = unsafe_debug_print l pp; return ()
let warn pp = unsafe_warn pp; return ()
