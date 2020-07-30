open Cerb_frontend.Exception
module CB = Cerb_backend



type ('a,'e) t = ('a, 'e) exceptM

let return : 'a -> ('a,'e) t = except_return

let fail : Locations.t -> 'e -> ('a, Locations.t * 'e) t = 
  fun loc e -> fail (loc,e)

let (let*) = except_bind

let liftM = except_fmap

let seq = except_sequence

let of_maybe = of_maybe

let to_bool = to_bool

let mapM : ('a -> ('b,'e) t) -> 'a list -> ('b list, 'e) t = 
  except_mapM

let iterM : ('a -> (unit,'e) t) -> 'a list -> (unit, 'e) t = 
  fun f l -> let* _ = mapM f l in return ()

let concat_mapM f l = 
  let* xs = seq (List.map f l) in
  return (List.concat xs)

let rec filter_map (f : 'a -> 'b option) (xs : 'a list) : 'b list = 
  match xs with
  | [] -> []
  | x :: xs ->
     match f x with
     | None -> filter_map f xs
     | Some y -> y :: filter_map f xs

let filter_mapM f l = 
  let* xs = seq (List.map f l) in
  return (filter_map (fun x -> x) xs)


let fold_leftM (f : 'a -> 'b -> ('c,'e) t) (a : 'a) (bs : 'b list) =
  List.fold_left (fun aM b -> let* a = aM in f a b) (return a) bs

(* maybe from Exception.lem *)
let fold_rightM (f : 'b -> 'a -> ('c,'e) t) (bs : 'b list) (a : 'a) =
  List.fold_right (fun b aM -> let* a = aM in f b a) bs (return a)


let pmap_foldM 
      (f : 'k -> 'x -> 'y -> ('y,'e) t)
      (map : ('k,'x) Pmap.map) (init: 'y) : ('y,'e) t =
  Pmap.fold (fun k v aM -> let* a = aM in f k v a) map (return init)

let pmap_iterM f m = 
  Pmap.fold (fun k v m -> let* () = m in f k v) 
    m (return ())

let pmap_mapM 
      (f: 'k -> 'v -> ('w,'e) t)
      (m : ('k,'v) Pmap.map)
      (cmp: 'k -> 'k -> int)
    : (('k,'w) Pmap.map, 'e) t
  = 
  pmap_foldM (fun k v m -> 
      let* v' = f k v in 
      return (Pmap.add k v' m)
    ) m (Pmap.empty cmp)


let tryM (m : ('a,'e1) exceptM) (m' : ('a,'e2) exceptM) =
  match m with
  | Result a -> Result a
  | Exception _ -> m'

let rec tryMs (m : ('a,'e1) exceptM) (ms : (('a,'e2) exceptM) list) =
  match m, ms with
  | Result a, _ -> Result a
  | Exception _, m' :: ms' -> tryMs m' ms'
  | Exception e, [] -> Exception e






let of_option (type a) loc err (o : a option) : (a,'e) exceptM =
  match o with
  | Some r -> return r
  | None -> fail loc err


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
