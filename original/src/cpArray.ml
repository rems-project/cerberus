module A = struct
  type 'a entry = int * 'a
  type 'a t = 'a data ref
  and 'a data =
    | Base of 'a array
    | Diff of 'a entry * 'a t

  let create size v = ref (Base (Array.create size v))
  let init size f = ref (Base (Array.init size f))

  let reroot t =
    let rec reroot_loop t cont =
      match !t with
      | Base _ -> cont ()
      | Diff ((i, v'), t') ->
          reroot_loop t' (fun () ->
            let () = match !t' with
              | (Base a) as data' ->
                  let v = a.(i) in
                  a.(i) <- v';
                  t  := data';
                  t' := Diff ((i, v), t)
              | Diff _ -> assert (false) in
            cont ()) in
    reroot_loop t (fun _ -> ())

  let rec get t i =
    match !t with
    | Base a -> a.(i)
    | Diff _ -> reroot t; get t i

  let set t i v' =
    let () = reroot t in
    match !t with
    | (Base a) as data' ->
        let v = a.(i) in
        if v <> v' then
          let t' = ref data' in
          a.(i) <- v'; t := Diff ((i, v), t'); t'
        else t
    | Diff _ -> assert (false)

  let update t i f = set t i (f (get t i))
end

module Growable = struct
  type 'a t = 'a A.t * int
  let err () = invalid_arg "index out of bounds"

  let size (_, s) = s
  let init size f = A.init size f, size
  let create size v = A.create size v, size
  let get (t, s) i = if i < s then A.get t i else err ()
  let set (t, s) i v = if i < s then (A.set t i v, s) else err ()
  let update (t, s) i f = if i < s then (A.update t i f, s) else err ()
  let rec grow (t, s) n f =
    match !t with
    | A.Base a ->
        let a' = Array.append (Array.sub a 0 s) (Array.init n f) in
        let () = t := A.Base a' in
        t, s + n
    | A.Diff _ -> A.reroot t; grow (t, s) n f
end

include A
