module type State = sig type state end

module EffMonad (M: State) = struct
  type state = M.state

  type 'a eff = Eff of (state -> 'a * state)

  let return (a: 't) : 't eff = Eff (fun st -> (a,st))

  let bind ((Eff ma): 'a eff) (f: 'a -> 'b eff) : 'b eff =
    Eff begin
      fun st ->
        let (a, st') = ma st in
        let Eff mb = f a in
        mb st'
    end

  let (>>=) = bind

  let (>>) m m' = m >>= fun _ -> m'

  let run : state -> 'a eff -> 'a * state =
    fun st (Eff ma) -> ma st

  let sequence ms =
    List.fold_right (
      fun m m' ->
      m  >>= fun x  ->
      m' >>= fun xs ->
      return (x :: xs)
    ) ms (return [])

  let sequence_ ms = List.fold_right (>>) ms (return ())
  let mapM  f ms = sequence (List.map f ms)
  let mapMi f ms = sequence (List.mapi f ms)
  let mapM2 f ms1 ms2  = sequence (List.map2 f ms1 ms2)
  let mapM_ f ms = sequence_ (List.map f ms)
  let mapM2_ f ms1 ms2 = sequence_ (List.map2 f ms1 ms2)

  let get : state eff =
    Eff (fun st -> (st, st))

  let put (st' : state) : unit eff =
    Eff (fun _ -> ((), st'))
end
