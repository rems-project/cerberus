let int : unit -> int =
  let counter = ref (-1) in
  fun () ->
    assert (!counter <> max_int);
    incr counter; !counter

let digest, set_digest =
  let digest = ref "" in
  (fun () -> !digest),
  (fun filename -> digest := Digest.file filename)