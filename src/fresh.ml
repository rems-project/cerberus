let int : unit -> int =
  let counter = ref (-1) in
  fun () ->
    assert (!counter <> max_int);
    incr counter; !counter