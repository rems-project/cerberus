let _tagDefs =
  ref (false, None)

let set_tagDefs v =
  if fst !_tagDefs then
    failwith "Tags definitions can be set only once"
  else
    _tagDefs := (true, Some v)

let tagDefs () =
  match snd !_tagDefs with
    | Some v ->
        v
    | None ->
        failwith "Tags definitions must be set by Tags.set_tagDefs before any use"
