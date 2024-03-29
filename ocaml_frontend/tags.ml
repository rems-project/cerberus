open Ctype

let _tagDefs =
  ref (false, None)

let reset_tagDefs () =
  _tagDefs := (false, None)

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

let with_tagDefs tagDefs f =
  let saved = !_tagDefs in
  _tagDefs := (true, Some tagDefs);
   let ret = f () in
  _tagDefs := saved;
  ret
