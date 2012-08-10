let buffer = ref BatMap.empty

let write f =
  let b = !buffer in
  buffer := f b

let read input =
  let name = CpInput.name input in
  try
    let _, content = BatMap.find name !buffer in
    content
  with Not_found ->
    let content = CpInput.read BatIO.read_all input in
    let f map = BatMap.add name (input, content) map in
    write f;
    content

