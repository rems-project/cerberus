type t = {
  name : string;
  input : 'a. (BatIO.input -> 'a) -> 'a
}

let read f {input; _} = input f
let name {name; _} = name

let file name =
  let input f = BatFile.with_file_in name f in
  {name; input}
