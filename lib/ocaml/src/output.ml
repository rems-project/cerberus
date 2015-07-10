open Pervasives_

type t = string

let file name = name
let write s name =
  let channel = open_out name in  
  output_string channel s;
  close_out channel
