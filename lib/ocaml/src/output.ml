open Pervasives_

type t = string

let file name = name

let write s name =
  BatFile.with_file_out name (fun o -> BatIO.nwrite o s)
