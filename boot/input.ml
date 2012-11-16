type t = string
type input = in_channel

let read f input =
  let channel = open_in input in  
  let result  = f channel in
  let ()      = close_in channel in
  result

let name input = input

let file name = name
