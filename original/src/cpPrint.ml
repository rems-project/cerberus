let pp_position p =
  let name = Position.name p in
  let input = CpInput.file name in
  let content = CpInputBuffer.read input in
  let first = Position.first_char p in
  let last  = Position.last_char p in
  BatString.slice ~first:first ~last:last content

let pp_program msg p = msg ^ (pp_position p) ^ "\n"

