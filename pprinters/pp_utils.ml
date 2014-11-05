let to_plain_string d =
  let buf = Buffer.create 50 in
  PPrint.ToBuffer.compact buf d;
  let str = Buffer.contents buf in
  Buffer.clear buf;
  str
