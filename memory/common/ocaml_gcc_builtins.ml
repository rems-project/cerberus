open Int64

let ctz n =
  let n = Nat_big_num.to_int64 n in
  assert (not (equal n zero));
  let rec aux acc z =
    if equal z zero then
      acc
    else
      aux (Nat_big_num.pred acc) (shift_left z 1) in
  aux (Nat_big_num.of_int 64) n

let bswap16 n =
  let n = Nat_big_num.to_int64 n in
  assert (equal zero (logand 0xffffffffffff0000L n));
  Nat_big_num.of_int64 begin
    logor (shift_right_logical (logand 0xff00L n) 8) (shift_left (logand 0xffL n) 8)
  end

let bswap32 n =
  let n = Nat_big_num.to_int64 n in
  assert (equal zero (logand 0xffffffff00000000L n));
  Nat_big_num.of_int64 begin
    logor
      (logor (shift_left (logand 0x0000ff00L n) 8) (shift_left (logand 0x000000ffL n) 24))
      (logor (shift_right_logical (logand 0xff000000L n) 24) (shift_right_logical (logand 0x00ff0000L n) 8))
  end

let bswap64 n =
  let n = Nat_big_num.to_int64 n in
  Nat_big_num.of_int64 begin
    logor
      (logor
        (logor (shift_left (logand 0x000000000000ff00L n) 40) (shift_left (logand 0x00000000000000ffL n) 56))
        (logor (shift_left (logand 0x0000000000ff0000L n) 24) (shift_left (logand 0x00000000ff000000L n) 8)))
      (logor
        (logor (shift_right_logical (logand 0x00ff000000000000L n) 40) (shift_right_logical (logand 0xff00000000000000L n) 56))
        (logor (shift_right_logical (logand 0x0000ff0000000000L n) 24) (shift_right_logical (logand 0x000000ff00000000L n) 8)))
  end
