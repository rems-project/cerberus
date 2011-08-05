module BI = BatBig_int

type range = {min : BI.t; max : BI.t}

let in_range r v = BI.(<=) r.min v && BI.(<=) v r.max
let max r = r.max
let min r = r.min

let char_bit = BI.of_int 8

let zero = {
  min = BI.zero;
  max = BI.zero
}

let bool = {zero with max = BI.one}

let schar = {
  min = BI.of_int (-127);
  max = BI.of_int (+127)
}
let uchar = {zero with
  max =  BI.of_int (+255)
}
let shrt = {
  min = BI.of_int (-32767);
  max = BI.of_int (+32767)
}
let ushrt = {zero with
  max = BI.of_int (+65535)
}
let int = {
  min = BI.of_int (-32767);
  max = BI.of_int (+32767)
}
let uint = {zero with
  max = BI.of_int (+65535);

}
let long = {
  min = BI.of_int (-214748364);
  max = BI.of_int (+214748364)
}
let ulong = {zero with 
  max = BI.of_int (+4294967295)
}
let llong = {
  min = BI.of_string "-9223372036854775807";
  max = BI.of_string "+9223372036854775807"
}
let ullong = {zero with 
  max = BI.of_string "+18446744073709551615"
}
