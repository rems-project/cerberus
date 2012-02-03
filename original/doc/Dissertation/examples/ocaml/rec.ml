type 'e exp = Num of int | Add of 'e * 'e
type 'a e = F of 'a * ('a e) exp

let rec map_num f (F (data, exp)) =
  F (data,
     match exp with
     | Num n -> f n
     | Add (e1, e2) -> Add (map_num f e1, map_num f e2)
  )
