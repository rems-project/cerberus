type 'a nested =
  | Atom of 'a
  | List of 'a nested list

type 'a nlist = 'a nested list

let rec string_of_nested_list f ns =
  let aux = function
    | Atom x -> f x
    | List nl -> string_of_nested_list f nl
  in "[" ^ String.concat " " (List.map aux ns) ^ "]"

let rec map f ns =
  let aux = function
    | Atom x -> Atom (f x)
    | List nl -> List (map f nl)
  in List.map aux ns

let map_aux f ns =
  let rec aux flag = function
    | [] -> []
    | Atom x :: ns ->
      Atom (f flag x) :: aux false ns
    | List ns1 :: ns2 ->
      List (aux true ns1) :: aux false ns2
  in aux false ns

let fold f ns acc =
  let rec aux acc = function
    | [] -> acc
    | Atom x :: ns ->
      let acc = f x acc in
      aux acc ns
    | List ns1 :: ns2 ->
      let acc = aux acc ns1 in
      aux acc ns2
  in aux acc ns
