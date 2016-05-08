(* Created by Victor Gomes 2016-02-08 *)
(* Some useful generic functions *)

let ( $ ) f x = f x

let ( % ) f g = (fun x -> f (g x))

let id = fun x -> x

module Option = struct
exception No_value

let get = function
  | Some a -> a
  | None -> raise No_value
end
