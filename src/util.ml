(* Created by Victor Gomes 2016-02-08 *)
(* Some useful generic functions *)

let ( $ ) f x = f x

let ( % ) f g = (fun x -> f (g x))

let ( %% ) f g = (fun x y -> f x (g y))

let id = fun x -> x

let flip f a b = f b a

let apply f x = f x

let uncurry f = (fun (x, y) -> f x y)

module Option = struct
exception No_value

let case_option f g = function
  | Some x -> f x
  | None -> g ()

let get x = case_option id (fun _ -> raise No_value) x

end

exception Unsupported of string
