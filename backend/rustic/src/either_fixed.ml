module Make (X : Type.T) = struct

type 'b t = Left of X.t | Right of 'b

let return x = Right x

let mzero x = Left x

let bind x f =
  match x with
  | Left a -> Left a
  | Right b -> f b

module Infix = struct
  let (>>=) = bind
end

end