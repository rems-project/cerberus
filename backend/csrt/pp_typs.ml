module BT = BaseTypes
module RE = Resources
module RT = ReturnTypes
module AT = ArgumentTypes
module FT = AT.Make(RT)
module LT = AT.Make(NoReturn)
open Pp


type bt = BT.t
type ct = (BT.t * RE.size)
type ft = FT.t
type lt = LT.t
let pp_bt = BT.pp true
let pp_ct (bt,size) = parens (BT.pp false bt ^^ comma ^^ Num.pp size)
let pp_ft = FT.pp
let pp_lt = Some (LT.pp)
let pp_funinfo _ = failwith "not implementeed"
let pp_funinfo_with_attributes _  = failwith "not implementeed"
