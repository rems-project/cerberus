module BT = BaseTypes
module RE = Resources
module RT = ReturnTypes
module AT = ArgumentTypes
module FT = AT.Make(RT)
module LT = AT.Make(False)
open Pp


type bt = BT.t
type ct = PreProcess.ctype_information
type ft = FT.t
type lt = LT.t
type st = CF.Ctype.ctype CF.Mucore.mu_struct_def * Global.struct_decl
type ut = CF.Ctype.ctype CF.Mucore.mu_union_def

let pp_bt = BT.pp true
let pp_ct (PreProcess.{bt;size;align;_}) = 
  parens (BT.pp false bt ^^ comma ^^ Z.pp size ^^ comma ^^ Z.pp align)
let pp_ft = FT.pp
let pp_lt = Some (LT.pp)
let pp_funinfo _ = failwith "not implemented"
let pp_funinfo_with_attributes _  = failwith "not implemented"


let pp_ut ut = CF.Pp_mucore.Pp_standard_typ.pp_ut ut
let pp_st (s,_) = CF.Pp_mucore.Pp_standard_typ.pp_st s

