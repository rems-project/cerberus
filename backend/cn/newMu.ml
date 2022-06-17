module AT = ArgumentTypes
module RT = ReturnTypes
module CF=Cerb_frontend

module SR_Types = struct
  type ct = Sctypes.t
  type bt = BaseTypes.t
  type ift = AT.ft
  type ict = ReturnTypes.t
  type ft = AT.ft
  type lt = AT.lt
  type st = Memory.struct_layout
  type gt = ct
  type ut = unit
  type mapping = Mapping.t
  type resource_predicates = (Sym.t * ResourcePredicates.definition) list
  type logical_predicates = (Sym.t * LogicalPredicates.definition) list
end

module Old = CF.Mucore.Make(CF.Mucore.SimpleTypes)
module New = CF.Mucore.Make(SR_Types)

module PP_TYPS = struct
  module T = SR_Types
  let pp_bt = BaseTypes.pp
  let pp_ct ct = Sctypes.pp ct
  let pp_ft = AT.pp RT.pp
  let pp_gt = pp_ct
  let pp_lt = AT.pp False.pp
  let pp_ut _ = Pp.string "todo: implement union type printer"
  let pp_st _ = Pp.string "todo: implement struct type printer"
end


module PP_MUCORE = CF.Pp_mucore.Make(CF.Pp_mucore.Basic)(PP_TYPS)
(* let pp_budget () = Some !debug_level *)
let pp_budget () = Some 10
let pp_pexpr e = PP_MUCORE.pp_pexpr e
let pp_tpexpr e = PP_MUCORE.pp_tpexpr (pp_budget ()) e
let pp_expr e = PP_MUCORE.pp_expr e
let pp_texpr e = PP_MUCORE.pp_texpr (pp_budget ()) e


