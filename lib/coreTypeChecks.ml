(* comparisons between CN base types and Core base types *)

module BT = BaseTypes
open Cerb_frontend.Core

let check_against_core_bt core_bt cn_bt =
  let fail msg = Result.Error msg in
  let module M = struct
    include Result

    type 'a t = ('a, Pp.document) Result.t

    let return = ok
  end
  in
  let open Effectful.Make (M) in
  let mismatch cbt bt =
    let msg1 =
      Pp.typ
        (Pp.string "mismatching core/CN types")
        (Pp.ineq (Pp_mucore.pp_core_base_type core_bt) (BT.pp cn_bt))
    in
    let msg2 =
      if BT.equal bt cn_bt then
        msg1
      else
        Pp.typ
          msg1
          (Pp.typ
             (Pp.string "inner mismatch")
             (Pp.ineq (Pp_mucore.pp_core_base_type cbt) (BT.pp bt)))
    in
    fail msg2
  in
  let rec check_object_type = function
    | OTy_integer, BT.Integer -> return ()
    | OTy_integer, BT.Bits _ -> return ()
    | OTy_pointer, BT.Loc () -> return ()
    | OTy_array t, BT.Map (param_t, t2) ->
      let@ () = check_object_type (OTy_integer, param_t) in
      check_object_type (t, t2)
    | OTy_struct tag, BT.Struct tag2 when Sym.equal tag tag2 -> return ()
    | OTy_union _tag, _ -> fail (Pp.string "unsupported: union types")
    | OTy_floating, _ -> fail (Pp.string "unsupported: floats")
    | core_obj_ty, bt -> mismatch (BTy_object core_obj_ty) bt
  in
  let rec check_core_base_type = function
    | BTy_unit, BT.Unit -> return ()
    | BTy_boolean, BT.Bool -> return ()
    | BTy_object ot, bt -> check_object_type (ot, bt)
    | BTy_loaded ot, bt -> check_object_type (ot, bt)
    | BTy_list cbt, BT.List bt -> check_core_base_type (cbt, bt)
    | BTy_tuple cbts, BT.Tuple bts when List.length bts == List.length bts ->
      let@ _ = ListM.map2M (Tools.curry check_core_base_type) cbts bts in
      return ()
    | BTy_storable, _ -> fail (Pp.string "unsupported: BTy_storable")
    | BTy_ctype, BT.CType -> return ()
    | cbt, bt -> mismatch cbt bt
  in
  check_core_base_type (core_bt, cn_bt)
