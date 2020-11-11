module CF = Cerb_frontend
open TypeErrors
open Resultat
open Pp
open IndexTerms

open Resources
module BT = BaseTypes
module LC = LogicalConstraints
module RT = ReturnTypes
module IT = IndexTerms


let integer_value_to_num loc iv = 
  match CF.Impl_mem.eval_integer_value iv with
  | Some v -> return v
  | None -> fail loc (Internal !^"integer_value_to_num")



(* adapting from impl_mem *)
let size_of_integer loc it = 
  let impl = CF.Ocaml_implementation.get () in
  match impl.sizeof_ity it with
  | Some n -> return (Z.of_int n)
  | None -> fail loc (Internal !^"sizeof_pointer returned None")

(* adapting from impl_mem *)
let align_of_integer loc it =
  let impl = CF.Ocaml_implementation.get () in
  match impl.alignof_ity it with
  | Some n -> return (Z.of_int n)
  | None -> fail loc (Internal !^"alignof_pointer returned None")

let representable_integer loc it =
  let* (min,max) = match it with
    | CF.Ctype.Bool -> 
       return (Z.of_int 0, Z.of_int 1)
    | _ -> 
       let* min = integer_value_to_num loc (CF.Impl_mem.min_ival it) in
       let* max = integer_value_to_num loc (CF.Impl_mem.max_ival it) in
       return (min, max)
  in
  let lc about = LC.LC (IT.in_range (Num min) (Num max) about) in
  return lc




(* adapting from impl_mem *)
let size_of_pointer loc =
  let impl = CF.Ocaml_implementation.get () in
  match impl.sizeof_pointer with
  | Some n -> return (Z.of_int n)
  | None -> fail loc (Internal !^"sizeof_pointer returned None")

(* from impl_mem *)
let align_of_pointer loc =
  let impl = CF.Ocaml_implementation.get () in
  match impl.alignof_pointer  with
  | Some n -> return (Z.of_int n)
  | None -> fail loc (Internal !^"alignof_pointer returned None")


let representable_pointer loc = 
  let* pointer_byte_size = size_of_pointer loc in
  let pointer_size = Z.mult_big_int pointer_byte_size (Z.of_int 8) in
  let max = Z.power_int_positive_big_int 2 (Z.sub_big_int pointer_size (Z.of_int 1)) in
  let rangef about = 
    LC.LC (IT.And [IT.LocLE (Pointer Z.zero, about); 
                   IT.LocLE (about, Pointer max)])
  in
  return rangef
  





let lookup_struct_in_tagDefs loc (BT.Tag tag) =
  match Pmap.lookup tag (CF.Tags.tagDefs ()) with
  | Some (CF.Ctype.StructDef (fields,flexible_array_member)) -> 
     return (fields,flexible_array_member)
  | Some (UnionDef _) -> fail loc (Generic !^"expected struct")
  | None -> 
     fail loc (Generic (!^"struct" ^^^ (BT.pp_tag (BT.Tag tag)) ^^^ !^"not defined"))


let size_of_ctype loc ct = 
  let s = CF.Impl_mem.sizeof_ival ct in
  integer_value_to_num loc s

let align_of_ctype loc ct = 
  let s = CF.Impl_mem.alignof_ival ct in
  integer_value_to_num loc s

let rec representable_ctype loc (CF.Ctype.Ctype (_,ct_)) =
  let open CF.Ctype in
  match ct_ with
  | Void -> return (fun it -> LC.LC (EQ (it , Unit)))
  | Basic (Integer it) -> representable_integer loc it
  | Basic (Floating _) -> fail loc (Unsupported !^"floats")
  | Array _ -> fail loc (Unsupported !^"arrays")
  | Function _ -> fail loc (Unsupported !^"todo: function pointers")
  | Pointer _ -> representable_pointer loc
  | Atomic ct -> representable_ctype loc ct
  | Struct tag -> representable_struct loc (BT.Tag tag)
  | Union _ -> fail loc (Unsupported !^"union types")

and representable_struct loc (Tag tag) = 
  let* (fields,_) = lookup_struct_in_tagDefs loc (BT.Tag tag) in
  let* member_rangefs =
    ListM.mapM (fun (id, (_, _, ct)) ->
        let CF.Ctype.Ctype (annot,_) = ct in
        let loc = Loc.update_a loc annot in
        let* rangef = representable_ctype loc ct in
        return (BT.Member (Id.s id),rangef)
      ) fields
  in
  let rangef about = 
    let lcs = 
      List.map (fun (member, rangef) ->
          let (LC.LC c) = rangef (IT.Member (Tag tag, about, member)) in
          c
        ) member_rangefs
    in
    (LC.LC (And lcs))
  in
  return rangef


let size_of_struct loc (BT.Tag s) =
  size_of_ctype loc (CF.Ctype.Ctype ([], CF.Ctype.Struct s))

let align_of_struct loc (BT.Tag s) =
  align_of_ctype loc (CF.Ctype.Ctype ([], CF.Ctype.Struct s))


let member_offset loc (BT.Tag tag) (BT.Member id) = 
  let iv = CF.Impl_mem.offsetof_ival (CF.Tags.tagDefs ()) 
             tag (Id.parse (Loc.unpack loc) id) 
  in
  integer_value_to_num loc iv



let size_of_stored_type loc st = 
  match st with
  | St.ST_Ctype ct -> size_of_ctype loc ct
  | St.ST_Pointer -> size_of_pointer loc

let align_of_stored_type loc st = 
  match st with
  | St.ST_Ctype ct -> align_of_ctype loc ct
  | St.ST_Pointer -> align_of_pointer loc

let representable_stored_type loc st = 
  match st with
  | St.ST_Ctype ct -> representable_ctype loc ct
  | St.ST_Pointer -> representable_pointer loc
