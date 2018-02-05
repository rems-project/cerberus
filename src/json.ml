exception FailParseJSON of string

let throw s = raise (FailParseJSON s)

module type JSON =
sig
  type t
  val serialise: t -> Yojson.json
  val parse: Yojson.json -> t
end

(* Basic types *)

module StringJSON: (JSON with type t = string) =
struct
  type t = string
  let serialise s = `String s
  let parse = function
    | `String s -> s
    | _ -> throw "string"
end

module BoolJSON: (JSON with type t = bool) =
struct
  type t = bool
  let serialise b = `String (if b then "True" else "False")
  let parse = function
    | `String "True" -> true
    | `String "False" -> false
    | _ -> throw "bool"
end

module IntJSON: (JSON with type t = int) =
struct
  type t = int
  let serialise s = `String (string_of_int s)
  let parse = function
    | `String s -> int_of_string s
    | _ -> throw "int"
end

module BigIntJSON: (JSON with type t = Nat_big_num.num) =
struct
  type t = Nat_big_num.num
  let serialise n = `String (Nat_big_num.to_string n)
  let parse = function
    | `String n -> Nat_big_num.of_string n
    | _ -> throw "BigInt"
end

module PairJSON (T1: JSON) (T2: JSON): (JSON with type t = T1.t * T2.t) =
struct
  type t = T1.t * T2.t
  let serialise (x1, x2) = `List [T1.serialise x1; T2.serialise x2]
  let parse = function
    | `List [se1; se2] ->
      (T1.parse se1, T2.parse se2)
    | _ -> throw "pair"
end

module ListJSON (T: JSON): (JSON with type t = T.t list) =
struct
  type t = T.t list
  let serialise xs = `List (List.map T.serialise xs)
  let parse = function
    | `List ses -> List.map T.parse ses
    | _ -> throw "list"
end

module OptionJSON (T: JSON): (JSON with type t = T.t option) =
struct
  type t = T.t option
  let serialise = function
    | None -> `String "None"
    | Some x -> `Assoc [("Some", T.serialise x)]
  let parse = function
    | `String "None" -> None
    | `Assoc [("Some", se)] -> Some (T.parse se)
    | _ -> throw "option"
end

module SymJSON: (JSON with type t = Symbol.sym) =
struct
  type t = Symbol.sym
  module T = PairJSON(IntJSON)(OptionJSON(StringJSON))
  let serialise = function
    | Symbol.Symbol (n, sopt) -> `Assoc [("Symbol", T.serialise (n, sopt))]
  let parse = function
    | `Assoc [("Symbol", se)] ->
      let (n, sopt) =  T.parse se in Symbol.Symbol (n, sopt)
    | _ -> throw "Symbol.symbol"
end

(* TODO: this is very naive *)
module PMapSymJSON (T: JSON): (JSON with type t = (Symbol.sym, T.t) Pmap.map) =
struct
  type t = (Symbol.sym, T.t) Pmap.map
  module MapJSON = ListJSON(PairJSON(SymJSON)(T))
  let serialise m =
    Pmap.bindings_list m
    |> MapJSON.serialise
  let parse se =
    let rec create m = function
      | [] -> m
      | ((k,v)::xs) -> create (Pmap.add k v m) xs
    in
    create
      (Pmap.empty Symbol.instance_Basic_classes_Ord_Symbol_sym_dict.compare_method)
      (MapJSON.parse se)
end

(* Cabs *)

(* TODO: serialise location *)
module CabsIdJSON: (JSON with type t = Cabs.cabs_identifier) =
struct
  open Cabs
  type t = cabs_identifier
  let serialise = function
    | CabsIdentifier (_, s) -> `String s
  let parse = function
    | `String s -> CabsIdentifier (Location_ocaml.unknown, s)
    | _ -> throw "Cabs.cabs_identifier"
end

(* Ail *)

module AilIntBaseJSON: (JSON with type t = AilTypes.integerBaseType) =
struct
  open AilTypes
  type t = integerBaseType
  let serialise = function
    | Ichar -> `String "Ichar"
    | Short -> `String "Short"
    | Int_ -> `String "Int_"
    | Long -> `String "Long"
    | LongLong -> `String "LongLong"
    | IntN_t i -> `Assoc [("IntN_t", IntJSON.serialise i)]
    | Int_leastN_t i -> `Assoc[("Int_leastN_t", IntJSON.serialise i)]
    | Int_fastN_t i -> `Assoc[("Int_fastN_t", IntJSON.serialise i)]
    | Intmax_t -> `String "Intmax_t"
    | Intptr_t -> `String "Intptr_t"
  let parse = function
    | `String "Ichar" -> Ichar
    | `String "Short" -> Short
    | `String "Int_" -> Int_
    | `String "Long" -> Long
    | `String "LongLong" -> LongLong
    | `Assoc[("IntN_t", se)] -> IntN_t (IntJSON.parse se)
    | `Assoc[("Int_leastN_t", se)] -> Int_leastN_t (IntJSON.parse se)
    | `Assoc[("Int_fastN_t", se)] -> Int_fastN_t (IntJSON.parse se)
    | `String "Intmax_t" -> Intmax_t
    | `String "Intptr_t" -> Intptr_t
    | _ -> throw "Ailtypes.integerBaseType"
end

module AilIntJSON: (JSON with type t = AilTypes.integerType) =
struct
  open AilTypes
  type t = integerType
  let serialise = function
    | Char -> `String "Char"
    | Bool -> `String "Bool"
    | Signed ibt -> `Assoc [("Signed", AilIntBaseJSON.serialise ibt)]
    | Unsigned ibt -> `Assoc [("Unsigned", AilIntBaseJSON.serialise ibt)]
    | IBuiltin s -> `Assoc [("IBuiltin", StringJSON.serialise s)]
    | Enum i -> `Assoc [("Enum", SymJSON.serialise i)]
    | Size_t -> `String "Size_t"
    | Ptrdiff_t -> `String "Ptrdiff_t"
  let parse = function
    | `String "Char" -> Char
    | `String "Bool" -> Bool
    | `Assoc [("Signed", j)] -> Signed (AilIntBaseJSON.parse j)
    | `Assoc [("Unsigned", j)] -> Unsigned (AilIntBaseJSON.parse j)
    | `Assoc [("IBuiltin", j)] -> IBuiltin (StringJSON.parse j)
    | `Assoc [("Enum", j)] -> Enum (SymJSON.parse j)
    | `String "Size_t" -> Size_t
    | `String "Ptrdiff_t" -> Ptrdiff_t
    | _ -> throw "AilTypes.integerType"
end

module AilRealFloatingJSON: (JSON with type t = AilTypes.realFloatingType) =
struct
  open AilTypes
  type t = realFloatingType
  let serialise = function
    | Float -> `String "Float"
    | Double -> `String "Double"
    | LongDouble -> `String "LongDouble"
  let parse = function
    | `String "Float" -> Float
    | `String "Double" -> Double
    | `String "LongDouble" -> LongDouble
    | _ -> throw "AilType.realFloatingType"
end

module AilFloatingJSON: (JSON with type t = AilTypes.floatingType) =
struct
  open AilTypes
  type t = floatingType
  let serialise = function
    | RealFloating rft -> AilRealFloatingJSON.serialise rft
  let parse s = RealFloating (AilRealFloatingJSON.parse s)
end

module AilBasicJSON: (JSON with type t = AilTypes.basicType) =
struct
  open AilTypes
  type t = basicType
  let serialise = function
    | Integer i -> `Assoc [("Integer", AilIntJSON.serialise i)]
    | Floating f -> `Assoc [("Floating", AilFloatingJSON.serialise f)]
  let parse = function
    | `Assoc [("Integer", j)] -> Integer (AilIntJSON.parse j)
    | `Assoc [("Floating", j)] -> Floating (AilFloatingJSON.parse j)
    | _ -> throw "AilTypes.basicType"
end


module AilQualifiersJSON: (JSON with type t = AilTypes.qualifiers) =
struct
  open AilTypes
  type t = qualifiers
  let serialise q = `List [BoolJSON.serialise q.const;
                           BoolJSON.serialise q.restrict;
                           BoolJSON.serialise q.volatile]
  let parse = function
    | `List [c; r; v] ->
      { const=    BoolJSON.parse c;
        restrict= BoolJSON.parse r;
        volatile= BoolJSON.parse v;
      }
    | _ -> throw "Ailtypes.qualifiers"
end

(* Core_ctype *)

module CtypeJSON: (JSON with type t = Core_ctype.ctype0) =
struct
  open Core_ctype
  type t = ctype0
  module OptBigIntJSON = OptionJSON(BigIntJSON)
  let rec serialise = function
    | Void0 ->
      `String "Void"
    | Basic0 bt ->
      `Assoc [("Basic", AilBasicJSON.serialise bt)]
    | Array0 (ct, i_opt) ->
      `Assoc [("Array", `List [serialise ct; OptBigIntJSON.serialise i_opt])]
    | Function0 ((q,ct), qcts, b) ->
      `Assoc [("Function",
               `List [serialise_qual_ctype (q, ct);
                      `List (List.map serialise_qual_ctype qcts);
                      BoolJSON.serialise b])]
    | Pointer0 (q, ct) ->
      `Assoc [("Pointer", serialise_qual_ctype (q, ct))]
    | Atomic0 cty ->
      `Assoc [("Atomic", serialise cty)]
    | Struct0 tag ->
      `Assoc [("Struct", SymJSON.serialise tag)]
    | Union0 tag ->
      `Assoc [("Union", SymJSON.serialise tag)]
    | Builtin0 str ->
      `Assoc [("Builtin", StringJSON.serialise str)]
  and serialise_qual_ctype (q, ct) =
    `List [AilQualifiersJSON.serialise q; serialise ct]
  let rec parse = function
    | `String "Void" ->
      Void0
    | `Assoc [("Basic", aty)] ->
      Basic0 (AilBasicJSON.parse aty)
    | `Assoc [("Array", `List [cty; i_opt])] ->
      Array0 (parse cty, OptBigIntJSON.parse i_opt)
    | `Assoc [("Function", `List [qcty; `List qctys; b])] ->
      Function0 (parse_qual_ctype qcty,
                 List.map parse_qual_ctype qctys,
                 BoolJSON.parse b)
    | _ -> throw "Core_ctype.ctype"

  and parse_qual_ctype = function
    | `List [q; cty] -> (AilQualifiersJSON.parse q, parse cty)
    | _ -> throw "Core_ctype.ctype"
end

(* Tags *)

module TagDefJSON: (JSON with type t = Tags.tag_definition) =
struct
  open Tags
  type t = tag_definition
  module CCPairJSON = PairJSON(CabsIdJSON)(CtypeJSON)
  let serialise = function
    | StructDef xs ->
      `Assoc[("StructDef", `List (List.map CCPairJSON.serialise xs))]
    | UnionDef xs ->
      `Assoc[("UnionDef", `List (List.map CCPairJSON.serialise xs))]
  let parse = function
    | `Assoc [("StructDef", `List xs)] ->
      StructDef (List.map CCPairJSON.parse xs)
    | `Assoc [("UnionDef", `List xs)] ->
      UnionDef (List.map CCPairJSON.parse xs)
    | _ -> throw "Tags.tag_definition"
end

(* Core *)

module CoreObjectJSON: (JSON with type t = Core.core_object_type) =
struct
  open Core
  type t = core_object_type
  let rec serialise = function
    | OTy_integer -> `String "OTy_integer"
    | OTy_floating -> `String "OTy_floating"
    | OTy_pointer -> `String "OTy_pointer"
    | OTy_cfunction (co_opt, i, b) ->
      let co_opt_json = match co_opt with
        | None -> `String "None"
        | Some co -> `Assoc [("Some", serialise co)]
      in
      `Assoc [("OTy_cfunction",
               `List [co_opt_json; IntJSON.serialise i; BoolJSON.serialise b])]
    | OTy_array co ->
      `Assoc [("OTy_array", serialise co)]
    | OTy_struct s ->
      `Assoc [("OTy_struct", SymJSON.serialise s)]
    | OTy_union s ->
      `Assoc [("OTy_union", SymJSON.serialise s)]
  let rec parse = function
    | `String "OTy_integer" -> OTy_integer
    | `String "OTy_floating" -> OTy_floating
    | `String "OTy_pointer" -> OTy_pointer
    | `Assoc [("OTy_cfunction", `List [co_opt_json; i; b] )] ->
      let co_opt = match co_opt_json with
        | `String "None" -> None
        | `Assoc [("Some", co)] -> Some (parse co)
        | _ -> throw "Core.core_object_type"
      in
      OTy_cfunction (co_opt, IntJSON.parse i, BoolJSON.parse b)
    | `Assoc [("OTy_array", co)] ->
      OTy_array (parse co)
    | `Assoc [("OTy_struct", sym)] ->
      OTy_struct (SymJSON.parse sym)
    | `Assoc [("OTy_union", sym)] ->
      OTy_union (SymJSON.parse sym)
    | _ -> throw "Core.core_object_type"
end

module CoreBaseJSON: (JSON with type t = Core.core_base_type) =
struct
  open Core
  type t = core_base_type
  let rec serialise = function
    | BTy_unit -> `String "BTy_unit"
    | BTy_boolean -> `String "BTy_boolean"
    | BTy_ctype -> `String "BTy_ctype"
    | BTy_list cbt -> `Assoc [("BTy_list", serialise cbt)]
    | BTy_tuple cbts -> `Assoc [("BTy_tuple", `List (List.map serialise cbts))]
    | BTy_object co -> `Assoc [("BTy_object", CoreObjectJSON.serialise co)]
    | BTy_loaded co -> `Assoc [("BTy_loaded", CoreObjectJSON.serialise co)]
  let rec parse = function
    | `String "BTy_unit" -> BTy_unit
    | `String "BTy_boolean" -> BTy_boolean
    | `String "BTy_ctype" -> BTy_ctype
    | `Assoc [("BTy_list", cbt)] -> BTy_list (parse cbt)
    | `Assoc [("BTy_tuple", `List cbts)] -> BTy_tuple (List.map parse cbts)
    | `Assoc [("BTy_object", cbt)] -> BTy_object (CoreObjectJSON.parse cbt)
    | `Assoc [("BTy_loaded", cbt)] -> BTy_loaded (CoreObjectJSON.parse cbt)
    | _ -> throw "Core.core_base_type"
end

module CoreTypeJSON: (JSON with type t = Core.core_type) =
struct
  open Core
  type t = core_type
  let serialise = function
    | TyBase cbt -> `Assoc [("TyBase", CoreBaseJSON.serialise cbt)]
    | TyEffect cbt -> `Assoc [("TyEffect", CoreBaseJSON.serialise cbt)]
  let parse = function
    | `Assoc [("TyBase", cbt)] -> TyBase (CoreBaseJSON.parse cbt)
    | `Assoc [("TyEffect", cbt)] -> TyEffect (CoreBaseJSON.parse cbt)
    | _ -> throw "Core.core_ctype"
end


module CoreBinopJSON: (JSON with type t = Core.binop) =
struct
  open Core
  type t = binop
  let serialise = function
   | OpAdd -> `String "OpAdd"
   | OpSub -> `String "OpSub"
   | OpMul -> `String "OpMul"
   | OpDiv -> `String "OpDiv"
   | OpRem_t -> `String "OpRem_t"
   | OpRem_f -> `String "OpRem_f"
   | OpExp -> `String "OpExp"
   | OpEq -> `String "OpEq"
   | OpGt -> `String "OpGt"
   | OpLt -> `String "OpLt"
   | OpGe -> `String "OpGe"
   | OpLe -> `String "OpLe"
   | OpAnd -> `String "OpAnd"
   | OpOr -> `String "OpOr"
  let parse = function
   | `String "OpAdd" -> OpAdd
   | `String "OpSub" -> OpSub
   | `String "OpMul" -> OpMul
   | `String "OpDiv" -> OpDiv
   | `String "OpRem_t" -> OpRem_t
   | `String "OpRem_f" -> OpRem_f
   | `String "OpExp" -> OpExp
   | `String "OpEq" -> OpEq
   | `String "OpGt" -> OpGt
   | `String "OpLt" -> OpLt
   | `String "OpGe" -> OpGe
   | `String "OpLe" -> OpLe
   | `String "OpAnd" -> OpAnd
   | `String "OpOr" -> OpOr
   | _ -> throw "Core.binop"
end

module CorePolarityJSON: (JSON with type t = Core.polarity) =
struct
  open Core
  type t = polarity
  let serialise = function
    | Pos -> `String "Pos"
    | Neg -> `String "Neg"
  let parse = function
    | `String "Pos" -> Pos
    | `String "Neg" -> Neg
    | _ -> throw "Core.polarity"
end

module ImplConstJSON:
  (JSON with type t = Implementation_.implementation_constant) =
struct
  open Implementation_
  type t = implementation_constant
  let serialise = function
    | Environment__startup_name -> `String "Environment__startup_name"
    | Environment__startup_type -> `String "Environment__startup_type"
    | Characters__bits_in_byte -> `String "Characters__bits_in_byte"
    | Characters__execution_character_set_values ->
      `String "Characters__execution_character_set_values"
    | Characters__plain_char_is_signed ->
      `String "Characters__plain_char_is_signed"
    | Characters__TODO1 -> `String "Characters__TODO1"
    | Characters__TODO2 -> `String "Characters__TODO2"
    | Characters__TODO3 -> `String "Characters__TODO3"
    | Characters__TODO4 -> `String "Characters__TODO4"
    | Characters__TODO5 -> `String "Characters__TODO5"
    | Characters__TODO6 -> `String "Characters__TODO6"
    | Characters__TODO7 -> `String "Characters__TODO7"
    | Characters__TODO8 -> `String "Characters__TODO8"
    | Characters__TODO9 -> `String "Characters__TODO9"
    | Characters__TODO10 -> `String "Characters__TODO10"
    | Integer__encode -> `String "Integer__encode"
    | Integer__decode -> `String "Integer__decode"
    | Integer__conv_nonrepresentable_signed_integer ->
      `String "Integer__conv_nonrepresentable_signed_integer"
    | Sizeof -> `String "Sizeof"
    | Alignof -> `String "Alignof"
    | SHR_signed_negative -> `String "SHR_signed_negative"
    | Bitwise_complement -> `String "Bitwise_complement"
    | Plain_bitfield_sign -> `String "Plain_bitfield_sign"
    | Bitfield_other_types -> `String "Bitfield_other_types"
    | Atomic_bitfield_permitted -> `String "Atomic_bitfield_permitted"
    | Ctype_min -> `String "Ctype_min"
    | Ctype_max -> `String "Ctype_max"
    | StdFunction str -> `Assoc [("StdFunction", StringJSON.serialise str)]
  let parse = function
    | `String "Environment__startup_name" -> Environment__startup_name
    | `String "Environment__startup_type" -> Environment__startup_type
    | `String "Characters__bits_in_byte" -> Characters__bits_in_byte
    | `String "Characters__execution_character_set_values" ->
      Characters__execution_character_set_values
    | `String "Characters__plain_char_is_signed" ->
      Characters__plain_char_is_signed
    | `String "Characters__TODO1" -> Characters__TODO1
    | `String "Characters__TODO2" -> Characters__TODO2
    | `String "Characters__TODO3" -> Characters__TODO3
    | `String "Characters__TODO4" -> Characters__TODO4
    | `String "Characters__TODO5" -> Characters__TODO5
    | `String "Characters__TODO6" -> Characters__TODO6
    | `String "Characters__TODO7" -> Characters__TODO7
    | `String "Characters__TODO8" -> Characters__TODO8
    | `String "Characters__TODO9" -> Characters__TODO9
    | `String "Characters__TODO10" -> Characters__TODO10
    | `String "Integer__encode" -> Integer__encode
    | `String "Integer__decode" -> Integer__decode
    | `String "Integer__conv_nonrepresentable_signed_integer" ->
      Integer__conv_nonrepresentable_signed_integer
    | `String "Sizeof" -> Sizeof
    | `String "Alignof" -> Alignof
    | `String "SHR_signed_negative" -> SHR_signed_negative
    | `String "Bitwise_complement" -> Bitwise_complement
    | `String "Plain_bitfield_sign" -> Plain_bitfield_sign
    | `String "Bitfield_other_types" -> Bitfield_other_types
    | `String "Atomic_bitfield_permitted" -> Atomic_bitfield_permitted
    | `String "Ctype_min" -> Ctype_min
    | `String "Ctype_max" -> Ctype_max
    | `Assoc [("StdFunction", str)] -> StdFunction (StringJSON.parse str)
    | _ -> throw "Implementation_.implementation_constant"
end

module CoreName: (JSON with type t = Core.name) =
struct
  open Core
  type t = name
  let serialise = function
    | Sym s -> `Assoc [("Sym", SymJSON.serialise s)]
    | Impl ic -> `Assoc [("Impl", ImplConstJSON.serialise ic)]
  let parse = function
    | `Assoc [("Sym", s)] -> Sym (SymJSON.parse s)
    | `Assoc [("Impl", ic)] -> Impl (ImplConstJSON.parse ic)
    | _ -> throw "Core.name"
end

(* Core Run *)

module CoreRunErrorsJSON: (JSON with type t = Errors.core_run_error) =
struct
  open Errors
  type t = core_run_error
  let serialise = function
    | Illformed_program s ->
      `List [`String "Illformed_program"; StringJSON.serialise s]
    | Found_empty_stack s ->
      `List [`String "Found_empty_stack"; StringJSON.serialise s]
    | Reached_end_of_proc ->
      `String "Reached_end_of_proc"
    | Unknown_impl ->
      `String "Unknown_impl"
    | Unresolved_symbol sym ->
      `List [`String "Unresolved_symbol"; SymJSON.serialise sym]
  let parse = function
    | `List [`String "Illformed_program"; se] ->
      Illformed_program (StringJSON.parse se)
    | `List [`String "Found_empty_stack"; se] ->
      Found_empty_stack (StringJSON.parse se)
    | `String "Reached_end_of_proc" ->
      Reached_end_of_proc
    | `String "Unknown_impl" ->
      Unknown_impl
    | `List [`String "Unresolved_symbol"; se] ->
      Unresolved_symbol (SymJSON.parse se)
    | _ -> throw "core run error"
end

(* TODO: serialise Cmm_op.symState *)
(* TODO: serialise Core_value *)
module DriverResultJSON: (JSON with type t = Driver.driver_result) =
struct
  open Driver
  type t = Driver.driver_result
  let dummy_cmm_op = Cmm_op.symInitialState Cmm_op.symInitialPre
  let dummy_core_value = Core.Vunit
  let serialise dr =
    `List [BoolJSON.serialise dr.dres_blocked;
           IntJSON.serialise dr.dres_driver_steps;
           IntJSON.serialise dr.dres_core_run_steps;
           StringJSON.serialise dr.dres_stdout]
  let parse = function
    | `List [blocked; driver_steps; core_run_steps; stdout] ->
      { dres_blocked=           BoolJSON.parse blocked;
        dres_concurrency_state= dummy_cmm_op;
        dres_driver_steps=      IntJSON.parse driver_steps;
        dres_core_run_steps=    IntJSON.parse core_run_steps;
        dres_core_value=        dummy_core_value;
        dres_stdout=            StringJSON.parse stdout;
      }
    | _ -> throw "driver result"
end

(* TODO: Serialise location and UBs *)
module KillReasonJSON (T: JSON):
  (JSON with type t = T.t Nondeterminism.kill_reason) =
struct
  open Nondeterminism
  type t = T.t Nondeterminism.kill_reason
  let serialise = function
    | Undef0 (loc, ubs) -> `List [`String "Undef"]
    | Error0 (loc, err) -> `List [`String "Error"; StringJSON.serialise err]
    | Other err -> `List [`String "Other"; T.serialise err]
  let parse = function
    | `List[`String "Undef"] ->
      Undef0 (Location_ocaml.unknown, [])
    | `List[`String "Error"; se] ->
      Error0 (Location_ocaml.unknown, StringJSON.parse se)
    | `List[`String "Other"; se] ->
      Other (T.parse se)
    | _ -> throw "kill reason"

end

module NDStatusJSON (T1: JSON) (T2: JSON):
  (JSON with type t = (T1.t, T2.t) Nondeterminism.nd_status) =
struct
  open Nondeterminism
  type t = (T1.t, T2.t) Nondeterminism.nd_status
  module T3 = KillReasonJSON(T2)
  let serialise = function
    | Active x -> `List [`String "Active"; T1.serialise x]
    | Killed err -> `List [`String "Killed"; T3.serialise err]
  let parse = function
    | `List [`String "Active"; se] -> Active (T1.parse se)
    | `List [`String "Killed"; se] -> Killed (T3.parse se)
    | _ -> throw "nd_status"
end

let () = print_endline "JSON INIT"

