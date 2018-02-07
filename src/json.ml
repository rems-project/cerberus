exception FailParseJSON of string

let throw s = raise (FailParseJSON s)

type json =
    [ `Assoc of (string * json) list
    | `Bool of bool
    | `Float of float
    | `Floatlit of string
    | `Int of int
    | `Intlit of string
    | `List of json list
    | `Null
    | `String of string
    | `Stringlit of string
    | `Tuple of json list
    | `Variant of string * json option ]

module type JSON =
sig
  type t
  val serialise: t -> json
  val parse: json -> t
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

module SymPrefixJSON: (JSON with type t = Symbol.prefix) =
struct
  open Symbol
  type t = prefix
  let serialise = function
    | PrefSource ss ->
      `Assoc [("PrefSource", `List (List.map SymJSON.serialise ss))]
    | PrefOther str ->
      `Assoc [("PrefOther", StringJSON.serialise str)]
  let parse = function
    | `Assoc [("PrefSource", `List ss)] ->
      PrefSource (List.map SymJSON.parse ss)
    | `Assoc [("PrefOther", str)] ->
      PrefOther (StringJSON.parse str)
    | _ -> throw "Symbol.prefix"
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
