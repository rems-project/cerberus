open Json
open Core

module ObjectTypeJSON: (JSON with type t = core_object_type) =
struct
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
        | _ -> throw "._object_type"
      in
      OTy_cfunction (co_opt, IntJSON.parse i, BoolJSON.parse b)
    | `Assoc [("OTy_array", co)] ->
      OTy_array (parse co)
    | `Assoc [("OTy_struct", sym)] ->
      OTy_struct (SymJSON.parse sym)
    | `Assoc [("OTy_union", sym)] ->
      OTy_union (SymJSON.parse sym)
    | _ -> throw "._object_type"
end

module BaseTypeJSON: (JSON with type t = core_base_type) =
struct
  type t = core_base_type
  let rec serialise = function
    | BTy_unit -> `String "BTy_unit"
    | BTy_boolean -> `String "BTy_boolean"
    | BTy_ctype -> `String "BTy_ctype"
    | BTy_list cbt -> `Assoc [("BTy_list", serialise cbt)]
    | BTy_tuple cbts -> `Assoc [("BTy_tuple", `List (List.map serialise cbts))]
    | BTy_object co -> `Assoc [("BTy_object", ObjectTypeJSON.serialise co)]
    | BTy_loaded co -> `Assoc [("BTy_loaded", ObjectTypeJSON.serialise co)]
  let rec parse = function
    | `String "BTy_unit" -> BTy_unit
    | `String "BTy_boolean" -> BTy_boolean
    | `String "BTy_ctype" -> BTy_ctype
    | `Assoc [("BTy_list", cbt)] -> BTy_list (parse cbt)
    | `Assoc [("BTy_tuple", `List cbts)] -> BTy_tuple (List.map parse cbts)
    | `Assoc [("BTy_object", cbt)] -> BTy_object (ObjectTypeJSON.parse cbt)
    | `Assoc [("BTy_loaded", cbt)] -> BTy_loaded (ObjectTypeJSON.parse cbt)
    | _ -> throw "._base_type"
end

module TypeJSON: (JSON with type t = core_type) =
struct
  type t = core_type
  let serialise = function
    | TyBase cbt -> `Assoc [("TyBase", BaseTypeJSON.serialise cbt)]
    | TyEffect cbt -> `Assoc [("TyEffect", BaseTypeJSON.serialise cbt)]
  let parse = function
    | `Assoc [("TyBase", cbt)] -> TyBase (BaseTypeJSON.parse cbt)
    | `Assoc [("TyEffect", cbt)] -> TyEffect (BaseTypeJSON.parse cbt)
    | _ -> throw "._ctype"
end


module BinopJSON: (JSON with type t = binop) =
struct
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
   | _ -> throw ".binop"
end

module PolarityJSON: (JSON with type t = polarity) =
struct
  type t = polarity
  let serialise = function
    | Pos -> `String "Pos"
    | Neg -> `String "Neg"
  let parse = function
    | `String "Pos" -> Pos
    | `String "Neg" -> Neg
    | _ -> throw ".polarity"
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

module NameJSON: (JSON with type t = name) =
struct
  type t = name
  let serialise = function
    | Sym s -> `Assoc [("Sym", SymJSON.serialise s)]
    | Impl ic -> `Assoc [("Impl", ImplConstJSON.serialise ic)]
  let parse = function
    | `Assoc [("Sym", s)] -> Sym (SymJSON.parse s)
    | `Assoc [("Impl", ic)] -> Impl (ImplConstJSON.parse ic)
    | _ -> throw ".name"
end

module ValueJSON: (JSON with type t = value) =
struct
  type t = value
  let serialise_field (cid, mv) =
    `List [CabsIdJSON.serialise cid; Ocaml_mem.serialise_mem_value mv]
  let rec serialise_object_value = function
    | OVinteger iv ->
      `Assoc [("OVinteger", Ocaml_mem.serialise_integer_value iv)]
    | OVfloating fv ->
      `Assoc [("OVfloating", Ocaml_mem.serialise_floating_value fv)]
    | OVpointer pv ->
      `Assoc [("OVpointer", Ocaml_mem.serialise_pointer_value pv)]
    | OVcfunction n ->
      `Assoc [("OVcfunction", NameJSON.serialise n)]
    | OVarray lvs ->
      `List (List.map serialise_loaded_value lvs)
    | OVstruct (sym, fs) ->
      `Assoc [("OVstruct", `List [SymJSON.serialise sym;
                                  `List (List.map serialise_field fs)])]
    | OVunion (sym, cid, mv) ->
      `Assoc [("OVunion", `List [SymJSON.serialise sym;
                                 serialise_field (cid, mv)])]
    | OVcomposite (iv1, iv2, mv) ->
      `Assoc [("OVcomposite", `List [Ocaml_mem.serialise_integer_value iv1;
                                     Ocaml_mem.serialise_integer_value iv2;
                                     Ocaml_mem.serialise_mem_value mv])]
  and serialise_loaded_value = function
    | LVspecified ov -> `Assoc [("LVspecified", serialise_object_value ov)]
    | LVunspecified cty -> `Assoc [("LVunspecified", CtypeJSON.serialise cty)]
  let rec serialise = function
    | Vobject vo -> `Assoc [("Vobject", serialise_object_value vo)]
    | Vloaded vl -> `Assoc [("Vloaded", serialise_loaded_value vl)]
    | Vunit -> `String "Vunit"
    | Vtrue -> `String "Vtrue"
    | Vfalse -> `String "Vfalse"
    | Vctype cty -> `Assoc [("Vctype", CtypeJSON.serialise cty)]
    | Vlist (cbt, vs) ->
      `Assoc [("Vlist", `List [BaseTypeJSON.serialise cbt;
                               `List (List.map serialise vs)])]
    | Vtuple vs ->
      `Assoc [("Vtuple", `List (List.map serialise vs))]
  let parse _ = failwith "value"
end

module CtorJSON: (JSON with type t = ctor) =
struct
  type t = ctor
  let serialise = function
    | Cnil _ -> `String "Cnil"
    | Ccons -> `String "Ccons"
    | Ctuple -> `String "Ctuple"
    | Carray -> `String "Carray"
    | Civmax -> `String "Civmax"
    | Civmin -> `String "Civmin"
    | Civsizeof -> `String "Civsizeof"
    | Civalignof -> `String "Civalignof"
    | CivCOMPL -> `String "CivCOMPL"
    | CivAND -> `String "CivAND"
    | CivOR -> `String "CivOR"
    | CivXOR -> `String "CivXOR"
    | Cspecified -> `String "Cspecified"
    | Cunspecified -> `String "Cunspecified"
    | Cfvfromint -> `String "Cfvfromint"
    | Civfromfloat -> `String "Civfromfloat"
  let parse _ = failwith "ctor"
end

module PatternJSON: (JSON with type t = pattern) =
struct
  type t = pattern
  module OptionSymJSON = OptionJSON(SymJSON)
  let rec serialise = function
    | CaseBase (sym_opt, cbt) ->
      `Assoc [("CaseBase", `List [OptionSymJSON.serialise sym_opt;
                                  BaseTypeJSON.serialise cbt])]
    | CaseCtor (ctor, pats) ->
      `Assoc [("CaseCtor", `List [CtorJSON.serialise ctor;
                                  `List (List.map serialise pats)])]
  let parse _ = failwith "pattern"
end

module PexprJSON: (JSON with type t = pexpr) =
struct
  type t = pexpr
  let rec serialise_pe = function
    | PEsym sym ->
      `Assoc [("PEsym", SymJSON.serialise sym)]
    | PEimpl impl ->
      `Assoc [("PEimpl", ImplConstJSON.serialise impl)]
    | PEval v ->
      `Assoc [("PEval", ValueJSON.serialise v)]
    | PEconstrained (ivcs) -> failwith "TODO: CONSTRAINED"
    | PEundef undef ->
      (* TODO: this does not work when parsing it back *)
      `Assoc [("PEundef", `String (Undefined.stringFromUndefined_behaviour undef))]
    | PEerror (str, pe) ->
      `Assoc [("PError", `List [StringJSON.serialise str; serialise pe])]
    | PEctor (ctor, pes) ->
      `Assoc [("PEctor", `List [CtorJSON.serialise ctor;
                                `List (List.map serialise pes)])]
    | PEcase (pe, pats) ->
      `Assoc [("PEcase", `List [serialise pe;
                                `List (List.map serialise_pat pats)])]
    | PEarray_shift (pe, cty, pe_off) ->
      `Assoc [("PEarray_shift", `List [serialise pe;
                                       CtypeJSON.serialise cty;
                                       serialise pe_off])]
    | PEmember_shift (pe, sym, cid) ->
      `Assoc [("PEmember_shift", `List [SymJSON.serialise sym;
                                        CabsIdJSON.serialise cid])]
    | PEnot pe ->
      `Assoc [("PEnot", serialise pe)]
    | PEop (bop, pe1, pe2) ->
      `Assoc [("PEop", `List [BinopJSON.serialise bop;
                              serialise pe1; serialise pe2])]
    | PEstruct (sym, fs) ->
      `Assoc [("PEstruct", `List [SymJSON.serialise sym;
                                  `List (List.map serialise_field fs)])]
    | PEunion (sym, cid, pe) ->
      `Assoc [("PEunion", `List [SymJSON.serialise sym;
                                 CabsIdJSON.serialise cid;
                                 serialise pe])]
    | PEcall (n, pes) ->
      `Assoc [("PEcall", `List [NameJSON.serialise n;
                                `List (List.map serialise pes)])]
    | PElet (pat, pe, body) ->
      `Assoc [("PElet", `List [PatternJSON.serialise pat;
                               serialise pe; serialise body])]
    | PEif (pe1, pe2, pe3) ->
      `Assoc [("PEif", `List [serialise pe1; serialise pe2; serialise pe3])]
    | PEis_scalar pe ->
      `Assoc [("PEis_scalar", serialise pe)]
    | PEis_integer pe ->
      `Assoc [("PEis_integer", serialise pe)]
    | PEis_signed pe ->
      `Assoc [("PEis_signed", serialise pe)]
    | PEis_unsigned pe ->
      `Assoc [("PEis_unsigned", serialise pe)]
  and serialise = function
    | Pexpr (_, _, pe) -> serialise_pe pe
  and serialise_field (cid, pe) =
    `List [CabsIdJSON.serialise cid; serialise pe]
  and serialise_pat (pat, pe) =
    `List [PatternJSON.serialise pat; serialise pe]
  let parse _ = failwith "pexpr"
end

module MemOrderJSON: (JSON with type t = Cmm_csem.memory_order) =
struct
  open Cmm_csem
  type t = memory_order
  let serialise = function
    | NA -> `String "NA"
    | Seq_cst -> `String "Seq_cst"
    | Relaxed -> `String "Relaxed"
    | Release -> `String "Release"
    | Acquire -> `String "Acquire"
    | Consume -> `String "Consume"
    | Acq_rel -> `String "Acq_rel"
  let parse = function
    | `String "NA" -> NA
    | `String "Seq_cst" -> Seq_cst
    | `String "Relaxed" -> Relaxed
    | `String "Release" -> Release
    | `String "Acquire" -> Acquire
    | `String "Consume" -> Consume
    | `String "Acq_rel" -> Acq_rel
    | _ -> throw "Cmm_csem.memory_order"
end

module MemOpJSON: (JSON with type t = Mem_common.memop) =
struct
  open Mem_common
  type t = memop
  let serialise = function
    | PtrEq -> `String "PtrEq"
    | PtrNe -> `String "PtrNe"
    | PtrLt -> `String "PtrLt"
    | PtrGt -> `String "PtrGt"
    | PtrLe -> `String "PtrLe"
    | PtrGe -> `String "PtrGe"
    | Ptrdiff -> `String "PtrDiff"
    | IntFromPtr -> `String "IntFromPtr"
    | PtrFromInt -> `String "PtrFromInt"
    | PtrValidForDeref -> `String "PtrValidForDeref"
    | PtrWellAligned -> `String "PtrWellAligned"
    | Memcmp -> `String "Memcmp"
  let parse _ = failwith "Mem_comon.memop"
end

module ActionJSON: (JSON with type t = unit action0) =
struct
  type t = unit action0
  let rec serialise_act = function
    | Create (pe1, pe2, pre) ->
      `Assoc [("Create", `List [PexprJSON.serialise pe1;
                                PexprJSON.serialise pe2;
                                SymPrefixJSON.serialise pre])]
    | Alloc0 (pe1, pe2, pre) ->
      `Assoc [("Alloc", `List [PexprJSON.serialise pe1;
                               PexprJSON.serialise pe2;
                               SymPrefixJSON.serialise pre])]
    | Kill pe ->
      `Assoc [("Kill", PexprJSON.serialise pe)]
    | Store0 (pe1, pe2, pe3, mo) ->
      `Assoc [("Store", `List [PexprJSON.serialise pe1;
                               PexprJSON.serialise pe2;
                               PexprJSON.serialise pe3;
                               MemOrderJSON.serialise mo])]
    | Load0 (pe1, pe2, mo) ->
      `Assoc [("Load", `List [PexprJSON.serialise pe1;
                              PexprJSON.serialise pe2;
                              MemOrderJSON.serialise mo])]
    | RMW0 (pe1, pe2, pe3, pe4, mo1, mo2) ->
      `Assoc [("RMW", `List [PexprJSON.serialise pe1;
                             PexprJSON.serialise pe2;
                             PexprJSON.serialise pe3;
                             PexprJSON.serialise pe4;
                             MemOrderJSON.serialise mo1;
                             MemOrderJSON.serialise mo2])]
    | Fence0 mo ->
      `Assoc [("Fence", MemOrderJSON.serialise mo)]
  and serialise = function
    | Action (_, _, act) -> serialise_act act
  let parse _ = failwith "action"
end

module PactionJSON: (JSON with type t = unit paction) =
struct
  type t = unit paction
  let serialise = function
    | Paction (p, a) -> `List [PolarityJSON.serialise p; ActionJSON.serialise a]
  let parse _ = failwith "paction"
end

module ExprJSON: (JSON with type t = unit expr) =
struct
  type t = unit expr
  let rec serialise_expr = function
    | Epure pe ->
      `Assoc [("Epure", PexprJSON.serialise pe)]
    | Ememop (memop, es) ->
      `Assoc [("Ememop", `List [MemOpJSON.serialise memop;
                                `List (List.map PexprJSON.serialise es)])]
    | Eaction act ->
      `Assoc [("Eaction", PactionJSON.serialise act)]
    | Ecase (pe, pats) ->
      `Assoc [("Ecase", `List [PexprJSON.serialise pe;
                               `List (List.map serialise_pat pats)])]
    | Elet (pat, pe1, e2) ->
      `Assoc [("Elet", `List [PatternJSON.serialise pat;
                              PexprJSON.serialise pe1;
                              serialise e2])]
    | Eif (pe1, e2, e3) ->
      `Assoc [("Eif", `List [PexprJSON.serialise pe1;
                             serialise e2;
                             serialise e3])]
    | Eskip ->
      `String "Eskip"
    | Eccall (_, pe, pes) ->
      `Assoc [("Eccall", `List [PexprJSON.serialise pe;
                                `List (List.map PexprJSON.serialise pes)])]
    | Eproc (_, n, pes) ->
      `Assoc [("Eproc", `List [NameJSON.serialise n;
                               `List (List.map PexprJSON.serialise pes)])]
    | Eunseq es ->
      `List (List.map serialise es)
    | Ewseq (pat, e1, e2) ->
      `Assoc [("Ewseq", `List [PatternJSON.serialise pat;
                               serialise e1;
                               serialise e2])]
    | Esseq (pat, e1, e2) ->
      `Assoc [("Esseq", `List [PatternJSON.serialise pat;
                               serialise e1;
                               serialise e2])]
    | Easeq ((sym, cbty), act, pact) ->
      `Assoc [("Easeq", `List [SymJSON.serialise sym;
                               BaseTypeJSON.serialise cbty;
                               ActionJSON.serialise act;
                               PactionJSON.serialise pact])]
    | Eindet (i, e) ->
      `Assoc [("Eindent", `List [IntJSON.serialise i;
                                 serialise e])]
    | Ebound (i, e) ->
      `Assoc [("Ebound", `List [IntJSON.serialise i;
                                 serialise e])]
    | End es ->
      `Assoc [("End", `List (List.map serialise es))]
    | Esave ((sym, cbty), args, e) ->
      let serialise_args (sym, (cbty, pe)) =
        `List [SymJSON.serialise sym;
               BaseTypeJSON.serialise cbty;
               PexprJSON.serialise pe]
      in `Assoc [("Esave", `List [SymJSON.serialise sym;
                                  BaseTypeJSON.serialise cbty;
                                  `List (List.map serialise_args args);
                                  serialise e])]
    | Erun (_, sym, pes) ->
      `Assoc [("Erun", `List [SymJSON.serialise sym;
                              `List (List.map PexprJSON.serialise pes)])]
    | Epar es ->
      `Assoc [("Epar", `List (List.map serialise es))]
    | Ewait i ->
      `Assoc [("Ewait", IntJSON.serialise i)]
  and serialise = function
    | Expr (_, e) -> serialise_expr e
  and serialise_pat (pat, e) =
    `List [PatternJSON.serialise pat; serialise e]
  let parse _ = failwith "expr"
end

module ImplDecJSON: (JSON with type t = impl_decl) =
struct
  type t = impl_decl
  let serialise = function
    | Def (cbty, pe) ->
      `Assoc [("Def", `List [BaseTypeJSON.serialise cbty;
                             PexprJSON.serialise pe])]
    | IFun (cbty, args, pe) ->
      let serialise_args (sym, cbty) =
        `List [SymJSON.serialise sym; BaseTypeJSON.serialise cbty]
      in
      `Assoc [("IFun", `List [BaseTypeJSON.serialise cbty;
                              `List (List.map serialise_args args);
                              PexprJSON.serialise pe])]
  let parse _ = failwith "impl_decl"
end

module FunDecJSON: (JSON with type t = unit fun_map_decl) =
struct
  type t = unit fun_map_decl
  let serialise_args (sym, cbty) =
    `List [SymJSON.serialise sym; BaseTypeJSON.serialise cbty]
  let serialise = function
    | Fun (cbty, args, pe) ->
      `Assoc [("Fun", `List [BaseTypeJSON.serialise cbty;
                             `List (List.map serialise_args args);
                             PexprJSON.serialise pe])]
    | ProcDecl (cbty, cbtys) ->
      `Assoc [("ProcDecl", `List [BaseTypeJSON.serialise cbty;
                                  `List (List.map BaseTypeJSON.serialise cbtys)])]
    | Proc (cbty, args, e) ->
      `Assoc [("Proc", `List [BaseTypeJSON.serialise cbty;
                              `List (List.map serialise_args args);
                              ExprJSON.serialise e])]
  let parse _ = failwith "impl_decl"
end

module FileJSON: (JSON with type t = unit file) =
struct
  type t = unit file
  module OptSymJSON = OptionJSON(SymJSON)
  module ImplMapJSON = PMapSymJSON(ImplDecJSON)
  module FunMapJSON = PMapSymJSON(FunDecJSON)
  module TagMapJSON = PMapSymJSON(TagDefJSON)

  let serialise_globs (sym, cbty, e) =
    `List [SymJSON.serialise sym;
           BaseTypeJSON.serialise cbty;
           ExprJSON.serialise e]
  let serialise core_file = `List [
      OptSymJSON.serialise core_file.main;
      TagMapJSON.serialise core_file.tagDefs;
      FunMapJSON.serialise core_file.stdlib;
      (* ImplMapJSON.serialise core_file.impl; *)
      `List (List.map serialise_globs core_file.globs);
      FunMapJSON.serialise core_file.funs;
    ]
  let parse _ = failwith "core_file"
end


(*  Run *)

module RunErrorsJSON: (JSON with type t = Errors.core_run_error) =
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
    | _ -> throw " run error"
end

(* TODO: serialise Cmm_op.symState *)
(* TODO: serialise _value *)
module DriverResultJSON: (JSON with type t = Driver.driver_result) =
struct
  open Driver
  type t = Driver.driver_result
  let dummy_cmm_op = Cmm_op.symInitialState Cmm_op.symInitialPre
  let dummy_core_value = Vunit
  let serialise dr =
    `List [BoolJSON.serialise dr.dres_blocked;
           IntJSON.serialise dr.dres_driver_steps;
           IntJSON.serialise dr.dres_core_run_steps;
           StringJSON.serialise dr.dres_stdout]
  let parse = function
    | `List [blocked; driver_steps; _run_steps; stdout] ->
      { dres_blocked=           BoolJSON.parse blocked;
        dres_concurrency_state= dummy_cmm_op;
        dres_driver_steps=      IntJSON.parse driver_steps;
        dres_core_run_steps=    IntJSON.parse _run_steps;
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

module DriverStateJSON: (JSON with type t = Driver.driver_state) =
struct
  open Driver
  type t = driver_state
  let serialise _ = failwith ""
  let parse _ = failwith ""
end

module ND2 = NDStatusJSON(DriverResultJSON)(DriverResultJSON)
