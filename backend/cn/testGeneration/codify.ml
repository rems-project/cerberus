module BT = BaseTypes
module IT = IndexTerms
open Utils
module CF = Cerb_frontend
open CF
open Dsl

type test_framework = GTest

let codify_sym = codify_sym

let rec codify_it_ (e : BT.t IT.term_) : string option =
  let exception Unsupported_codify_it in
  try
    Some
      (match e with
       | Const Null ->
         "nullptr"
       | Const (Bits ((Signed, bits), n)) when bits <= 16 ->
         Int64.to_string (Z.to_int64 n)
       | Const (Bits ((Unsigned, bits), n)) when bits <= 16 ->
         Int64.to_string (Z.to_int64 n) ^ "U"
       | Const (Bits ((Signed, bits), n)) when bits <= 32 ->
         Int64.to_string (Z.to_int64 n) ^ "L"
       | Const (Bits ((Unsigned, bits), n)) when bits <= 32 ->
         string_of_int (Z.to_int n) ^ "UL"
       | Const (Bits ((Signed, bits), n)) when bits <= 64 ->
         Int64.to_string (Z.to_int64 n) ^ "LL"
       | Const (Bits ((Unsigned, bits), n)) when bits <= 64 ->
         Int64.to_string (Z.to_int64 n) ^ "ULL"
       | Const (Bool b) ->
         string_of_bool b
       | Sym x ->
         codify_sym x
       | Unop (Not, e') ->
         "(!" ^ codify_it e' ^ ")"
       | Unop (Negate, e') ->
         "(-" ^ codify_it e' ^ ")"
       | Binop (And, e1, e2) ->
         "(" ^ codify_it e1 ^ " && " ^ codify_it e2 ^ ")"
       | Binop (Or, e1, e2) ->
         codify_it e1 ^ " || " ^ codify_it e2 ^ ")"
       | Binop (Implies, e1, e2) ->
         "((!" ^ codify_it e1 ^ ") || " ^ codify_it e2 ^ ")"
       | Binop (Add, e1, e2) ->
         "(" ^ codify_it e1 ^ " + " ^ codify_it e2 ^ ")"
       | Binop (Sub, e1, e2) ->
         "(" ^ codify_it e1 ^ " - " ^ codify_it e2 ^ ")"
       | Binop (Mul, e1, e2)
       | Binop (MulNoSMT, e1, e2) ->
         "(" ^ codify_it e1 ^ " * " ^ codify_it e2 ^ ")"
       | Binop (Div, e1, e2)
       | Binop (DivNoSMT, e1, e2) ->
         "(" ^ codify_it e1 ^ " / " ^ codify_it e2 ^ ")"
       | Binop (XORNoSMT, e1, e2) ->
         "(" ^ codify_it e1 ^ " ^ " ^ codify_it e2 ^ ")"
       | Binop (BWAndNoSMT, e1, e2) ->
         "(" ^ codify_it e1 ^ " & " ^ codify_it e2 ^ ")"
       | Binop (BWOrNoSMT, e1, e2) ->
         "(" ^ codify_it e1 ^ " | " ^ codify_it e2 ^ ")"
       | Binop (ShiftLeft, e1, e2) ->
         "(" ^ codify_it e1 ^ " << " ^ codify_it e2 ^ ")"
       | Binop (ShiftRight, e1, e2) ->
         "(" ^ codify_it e1 ^ " >> " ^ codify_it e2 ^ ")"
       | Binop (LT, e1, e2)
       | Binop (LTPointer, e1, e2) ->
         "(" ^ codify_it e1 ^ " < " ^ codify_it e2 ^ ")"
       | Binop (LE, e1, e2)
       | Binop (LEPointer, e1, e2) ->
         "(" ^ codify_it e1 ^ " <= " ^ codify_it e2 ^ ")"
       | Binop (EQ, e1, e2) ->
         "(" ^ codify_it e1 ^ " == " ^ codify_it e2 ^ ")"
       | Binop (Mod, e1, e2) ->
         "(" ^ codify_it e1 ^ " % " ^ codify_it e2 ^ ")"
       | ITE (e1, e2, e3) ->
         "(" ^ codify_it e1 ^ " ? " ^ codify_it e2 ^ " : " ^ codify_it e3 ^ ")"
       (* *)
       | _ ->
         raise Unsupported_codify_it)
  with
  | Unsupported_codify_it ->
    None


and codify_it (e : IT.t) : string =
  let (IT (e_, _, _)) = e in
  match codify_it_ e_ with
  | Some str ->
    str
  | None ->
    failwith ("unsupported operation " ^ Pp_utils.to_plain_pretty_string (IT.pp e))


let rec codify_gen' (g : gen) : string =
  match g with
  | Arbitrary ty ->
    "rc::gen::arbitrary<" ^ string_of_ctype ty ^ ">()"
  | Return (ty, e) ->
    "rc::gen::just<" ^ string_of_ctype ty ^ ">(" ^ codify_it e ^ ")"
  | Filter (x', ty, e, g') ->
    let gen = codify_gen' g' in
    "rc::gen::suchThat("
    ^ gen
    ^ ", [=]("
    ^ string_of_ctype ty
    ^ " "
    ^ codify_sym x'
    ^ "){ return "
    ^ codify_it e
    ^ "; })"
  | Map (x', ty, e, g') ->
    let gen = codify_gen' g' in
    "rc::gen::map("
    ^ gen
    ^ ", [=]("
    ^ string_of_ctype ty
    ^ " "
    ^ codify_sym x'
    ^ "){ return "
    ^ codify_it e
    ^ "; })"
  | Alloc (ty, x) ->
    "rc::gen::just<" ^ string_of_ctype ty ^ ">(&" ^ codify_sym x ^ ")"
  | Struct (ty, ms) ->
    "rc::gen::just<"
    ^ string_of_ctype ty
    ^ ">({ "
    ^ String.concat ", " (List.map (fun (x, y) -> "." ^ x ^ " = " ^ codify_sym y) ms)
    ^ "})"


let codify_gen (x : Sym.sym) (g : gen) : string =
  "/* "
  ^ string_of_gen g
  ^ " */\n"
  ^ "auto "
  ^ codify_sym x
  ^ " = *"
  ^ codify_gen' g
  ^ ";\n"


let rec codify_gen_context (gtx : gen_context) : string =
  match gtx with
  | (x, g) :: gtx' ->
    codify_gen x g ^ codify_gen_context gtx'
  | [] ->
    ""


let codify_pbt_header
  (tf : test_framework)
  (suite : string)
  (test : string)
  (oc : out_channel)
  : unit
  =
  match tf with
  | GTest ->
    output_string
      oc
      ("\nRC_GTEST_PROP(Test" ^ String.capitalize_ascii suite ^ ", " ^ test ^ ", ()){\n")


let codify_pbt
  (tf : test_framework)
  (instrumentation : Core_to_mucore.instrumentation)
  (args : (Symbol.sym * Ctype.ctype) list)
  (index : int)
  (oc : out_channel)
  (gtx : gen_context)
  : unit
  =
  codify_pbt_header tf (codify_sym instrumentation.fn) ("Test" ^ string_of_int index) oc;
  output_string oc (codify_gen_context gtx);
  output_string oc (codify_sym instrumentation.fn);
  output_string oc "(";
  output_string oc (args |> List.map fst |> List.map codify_sym |> String.concat ", ");
  output_string oc ");\n";
  match tf with
  | GTest ->
    output_string oc "}\n\n"
