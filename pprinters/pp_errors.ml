open Lexing

open Errors
open TypingError
open Constraint

open Global_ocaml
open Location_ocaml

open Colour
open Pp_prelude

type kind =
  | Error
  | Warning
  | Note

let string_of_kind = function
  | Error ->
      ansi_format [Bold; Red] "error:"
  | Warning ->
      ansi_format [Bold; Magenta] "warning:"
  | Note ->
      ansi_format [Bold; Black] "note:"


let string_of_cid (Cabs.CabsIdentifier (_, s)) = s
let string_of_ctype ty = String_ail.string_of_ctype AilTypes.no_qualifiers ty
let string_of_sym = Pp_symbol.to_string_pretty
let string_of_gentype = String_ail.string_of_genType

let string_of_cparser_cause = function
  | Cparser_invalid_symbol ->
      "invalid symbol"
  | Cparser_invalid_line_number n ->
      "invalid line directive:" ^ n
  | Cparser_unexpected_eof ->
      "unexpected end of file"
  | Cparser_non_standard_string_concatenation ->
      "unsupported non-standard concatenation of string literals"
  | Cparser_unexpected_token str ->
      "unexpected token '"^ str ^ "'"

let string_of_constraint_violation = function
  | FunctionCallIncompleteReturnType ty ->
      "calling function with incomplete return type '" ^ string_of_ctype ty ^ "'"
  | FunctionCallArrayReturnType ty ->
      "calling function returning an array type '" ^ string_of_ctype ty ^ "'"
  | FunctionCallIncorrectType ->
      "called object type is not a function or function pointer"
  | MemberofReferenceBaseTypeLvalue (qs, ty) ->
      "member reference base type '" ^ String_ail.string_of_ctype qs ty ^ "' is not a structure or union"
  | MemberofReferenceBaseTypeRvalue gty ->
      "member reference base type '" ^ string_of_gentype gty ^ "' is not a structure or union"
  | MemberofNoMemberLvalue (memb, qs, ty) ->
      "no member named '" ^ string_of_cid memb ^ "' in '" ^ String_ail.string_of_ctype qs ty ^ "'"
  | MemberofNoMemberRvalue (memb, gty) ->
      "no member named '" ^ string_of_cid memb ^ "' in '" ^ string_of_gentype gty ^ "'"
  | MemberofptrReferenceTypeNotPointer gty ->
      "member reference type '" ^ string_of_gentype gty ^ "' is not a pointer" ^
      (if GenTypesAux.is_struct_or_union0 gty then "; did you mean to use '.'?" else "")
  | MemberofptrReferenceBaseType (qs, ty) ->
      "member reference base type '" ^ String_ail.string_of_ctype qs ty ^ "' is not a structure or union"
  | MemberofptrNoMember (memb, qs, ty) ->
      "no member named '" ^ string_of_cid memb ^ "' in '" ^ String_ail.string_of_ctype qs ty ^ "'"
  | InvalidTypeCompoundLiteral ->
      "compound literal has invalid type"
  | UnaryExpressionNotLvalue ->
      "expression is not assignable"
  | InvalidArgumentTypeUnaryIncrement ty ->
      "cannot increment value of type '" ^ string_of_ctype ty ^ "'"
  | InvalidArgumentTypeUnaryDecrement ty ->
      "cannot decrement value of type '" ^ string_of_ctype ty ^ "'"
  | UnaryAddressNotRvalue gty ->
      "cannot take address of an rvalue of type '" ^ string_of_gentype gty ^ "'"
  | UnaryAddressRegisterLvalue ->
      "address of lvalue declared with register storage-class specifier"
  | IndirectionNotPointer ->
      "the * operator expects a pointer operand"
  | InvalidArgumentTypeUnaryExpression gty ->
      "invalid argument type '" ^ string_of_gentype gty ^ "' to unary expression"
  | MultiplicativeInvalidOperandsType (gty1, gty2)
  | AdditiveOperandsArithmeticType (gty1, gty2)
  | BitwiseShiftInvalidOperandsType (gty1, gty2)
  | RelationalInvalidOperandsType (gty1, gty2)
  | EqualityInvalidOperandsType (gty1, gty2)
  | BitwiseAndInvalidOperandsType (gty1, gty2)
  | BitwiseXorInvalidOperandsType (gty1, gty2)
  | BitwiseOrInvalidOperandsType (gty1, gty2)
  | AndInvalidOperandsType (gty1, gty2)
  | OrInvalidOperandsType (gty1, gty2) ->
      "invalid operands to binary expression ('" ^ string_of_gentype gty1 ^ "' and '" ^ string_of_gentype gty2 ^ "')"
  | ConditionalOperatorControlType gty ->
      "'" ^ string_of_gentype gty ^ "' is not a scalar type"
  | ConditionalOperatorInvalidOperandTypes (gty1, gty2) ->
      "type mismatch in conditional expression ('" ^ string_of_gentype gty1 ^ "' and '" ^ string_of_gentype gty2 ^ "')"
  | AssignmentModifiableLvalue ->
      "expression is not assignable"
  | SimpleAssignmentViolation (IncompatibleType, ty1, gty2)  ->
      "assigning to '" ^ string_of_ctype ty1 ^ "' from incompatible type '" ^ string_of_gentype gty2 ^ "'"
  | SimpleAssignmentViolation (IncompatiblePointerType, ty1, gty2) ->
      "incompatible pointer types assigning to '" ^ string_of_ctype ty1 ^ "' from '" ^ string_of_gentype gty2 ^ "'"
  | SimpleAssignmentViolation (DiscardsQualifiers, ty1, gty2) ->
      "assigning to '" ^ string_of_ctype ty1 ^ "' from '" ^ string_of_gentype gty2 ^ "' discards qualifiers"
  | IntegerConstantOutRange ->
      "integer constant not in the range of the representable values for its type"
  | NoLinkageMultipleDeclaration x ->
      "multiple declaration of '" ^ string_of_cid x ^ "'"
  | TypedefRedefinition ->
      "typedef redefinition with different types"
  | TypedefRedefinitionVariablyModifiedType ->
      "typedef redefinition of a variably modified type"
  | IllegalMultipleStorageClasses
  | IllegalMultipleStorageClassesThreadLocal ->
      "multiple incompatible storage class specifiers"
  | ThreadLocalShouldAppearInEveryDeclaration ->
      "non-thread-local declaration follows a thread-local declaration"
  | ThreadLocalFunctionDeclaration ->
      "_Thread_local in function declaration"
  | StructMemberIncompleteType (qs, ty) ->
      "member has incomplete type '" ^ String_ail.string_of_ctype qs ty ^ "'"
  | StructMemberFunctionType f ->
      "member '" ^ string_of_cid f ^ "' declared as a function"
  | StructMemberFlexibleArray ->
      "struct has a flexible array member"
  | NoTypeSpecifierInDeclaration ->
      "at least one type specifier should be given in the declaration"
  | IllegalTypeSpecifierInDeclaration ->
      "illegal combination of type specifiers"
  | StructDeclarationLacksDeclaratorList ->
      "non-anonymous struct/union must contain a declarator list"
  | WrongTypeEnumConstant ->
      "expression is not an integer constant expression"
  | LabelStatementOutsideSwitch ->
      "label statement outside switch"
  | LabelRedefinition l ->
      "redefinition of '" ^ string_of_cid l ^ "'"
  | SwitchStatementControllingExpressionNotInteger ->
      "statement requires expression of integer type"
  | IfStatementControllingExpressionNotScalar
  | IterationStatementControllingExpressionNotScalar ->
      "statement requires expression of scalar type"
  | StaticAssertFailed msg ->
      "static assert expression failed: " ^ msg
  | WrongTypeFunctionIdentifier ->
      "function identifier must have a function type"
  | EnumTagIncomplete ->
      "incomplete enum type"
  | AtomicTypeConstraint ->
      "invalid use of _Atomic"
  | RestrictQualifiedPointedTypeConstraint ty ->
      "pointer to type '" ^ string_of_ctype ty ^ "' may not be restrict qualified"
  | RestrictQualifiedTypeConstraint ->
      "restrict requires a pointer"
  | TagRedefinition sym ->
      "redefinition of '" ^ string_of_sym sym ^ "'"
  | TagRedeclaration sym ->
      "use of '" ^ string_of_sym sym ^ "' with tag type that does not match previous declaration"
  | UndeclaredLabel l ->
      "use of undeclared label '" ^ string_of_cid l ^ "'"
  | ContinueOutsideLoop ->
      "continue statement outside a loop"
  | BreakOutsideSwtichOrLoop ->
      "break statement outside a switch or a loop"
  | NonVoidReturnVoidFunction ->
      "void function should not return a value"
  | VoidReturnNonVoidFunction ->
      "non-void function should return a value"
  | ReturnAsSimpleAssignment (IncompatibleType, ty1, gty2) ->
      "returning '" ^ string_of_gentype gty2 ^ "' from a function with incompatible result type '" ^ string_of_ctype ty1 ^ "'"
  | ReturnAsSimpleAssignment (IncompatiblePointerType, ty1, gty2) ->
      "incompatible pointer types returning '" ^ string_of_gentype gty2 ^ "' from a function with result type '" ^ string_of_ctype ty1 ^ "'"
  | ReturnAsSimpleAssignment (DiscardsQualifiers, ty1, gty2) ->
      "returning '" ^ string_of_gentype gty2 ^ "' from a function with result type '" ^ string_of_ctype ty1 ^ "' discards qualifiers"
  | ArrayDeclarationNegativeSize ->
      "array declared with a negative or zero size"
  | ArrayDeclarationIncompleteType ->
      "array has incomplete type"
  | ArrayDeclarationFunctionType ->
      "element of the array has function type"
  | ArrayDeclarationQsAndStaticOnlyOutmost ->
      "type qualifiers or 'static' used in array declarator can only used in the outmost type derivation"
  | ArrayDeclarationQsAndStaticOutsideFunctionProto ->
      "type qualifiers or 'static' used in array declarator outside of function prototype"
  | IllegalReturnTypeFunctionDeclarator ->
      "function cannot return a function type or an array type"
  | IllegalStorageClassFunctionDeclarator ->
      "invalid storage class specifier in function declarator"
  | IncompleteParameterTypeFunctionDeclarator ->
      "incomplete type"
  | IllegalInitializer ->
      "illegal initializer"
  | IllegalStorageClassStaticOrThreadInitializer ->
      "initializer element is not a compile-time constant"
  | IllegalLinkageAndInitialization ->
      "identifier linkage forbids to have an initializer"
  | IllegalTypeArrayDesignator ->
      "expression is not an integer constant expression"
  | IllegalSizeArrayDesignator ->
      "array designator value is negative"
  | InitializationAsSimpleAssignment (IncompatibleType, ty1, gty2) ->
      "initializing '" ^ string_of_ctype ty1 ^ "' with an expression of incompatible type '" ^ string_of_gentype gty2 ^ "'"
  | InitializationAsSimpleAssignment (IncompatiblePointerType, ty1, gty2) ->
      "incompatible pointer types initializing '" ^ string_of_ctype ty1 ^ "' with an expression of type '" ^ string_of_gentype gty2 ^ "'"
  | InitializationAsSimpleAssignment (DiscardsQualifiers, ty1, gty2) ->
      "initializing '" ^ string_of_ctype ty1 ^ "' with an expression of type '" ^ string_of_gentype gty2 ^ "' discards qualifiers"
  | IllegalStorageClassIterationStatement
  | IllegalStorageClassFileScoped
  | IllegalStorageClassFunctionDefinition ->
      "illegal storage class"
  | IllegalIdentifierTypeVoidInFunctionDefinition ->
      "argument may not have 'void' type"
  | UniqueVoidParameterInFunctionDefinition ->
      "'void' must be the first and only parameter if specified"
  | FunctionParameterAsSimpleAssignment (IncompatibleType, ty1, gty2) ->
      "passing '" ^ string_of_gentype gty2 ^ "' to parameter of incompatible type '" ^ string_of_ctype ty1 ^ "'"
  | FunctionParameterAsSimpleAssignment (IncompatiblePointerType, ty1, gty2) ->
      "incompatible pointer types passing '" ^ string_of_gentype gty2 ^ "' to parameter of type '" ^ string_of_ctype ty1 ^ "'"
  | FunctionParameterAsSimpleAssignment (DiscardsQualifiers, ty1, gty2) ->
      "passing '" ^ string_of_gentype gty2 ^ "' to parameter of type '" ^ string_of_ctype ty1 ^ "' discards qualifiers"
  | ExternalRedefinition sym ->
      "redefinition of '" ^ string_of_sym sym ^ "'"
  | AssertMacroExpressionScalarType ->
      "assert expression should have scalar type"

let string_of_misc_violation = function
  | MultipleEnumDeclaration x ->
      "redefinition of '" ^ string_of_cid x ^ "'"
  | EnumSimpleDeclarationConstruction ->
      "such construction is not allowed for enumerators"
  | UndeclaredIdentifier str ->
      "use of undeclared identifier '" ^ str ^ "'"
  | ArrayDeclarationStarIllegalScope ->
      "star modifier used outside of function prototype"
  | ArrayCharStringLiteral ->
      "string literals must be of type array of characters"
  | UniqueVoidParameterInFunctionDeclaration ->
      "'void' must be the first and only parameter if specified"
  | TypedefInitializer ->
      "illegal initializer in type definition"

let string_of_desugar_cause = function
  | Desugar_ConstraintViolation e ->
      (ansi_format [Bold] "constraint violation: ") ^ string_of_constraint_violation e
  | Desugar_MiscViolation e ->
      string_of_misc_violation e
  | Desugar_UndefinedBehaviour ub ->
      (ansi_format [Bold] "undefined behaviour: ") ^ Undefined.ub_short_string ub
  | Desugar_NeverSupported str ->
      "feature that will never supported: " ^ str
  | Desugar_NotYetSupported str ->
      "feature not yet supported: " ^ str
  | Desugar_TODO msg ->
      "TODO: " ^ msg

let string_of_ail_typing_misc_error = function
  | UntypableIntegerConstant i ->
      "integer constant cannot be represented by any type"
  | ParameterTypeNotAdjusted ->
      "internal: the parameter type was not adjusted"

let string_of_ail_typing_error = function
  | TError_ConstraintViolation tcv ->
      (ansi_format [Bold] "constraint violation: ") ^ string_of_constraint_violation tcv
  | TError_UndefinedBehaviour ub ->
      (ansi_format [Bold] "undefined behaviour: ") ^ Undefined.ub_short_string ub
  | TError_MiscError tme ->
      string_of_ail_typing_misc_error tme
  (* TODO *)
  | TError std ->
      "[Ail typing] (" ^ std ^ ")\n  \"" ^ std ^ "\""
  | _ ->
      "[Ail typing error]"

let string_of_core_typing_cause = function
  | Undefined_startup sym ->
      "Undefined_startup " ^ Pp_symbol.to_string sym
  | MismatchObject (expected_oTy, found_oTy) ->
      "MismatchObject(" ^
      String_core.string_of_core_object_type expected_oTy ^ ", " ^
      String_core.string_of_core_object_type found_oTy ^ ")"
  | Mismatch (info_str, expected_bTy, found_bTy) ->
      "Mismatch(" ^ info_str ^ ", " ^
      String_core.string_of_core_base_type expected_bTy ^ ", " ^
      String_core.string_of_core_base_type found_bTy ^ ")"
  | MismatchIf (then_bTy, else_bTy) ->
      "MismatchIf"
  | MismatchIfCfunction (xs_then, xs_else) ->
      (* of (core_base_type * list core_base_type) (* then *) * (core_base_type * list core_base_type) (* else *) *)
      "MismatchIfCfunction(TODO)"
  | EmptyArray ->
      "EmptyArray"
  | CtorWrongNumber (expected_n, found_n) ->
      "CtorWrongNumber(" ^ string_of_int expected_n ^ ", " ^ string_of_int found_n ^ ")"
  | HeterogenousArray (expected_oTy, found_oTy) ->
      "HeterogenousArray(" ^
      String_core.string_of_core_object_type expected_oTy ^ ", " ^
      String_core.string_of_core_object_type found_oTy ^ ")"
  | HeterogenousList (expected_bTy, found_bTy) ->
      "HeterogenousList(" ^
      String_core.string_of_core_base_type expected_bTy ^ ", " ^
      String_core.string_of_core_base_type found_bTy ^ ")"
  | InvalidTag tag_sym ->
      "InvalidTag(" ^ Pp_symbol.to_string tag_sym ^ ")"
  | InvalidMember (tag_sym, Cabs.CabsIdentifier (_, memb_str)) ->
      "InvalidMember(" ^ Pp_symbol.to_string tag_sym ^ ", " ^ memb_str ^ ")"
  | CoreTyping_TODO str ->
      "CoreTyping_TODO(" ^ str ^ ")"
  | TooGeneral ->
      "TooGeneral"

let string_of_core_run_cause = function
  | Illformed_program str ->
      "ill-formed program: `" ^ str ^ "'"
  | Found_empty_stack str ->
      "found an empty stack: `" ^ str ^ "'"
  | Reached_end_of_proc ->
      "reached the end of a procedure"
  | Unknown_impl ->
      "unknown implementation constant"
  | Unresolved_symbol sym ->
      "unresolved symbol: " ^ (Pp_utils.to_plain_string (Pp_ail.pp_id sym))

let short_message = function
  | CPARSER ccause ->
      string_of_cparser_cause ccause
  | DESUGAR dcause ->
      string_of_desugar_cause dcause
  | AIL_TYPING terr ->
      string_of_ail_typing_error terr
  | CORE_TYPING tcause ->
      string_of_core_typing_cause tcause
  | CORE_RUN cause ->
      string_of_core_run_cause cause
  | UNSUPPORTED str ->
      "unsupported " ^ str
  | PARSER str ->
      "TODO(msg) PARSER ==> " ^ str
  | OTHER str ->
      "TODO(msg) OTHER ==> " ^ str

type std_ref =
  | StdRef of string list
  | UnknownRef
  | NoRef

let std_ref_of_option = function
  | Some ref -> StdRef [ref]
  | None -> UnknownRef

let get_misc_violation_ref = function
  (* TODO: check if footnote is being printed *)
  | MultipleEnumDeclaration _ ->
      StdRef ["§6.7.2.2#3"; "FOOTNOTE.127"]
  | EnumSimpleDeclarationConstruction ->
      StdRef ["§6.7.2.3#7"; "FOOTNOTE.131"]
  | UndeclaredIdentifier _ ->
      StdRef ["§6.5.1#2"]
  | ArrayDeclarationStarIllegalScope ->
      StdRef ["§6.7.6.2#4, 2nd sentence"]
  | ArrayCharStringLiteral ->
      StdRef ["§6.7.9#14"]
  | UniqueVoidParameterInFunctionDeclaration
  | TypedefInitializer ->
      UnknownRef

let get_desugar_ref = function
  | Desugar_ConstraintViolation e ->
      StdRef (Constraint.std_of_violation e)
  | Desugar_UndefinedBehaviour ub ->
      std_ref_of_option @@ Undefined.std_of_undefined_behaviour ub
  | Desugar_NotYetSupported _ ->
      NoRef
  | Desugar_MiscViolation e ->
      get_misc_violation_ref e
  | _ ->
      UnknownRef

let get_std_ref = function
  | CPARSER _ ->
      NoRef
  | DESUGAR dcause ->
      get_desugar_ref dcause
  | AIL_TYPING tcause ->
      StdRef (std_of_ail_typing_error tcause)
  | _ ->
      NoRef

let get_quote ref =
  let key =
    String.split_on_char ',' ref |> List.hd (* remove everything after ',' *)
  in
  match !!cerb_conf.n1507 with
  | Some (`Assoc xs) ->
    begin match List.assoc_opt key xs with
      | Some (`String b) -> "\n" ^ b
      | _ -> "(ISO C11 quote not found)"
    end
  | _ -> failwith "Missing N1507 json file..."

let make_message loc err k =
  let (head, pos) = Location_ocaml.head_pos_of_location loc in
  let kind = string_of_kind k in
  let msg = ansi_format [Bold] (short_message err) in
  let rec string_of_refs = function
    | [] -> "unknown ISO C reference"
    | [ref] -> ref
    | ref::refs -> ref ^ ", " ^ string_of_refs refs
  in
  let rec string_of_quotes = function
    | [] -> "no C11 reference"
    | [ref] -> ansi_format [Bold] ref ^ ": " ^ get_quote ref
    | ref::refs -> ansi_format [Bold] ref ^ ": " ^ get_quote ref ^ "\n\n" ^ string_of_quotes refs
  in
  match !!cerb_conf.error_verbosity, get_std_ref err with
  | Basic, _
  | _, NoRef ->
      Printf.sprintf "%s %s %s\n%s" head kind msg pos
  | RefStd, StdRef refs ->
      Printf.sprintf "%s %s %s (%s)\n%s" head kind msg (string_of_refs refs) pos
  | RefStd, UnknownRef
  | QuoteStd, UnknownRef ->
      Printf.sprintf "%s %s %s (unknown ISO C reference)\n%s" head kind msg pos
  | QuoteStd, StdRef refs ->
      Printf.sprintf "%s %s %s\n%s\n%s" head kind msg pos (string_of_quotes refs)

let to_string (loc, err) =
  make_message loc err Error
