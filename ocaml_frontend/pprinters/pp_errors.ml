open Lexing

open Errors
open TypingError
open Constraint

open Cerb_global
open Cerb_location

open Cerb_colour
open Cerb_pp_prelude

type kind =
  | Error
  | Warning
  | Note

let string_of_kind = function
  | Error ->
      ansi_format ~err:true [Bold; Red] "error:"
  | Warning ->
      ansi_format ~err:true [Bold; Magenta] "warning:"
  | Note ->
      ansi_format ~err:true [Bold; Black] "note:"


let string_of_cid (Symbol.Identifier (_, s)) = s
let string_of_ctype ty = String_ail.string_of_ctype ~is_human:true Ctype.no_qualifiers ty
let string_of_sym = Pp_symbol.to_string_pretty
let string_of_gentype = String_ail.string_of_genType

let string_of_cparser_cause = function
  | Cparser_invalid_symbol ->
      "invalid symbol"
  | Cparser_invalid_string_character ->
      "invalid string character"
  | Cparser_invalid_line_number n ->
      "invalid line directive:" ^ n
  | Cparser_unexpected_eof ->
      "unexpected end of file"
  | Cparser_unexpected_token str ->
      "unexpected token " ^ str
  | Cparser_non_standard_string_concatenation ->
      "unsupported non-standard concatenation of string literals"
  | Cparser_extra_semi AFTER_FUNCTION ->
      "found a semicolon after a function definition"
  | Cparser_extra_semi INSIDE_STRUCT ->
      "found an extra semicolon inside a struct definition"
  | Cparser_extra_semi INSIDE_UNION ->
      "found an extra semicolon inside a union definition"
  | Cparser_KnR_declaration ->
      "found K&R-style declaration (unsupported)"
  | Cparser_nested_comment ->
      "nested comment"
  | Cparser_unterminated_comment str ->
      "unterminated " ^ str ^ " comment"
  | Cparser_mismatched_magic_comment ->
      "magic comment syntax at open but not close"
  | Cparser_experimental_keyword str -> 
      "experimental keyword '" ^ str ^ "' (use of experimental features is discouraged)"
  | Cparser_unimplemented_keyword str -> 
      "unimplemented keyword '" ^ str ^ "'"


let string_of_constraint_violation = function
  | FunctionCallIncompleteReturnType ty ->
      "calling function with incomplete return type '" ^ string_of_ctype ty ^ "'"
  | FunctionCallArrayReturnType ty ->
      "calling function returning an array type '" ^ string_of_ctype ty ^ "'"
  | FunctionCallIncorrectType ->
      "called object type is not a function or function pointer"
  | FunctionCallTooManyArguments (expected, have) ->
      "too many arguments to function call, expected " ^ string_of_int expected ^ ", have " ^ string_of_int have
  | FunctionCallTooFewArguments (expected, have) ->
      "too few arguments to function call, expected " ^ string_of_int expected ^ ", have " ^ string_of_int have
  | MemberofReferenceBaseTypeLvalue (qs, ty) ->
      "member reference base type '" ^ String_ail.string_of_ctype ~is_human:true qs ty ^ "' is not a structure or union"
  | MemberofReferenceBaseTypeRvalue gty ->
      "member reference base type '" ^ string_of_gentype gty ^ "' is not a structure or union"
  | MemberofNoMemberLvalue (memb, qs, ty) ->
      "no member named '" ^ string_of_cid memb ^ "' in '" ^ String_ail.string_of_ctype ~is_human:true qs ty ^ "'"
  | MemberofNoMemberRvalue (memb, gty) ->
      "no member named '" ^ string_of_cid memb ^ "' in '" ^ string_of_gentype gty ^ "'"
  | MemberofIncompleteLvalue (qs, ty) ->
      "struct/union type '" ^ String_ail.string_of_ctype ~is_human:true qs ty ^ "' in . operator is incomplete"
  | MemberofIncompleteRvalue gty ->
      "struct/union type '" ^ string_of_gentype gty ^ "' in . operator is incomplete"
  | MemberofptrReferenceTypeNotPointer gty ->
      "member reference type '" ^ string_of_gentype gty ^ "' is not a pointer" ^
      (if GenTypesAux.is_struct_or_union0 gty then "; did you mean to use '.'?" else "")
  | MemberofptrReferenceBaseType (qs, ty) ->
      "member reference base type '" ^ String_ail.string_of_ctype ~is_human:true qs ty ^ "' is not a structure or union"
  | MemberofptrNoMember (memb, qs, ty) ->
      "no member named '" ^ string_of_cid memb ^ "' in '" ^ String_ail.string_of_ctype ~is_human:true qs ty ^ "'"
  | MemberofptrIncomplete (qs, ty) ->
      "struct/union type '" ^ String_ail.string_of_ctype ~is_human:true qs ty ^ "' in -> operator is incomplete"
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
  | SizeofInvalidApplication gty ->
      let suffix =
        if GenTypesAux.is_function0 gty then "a function type"
        else "an incomplete type '" ^ string_of_gentype gty ^ "'"
      in "invalid application of 'sizeof' to " ^ suffix
  | AlignofInvalidApplication (qs, ty) ->
      let suffix =
        if AilTypesAux.is_function ty then "a function type"
        else "an incomplete type '" ^ String_ail.string_of_ctype ~is_human:true qs ty ^ "'"
      in "invalid application of '_Alignof' to " ^ suffix
  | CastInvalidType (qs, ty) ->
      "used type '" ^ String_ail.string_of_ctype ~is_human:true qs ty ^ "' where scalar type is required"
  | CastPointerToFloat ->
      "pointer cannot be cast to type 'float'"
  | CastFloatToPointer ->
      "operand of type 'float' cannot be cast to a pointer type"
  | ArithBinopOperandsType (_, gty1, gty2)
  | RelationalInvalidOperandsType (gty1, gty2)
  | EqualityInvalidOperandsType (gty1, gty2)
  | AndInvalidOperandsType (gty1, gty2)
  | OrInvalidOperandsType (gty1, gty2)
  | CompoundAssignmentAddSubOperandTypes (gty1, gty2)
  | CompoundAssignmentOthersOperandTypes (_, gty1, gty2) ->
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
  | SimpleAssignmentViolation (NotArithmetic, ty1, gty2) ->
      "assigning to '" ^ string_of_ctype ty1 ^ "' from non arithmetic type '" ^ string_of_gentype gty2 ^ "'"
  | SimpleAssignmentViolation (BoolExpectsArithmeticOrPointer, ty1, gty2) ->
      "assigning to '" ^ string_of_ctype ty1 ^ "' from non scalar type '" ^ string_of_gentype gty2 ^ "'"
  | IntegerConstantOutRange ->
      "integer constant not in the range of the representable values for its type"
  | NoLinkageMultipleDeclaration x ->
      "multiple declaration of '" ^ string_of_cid x ^ "'"
  | TypedefRedefinition ->
      "typedef redefinition with different types"
  | TypedefRedefinitionVariablyModifiedType ->
      "typedef redefinition of a variably modified type"
  | SameScopeIncompatibleDeclarations ->
      "multiple declarations in the same scope with incompatible types"
  | IllegalMultipleStorageClasses
  | IllegalMultipleStorageClassesThreadLocal ->
      "multiple incompatible storage class specifiers"
  | ThreadLocalShouldAppearInEveryDeclaration ->
      "non-thread-local declaration follows a thread-local declaration"
  | ThreadLocalFunctionDeclaration ->
      "_Thread_local in function declaration"
  | StructMemberIncompleteType (qs, ty) ->
      "member has incomplete type '" ^ String_ail.string_of_ctype ~is_human:true qs ty ^ "'"
  | StructMemberFunctionType f ->
      "member '" ^ string_of_cid f ^ "' declared as a function"
  | StructMemberFlexibleArray ->
      "struct member has a type with a flexible array member"
  | StructMemberFlexibleArrayInArray ->
      "struct member with a flexible array member found as element of an array"
  | IllegalFlexibleArrayMember tag_ident ->
      "found a flexible array member in a structure with less than one named member: " ^
      string_of_cid tag_ident
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
  | CaseStatementOverlap prev_loc ->
      "duplicate case value"
  | MutipleDefaultStatement prev_loc ->
      "multiple default labels in one switch"
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
  | BreakOutsideSwitchOrLoop ->
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
  | ReturnAsSimpleAssignment (NotArithmetic, ty1, gty2) ->
      "returning '" ^ string_of_gentype gty2 ^ "' from a function with an arithmetic result type '" ^ string_of_ctype ty1 ^ "'"
  | ReturnAsSimpleAssignment (BoolExpectsArithmeticOrPointer, ty1, gty2) ->
      "returning non scalar type '" ^ string_of_gentype gty2 ^ "' from a function with result type '" ^ string_of_ctype ty1 ^ "'"
  | IllegalAlignas kind (* §6.7.5#2 *) ->
      let kind_str =
        match kind with
          | IllegalAlignas_typedef ->
              "a typedef"
          | IllegalAlignas_bitfield ->
              "a bitfield"
          | IllegalAlignas_function ->
              "a function"
          | IllegalAlignas_parameter ->
              "a parameter"
          | IllegalAlignas_register ->
              "an object declared with the register storage-class specifier" in
      "alignment specifier is in the declaration of " ^ kind_str
  | AlignasNotIntegerConstant (* §6.7.5#3, sentence 1 *) ->
      "expression in an alignment specifier is not an integer constant expression"
  | AlignasInvalidIntegerConstant (* §6.7.5#3, sentence 2 *) ->
      "alignment specifier with that does not evaluate to a valid fundamental alignment"
  | AlignasLessThanRequired decl_ty (* §6.7.5#4 *) ->
      "alignment specifier less strict than the declaration type '" ^ string_of_ctype decl_ty ^ "'"
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
  | IllegalInitialisation (InitialisedIncomplete ty) ->
      "initialisation of an entity with an incomplete type: '" ^ string_of_ctype ty ^ "'"
  | IllegalInitialisation InitialisedVLA ->
      "initialisation of a variable length array"
  | IllegalStorageClassStaticOrThreadInitializer ->
      "initializer element is not a compile-time constant"
  | IllegalLinkageAndInitialization ->
      "identifier linkage forbids to have an initializer"
  | IllegalArrayDesignatorUsage ->
      "array designator used for an entity with a non-array type"
  | IllegalTypeArrayDesignator ->
      "expression is not an integer constant expression"
  | IllegalSizeArrayDesignator ->
      "array designator value is negative"
  | IllegalMemberDesignatorUsage ->
      "member designator used for an entity with a non-struct/union type"
  | IllegalMemberDesignatorFlexibleArrayMember (Symbol.Identifier (_, memb_str)) ->
      "member designator '." ^ memb_str ^ "' refers to a flexible array member"
  | IllegalMemberDesignator (Symbol.Identifier (_, memb_str), ty) ->
      "member designator '." ^ memb_str ^ "' does not refer to a valid member for type '" ^ string_of_ctype ty ^ "'"
  | InitializationAsSimpleAssignment (IncompatibleType, ty1, gty2) ->
      "initializing '" ^ string_of_ctype ty1 ^ "' with an expression of incompatible type '" ^ string_of_gentype gty2 ^ "'"
  | InitializationAsSimpleAssignment (IncompatiblePointerType, ty1, gty2) ->
      "incompatible pointer types initializing '" ^ string_of_ctype ty1 ^ "' with an expression of type '" ^ string_of_gentype gty2 ^ "'"
  | InitializationAsSimpleAssignment (DiscardsQualifiers, ty1, gty2) ->
      "initializing '" ^ string_of_ctype ty1 ^ "' with an expression of type '" ^ string_of_gentype gty2 ^ "' discards qualifiers"
  | InitializationAsSimpleAssignment (NotArithmetic, ty1, gty2) ->
      "initializing '" ^ string_of_ctype ty1 ^ "' with an expression with a non arithmetic type '" ^ string_of_gentype gty2 ^ "'"
  | InitializationAsSimpleAssignment (BoolExpectsArithmeticOrPointer, ty1, gty2) ->
      "initializing '" ^ string_of_ctype ty1 ^ "' with an expression with a non scalar type '" ^ string_of_gentype gty2 ^ "'"
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
  | FunctionParameterAsSimpleAssignment (NotArithmetic, ty1, gty2) ->
      "passing non arithmetic '" ^ string_of_gentype gty2 ^ "' to parameter of type '" ^ string_of_ctype ty1 ^ "'"
  | FunctionParameterAsSimpleAssignment (BoolExpectsArithmeticOrPointer, ty1, gty2) ->
      "passing non scalar '" ^ string_of_gentype gty2 ^ "' to parameter of type '" ^ string_of_ctype ty1 ^ "'"
  | TentativeNotCompleted ty ->
      "tentative definition with type '" ^ string_of_ctype ty ^ "' which is not completed by the end of the translation unit"
  | ExternalRedefinition sym ->
      "redefinition of '" ^ string_of_sym sym ^ "'"
  | AssertMacroExpressionScalarType ->
      "assert expression should have scalar type"
  | AtomicAddressArgumentMustBeAtomic (_, ty) ->
      "address argument to atomic operation must be a pointer to _Atomic type ('" ^ string_of_ctype ty ^ "' invalid)"
  | AtomicAddressArgumentMustBePointer (_, gty) ->
      "address argument to atomic operation must be a pointer ('" ^ string_of_gentype gty ^ "' invalid)"
  | GNUConditionalOperatorInvalidOperandType gty ->
      "illtypd second operand in a GNU ?: expression ('" ^ string_of_gentype gty ^ "')"
  | GNUBuiltinChooseExprNotIntegerConstant ->
      "first operand of __builtin_choose_expr() is not an integer constant expression"

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
      (ansi_format ~err:true [Bold] "constraint violation: ") ^ string_of_constraint_violation e
  | Desugar_MiscViolation e ->
      string_of_misc_violation e
  | Desugar_UndefinedBehaviour ub ->
      (ansi_format ~err:true [Bold] "undefined behaviour: ") ^ Undefined.ub_short_string ub
  | Desugar_NeverSupported str ->
      "feature that will never supported: " ^ str
  | Desugar_NotYetSupported str ->
      "feature not yet supported: " ^ str
  | Desugar_agnosticFailure str ->
      "agnostic mode could not carry on: `" ^ str ^ "' (consider removing --agnotic)"
  | Desugar_illtypedIntegerConstant ->
      "failed to typecheck an integer constant expression"
  | Desugar_CN e ->
      Cn_ocaml.string_of_error e
  | Desugar_TODO msg ->
      "TODO: " ^ msg

let string_of_ail_typing_misc_error = function
  | UntypableIntegerConstant i ->
      "integer constant cannot be represented by any type"
  | UnableToTypeIntegerConstant ->
      "the implementation setting is not complete enough to type the integer constant. \
       Try using another implementation of the --agnostic flag"
  | ParameterTypeNotAdjusted ->
      "internal: the parameter type was not adjusted"
  | VaStartArgumentType ->
      "the first argument of 'va_start' must be of type 'va_list'"
  | VaArgArgumentType ->
      "the first argument of 'va_arg' must be of type 'va_list'"
  | GenericFunctionMustBeDirectlyCalled ->
      "builtin generic functions must be directly called"

let string_of_ail_typing_error = function
  | TError_ConstraintViolation tcv ->
      (ansi_format ~err:true [Bold] "constraint violation: ") ^ string_of_constraint_violation tcv
  | TError_UndefinedBehaviour ub ->
      (ansi_format ~err:true [Bold] "undefined behaviour: ") ^ Undefined.ub_short_string ub
  | TError_MiscError tme ->
      string_of_ail_typing_misc_error tme
  | TError_NotYetSupported str ->
      "feature not yet supported: " ^ str
  | TError_CN Cn.CNErr_typing_TODO ->
      "CN typing error"

let string_of_bty =
  String_core.string_of_core_base_type

let string_of_name = function
  | Core.Sym sym -> string_of_sym sym
  | Core.Impl impl -> Implementation.string_of_implementation_constant impl

let string_of_binop bop =
  let open Core in
  match bop with
  | OpAdd -> "+"
  | OpSub -> "-"
  | OpMul -> "*"
  | OpDiv -> "/"
  | OpRem_t -> "rem_t"
  | OpRem_f -> "rem_f"
  | OpExp -> "^"
  | OpEq -> "="
  | OpGt -> ">"
  | OpLt -> "<"
  | OpGe -> ">="
  | OpLe -> "<="
  | OpAnd -> "/\\"
  | OpOr -> "\\/"

let string_of_core_typing_cause = function
  | UndefinedStartup sym ->
      "undefined startup procedure '" ^ string_of_sym sym ^ "'"
  | Mismatch (str, expected, found) ->
      (if !Cerb_debug.debug_level > 0 then "(" ^ str ^ "):\n" else "") ^
      "this expression is of type '" ^ string_of_bty found ^
      "' but an expression of type '" ^ string_of_bty expected ^ "' was expected"
  | MismatchBinaryOperator bop ->
      "incompatible operand types to binary operation '" ^ string_of_binop bop ^ "'"
  | TooGeneral ->
      "unable to infer the type of this expression (too general)"
  | MismatchIf (then_bTy, else_bTy) ->
      "type mismatch in conditional expression ('" ^ string_of_bty then_bTy ^ "' and '" ^ string_of_bty else_bTy ^ "')"
  | MismatchExpected (str, expected, found) ->
      (if !Cerb_debug.debug_level > 0 then "(" ^ str ^ "):\n" else "") ^
      "this expression is of type '" ^ found ^
      "' but an expression of type '" ^ string_of_bty expected ^ "' was expected"
  | MismatchFound (str, expected, m_found) ->
      (if !Cerb_debug.debug_level > 0 then "(" ^ str ^ "):\n" else "") ^
      (match m_found with Some found -> "this expression is of type '" ^ string_of_bty found ^ "' but " | None -> "") ^
      "an expression of type '" ^ expected ^ "' was expected"
  | CFunctionExpected nm ->
      "symbol '" ^ string_of_name nm ^ "' has incorrect type, a symbol of type 'cfunction' was expected"
  | CFunctionParamsType ->
      "core procedures used as C functions must only have pointer parameters (or list of pointers when variadic)"
  | CFunctionReturnType ->
      "core procedures used as C functions must return unit or an object value"
  | UnresolvedSymbol nm ->
      "unresolved symbol '" ^ string_of_name nm ^ "'"
  | FunctionOrProcedureSymbol sym ->
      "unexpected function/procedure '" ^ string_of_sym sym ^ "'"
  | HeterogenousList (expected_bTy, found_bTy) ->
      "HeterogenousList(" ^
      String_core.string_of_core_base_type expected_bTy ^ ", " ^
      String_core.string_of_core_base_type found_bTy ^ ")"
  | InvalidTag tag_sym ->
      "InvalidTag(" ^ Pp_symbol.to_string tag_sym ^ ")"
  | InvalidMember (tag_sym, Symbol.Identifier (_, memb_str)) ->
      "InvalidMember(" ^ Pp_symbol.to_string tag_sym ^ ", " ^ memb_str ^ ")"
  | CoreTyping_TODO str ->
      "CoreTyping_TODO(" ^ str ^ ")"

let string_of_core_linking_cause = function
  | DuplicateExternalName (Symbol.Identifier (_, name)) ->
      "duplicate external symbol: " ^ name
  | DuplicateMain ->
      "duplicate main function"
  | IncompatibleCallingConvention ->
      "incompatible calling conventions"


let string_of_core_run_cause = function
  | Illformed_program str ->
      "ill-formed program: `" ^ str ^ "'"
  | Found_empty_stack str ->
      "found an empty stack: `" ^ str ^ "'"
  | Reached_end_of_proc ->
      "reached the end of a procedure"
  | Unknown_impl ->
      "unknown implementation constant"
  | Unresolved_symbol (loc, sym) ->
      "unresolved symbol: " ^ (Pp_utils.to_plain_string (Pp_ail.pp_id sym)) ^ " at " ^ Cerb_location.location_to_string loc

let string_of_core_parser_cause = function
  | Core_lexer (Core_lexer_invalid_symbol c) ->
      "invalid symbol '"^ String.make 1 c ^ "'"
  | Core_lexer (Core_lexer_invalid_implname str) ->
      "invalid impl-name '"^ str ^ "'"
  | Core_lexer (Core_lexer_invalid_ubname str) ->
      "invalid ub-name '"^ str ^ "'"
  | Core_parser_unexpected_token str ->
      "unexpected token '"^ str ^ "'"
  | Core_parser_unresolved_symbol str ->
      "unresolved symbol '" ^ str ^ "'"
  | Core_parser_multiple_declaration str ->
      "multiple declaration of '" ^ str ^ "'"
  | Core_parser_ctor_wrong_application (expected, found) ->
      "wrong number of expression in application, expected " ^ string_of_int expected ^ ", found " ^ string_of_int found
  | Core_parser_wrong_decl_in_std ->
      "wrong declaration in std" (* TODO: ?? *)
  | Core_parser_unknown_ctype str ->
      "unknown ctype '" ^ str ^ "'"
  | Core_parser_undefined_startup ->
      "undefined startup function"
  | Core_parser_internal_error str ->
      "internal error in the Core parser: " ^ str

let string_of_driver_cause = function
  | Driver_UB ubs ->
      String.concat "\n" @@ List.map (fun ub -> (ansi_format ~err:true [Bold] "undefined behaviour: ") ^ Undefined.ub_short_string ub) ubs

let short_message = function
  | CPP err ->
      err
  | CPARSER ccause ->
      string_of_cparser_cause ccause
  | DESUGAR dcause ->
      string_of_desugar_cause dcause
  | AIL_TYPING terr ->
      string_of_ail_typing_error terr
  | CORE_TYPING tcause ->
      string_of_core_typing_cause tcause
  | CORE_LINKING lcause ->
      string_of_core_linking_cause lcause
  | CORE_RUN cause ->
      string_of_core_run_cause cause
  | UNSUPPORTED str ->
      "unsupported " ^ str
  | CORE_PARSER ccause ->
      string_of_core_parser_cause ccause
  | DRIVER dcause ->
      string_of_driver_cause dcause

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

let get_driver_ref = function
  | Driver_UB ubs ->
    StdRef (List.concat
              (List.map (fun ub ->
                   match Undefined.std_of_undefined_behaviour ub with
                   | Some x -> [x]
                   | None -> []) ubs))

let get_std_ref = function
  | CPARSER _ ->
      NoRef
  | DESUGAR dcause ->
      get_desugar_ref dcause
  | AIL_TYPING tcause ->
      StdRef (std_of_ail_typing_error tcause)
  | DRIVER dcause ->
      get_driver_ref dcause
  | _ ->
      NoRef

let get_quote ref =
  let key =
    String.split_on_char ',' ref |> List.hd (* remove everything after ',' *)
  in
  match Cerb_global.n1570 () with
  | Some (`Assoc xs) ->
    begin match List.assoc_opt key xs with
      | Some (`String b) -> "\n" ^ b
      | _ -> "(ISO C11 quote not found)"
    end
  | _ -> failwith "Missing N1507 json file..."

let make_message loc err k =
  let (head, pos) = Cerb_location.head_pos_of_location loc in
  let kind = string_of_kind k in
  let msg = ansi_format ~err:true [Bold] (short_message err) in
  let rec string_of_refs = function
    | [] -> "unknown ISO C reference"
    | [ref] -> ref
    | ref::refs -> ref ^ ", " ^ string_of_refs refs
  in
  let rec string_of_quotes = function
    | [] -> "no C11 reference"
    | [ref] -> ansi_format ~err:true [Bold] ref ^ ": " ^ get_quote ref
    | ref::refs -> ansi_format ~err:true [Bold] ref ^ ": " ^ get_quote ref ^ "\n\n" ^ string_of_quotes refs
  in
  match Cerb_global.verbose (), get_std_ref err with
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
  match err with
  | CPP err -> err (* NOTE: the err string is already formatted by CPP *)
  | _ -> make_message loc err Error

let fatal msg =
  prerr_endline (ansi_format ~err:true [Bold; Red] "error: " ^ ansi_format ~err:true [Bold] msg);
  exit 1
