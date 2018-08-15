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

let get_line n ic =
  seek_in ic 0;
  let rec aux = function
    | 1 -> input_line ic
    | n -> let _ = input_line ic in
           aux (n-1) in
  aux n

let string_of_pos pos =
  ansi_format [Bold] (
    Printf.sprintf "%s:%d:%d:" pos.pos_fname pos.pos_lnum (1 + pos.pos_cnum - pos.pos_bol)
  )

external terminal_size: unit -> (int * int) option = "terminal_size"

let string_at_line fname lnum cpos =
  try
    if Sys.file_exists fname then
      let ic = open_in fname in
      let l =
        let l_ = get_line lnum ic in
        match terminal_size () with
          | None ->
              (None, l_)
          | Some (_, term_col) ->
              if cpos >= term_col then begin
                (* The cursor position is beyond the width of the terminal *)
                let mid = term_col / 2 in
                let start  = max 0 (cpos - mid) in
                let n = String.length l_ - start in
                ( Some (cpos - start + 5)
                , if n + 5 <= term_col then
                    "  ..." ^ String.sub l_ start n
                  else
                  "  ..." ^ String.sub l_ start (term_col - 5 - 3) ^ "..." )
              end else if String.length l_ > term_col then
                (* The cursor is within the terminal width, but the line needs
                   to be truncated *)
                (None, String.sub l_ 0 (term_col - 3) ^ "...")
              else
                (None, l_) in
      close_in ic;
      Some l
    else
      None
  with
    End_of_file ->
      (* TODO *)
      None

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
  | InvalidTypeCompoundLiteral ->
      "compound literal has invalid type"
  | ExpressionNotLvalue ->
      "expression is not assignable"
  | InvalidArgumentTypeUnaryIncrement ->
      "invalid argument type to the increment operator"
  | InvalidArgumentTypeUnaryDecrement ->
      "invalid argument type to the increment operator"
  | UnaryAddressNotRvalue ->
      "cannot take address of an rvalue"
  | UnaryAddressRegisterLvalue ->
      "address of lvalue declared with register storage-class specifier"
  | IndirectionNotPointer ->
      "the * operator expects a pointer operand"
  | InvalidArgumentTypeUnaryExpression ->
      "invalid argument type to unary expression"
  | AssignmentIncompatibleType ty ->
      "assigning to '" ^ String_ail.string_of_ctype AilTypes.no_qualifiers ty ^ "' from incompatible type"
  | AssignmentIncompatiblePointerType ->
      "assigning to incompatible pointer types"
  | AssignmentDiscardsQualifiers ->
      "assignment discards qualifiers"
  | IntegerConstantOutRange ->
      "integer constant not in the range of the representable values for its type"
  | NoLinkageMultipleDeclaration (Cabs.CabsIdentifier (_, str)) ->
      "multiple declaration of '" ^ str ^ "'"
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
  | StructMemberFunctionType (Cabs.CabsIdentifier (_, f)) ->
      "member '" ^ f ^ "' declared as a function"
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
  | LabelRedefinition (Cabs.CabsIdentifier (_, str)) ->
      "redefinition of '" ^ str ^ "'"
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
      "pointer to type '" ^ String_ail.string_of_ctype AilTypes.no_qualifiers ty ^ "' may not be restrict qualified"
  | RestrictQualifiedTypeConstraint ->
      "restrict requires a pointer"
  | TagRedefinition sym ->
      "redefinition of '" ^ Pp_symbol.to_string_pretty sym ^ "'"
  | TagRedeclaration sym ->
      "use of '" ^ Pp_symbol.to_string_pretty sym ^ "' with tag type that does not match previous declaration"
  | UndeclaredLabel (Cabs.CabsIdentifier (_, str)) ->
      "use of undeclared label '" ^ str ^ "'"
  | ContinueOutsideLoop ->
      "continue statement outside a loop"
  | BreakOutsideSwtichOrLoop ->
      "break statement outside a switch or a loop"
  | NonVoidReturnVoidFunction ->
      "void function should not return a value"
  | VoidReturnNonVoidFunction ->
      "non-void function should return a value"
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
  | IllegalStorageClassIterationStatement
  | IllegalStorageClassFileScoped
  | IllegalStorageClassFunctionDefinition ->
      "illegal storage class"
  | IllegalIdentifierTypeVoidInFunctionDefinition ->
      "argument may not have 'void' type"
  | UniqueVoidParameterInFunctionDefinition ->
      "'void' must be the first and only parameter if specified"
  | ExternalRedefinition sym ->
      "redefinition of '" ^ Pp_utils.to_plain_string (Pp_ail.pp_id sym) ^ "'"

let string_of_misc_violation = function
  | MultipleEnumDeclaration (Cabs.CabsIdentifier (_, str)) ->
      "redefinition of '" ^ str ^ "'"
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
  | StdRef of string
  | UnknownRef
  | NoRef

let std_ref_of_option = function
  | Some ref -> StdRef ref
  | None -> UnknownRef

let get_misc_violation_ref = function
  (* TODO: check if footnote is being printed *)
  | MultipleEnumDeclaration _ ->
      StdRef "§6.7.2.2#3, FOOTNOTE.127"
  | EnumSimpleDeclarationConstruction -> 
      StdRef "§6.7.2.3#7, FOOTNOTE 131"
  | UndeclaredIdentifier _ ->
      StdRef "§6.5.1#2"
  | ArrayDeclarationStarIllegalScope ->
      StdRef "§6.7.6.2#4, 2nd sentence"
  | ArrayCharStringLiteral ->
      StdRef "§6.7.9#14"
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
      std_ref_of_option @@ std_of_ail_typing_error tcause
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
  let head = match loc with
    | Loc_unknown ->
        "unknown location "
    | Loc_other str ->
        "other location (" ^ str ^ ") "
    | Loc_point pos ->
        string_of_pos pos
    | Loc_region (start_p, _, _) ->
        string_of_pos start_p
  in
  let kind = string_of_kind k in
  let msg = ansi_format [Bold] (short_message err) in
  let pos = match loc with
    | Loc_point pos ->
        let cpos = pos.pos_cnum - pos.pos_bol in
        (match string_at_line pos.pos_fname pos.pos_lnum cpos with
          | Some (cpos'_opt, l) ->
              let cpos = match cpos'_opt with
                | Some cpos' -> cpos'
                | None       -> cpos in
              l ^ "\n" ^
              ansi_format [Bold; Green] (String.init (cpos + 1) (fun n -> if n < cpos then ' ' else '^'))
          | None ->
              "")
    | Loc_region (start_p, end_p, cursor_p_opt) ->
        let cpos1 = start_p.pos_cnum - start_p.pos_bol in
        (match string_at_line start_p.pos_fname start_p.pos_lnum cpos1 with
          | Some (_, l) ->
              let cpos2 =
                if start_p.pos_lnum = end_p.pos_lnum then
                  end_p.pos_cnum - end_p.pos_bol
                else
                  String.length l in
              let cursor = match cursor_p_opt with
                | Some cursor_p ->
                    cursor_p.pos_cnum - cursor_p.pos_bol 
                | None ->
                    cpos1 in
              l ^ "\n" ^
              ansi_format [Bold; Green] (
                String.init ((max cursor cpos2) + 1)
                  (fun n -> if n = cursor then '^' else if n >= cpos1 && n < cpos2 then '~' else ' ')
              )
          | None ->
              "")
    | _ -> ""
  in
  match !!cerb_conf.error_verbosity, get_std_ref err with
  | Basic, _
  | _, NoRef ->
      Printf.sprintf "%s %s %s\n%s" head kind msg pos
  | RefStd, StdRef ref ->
      Printf.sprintf "%s %s %s (%s)\n%s" head kind msg ref pos
  | RefStd, UnknownRef
  | QuoteStd, UnknownRef ->
      Printf.sprintf "%s %s %s (unknown ISO C reference)\n%s" head kind msg pos
  | QuoteStd, StdRef ref ->
      Printf.sprintf "%s %s %s\n%s\n%s: %s" head kind msg pos
        (ansi_format [Bold] ref) (get_quote ref)

let to_string (loc, err) =
  make_message loc err Error
