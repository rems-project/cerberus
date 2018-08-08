open Lexing

open Errors
open TypingError

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
  | IllegalStorageClassFileScoped ->
      "illegal storage class"

let string_of_desugar_cause = function
  | Desugar_ConstraintViolation e ->
      (ansi_format [Bold] "contraint violation: ") ^ string_of_constraint_violation e
  | Desugar_OldConstraintViolation msg ->
      "violation of constraint " ^ msg
  | Desugar_UndeclaredIdentifier str ->
      "use of undeclared identifier '" ^ str ^ "'"
  | Desugar_OtherViolation msg ->
      "other violation: " ^ msg
  | Desugar_UndefinedBehaviour ub ->
      (ansi_format [Bold] "undefined behaviour: ") ^ Undefined.ub_short_string ub
  | Desugar_ExternalObjectRedefinition sym ->
      "redefinition of an external object: " ^
      Pp_utils.to_plain_string (Pp_ail.pp_id sym)
  | Desugar_FunctionRedefinition sym ->
       "(TODO msg) redefinition of '" ^
      (Pp_utils.to_plain_string (Pp_ail.pp_id sym)) ^ "'\n"
  | Desugar_BlockScoped_Thread_local_alone ->
      "Violation of constraint 6.7.1#3 Storage-class specifiers, Contraints: \
       ``In the declaration of an object with block scope, if the declaration \
       specifiers include _Thread_local, they shall also include either static \
       or extern. [...].. ``\n"
  | Desugar_NotConstantExpression ->
      "found a non-contant expression in place of a constant one.\n"
  | Desugar_MultipleDeclaration (Cabs.CabsIdentifier (_, str)) ->
      "violation of constraint (§6.7#3): multiple declaration of `" ^
      str ^ "'."
  | Desugar_InvalidMember ((Cabs.CabsIdentifier (_, str)), ty) ->
      "member '" ^ str ^ "' is not defined for type '" ^
      String_ail.string_of_ctype AilTypes.no_qualifiers ty ^ "'"
  | Desugar_NonvoidReturn ->
      "non-void function should return a value"
  | Desugar_Redefinition sym ->
      "redefinition of: " ^ Pp_utils.to_plain_string (Pp_ail.pp_id sym)
  | Desugar_NeverSupported str ->
      "feature that will never supported: " ^ str
  | Desugar_NotyetSupported str ->
      "feature not yet supported: " ^ str
  | Desugar_TODOCTOR str ->
      "Desugar_TODOCOTR[" ^ str ^ "]"
  | Desugar_impossible ->
      "impossible error"
  | Desugar_constantExpression_notInteger str ->
      "TODO(msg) Desugar_constantExpression_notInteger: " ^ str
  | Desugar_constantExpression_UB ubs ->
      "TODO(msg) Desugar_constantExpression_UB: " ^
      Pp_utils.to_plain_string (
        comma_list (fun z -> !^ (Undefined.pretty_string_of_undefined_behaviour z))
        ubs
      )

let string_of_ail_typing_error = function
  | TError_indirection_not_pointer ->
      "the * operator expects a pointer operand"
  | TError_main_return_type ->
      "return type of 'main' should be 'int'"
  | TError_main_not_function ->
      "variable named 'main' with external linkage has undefined behavior"
  | TError_main_param1 ->
      "invalid parameter type for 'main': first parameter must be of type 'int'"
  | TError_main_param2 ->
      "invalid parameter type for 'main': second parameter must be of type 'char **'"
  | TError std ->
      "[Ail typing] (" ^ std ^ ")\n  \"" ^ Pp_std.quote std ^ "\""
  | TError_undef ub ->
      "[Ail typing] found undefined behaviour: " ^
      Undefined.pretty_string_of_undefined_behaviour ub
  | TError_lvalue_coercion ty ->
      "[Ail typing error]\n failed lvalue coercion of type \"" ^
      Pp_utils.to_plain_string (Pp_ail.pp_ctype AilTypes.no_qualifiers ty) ^ "\""
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


let get_constraint_violation_ref = function
  | IllegalStorageClassFileScoped ->
      StdRef "§6.9#2"

let get_desugar_ref = function
  | Desugar_ConstraintViolation e ->
      get_constraint_violation_ref e
  | Desugar_UndefinedBehaviour ub ->
      (match Undefined.std_of_undefined_behaviour ub with
        | Some ref -> StdRef ref
        | None -> UnknownRef)
  | Desugar_UndeclaredIdentifier _ ->
      StdRef "§6.5.1#2"
  | Desugar_NonvoidReturn ->
      StdRef "§6.8.6.4#1, 2nd sentence"
  | _ ->
      UnknownRef

let get_ail_typing_ref = function
  | TError_main_return_type ->
      StdRef "§5.1.2.2.1#1, 2nd sentence"
  | TError_main_param1
  | TError_main_param2 ->
      StdRef "§5.1.2.2.1#1"
  | TError_indirection_not_pointer ->
      StdRef "§6.5.3.2#2"
  | _ ->
      UnknownRef

let get_std_ref = function
  | CPARSER _ ->
      NoRef
  | DESUGAR dcause ->
      get_desugar_ref dcause
  | AIL_TYPING tcause ->
      get_ail_typing_ref tcause
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


(*
let std_ref = function
  | Desugar_cause (Desugar_UndeclaredIdentifier _) ->
      "§6.5.1#2"
  | Desugar_cause Desugar_NonvoidReturn ->
    "§6.8.6.4#1, 2nd sentence"

  | AIL_TYPING TError_main_return_type ->
      "§5.1.2.2.1#1, 2nd sentence"
  | AIL_TYPING TError_main_not_function ->
      "blah"
  | AIL_TYPING TError_main_param1
  | AIL_TYPING TError_main_param2 ->
      "§5.1.2.2.1#1"
  | AIL_TYPING TError_indirection_not_pointer ->
      "§6.5.3.2#2"
  | AIL_TYPING (TError_TODO n) ->
      "Ail typing error (TODO " ^ string_of_int n ^ ")"
  | AIL_TYPING (TError std) ->
      std

  | Desugar_cause (Desugar_ConstraintViolation str) ->
      str
  | Core_run_cause _  ->
      "TODO: core_run_cause"
  | Core_typing_cause cause ->
      "Core typing error: " ^ 
      begin match cause with
        | Undefined_startup sym ->
            "undefined startup fun/proc '" ^ Pp_utils.to_plain_string (Pp_ail.pp_id sym) ^ "'"
        | MismatchObject (oTy1, oTy2) ->
            "mismatching object types, expecting: " ^ String_core.string_of_core_object_type oTy1 ^
            "found: " ^ String_core.string_of_core_object_type oTy2
        | Mismatch (str, bTy1, bTy2) ->
            "mismatching base types (in " ^ str ^ "), expecting: " ^ String_core.string_of_core_base_type bTy1 ^
            " -- found: " ^ String_core.string_of_core_base_type bTy2
        | MismatchIf (bTy1, bTy2) ->
            "mismatching types in a if-expression, then branch: " ^ String_core.string_of_core_base_type bTy1 ^
            " -- else branch: " ^ String_core.string_of_core_base_type bTy2
        | MismatchIfCfunction ((ret_bTy1, bTys1), (ret_bTy2, bTys2)) ->
            "mismatching signatures in a Cfunction if-expression, then branch: " ^
            Pp_utils.to_plain_string (Pp_core.Basic.pp_core_base_type ret_bTy1 ^^ P.parens (comma_list Pp_core.Basic.pp_core_base_type bTys1)) ^
            " -- else branch: " ^
            Pp_utils.to_plain_string (Pp_core.Basic.pp_core_base_type ret_bTy1 ^^ P.parens (comma_list Pp_core.Basic.pp_core_base_type bTys1))
        | EmptyArray ->
            "found an empty array"
        | CtorWrongNumber _ (*of nat (* expected *) * nat (* found *)*) ->
            "TODO(msg) CtorWrongNumber"
        | HeterogenousArray _ (* of core_object_type (* expected *) * core_object_type (* found *) *) ->
            "TODO(msg) HeterogenousArray"
        | HeterogenousList _ (* of core_base_type (* expected *) * core_base_type (* found *) *) ->
            "TODO(msg) HeterogenousList"
        | InvalidMember _ (* of Symbol.sym * Cabs.cabs_identifier *) ->
            "TODO(msg) InvalidMember"
        | CoreTyping_TODO str ->
            "TODO(msg) " ^ str
        | TooGeneral ->
            "too general"
      end
  | PARSER str ->
      "TODO: parsing error ==> " ^ str
  | _ ->
      "TODO: pp_errors std_ref"
   *)

