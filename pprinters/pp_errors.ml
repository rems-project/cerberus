open Global_ocaml
open Location_ocaml

open Lexing


open Errors
open TypingError

open Colour


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


let string_at_line fname lnum =
  if Sys.file_exists fname then
    let ic = open_in fname in
    let l =
      let l_ = get_line lnum ic in
      if String.length l_ > 100 then
        String.sub l_ 0 100 ^ " ... "
      else
        l_ in
    close_in ic;
    Some l
  else
    None
(*
 ^ "\n" ^
    ansi_format [Bold; Green] (String.init (cpos + 1) (fun n -> if n < cpos then ' ' else '^'))
  else
    ""
*)

(* we need this for old version of OCaml *)
let my_string_init n f =
  let str = String.create n in
  for i = 0 to n - 1 do
    String.unsafe_set str i (f i)
  done;
  str


let make_message loc k str =
  begin
    fun z -> match loc with
      | Loc_unknown ->
          "unknown location " ^ z
      | Loc_point pos ->
          Printf.sprintf "%s %s\n" (string_of_pos pos) z ^
          (match string_at_line pos.pos_fname pos.pos_lnum with
            | Some l ->
                let cpos = pos.pos_cnum - pos.pos_bol in
                l ^ "\n" ^
                ansi_format [Bold; Green] ((* Bytes.init *) my_string_init (cpos + 1) (fun n -> if n < cpos then ' ' else '^'))
            | None ->
                "")
      | Loc_region (start_p, end_p, cursor_p_opt) ->
          let cpos1 = start_p.pos_cnum - start_p.pos_bol in
          Printf.sprintf "%s %s\n" (string_of_pos start_p) z ^
          (match string_at_line start_p.pos_fname start_p.pos_lnum with
            | Some l ->
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
                ansi_format [Bold; Green] ((* String.init *) my_string_init (cpos2 + 1)
                                             (fun n -> if n = cursor then '^' else if n >= cpos1 && n < cpos2 then '~' else ' ')
                                          )




            | None ->
                "")


(* TODO *)
(*
        Printf.sprintf "%s %s\n%s" (string_of_pos start_p) z
            (string_at_pos start_p.pos_fname start_p.pos_lnum (start_p.pos_cnum - start_p.pos_bol))
*)
  end (string_of_kind k ^ " " ^ ansi_format [Bold] str)
  
(*
  Lexing.(
    let cpos = start_p.pos_cnum - start_p.pos_bol in
    ansi_format [Bold] (
      Printf.sprintf "%s:%d:%d: " start_p.pos_fname start_p.pos_lnum (cpos+1)
    ) ^ string_of_kind k ^ " " ^ ansi_format [Bold] str ^
    
    if Sys.file_exists start_p.pos_fname then
      let ic = open_in start_p.pos_fname in
      let l =
        let l_ = get_line start_p.pos_lnum ic in
        if String.length l_ > 100 then
          String.sub l_ 0 100 ^ " ... "
        else
          l_ in
      close_in ic;
      "\n" ^ l ^ "\n" ^
      ansi_format [Bold; Green] (String.init (cpos + 1) (fun n -> if n < cpos then ' ' else '^'))
    else
      ""
  )
*)


(*
let location_to_string  = function
  | Some p ->
      let f = Location.first_line p in
      let l = Location.last_line  p in
      if f = l then
        "line " ^ string_of_int f
      else
        "lines " ^ string_of_int f ^ "-" ^ string_of_int l
  | None -> "Unknown location"
*)


let location_to_string loc =
  let string_of_pos pos =
    Printf.sprintf "%s:%d:%d:" pos.pos_fname pos.pos_lnum (1+pos.pos_cnum-pos.pos_bol) in
  
  match loc with
    | Loc_unknown ->
        "unknown location"
    | Loc_point pos ->
        string_of_pos pos
    | Loc_region (pos, _, _) ->
        (* TODO *)
        string_of_pos pos



let desugar_cause_to_string = function
  | Desugar_NoStartup str ->
      "could not find the startup function (" ^ str ^ ")"
  | Desugar_ConstraintViolation msg ->
      "violation of contraint " ^ msg
  | Desugar_OtherViolation msg ->
      "other violation: " ^ msg
  
(* TODO: move these to Desugar_ConstraintViolation *)
  | Desugar_FunctionRedefinition sym ->
       "(TODO msg) redefinition of '" ^ (Pp_utils.to_plain_string (Pp_ail.pp_id sym)) ^ "'\n"
  | Desugar_BlockScoped_Thread_local_alone ->
      "Violation of constraint 6.7.1#3 Storage-class specifiers, Contraints: \
       ``In the declaration of an object with block scope, if the declaration \
       specifiers include _Thread_local, they shall also include either static \
       or extern. [...].. ``\n"
(*
  | CABS_TO_AIL_THREAD_LOCAL_FUNCTION ->
      "Violation of constraint 6.7.1#4 Storage-class specifiers, Contraints: \
       ``_Thread_local shall not appear in the declaration specifiers of a \
       function declaration.``\n"
  | CABS_TO_AIL_BLOCK_FUNCTION_STORAGE ->
      "Violation of constraint 6.7.1#7 Storage-class specifiers, Contraints: \
       ``The declaration of an identifier for a function that has block scope \
       shall have no explicit storage-class specifier other than extern.``\n"
  | CABS_TO_AIL_CASE_NOT_INTEGER_CONSTANT_EXRESSION ->
      "Violation of constraint 6.8.4.2#3 The switch statement, Constraints: \
       ``The expression of each case label shall be an integer constant \
       expression [...]``\n"
*)
  | Desugar_NotConstantExpression ->
      "found a non-contant expression in place of a constant one.\n"
  | Desugar_MultipleDeclaration (CabsIdentifier (_, str)) ->
      "violation of constraint (§6.7#3): multiple declaration of `" ^ str ^ "'."
(*
  | CABS_TO_AIL_DUPLICATED_LABEL ->
    "Violation of contraint 6.8.1#3 Labeled statements, Constaints: ``Label \
     names shall be unique within a function.``\n"
  | CABS_TO_AIL_UNDECLARED_IDENTIFIER id ->
      "FOUND> " ^ id ^
      "\nViolation of constraint 6.7#3 as described by footnote 91 \
       ``..[A]n undeclared identifier is a violation of syntax..``\n"
  (* TODO: find if there is some relevant text in the std *)
  | CABS_TO_AIL_UNDECLARED_TYPENAME id ->
      "Found undeclared typename> " ^ id
  | CABS_TO_AIL_MULTIPLE_STORAGE_CLASS ->
      "Violation of constraint 6.7.1#1 Storage-class specifiers, Contraints: \
       ``..At most, one storage-class specifier may be given [...]..``\n"
  | CABS_TO_AIL_ITERATION_DECLARATON_WRONG_STORAGE ->
      "Violation of constraint 6.8.5#3 Iteration statements, \
       Constraints: ..The declaration part of a for statement \
       shall only declare identifiers for objects having storage \
       class auto or register.. in\n"
*)
  | Desugar_NeverSupported str ->
      "this feature won't be supported: " ^ str ^ "."

  | Desugar_NotyetSupported str ->
      "this feature is not supported: " ^ str ^ "."

  | Desugar_TODOCTOR str ->
      "Desugar_TODOCOTR[" ^ str ^ "]"
  
  | Desugar_impossible ->
      "impossible error"




let std_ref = function
  | Desugar_cause Desugar_NonvoidReturn ->
    "§6.8.6.4#1, 2nd sentence"

  | AIL_TYPING TError_main_return_type ->
      "§5.1.2.2.1#1, 2nd sentence"
  | AIL_TYPING (TError_TODO n) ->
      "Ail typing error (TODO " ^ string_of_int n ^ ")"
  | Desugar_cause (Desugar_ConstraintViolation str) ->
      str
  | _ ->
      "TODO"



let short_message = function
  | Desugar_cause (Desugar_MultipleDeclaration (CabsIdentifier (_, str))) ->
      "redeclaration of '" ^ str ^ "'"
  | Desugar_cause (Desugar_NoStartup str) ->
      "expecting declaration of a startup function '" ^ str ^ "'"
  
  | Desugar_cause Desugar_NonvoidReturn ->
(*      "non-void function 'main' should return a value" *)
      "non-void function should return a value" 

  | Desugar_cause dcause ->
      "[During desugaring] " ^ desugar_cause_to_string dcause


  | AIL_TYPING TError_main_return_type ->
      "return type of 'main' should be 'int'"

  | AIL_TYPING (TError_main_params qs_tys) ->
      "invalid parameter types for 'main': (" ^ String.concat ", " (List.map (fun (_, ty) -> String_ail.string_of_ctype ty) qs_tys) ^ ")"

      
      | CSEM_NOT_SUPPORTED msg ->
          "Csem doesn't yet support `" ^ msg ^"'"
      
      | CSEM_HIP msg ->
          "HIP, this doesn't work yet: `" ^ msg ^ "'"
      
      (* Cabs0_to_ail *)
      | CONSTRAINT_6_6__3 ->
          "Violation of constraint 6.6#3 [Constant expressions] `Constant \
           expressions shall not contain assignment, increment, decrement, \
           function-call, or comma operators, except when they are contained \
           within a subexpression that is not evaluated.'\n"

    | AIL_TYPING (TError std) ->
        "[Ail typing error] (" ^ std ^ ")\n \"" ^ Pp_std.quote std ^ "\""

    | AIL_TYPING (TError_lvalue_coercion ty) ->
        "[Ail typing error]\n failed lvalue coercion of type \"" ^ Pp_utils.to_plain_string (Pp_ail.pp_ctype ty) ^ "\""

    | _ ->
        "TODO ERROR MESSAGE"



let to_string (loc, err) =
  make_message loc Error
  begin
    match !!cerb_conf.error_verbosity with
      | Basic ->
          short_message err
      | RefStd ->
          short_message err ^ ". (" ^ std_ref err ^ ")"
      | QuoteStd ->
          failwith "TODO"
  end

(*
  begin
    match err with
      
      | Desugar_cause dcause ->
          "[During desugaring] " ^ desugar_cause_to_string dcause
      
      | CSEM_NOT_SUPPORTED msg ->
          "Csem doesn't yet support `" ^ msg ^"'"
      
      | CSEM_HIP msg ->
          "HIP, this doesn't work yet: `" ^ msg ^ "'"
      
      (* Cabs0_to_ail *)
      | CONSTRAINT_6_6__3 ->
          "Violation of constraint 6.6#3 [Constant expressions] `Constant \
           expressions shall not contain assignment, increment, decrement, \
           function-call, or comma operators, except when they are contained \
           within a subexpression that is not evaluated.'\n"
    

(*
    | AIL_TYPING (TError_main_return_type) ->
        
*)


    | AIL_TYPING (TError std) ->
        "[Ail typing error] (" ^ std ^ ")\n \"" ^ Pp_std.quote std ^ "\""

    | AIL_TYPING (TError_lvalue_coercion ty) ->
        "[Ail typing error]\n failed lvalue coercion of type \"" ^ Pp_utils.to_plain_string (Pp_ail.pp_ctype ty) ^ "\""


(*

    | AIL_TYPECHECK_CALL_RETURN ->
        "Violation of constraint 6.5.2.2#1 Function calls, Constraints: ``The \
         expression that denotes the function shall have type pointer to \
         function returning void or returning a complete object type other than \
         an array type.``"
    | AIL_TYPECHECK_CALL_ARGUMENTS_ASSIGNABLE ->
        "Violation of constraint 6.5.2.2#1 Function calls, Constraints: ``Each \
         argument shall have a type such that its value may be assigned to an \
         object [...] of the type corresponding to its parameter.``"
    | AIL_TYPECHECK_CALL_NUMBER_OF_ARGUMENTS ->
        "Violation of constraint 6.5.2.2#1 Function calls, Constraints: ``[T]he \
         number of arguments shall agree with the number of parameters.``"
    | AIL_TYPECHECK_CALL_FUNCTION_POINTER ->
        "Violation of constraint 6.5.2.2#1 Function calls, Constraints: ``The \
         expression that denotes the function shall have type pointer to \
         function [...].``"
    
    | AIL_TYPECHECK_INCR_LVALUE ->
        "Violation of constraint 6.5.2.4#1 Postfix increment and decrement \
         operators, Constraints: ``The operand of the postfix [...] decrement \
         operator [...] shall be a modifiable lvalue.``"
    | AIL_TYPECHECK_INCR_REAL_OR_POINTER ->
        "Violation of constraint 6.5.2.4#1 Postfix increment and decrement \
         operators, Constraints: ``The operand of the postfix [...] decrement \
         operator [...] shall have [...] real or pointer type [...].``"
    
    | AIL_TYPECHECK_ADDRESS_FUNCTION_OR_LVALUE ->
        "Violation of constraint 6.5.3.2#1 Address and indirection operators, \
         Constraints: ``The operand of the & operator shall be either a function \
         designator [...] or an lvalue that designates an object [...].``"
    
    | AIL_TYPECHECK_INDIRECTION_POINTER ->
         "Violation of constraint 6.5.3.2#2 Address and indirection operators, \
          Constraints: ``The operand of the unary * operator shall have pointer \
          type.``"
    
    | AIL_TYPECHECK_MINUS_ARITHMETIC ->
        "Violation of constraint 6.5.3.3#1 Unary arithmetic operators, \
         Constraints: ``The operand of the unary [...] - operator shall have \
         arithmetic type [...].``"
    
    | AIL_TYPECHECK_PLUS_ARITHMETIC ->
        "Violation of constraint 6.5.3.3#1 Unary arithmetic operators, \
         Constraints: ``The operand of the unary + [...] operator shall have \
         arithmetic type [...].``"
    
    | AIL_TYPECHECK_BNOT_INTEGER ->
        "Violation of constraint 6.5.3.3#1 Unary arithmetic operators, \
         Constraints: ``The operand [...] of the ~ operator [shall have] integer \
         type [...].``"
    
    | AIL_TYPECHECK_SIZEOF_INCOMPLETE ->
        "Violation of constraint 6.5.3.4#1 The sizeof and alignof operators, \
         Constraints: ``The sizeof operator shall not be applied to an [...] \
         incomplete type [...].``"
    | AIL_TYPECHECK_SIZEOF_FUNCTION ->
        "Violation of constraint 6.5.3.4#1 The sizeof and alignof operators, \
         Constraints: ``The sizeof operator shall not be applied to [a] [...] \
         function type [...].``"
    
    | AIL_TYPECHECK_ALIGNOF_INCOMPLETE ->
        "Violation of constraint 6.5.3.4#1 The sizeof and alignof operators, \
         Constraints: ``The alignof operator shall not be applied to [...] an \
         incomplete type.``"
    
    | AIL_TYPECHECK_CAST_NAME_SCALAR ->
        "Violation of constraint 6.5.4#1 Cast operators, Constraints: ``[T]he \
         type name shall specify [...] scalar type [...].``"
    | AIL_TYPECHECK_CAST_OPERAND_SCALAR ->
        "Violation of constraint 6.5.4#1 Cast operators, Constraints: ``[T]he \
         operand shall have scalar type.``"
    
    | AIL_TYPECHECK_MUL_ARITHMETIC ->
        "Violation of constraint 6.5.5#2 Multiplicative operators, Contraints: \
         ``Each operand shall have arithmetic type.``"
    
    | AIL_TYPECHECK_MOD_INTEGER ->
        "Violation of constraint 6.5.5#2 Multiplicative operators, Contraints: \
         ``The operands of the % operator shall have integer type.``"
    
    | AIL_TYPECHECK_ADD_POINTER_INTEGER ->
        "Violation of constraint 6.5.6#2 Additive operators, Constraints: \
         ``[O]ne operand shall be a pointer to a complete object type and the \
         other shall have integer type.`` (Second operand is not of integer \
         type.)"
    | AIL_TYPECHECK_ADD_INTEGER_POINTER ->
        "Violation of constraint 6.5.6#2 Additive operators, Constraints: \
         ``[O]ne operand shall be a pointer to a complete object type and the \
         other shall have integer type.`` (First operand is not of integer type.)"
    | AIL_TYPECHECK_ADD_ALL ->
        "Violation of constraint 6.5.6#2 Additive operators, Constraints: \
         `` [E]ither both operands shall have arithmetic type, or one operand \
         shall be a pointer to a complete object type and the other shall have \
         integer type.``"
    
    | AIL_TYPECHECK_SUB_POINTER_TO_COMPLETE_OBJECT_FIRST ->
        "Violation of constraint 6.5.6#3 Additive operators, Constraint: \
         ``[B]oth operands [shall be] pointers to [...] compatible complete \
         object types [...].`` (Operands are pointers but the left operand \
         doesn't point to a complete object.)"
    | AIL_TYPECHECK_SUB_POINTER_TO_COMPLETE_OBJECT_SECOND ->
        "Violation of constraint 6.5.6#3 Additive operators, Constraint: \
         ``[B]oth operands [shall be] pointers to [...] compatible complete \
         object types [...].`` (Operands are pointers but the right operand \
         doesn't point to a complete object.)"
    | AIL_TYPECHECK_SUB_COMPATIBLE_POINTERS ->
        "Violation of constraint 6.5.6#3 Additive operators, Constraint: \
         ``[B]oth operands [shall be] pointers to [...] compatible complete \
         object types [...].`` (Operands are pointers to incompatible types.)"
    | AIL_TYPECHECK_SUB_POINTER_TO_COMPLETE_OBJECT ->
        "Violation of constraint 6.5.6#3 Additive operators, Constraints: \
         ``[T]he left operand [shall be] a pointer to a complete object type and \
         the right operand [shall have] integer type.`` (Left operand is a \
         pointer, right operand is not a pointer but the left operand doesn't \
         pointer to a complete object.)"
    | AIL_TYPECHECK_SUB_INTEGER_OR_POINTER ->
        "Violation of constraint 6.5.6#3 Additive operators, Constraints: \
         ``[B]oth operands [shall either be] pointers to [...] compatible \
         complete object types[,] or the left operand [shall be] a pointer to a \
         complete object type and the right operand [shall have] integer type.`` \
         (Second operand expected to be a pointer or an integer.)"
    | AIL_TYPECHECK_SUB_ALL ->
        "Violation of constraint 6.5.6#3 Additive operators, Constraints: \
         ``[B]oth operands [shall] have arithmetic type[, or shall be] pointers \
         to [...] compatible complete object types[,] or the left operand [shall \
         be] a pointer to a complete object type and the right operand [shall \
         have] integer type.``"
    
    | AIL_TYPECHECK_SHR_INTEGER_FIRST ->
        "Violation of constraint 6.5.7#2 Bitwise shift operators, Constraints: \
         ``Each of the operands shall have integer type.`` (Left operand is not \
         an integer.)"
    | AIL_TYPECHECK_SHR_INTEGER_SECOND ->
        "Violation of constraint 6.5.7#2 Bitwise shift operators, Constraints: \
         ``Each of the operands shall have integer type.`` (Right operand is not \
         an integer.)"
    
    | AIL_TYPECHECK_GE_COMPATIBLE ->
        "Violation of constraint 6.5.8#2 Relational operators, Constraints: \
         ``[B]oth operands [shall be] pointers to [...] compatible object \
         types.`` (Operands are pointers to incompatible object types.)"
    | AIL_TYPECHECK_GE_POINTER_TO_OBJECT_FIRST ->
        "Violation of constraint 6.5.8#2 Relational operators, Constraints: \
         ``[B]oth operands [shall be] pointers to [...] compatible object \
         types.`` (Both operands are pointers but the left operand doesn't point \
         point to an object.)"
    | AIL_TYPECHECK_GE_POINTER_TO_OBJECT_SECOND ->
        "Violation of constraint 6.5.8#2 Relational operators, Constraints: \
         ``[B]oth operands [shall be] pointers to [...] compatible object \
         types.`` (Both operands are pointers but the right operand doesn't point \
         point to an object.)"
    | AIL_TYPECHECK_GE_REAL ->
        "Violation of constraint 6.5.8#2 Relational operators, Constraints: \
         ``[B]oth operands [shall] have real type [...].`` (First operand has \
         type real but second doesn't.)"
    | AIL_TYPECHECK_GE_ALL ->
        "Violation of constraint 6.5.8#2 Relational operators, Constraints: \
         ``One of the following shall hold: both operands have real type or both \
         operands are pointers to [...] compatible types.``"
    
    | AIL_TYPECHECK_NE_POINTERS ->
        "Constraint 6.5.9#2 Equality operators, Constraints: ``One of the \
         following shall hold: [...] both operands are pointers to [...] \
         compatible types[, or] one operand is a pointer to an object type and \
         the other is a pointer to [...] void[, or] one operand is a pointer and \
         the other is a null pointer constant.`` (Both operand are pointers but \
         none of the other constraints are satisfied.)"
    | AIL_TYPECHECK_NE_NULL_POINTER_CONSTANT_FIRST ->
        "Constraint 6.5.9#2 Equality operators, Constraints: ``[O]ne operand is \
         a pointer and the other is a null pointer constant.`` (Right operand is \
         a pointer but the left operand isn't a null pointer constant.)"
    | AIL_TYPECHECK_NE_NULL_POINTER_CONSTANT_SECOND ->
        "Constraint 6.5.9#2 Equality operators, Constraints: ``[O]ne operand is \
         a pointer and the other is a null pointer constant.`` (Left operand is \
         a pointer but the right operand isn't a null pointer constant.)"
    | AIL_TYPECHECK_NE_ARITHMETIC ->
        "Constraint 6.5.9#2 Equality operators, Constraints: ``[B]oth operands \
         [shall] have arithmetic type.`` (Left operand has arithmetic type but
         right operand doesn't.)"
    | AIL_TYPECHECK_NE_ALL ->
        "Constraint 6.5.9#2 Equality operators, Constraints: ``One of the \
         following shall hold: both operands have arithmetic type[, or] both \
         operands are pointers to [...] compatible types[, or] one operand is a \
         pointer to an object type and the other is a pointer to [...] void[, \
         or] one operand is a pointer and the other is a null pointer constant.``"
    
    | AIL_TYPECHECK_BAND_INTEGER ->
        "Violation of constraint 6.5.10#2 Bitwise AND operator, Contraints: \
         ``Each of the operands shall have integer type.``"
    
    | AIL_TYPECHECK_XOR_INTEGER ->
        "Violation of constraint 6.5.11#2 Bitwise exclusive OR operator, \
         Contraints: ``Each of the operands shall have integer type.``"
    
    | AIL_TYPECHECK_BOR_INTEGER ->
        "Violation of constraint 6.5.12#2 Bitwise inclusive OR operator, \
         Contraints: ``Each of the operands shall have integer type.``"
    
    | AIL_TYPECHECK_AND_SCALAR ->
        "Violation of constraint 6.5.13#2 Logical AND operator, Constraints: \
         ``Each of the operands shall have scalar type.``"
    
    | AIL_TYPECHECK_OR_SCALAR ->
        "Violation of constraint 6.5.14#2 Logical OR operator, Contraints: \
         ``Each of the operands shall have scalar type.``"
    
    | AIL_TYPECHECK_CONDITIONAL_SCALAR_FIRST ->
        "Violation of constraint 6.5.15#2 Conditional operator, Constraints: \
         ``The first operand shall have scalar type.``"
    | AIL_TYPECHECK_CONDITIONAL_NULL_POINTER_CONSTANT_SECOND ->
        "Violation of constraint 6.5.15#3 Conditional operator, Constraints: \
          (Third operand is a pointer but the second operand is not a null pointer constant.)"
    | AIL_TYPECHECK_CONDITIONAL_NULL_POINTER_CONSTANT_THIRD ->
        "Violation of constraint 6.5.15#3 Conditional operator, Constraints: \
         ``[T]he following shall hold for the second and third operands: [...] \
         one operand is a pointer to an object type and the other is a pointer \
         to [...] void.`` (Third operand is a pointer but the second operand is \
         not a null pointer constant.)"
    | AIL_TYPECHECK_CONDITIONAL_POINTERS ->
        "Violation of constraint 6.5.15#3 Conditional operator, Constraints: \
         ``One of the following shall hold for the second and third operands: \
         [Either] both operands have the same structure or union type[, or] both \
         operands have void type[, or] both operands are pointers to [...] \
         compatible types[, or] one operand is a pointer and the other is a null \
         pointer constant[, or] one operand is a pointer to an object type and \
         the other is a pointer [...] to void.`` (Second and third operands are \
         pointers but none of the other constraints are satisfied.)"
    | AIL_TYPECHECK_CONDITIONAL_COMPATIBLE_POINTERS ->
        "Violation of constraint 6.5.15#3 Conditional operator, Constraints: \
         ``[T]he following shall hold for the second and third operands: [...] \
         both operands are pointers to compatible types [...].`` (Second and \
         third operand are pointers to incompatible types.)"
    | AIL_TYPECHECK_CONDITIONAL_ARITHMETIC_SECOND ->
        "Violation of constraint 6.5.15#3 Conditional operator, Constraints: \
         ``[T]he following shall hold for the second and third operands: [...] \
         both operands have arithmetic type [...].`` (Second operand has
         arithmetic type but the third doesn't.)"
    | AIL_TYPECHECK_CONDITIONAL_STRUCTURE_OR_UNION ->
        "Violation of constraint 6.5.15#3 Conditional operator, Constraints: \
         ``[T]he following shall hold for the second and third operands: [...] \
         both operands have the same structure or union type [...].``"
    | AIL_TYPECHECK_CONDITIONAL_ALL ->
        "Violation of constraint 6.5.15#3 Conditional operator, Constraints: \
         ``One of the following shall hold for the second and third operands: \
         [Either] both operands have arithmetic type[, or] both operands have \
         the same structure or union type[, or] both operands have void type[, \
         or] both operands are pointers to [...] compatible types[, or] one \
         operand is a pointer and the other is a null pointer constant[, or] one \
         operand is a pointer to an object type and the other is a pointer [...] \
         to void.``"
    
    | AIL_TYPECHECK_ASSIGN_LVALUE ->
        "Violation of constraint 6.5.16#1 Assignment operators, Constraints: \
         ``An assignment operator shall have a modifiable lvalue as its left \
         operand.``"
    | AIL_TYPECHECK_ASSIGN_STRUCTURE_OR_UNION ->
        "Violation of constraint 6.5.16.1#1 Simple assignment, Constraints: \
         ``[T]he left operand has [...] structure or union type compatible with \
         the type of the right [...]``"
    | AIL_TYPECHECK_ASSIGN_VOID_POINTER_QUALIFIERS ->
        "Violation of constraint 6.5.16.1#1 Simple assignment, Constraints: \
         ``[T]he left operand [shall have] [...] pointer type, and [...] one \
         operand [shall be] a pointer to an object type, and the other [shall be]\
         a pointer to [...] void, and the type pointed to by the left has all \
         the qualifiers of type pointed to by the right [...].`` (Left operand \
         doesn't have all the qualifiers of the right operand.)"
    | AIL_TYPECHECK_ASSIGN_VOID_POINTER_FIRST ->
        "Violation of constraint 6.5.16.1#1 Simple assignment, Constraints: \
         ``[T]he left operand [shall have] [...] pointer type, and [...] one \
         operand [shall be] a pointer to an object type, and the other [shall \
         be] a pointer to [...] void [...].`` (Left operand is a void pointer \
         but the right operand is not a pointer to an object type.)"
    | AIL_TYPECHECK_ASSIGN_VOID_POINTER_SECOND ->
        "Violation of constraint 6.5.16.1#1 Simple assignment, Constraints: \
         ``[T]he left operand [shall have] [...] pointer type, and [...] one \
         operand [shall be] a pointer to an object type, and the other [shall \
         be] a pointer to [...] void [...].`` (Right operand is a void pointer \
         but the left operand is not a pointer to an object type.)"
    | AIL_TYPECHECK_ASSIGN_POINTER_QUALIFIERS ->
        "Violation of constraint 6.5.16.1#1 Simple assignment, Constraints: \
         ``[T]he left operand [shall have] [...] pointer type and [...] both \
         operands [shall be] pointers to [...] compatible types, and the type \
         pointed to by the left [shall have] all the qualifiers of the type \
         pointed to by the right [...].`` (Left operand doesn't  have all the \
         qualifiers of the right operand.)"
    | AIL_TYPECHECK_ASSIGN_COMPATIBLE_POINTERS ->
      "Violation of constraint 6.5.16.1#1 Simple assignment, Constraints: \
       ``[T]he left operand [shall have] [...] pointer type and [...] both \
       operands [shall be] pointers to [...] compatible types [...].`` \
       (Operands are pointers to incompatible types.)"
    | AIL_TYPECHECK_ASSIGN_POINTERS ->
        "Violation of constraint 6.5.16.1#1 Simple assignment, Constraints: \
         ``One of the following shall hold: [...] both operands are pointer to \
         [...] compatible types, and the type pointed to by the left has all the \
         qualifiers of the type pointed to by the right[, or] the left operand \
         has [...] pointer type, and [...] one operand is a pointer to an object \
         type, and the other is a pointer to [...] void, and the type pointed to \
         by the left has all the qualifiers of the type pointed to by the \
         right[, or] the left operand is [a] [...] pointer, and the right is a \
         null pointer constant.`` (Both operands are pointer but none of the \
        others constraints is satisfied.)"
    | AIL_TYPECHECK_ASSIGN_NULL_POINTER_CONSTANT ->
        "Violation of constraint 6.5.16.1#1 Simple assignment, Constraints: \
         ``[T]he left operand is [a] [...] pointer, and the right is a null \
         pointer constant.`` (Left operand is a point but right operand is not \
         a pointer nor a null pointer constant.)"
    | AIL_TYPECHECK_ASSIGN_ALL ->
        "Violation of constraint 6.5.16.1#1 Simple assignment, Constraints: \
         ``One of the following shall hold: the left operand has [...] \
         arithmetic type, and the right has arithmetic type[, or] the left \
         operand has [...] structure or union type compatible with the type of \
         the right[, or] the left operand has [...] pointer type, and [...] both \
         operands are pointer to [...] compatible types, and the type pointed to \
         by the left has all the qualifiers of the type pointed to by the \
         right[, or] the left operand has [...] pointer type, and [...] one \
         operand is a pointer to an object type, and the other is a pointer to \
         [...] void, and the type pointed to by the left has all the qualifiers \
         of the type pointed to by the right[, or] the left operand is [a] [...] \
         pointer, and the right is a null pointer constant[, or] the left \
         operand has type [...] _Bool, and the right is a pointer.``"
    
    | AIL_TYPECHECK_ASSIGN_SUB_POINTER ->
        "Violation of constraint 6.5.16.2#1 Compound assignment, Constraints: \
         ``[T]he left operand shall be [a] [...] pointer to a complete object \
         type, and the right shall have integer type [...].`` (Left operand is a \
         pointer to a complete object but the right operand doesn't have integer \
         type.)"
    | AIL_TYPECHECK_ASSIGN_SUB_ARITHMETIC ->
        "Violation of constraint 6.5.16.2#1 Compound assignment, Constraints: \
         ``[T]he left operand shall have [...] arithmetic type, and the right \
         shall have arithmetic type.`` (Left operand has arithmetic type but the \
         right operand doesn't.)"
    | AIL_TYPECHECK_ASSIGN_SUB_ALL ->
        "Violation of constraint 6.5.16.2#1 Compound assignment, Constraints: \
         ``For the operators += and -= only, either the left operand shall be \
         [a] [...] pointer to a complete object type, and the right shall have \
         integer type[, or] the left operand shall have [...] arithmetic type \
         and the right shall have arithmetic type.``"
    
    | AIL_TYPECHECK_ASSIGN_OTHER_ARITHMETIC ->
        "Violation of constraint 6.5.16.2#2 Compound assignment, Constraints: \
         ``[T]he left operand shall have [...] arithmetic type [...].``"
    
    | AIL_TYPECHECK_IF_SCALAR ->
        "Violation of constraint 6.8.4.1 The if statement, Constraints: ``The \
         controlling expression of an if statement shall have scalar type.``"
    
    | AIL_TYPECHECK_WHILE_SCALAR ->
        "Violation of constraint 6.8.4.1 Iteration statements, Constraints: \
         ``The controlling expression of an iteration statement shall have \
         scalar type.``"
    
    | AIL_TYPECHECK_WHILE_SCALAR ->
        "Violation of constraint 6.8.4.1 Iteration statements, Constraints: \
         ``The controlling expression of an iteration statement shall have \
         scalar type.``"
    
    | AIL_TYPECHECK_SWITCH_INTEGER ->
        "[Violation of constraint 6.8.4.2#1] The switch statement, Constraints: \
         ``The controlling expression of a switch statement shall have integer type.``"
    
    | AIL_TYPECHECK_LVALUE_UNDEFINED ->
        "Undefined behaviour according to 6.3.2.1#2 Lvalues, arrays, and \
         function designators: ``If the value has an incomplete type and does \
         not have array type, the behaviour is undefined. [...]``"
    
    | AIL_TYPECHECK_UNSUPPORTED s ->
      "[Unsupported feature by Ail typecheck] " ^ s
    
 *)

    | CASE_OUTSIDE_SWITCH ->
        "[Violation of 6.8.1#1] Labeled statements, Constraints: ``A \
         case [...] label shall appear only in a switch statement.``"
    
    | DEFAULT_OUTSIDE_SWITCH ->
        "[Violation of 6.8.1#1] Labeled statements, Constraints: ``A \
         [...] default label shall appear only in a switch statement.``"
    
    | UNSUPPORTED msg -> msg
    
    | PARSER msg -> "[Parser] " ^ msg
    | OTHER msg -> "[Other] " ^ msg
    
    
(*
    (* Core typechecking *)
    | CORE_TYPECHECK_INCORRECT_EXPECTED (foundTy, expectedTy, e) ->
        "[Core Typechecking] found type `" ^ (* (Document.to_plain_string $ Core.Print.pp_core_type foundTy) ^ *) "', while expecting `" (* ^
         (Document.to_plain_string $ Core.Print.pp_core_type expectedTy) ^ "'.\n\n" *) ^ e 
    | CORE_TYPECHECK_IF_BRANCHES ->
        "[Core Typechecking] the two branches of a [if] must have the same type."
    
    | CORE_TYPECHECK_GET_FAILURE ->
        "[Core Typechecking] `get' failed to find a symbolic name."
    
    | CORE_TYPECHECK_CALL_NUMBER_OF_ARGUMENTS (seen, expected) ->
        "[Core Typechecking] incorrect number of argument, seen: " ^ (string_of_int seen) ^ " while expecting " ^ (string_of_int expected) ^ "."
    
    | CORE_TYPECHECK_CALL_ARGUMENT_EFFECT ->
        "[Core Typechecking] arguments of a call cannot have an effect type"
    
    | CORE_TYPECHECK_LET_EFFECT ->
        "[Core Typechecking] the first argument of let must be pure."
    
    | CORE_TYPECHECK_LET_TUPLE ->
        "[Core Typechecking] the first operand of a `let' cannot have a tuple type."
    | CORE_TYPECHECK_SEQ_PURE ->
        "[Core Typechecking] the first operand of `seq' operator must be effectful."
    
    
    | CORE_TYPECHECK_SEQ_INCOMPATIBLE_ARITY (patternArity, exprArity) ->
        "[Core Typechecking] incompatible arities in a seq expression: pattern arity = " ^
         string_of_int patternArity ^ ", while the type of the first argument has arity = " ^
         string_of_int exprArity ^ "."
    
    | CORE_TYPECHECK_UNSEQ_PURE e ->
        "[Core Typechecking] the operands of an unseq must all be effectful.\n\n" ^ e
    
    | CORE_TYPECHECK_UNDECLARED_FUNCTION fname ->
        "[Core Typechecking] the function `" ^ (Pp_symbol.to_string_pretty fname) ^ "' was not declared."
    
    | CORE_TYPECHECK_UNDECLARED_SYMBOL sym ->
        "[Core Typechecking] the symbolic name `" ^ (Pp_symbol.to_string_pretty sym) ^ "' was not declared."
    
    
    | CORE_TYPECHECK msg -> "[Core typechecking] " ^ msg
*)
    
    | CORE_UNDEF us ->
        let plural = List.length us > 1 in
        "[Core runtime] found " ^ (if plural then "some" else "an") ^ " undefined behaviour" ^ (if plural then "s" else "") ^ ":\n" ^
          List.fold_left (fun acc u ->
            acc ^ "  --> " ^ Undefined.pretty_string_of_undefined_behaviour u ^ "\n"
          ) "" us
  end (* ^ "\n" ^
  Lexing.(
    let ic = open_in start_p.pos_fname in
    seek_in ic start_p.pos_bol;
    input_line ic ^ "\n" ^
    String.make (start_p.pos_cnum - start_p.pos_bol) ' ' ^
    ansi_format [Bold; Green] "^"
  )
*)
*)
