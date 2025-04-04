open Core

open Cerb_pp_prelude
(*open Pp_ail*)

open Pp_ast
open Cerb_colour

module P = PPrint

let pp_symbol  a = !^ (ansi_format [Blue] (Pp_symbol.to_string_pretty a))

let pp_ident id = Pp_symbol.pp_identifier id

let pp_keyword w =
  !^ (ansi_format [Green] w)

let pp_pure_ctor w =
  !^ (ansi_format [Bold; Cyan] w)

let pp_eff_ctor w =
  !^ (ansi_format [Bold; Magenta] w)

let pp_impl    i = P.angles (!^ (ansi_format [Yellow] (Implementation.string_of_implementation_constant i)))

let pp_name = function
  | Sym a  -> pp_symbol a
  | Impl i -> pp_impl i


  (* type 'sym generic_object_value =  (* C object values *)
  | OVinteger of Impl_mem.integer_value (* integer value *)
  | OVfloating of Impl_mem.floating_value (* floating-point value *)
  | OVpointer of Impl_mem.pointer_value (* pointer value *)
  | OVarray of ( 'sym generic_loaded_value) list (* C array value *)
  | OVstruct of Symbol.sym * (Symbol.identifier * ctype * Impl_mem.mem_value) list (* C struct value *)
  | OVunion of Symbol.sym * Symbol.identifier * Impl_mem.mem_value (* C union value *)
 
 and 'sym generic_loaded_value =  (* potentially unspecified C object values *)
  | LVspecified of ( 'sym generic_object_value) (* non-unspecified loaded value *)
  | LVunspecified of ctype (* unspecified loaded value *)
 
  *)

let rec dtree_of_object_value = function
  | OVinteger ival ->
      Dleaf (pp_pure_ctor "OVinteger" ^^^ Impl_mem.pp_integer_value_for_core ival)
  | OVfloating fval ->
      Dleaf (pp_pure_ctor "OVfloating" ^^^
             Impl_mem.case_fval fval
               (fun () -> !^ "unspec(floating)")
              (fun fval -> !^(string_of_float fval)))
  | OVpointer ptrval ->
      Dleaf (pp_pure_ctor "OVpointer" ^^^ Impl_mem.pp_pointer_value ptrval)
  | OVarray lvals ->
      Dnode ( pp_pure_ctor "OVarray"
            , List.map dtree_of_loaded_value lvals)
  | OVstruct (tag_sym, xs) ->
      (* (Symbol.identifier * Ctype.ctype * Impl_mem.mem_value) list *)
      Dleaf (pp_pure_ctor "OVstruct" ^^^ !^ (ansi_format [Red] "TODO"))
  | OVunion (tag_sym, membr_ident, mval) ->
      Dleaf (pp_pure_ctor "OVunion" ^^^ !^ (ansi_format [Red] "TODO"))
and dtree_of_loaded_value = function
  | LVspecified oval ->
      Dnode (pp_pure_ctor "LVspecified", [dtree_of_object_value oval])
  | LVunspecified ty ->
      Dleaf (pp_pure_ctor "LVunspecified" ^^^ P.squotes (Pp_ail.pp_ctype Ctype.no_qualifiers ty))

let dtree_of_value = function
  | Vobject oval ->
      Dnode (pp_pure_ctor "Vobject", [dtree_of_object_value oval])
  | Vloaded lval ->
      Dnode (pp_pure_ctor "Vloaded", [dtree_of_loaded_value lval])
  | Vunit ->
      Dleaf (pp_pure_ctor "Vunit")
  | Vtrue ->
      Dleaf (pp_pure_ctor "Vtrue")
  | Vfalse ->
      Dleaf (pp_pure_ctor "Vfalse")
  | Vctype ty ->
      Dleaf (pp_pure_ctor "Vctype" ^^^ P.squotes (Pp_ail.pp_ctype Ctype.no_qualifiers ty))
  | Vlist (bTy, cvals) ->
      Dleaf (pp_pure_ctor "Vlist" ^^^ !^ (ansi_format [Red] "TODO"))
  | Vtuple cvals ->
      Dleaf (pp_pure_ctor "Vtuple" ^^^ !^ (ansi_format [Red] "TODO"))

 (* type 'sym generic_value =  (* Core values *)
  | Vobject of ( 'sym generic_object_value) (* C object value *)
  | Vloaded of ( 'sym generic_loaded_value) (* loaded C object value *)
  | Vunit
  | Vtrue
  | Vfalse
  | Vctype of ctype (* C type as value *)
  | Vlist of core_base_type * ( 'sym generic_value) list
  | Vtuple of ( 'sym generic_value) list tuple *)


let string_of_bop = function
  | OpAdd   -> "+"
  | OpSub   -> "-"
  | OpMul   -> "*"
  | OpDiv   -> "/"
  | OpRem_t -> "rem_t"
  | OpRem_f -> "rem_f"
  | OpExp   -> "^"
  | OpEq    -> "=="
  | OpGt    -> ">"
  | OpLt    -> "<"
  | OpGe    -> ">="
  | OpLe    -> "<="
  | OpAnd   -> "/\\"
  | OpOr    -> "\\/"

let string_of_iop = function
  | IOpAdd   -> "+"
  | IOpSub   -> "-"
  | IOpMul   -> "*"
  | IOpShl   -> "<<"
  | IOpShr   -> ">>"
(*  | OpDiv   -> "/"
  | OpRem_t -> "rem_t"
  | OpRem_f -> "rem_f"
  | OpExp   -> "^" *)

let dtree_of_pexpr pexpr =
  let rec self current_loc (Pexpr (annot, _, pexpr_)) =
    let current_loc =
      match Annot.get_loc annot with Some l -> l | _ -> current_loc in
    let self expr = self current_loc expr in
    
    let pp_ctor str =
      match Annot.get_loc annot with
        | Some loc ->
            pp_pure_ctor str ^^^ Cerb_location.pp_location ~clever:true loc
        | None ->
            pp_pure_ctor str in
    
    match pexpr_ with
      | PEsym sym ->
          Dleaf (pp_ctor "PEsym" ^^^ pp_symbol sym)
      | PEimpl iCst ->
          Dleaf (pp_ctor "PEimpl" ^^^ !^ (ansi_format [Red] "TODO"))
      | PEval cval ->
          Dnode (pp_ctor "PEval", [dtree_of_value cval])
      | PEconstrained xs ->
          Dleaf (pp_ctor "PEconstrained" ^^^ !^ (ansi_format [Red] "TODO"))
      | PEundef (loc, ub) ->
          Dleaf (pp_ctor "PEundef" ^^^ !^ (ansi_format [Red] "TODO"))
      | PEerror (str, pe) ->
          Dnode ( pp_ctor "PEerror" ^^^ P.dquotes (!^ (ansi_format [Red] str))
                , [self pe] )
      | PEctor (ctor, pes) ->
          Dnode (pp_ctor "PEctor" ^^^ Pp_core.Basic.pp_ctor ctor,
                 List.map self pes)
      | PEcase (pe, xs) ->
          Dleaf (pp_ctor "PEcase" ^^^ !^ (ansi_format [Red] "TODO"))
      | PEarray_shift (pe1, ty, pe2) ->
          Dleaf (pp_ctor "PEarray_shift" ^^^ !^ (ansi_format [Red] "TODO"))
      | PEmember_shift (pe, sym, ident) ->
          Dleaf (pp_ctor "PEmember_shift" ^^^ !^ (ansi_format [Red] "TODO"))
      | PEmemop (memop, pes) ->
          Dnode (pp_ctor "PEmemop" ^^^ Pp_mem.pp_pure_memop memop
                , List.map self pes)
      | PEnot pe ->
          Dnode (pp_ctor "PEnot", [self pe])
      | PEop (bop, pe1, pe2) ->
          Dnode ( pp_ctor "PEop" ^^^ P.squotes (!^ (string_of_bop bop))
                , [self pe1; self pe2] )
      | PEconv_int (ity, pe) ->
          Dnode ( pp_ctor "PEconv_int" ^^^
                  P.squotes (Pp_ail.pp_integerType ity)
                , [self pe] )
      | PEwrapI (ity, iop, pe1, pe2) ->
          Dnode ( pp_ctor "PEwrapI" ^^^
                  P.squotes (Pp_ail.pp_integerType ity) ^^^
                  P.squotes (!^ (string_of_iop iop))
                , [self pe1; self pe2] )
      | PEcatch_exceptional_condition (ity, iop, pe1, pe2) ->
          Dnode ( pp_ctor "PEcatch_exceptional_condition" ^^^
                  P.squotes (Pp_ail.pp_integerType ity) ^^^
                  P.squotes (!^ (string_of_iop iop))
                , [self pe1; self pe2] )
      | PEstruct (tag_sym, xs) ->
          Dnode ( pp_ctor "PEstruct" ^^^ P.squotes (pp_symbol tag_sym)
                , List.map self (List.map snd xs) )
      | PEunion (tag_sym, memb_ident, pe) ->
          Dnode ( pp_ctor "PEunion" ^^^
                        P.squotes ((pp_symbol tag_sym) ^^ P.colon ^^ (pp_ident memb_ident))
                , [self pe] )
      | PEcfunction pe ->
          Dnode ( pp_ctor "PEcfunction"
                , [self pe] )
      | PEmemberof (tag_sym, memb_ident, pe) ->
          Dnode ( pp_ctor "PEstruct" ^^^
                        P.squotes ((pp_symbol tag_sym) ^^ P.colon ^^ (pp_ident memb_ident))
                , [self pe] )
      | PEcall (nm, pes) ->
          Dnode (pp_ctor "PEcall" ^^^ pp_name nm,
                 List.map self pes)
      | PElet (pat, pe1, pe2) ->
          Dnode ( pp_ctor "PElet" (* ^^^ Pp_core.Basic.pp_pattern pat *)
                , [ self pe1; self pe2] )
      | PEif (pe1, pe2, pe3) ->
          Dnode ( pp_ctor "PEif"
                , [ self pe1; self pe2; self pe3 ] )
      | PEis_scalar pe ->
          Dnode ( pp_ctor "PEis_scalar"
                , [ self pe] )
      | PEis_integer pe ->
          Dnode ( pp_ctor "PEis_integer"
                , [ self pe] )
      | PEis_signed pe ->
          Dnode ( pp_ctor "PEis_signed"
                , [ self pe] )
      | PEis_unsigned pe ->
          Dnode ( pp_ctor "PEis_unsigned"
                , [ self pe] )
      | PEbmc_assume pe ->
          Dnode ( pp_ctor "PEbmc_assume"
                , [ self pe] )
      | PEare_compatible (pe1, pe2) ->
          Dnode ( pp_ctor "PEare_compatible"
                , [ self pe1; self pe2 ] )
      (* | _ ->
          Dleaf (pp_ctor ("Pexpr(TODO): " ^ Pp_utils.to_plain_pretty_string (Pp_core.WithLocations.pp_pexpr pexpr))) *)
  in
  self Cerb_location.unknown pexpr

let pp_action_ctor act =
  pp_keyword begin match act with
    | Create _ ->
        "create"
    | CreateReadOnly _ ->
        "create_readonly"
    | Alloc0 _ ->
        "alloc"
    | Kill _ ->
        "kill"
    | Store0 _ ->
        "store"
    | Load0 _ ->
        "load"
    | SeqRMW (false, _, _, _, _) ->
        "seq_rmw"
    | SeqRMW (true, _, _, _, _) ->
        "seq_rmw_with_forward"
    | RMW0 _ ->
        "rmw"
    | Fence0 _ ->
        "fence"
    | CompareExchangeStrong _ ->
        "cmpxchg_strong"
    | CompareExchangeWeak _ ->
        "cmpxchg_weak"
    | LinuxFence _ ->
        "linux_fence"
    | LinuxLoad _ ->
        "linux_load"
    | LinuxStore _ ->
        "linux_store"
    | LinuxRMW _ ->
        "linux_rmw"
  end

let dtree_of_action act =
  let (str, dtrees) =
    match act with
      | Create _ ->
          ( "create"
          , [] )
      | CreateReadOnly _ ->
          ( "create_readonly"
          , [] )
      | Alloc0 _ ->
          ( "alloc"
          , [] )
      | Kill _ ->
          ( "kill"
          , [] )
      | Store0 _ ->
          ( "store"
          , [] )
      | Load0 (pe1, pe2, mo) ->
          ( "load"
          , [ dtree_of_pexpr pe1
            ; dtree_of_pexpr pe2 ] )
      | SeqRMW (b, pe1, pe2, sym, pe3) ->
          let ctor_str =
            if b then
              "seq_rmw_with_forward"
            else
              "seq_rmw_with_forward" in
          ( ctor_str
          , [ dtree_of_pexpr pe1
            ; dtree_of_pexpr pe1
            ; Dleaf (pp_symbol sym)
            ; dtree_of_pexpr pe3 ] )
      | RMW0 _ ->
          ( "rmw"
          , [] )
      | Fence0 _ ->
          ( "fence"
          , [] )
      | CompareExchangeStrong _ ->
          ( "cmpxchg_strong"
          , [] )
      | CompareExchangeWeak _ ->
          ( "cmpxchg_weak"
          , [] )
      | LinuxFence _ ->
          ( "linux_fence"
          , [] )
      | LinuxLoad _ ->
          ( "linux_load"
          , [] )
      | LinuxStore _ ->
          ( "linux_store"
          , [] )
      | LinuxRMW _ ->
          ( "linux_rmw"
          , [] ) in
  Dnode ( !^ (ansi_format [Bold; Magenta] "Eaction") ^^^ pp_keyword str
        , dtrees )


let dtree_of_expr expr =
  let rec self current_loc (Expr (annot, expr_) as expr) =
    let current_loc =
      match Annot.get_loc annot with Some l -> l | _ -> current_loc in
    let self expr = self current_loc expr in

    let pp_ctor str =
      match Annot.get_loc annot with
        | Some loc ->
            pp_eff_ctor str ^^^ Cerb_location.pp_location ~clever:true loc
        | None ->
            pp_eff_ctor str in

    let module E = Stdlib.Either in
    let is_attr = function Annot.Aattrs (Annot.Attrs attrs) -> E.Left attrs | annot -> E.Right annot in
    let attrs, rest = List.partition_map is_attr annot in
    let attrs = Annot.Attrs (List.concat attrs) in

    match expr_ with
      | Epure pe ->
          Dnode ( pp_ctor "Epure"
                , (*add_std_annot*) [dtree_of_pexpr pe] )
(*
      | Ememop of Mem_common.memop * ('bty, 'sym) generic_pexpr list
*)
      | Eaction (Paction (p, Action (act_loc, _, act))) ->
          dtree_of_action act
(*
      | Ecase of ('bty, 'sym) generic_pexpr * ('sym generic_pattern * ('a, 'bty, 'sym) generic_expr) list
*)
      | Elet (pat, pe, e) ->
          Dnode ( pp_ctor "Elet" (* ^^^ Pp_core.Basic.pp_pattern pat *)
                , [ dtree_of_pexpr pe; self e] )

      | Eif (pe, e1, e2) ->
          Dnode ( pp_ctor "Eif"
                , [ dtree_of_pexpr pe; self e1; self e2 ] )

      | Eccall (_, pe1, pe2, pe3) ->
          with_attributes attrs begin
            Dnode (pp_ctor "Eccall",
                   List.map dtree_of_pexpr (pe1 :: pe2 :: pe3))
          end
(*
    | Eproc of 'a * 'sym generic_name * ('bty, 'sym) generic_pexpr list
*)
    | Eunseq es ->
        Dnode (pp_ctor "Eunseq", List.map self es)
    | Ewseq (pat, e1, e2) ->
        Dnode ( pp_ctor "Ewseq" (* ^^^ P.group (Pp_core.Basic.pp_pattern pat) *)
              , (*add_std_annot*) [ (* Dleaf (pp_ctor "TODO_pattern")
                                  ; *) self e1
                                  ; self e2 ] )
    | Esseq (pat, e1, e2) ->
        Dnode ( pp_ctor "Esseq" (* ^^^ P.group (Pp_core.Basic.pp_pattern pat) *)
              , (*add_std_annot*) [ (* Dleaf (pp_ctor "TODO_pattern")
                                  ; *) self e1
                                  ; self e2 ] )


(*
    | Easeq of ('sym * core_base_type) * ('a, 'bty, 'sym) generic_action *
        ('a, 'bty, 'sym) generic_paction
*)
    | Ebound e ->
        Dnode (pp_ctor "Ebound", [self e])
(*
    | End of ('a, 'bty, 'sym) generic_expr list
*)
    | Esave ((sym, bTy), _, e) (* of ('sym * core_base_type) * ('sym * ((core_base_type * (Ctype.ctype * bool) option) * ('bty, 'sym) generic_pexpr)) list * ('a, 'bty, 'sym) generic_expr *) ->
        Dnode ( pp_ctor "Esave" ^^^ pp_symbol sym ^^ P.colon ^^^ Pp_core.Basic.pp_core_base_type bTy
              , (*add_std_annot*) [ self e ] )
(*
    | Erun of 'a * 'sym * ('bty, 'sym) generic_pexpr list
    | Epar of ('a, 'bty, 'sym) generic_expr list
    | Ewait of Mem_common.thread_id
*)
      | _ ->
          Dleaf (pp_ctor ("TODO_expr ==> " ^ String_core.string_of_expr expr))
  in
  self Cerb_location.unknown expr


(*
Expr of Annot.annot list * ('a, 'bty, 'sym) generic_expr_
*)


let pp_expr expr =
  pp_doc_tree (dtree_of_expr expr)



let pp_field w = !^ (ansi_format [Bold; Green] w)


let dtree_of_tagDefs xs =
  let aux (sym, (loc, tagDef)) =
    Pp_ail_ast.dtree_of_tag_definition (sym, (loc, Annot.no_attributes, tagDef)) in
  Dnode ( pp_field ".tagDefs"
        , List.map aux (Pmap.bindings_list xs) )


let dtree_of_funinfo xs =
(*
(
  Symbol.sym
,
 Cerb_location.t * Annot.attributes * Ctype.ctype *
   (Symbol.sym option * Ctype.ctype) list * bool * bool
)
Pmap.map
*)
  let pp_ctype (Ctype.Ctype (annots, _) as ty) =
    begin match Annot.get_typedef  annots with
      | Some sym ->
        P.brackets (P.string "typedef" ^^ P.colon ^^^ pp_symbol sym) ^^ P.space
      | None ->
        P.empty
    end ^^
    Pp_ail.pp_ctype Ctype.no_qualifiers ty in
  let aux (sym, (loc, attrs, ty, params, is_variadic, has_proto)) =
    Dleaf (pp_symbol sym ^^ P.colon ^^^
           begin if has_proto then
            P.string "PROTO" ^^ P.space
           else
            P.empty
           end ^^
           begin if is_variadic then
            P.string "variadic" ^^ P.space
           else
            P.empty
           end ^^
           P.parens (P.separate_map (P.comma ^^ P.space) (fun (sym_opt, ty) ->
            begin match sym_opt with
              | None -> P.underscore
              | Some sym -> pp_symbol sym
            end ^^ P.colon ^^^ pp_ctype ty
           ) params) ^^^ P.string "->" ^^^
           pp_ctype ty)
  in
  Dnode ( pp_field ".funinfo"
        , List.map aux (Pmap.bindings_list xs) )


let dtree_of_globs xs =
  let aux (sym, glob) =
    match glob with
    | GlobalDef ((bTy,_), e) ->
        Dnode ( pp_field "GlobalDef" ^^^ pp_symbol sym ^^ P.colon ^^^ Pp_core.Basic.pp_core_base_type bTy
              , [dtree_of_expr e] )
    | GlobalDecl (bTy,_) ->
        Dleaf (pp_field "GlobalDecl" ^^^ pp_symbol sym ^^ P.colon ^^^ Pp_core.Basic.pp_core_base_type bTy)
  in
  Dnode (pp_field ".globs", List.map aux xs)


let dtree_of_funs xs =
  let aux (sym, decl) =
    let dtree_of_param (sym, bTy) =
      Dleaf (pp_symbol sym ^^ P.colon ^^^ Pp_core.Basic.pp_core_base_type bTy) in
    match decl with
      | Fun (bTy, params, pe) ->
          Dnode ( pp_field "Fun" ^^^ pp_symbol sym ^^ P.colon ^^^ Pp_core.Basic.pp_core_base_type bTy
                , [ Dnode (pp_field ".params", List.map dtree_of_param params)
                  ; Dnode (pp_field ".body", [dtree_of_pexpr pe]) ] )
      | Proc (loc, _mrk, bTy, params, e) ->
          Dnode ( pp_field "Proc" ^^^ pp_symbol sym ^^ P.colon ^^^ Pp_core.Basic.pp_core_base_type bTy
                , [ Dnode (pp_field ".params", List.map dtree_of_param params)
                  ; Dnode (pp_field ".body", [dtree_of_expr e]) ] )
      | ProcDecl (loc, ret_bTy, params_bTys) ->
          (* TODO: loc*)
          Dleaf ( pp_field "ProcDecl" ^^^ pp_symbol sym ^^ P.colon ^^^
                  P.parens (comma_list Pp_core.Basic.pp_core_base_type params_bTys) ^^^
                  P.string "->" ^^^ Pp_core.Basic.pp_core_base_type ret_bTy )
      | BuiltinDecl (loc, ret_bTy, params_bTys) ->
          (* TODO: loc*)
          Dleaf ( pp_field "BuiltinDecl" ^^^ pp_symbol sym ^^ P.colon ^^^
                  P.parens (comma_list Pp_core.Basic.pp_core_base_type params_bTys) ^^^
                  P.string "->" ^^^ Pp_core.Basic.pp_core_base_type ret_bTy )
  in
  Dnode ( pp_field ".funs"
        , List.map aux (Pmap.bindings_list xs) )


let pp_file file =
  pp_doc_tree begin
    Dnode ( pp_field "CoreFile" ^^ (P.optional (fun sym -> P.space ^^ P.parens (!^ "startup:" ^^^ pp_symbol sym)) file.main)
          , [ dtree_of_tagDefs file.tagDefs
            ; dtree_of_funinfo file.funinfo
            ; dtree_of_globs file.globs
            ; dtree_of_funs file.funs ] )
  end
