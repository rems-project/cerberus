(* stealing from pp_core_ast *)

open Cerb_pp_prelude
(*open Pp_ail*)

module CF = Cerb_frontend
open CF

open Pp_ast
open Cerb_colour

module P = PPrint

module PP = struct

  let pp_symbol  a = !^ (ansi_format [Blue] (Pp_symbol.to_string_pretty a))

  let pp_keyword w =
    !^ (ansi_format [Green] w)

  let pp_pure_ctor w =
    !^ (ansi_format [Bold; Cyan] w)

  let pp_eff_ctor w =
    !^ (ansi_format [Bold; Magenta] w)


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

  (* let pp_asym asym =  *)
  (*   let open Mucore in *)
  (*   pp_symbol asym.sym ^^^ Cerb_location.pp_location ~clever:false asym.loc *)

  (* let dtree_of_asym asym =  *)
  (*   Pp_ast.Dleaf (pp_asym asym) *)

  open Mucore

  module Pp_typ = Pp_mucore.Pp_typ

  let pp_act act =
    Pp_typ.pp_ct act.ct ^^^ Cerb_location.pp_location ~clever:false act.loc

  let dtree_of_act act = 
    Pp_ast.Dleaf (pp_act act)


  let rec dtree_of_object_value = function
    | M_OVinteger ival ->
        Dleaf (pp_pure_ctor "OVinteger" ^^^ Impl_mem.pp_integer_value_for_core ival)
    | M_OVfloating fval ->
        Dleaf (pp_pure_ctor "OVfloating" ^^^
               Impl_mem.case_fval fval
                 (fun () -> !^ "unspec(floating)")
                (fun fval -> !^(string_of_float fval)))
    | M_OVpointer ptrval ->
        Dleaf (pp_pure_ctor "OVpointer" ^^^ Impl_mem.pp_pointer_value ptrval)
    | M_OVarray lvals ->
        Dnode ( pp_pure_ctor "OVarray"
              , List.map dtree_of_object_value lvals)
    | M_OVstruct (tag_sym, xs) ->
        (* (Symbol.identifier * Ctype.ctype * Impl_mem.mem_value) list *)
        Dleaf (pp_pure_ctor "OVstruct" ^^^ !^ (ansi_format [Red] "TODO"))
    | M_OVunion (tag_sym, membr_ident, mval) ->
        Dleaf (pp_pure_ctor "OVunion" ^^^ !^ (ansi_format [Red] "TODO"))
  (* and dtree_of_loaded_value = function *)
  (*   | M_LVspecified oval -> *)
  (*       Dnode (pp_pure_ctor "LVspecified", [dtree_of_object_value oval]) *)

  and dtree_of_value = function
    | M_Vobject oval ->
        Dnode (pp_pure_ctor "Vobject", [dtree_of_object_value oval])
    (* | M_Vloaded lval -> *)
    (*     Dnode (pp_pure_ctor "Vloaded", [dtree_of_loaded_value lval]) *)
    | M_Vunit ->
        Dleaf (pp_pure_ctor "Vunit")
    | M_Vtrue ->
        Dleaf (pp_pure_ctor "Vtrue")
    | M_Vfalse ->
        Dleaf (pp_pure_ctor "Vfalse")
    | M_Vlist (bTy, cvals) ->
        Dleaf (pp_pure_ctor "Vlist" ^^^ !^ (ansi_format [Red] "TODO"))
    | M_Vtuple cvals ->
        Dleaf (pp_pure_ctor "Vtuple" ^^^ !^ (ansi_format [Red] "TODO"))
    | M_Vctype ctype ->
        Dleaf (pp_pure_ctor "Vctype" ^^^ !^ (ansi_format [Red] "TODO"))
    | M_Vfunction_addr sym ->
        Dleaf (pp_pure_ctor "Vfunction_addr"  ^^^ !^ (ansi_format [Red] "TODO"))
   (* type 'sym generic_value =  (* Core values *)
    | Vobject of ( 'sym generic_object_value) (* C object value *)
    | Vloaded of ( 'sym generic_loaded_value) (* loaded C object value *)
    | Vunit
    | Vtrue
    | Vfalse
    | Vctype of ctype (* C type as value *)
    | Vlist of core_base_type * ( 'sym generic_value) list
    | Vtuple of ( 'sym generic_value) list tuple *)


  let string_of_bop = Pp_core_ast.string_of_bop


  let dtree_of_pexpr (pexpr : 'ty mu_pexpr) =

    let rec self (M_Pexpr (loc, annot, _, pexpr_)) =

      let pp_ctor str =
        pp_pure_ctor str ^^^ 
          Cerb_location.pp_location ~clever:false loc
      in

      match pexpr_ with

        | M_PEsym sym ->
            Dleaf (pp_ctor "PEsym" ^^^ pp_symbol sym)
        (* | M_PEimpl iCst -> *)
        (*     Dleaf (pp_ctor "PEimpl" ^^^ !^ (ansi_format [Red] "TODO")) *)
        | M_PEval cval ->
            Dnode (pp_ctor "PEval", [dtree_of_value cval])
        | M_PEconstrained xs ->
            Dleaf (pp_ctor "PEconstrained" ^^^ !^ (ansi_format [Red] "TODO"))
        | M_PEctor (ctor, pes) ->
            Dleaf (pp_ctor "PEctor" ^^^ !^ (ansi_format [Red] "TODO"))
        | M_PEarray_shift (pe1, ty, pe2) ->
            Dleaf (pp_ctor "PEarray_shift" ^^^ !^ (ansi_format [Red] "TODO"))
        | M_PEmember_shift (pe, sym, ident) ->
            Dleaf (pp_ctor "PEmember_shift" ^^^ !^ (ansi_format [Red] "TODO"))
        | M_PEnot pe ->
            Dnode (pp_ctor "PEnot", [self pe])
        | M_PEop (bop, pe1, pe2) ->
            Dnode ( pp_ctor "PEop" ^^^ P.squotes (!^ (string_of_bop bop))
                  , [self pe1; self pe2] )
        | M_PEstruct (tag_sym, xs) ->
            assert false
        | M_PEunion (tag_sym, memb_ident, pe) ->
            assert false
        | M_PEmemberof (tag_sym, memb_ident, pe) ->
            assert false


        (* | M_PEcase (pe, xs) -> *)
        (*     Dleaf (pp_ctor "PEcase" ^^^ !^ (ansi_format [Red] "TODO")) *)
        | M_PElet (pat, pe1, pe2) ->
            Dnode ( pp_ctor "PElet" (* ^^^ Pp_core.Basic.pp_pattern pat *)
                  , [ self pe1; self pe2] )
        | M_PEif (pe1, pe2, pe3) ->
            Dnode ( pp_ctor "PEif"
                  , [ self pe1; self pe2; self pe3 ] )
        | M_PEundef (loc, ub) ->
            Dleaf (pp_ctor "PEundef" ^^^ !^ (ansi_format [Red] "TODO"))
        | M_PEerror (str, pe) ->
            Dnode ( pp_ctor "PEerror" ^^^ P.dquotes (!^ (ansi_format [Red] str))
                  , [self pe] )
        | _ ->
           Dnode ( pp_ctor ("Pexpr(TODO)")
                  , [Dleaf (Pp_mucore.pp_pexpr pexpr)])
    in
    self pexpr

  let pp_action_ctor act =
    pp_keyword begin match act with
      | M_Create _ ->
          "create"
      | M_CreateReadOnly _ ->
          "create_readonly"
      | M_Alloc _ ->
          "alloc"
      | M_Kill _ ->
          "kill"
      | M_Store _ ->
          "store"
      | M_Load _ ->
          "load"
      | M_RMW _ ->
          "rmw"
      | M_Fence _ ->
          "fence"
      | M_CompareExchangeStrong _ ->
          "cmpxchg_strong"
      | M_CompareExchangeWeak _ ->
          "cmpxchg_weak"
      | M_LinuxFence _ ->
          "linux_fence"
      | M_LinuxLoad _ ->
          "linux_load"
      | M_LinuxStore _ ->
          "linux_store"
      | M_LinuxRMW _ ->
          "linux_rmw"
    end

  let dtree_of_action act =
    let (str, dtrees) =
      match act with
        | M_Create _ ->
            ( "create"
            , [] )
        | M_CreateReadOnly _ ->
            ( "create_readonly"
            , [] )
        | M_Alloc _ ->
            ( "alloc"
            , [] )
        | M_Kill _ ->
            ( "kill"
            , [] )
        | M_Store _ ->
            ( "store"
            , [] )
        | M_Load (pe1, pe2, mo) ->
            ( "load"
            , [ dtree_of_act pe1
              ; dtree_of_pexpr pe2 ] )
        | M_RMW _ ->
            ( "rmw"
            , [] )
        | M_Fence _ ->
            ( "fence"
            , [] )
        | M_CompareExchangeStrong _ ->
            ( "cmpxchg_strong"
            , [] )
        | M_CompareExchangeWeak _ ->
            ( "cmpxchg_weak"
            , [] )
        | M_LinuxFence _ ->
            ( "linux_fence"
            , [] )
        | M_LinuxLoad _ ->
            ( "linux_load"
            , [] )
        | M_LinuxStore _ ->
            ( "linux_store"
            , [] )
        | M_LinuxRMW _ ->
            ( "linux_rmw"
            , [] ) in
    Dnode ( !^ (ansi_format [Bold; Magenta] "Eaction") ^^^ pp_keyword str
          , dtrees )


  let rec dtree_of_expr ((M_Expr (loc, annot, _ty, expr_)) as expr) =

      let pp_ctor str =
        pp_eff_ctor str ^^^ 
          Cerb_location.pp_location ~clever:false loc
      in

      match expr_ with
  (*
        | Ememop of Mem_common.memop * ('bty, 'sym) generic_pexpr list
  *)
        | M_Epure pe ->
            Dnode ( pp_ctor "Epure"
                  , (*add_std_annot*) [dtree_of_pexpr pe] )
         | M_Eskip ->
             Dleaf (pp_ctor "Eskip")
        | M_Eaction (M_Paction (p, M_Action (act_loc, act))) ->
            dtree_of_action act

  (*
      | Eccall of 'a * ('bty, 'sym) generic_pexpr *
          ('bty, 'sym) generic_pexpr * ('bty, 'sym) generic_pexpr list
      | Eproc of 'a * 'sym generic_name * ('bty, 'sym) generic_pexpr list
  *)
        (* | _ -> *)
        (*    Dleaf (pp_ctor ("Expr(TODO): " ^ MuPP.string_of_expr expr)) *)

  (*
        | Ecase of ('bty, 'sym) generic_pexpr * ('sym generic_pattern * ('a, 'bty, 'sym) generic_expr) list
        | Eif of ('bty, 'sym) generic_pexpr * ('a, 'bty, 'sym) generic_expr * ('a, 'bty, 'sym) generic_expr
  *)

      | M_Elet (pat, e1, e2) ->
          Dnode ( pp_ctor "Elet" (* ^^^ P.group (Pp_core.Basic.pp_pattern pat) *)
                , (*add_std_annot*) [ (* Dleaf (pp_ctor "TODO_pattern")
                                    ; *) dtree_of_pexpr e1
                                    ; dtree_of_expr e2 ] )
      | M_Ewseq (pat, e1, e2) ->
          Dnode ( pp_ctor "Ewseq" (* ^^^ P.group (Pp_core.Basic.pp_pattern pat) *)
                , (*add_std_annot*) [ (* Dleaf (pp_ctor "TODO_pattern")
                                    ; *) dtree_of_expr e1
                                    ; dtree_of_expr e2 ] )
      | M_Esseq (pat, e1, e2) ->
          Dnode ( pp_ctor "Esseq" (* ^^^ P.group (Pp_core.Basic.pp_pattern pat) *)
                , (*add_std_annot*) [ (* Dleaf (pp_ctor "TODO_pattern")
                                    ; *) dtree_of_expr e1
                                    ; dtree_of_expr e2 ] )
      (* | M_Eundef (loc, ub) -> *)
      (*    Dleaf (pp_ctor "PEundef" ^^^ !^ (ansi_format [Red] "TODO")) *)

      (* | M_Eerror (str, pe) -> *)
      (*     Dnode ( pp_ctor "Eerror" ^^^ P.dquotes (!^ (ansi_format [Red] str)) *)
      (*           , [dtree_of_pexpr pe] ) *)
      | M_Erun (l, asyms) ->
         Dnode ( pp_pure_ctor "Erun"
               , List.map dtree_of_pexpr asyms)

  (*
      | Easeq of ('sym * core_base_type) * ('a, 'bty, 'sym) generic_action *
          ('a, 'bty, 'sym) generic_paction
  *)
      | M_Ebound e ->
          Dnode (pp_ctor "Ebound", [dtree_of_expr e])
  (*
      | End of ('a, 'bty, 'sym) generic_expr list
  *)

  (*

      | Epar of ('a, 'bty, 'sym) generic_expr list
      | Ewait of Mem_common.thread_id
  *)
        | _ ->
           Dnode ( pp_ctor ("TExpr(TODO)")
                  , [Dleaf (Pp_mucore.pp_expr expr)])
            (* Dleaf (pp_ctor ("TODO_expr ==> " ^ MuPP.string_of_texpr expr)) *)


  (*
  Expr of Annot.annot list * ('a, 'bty, 'sym) generic_expr_
  *)


  let pp_expr expr =
    pp_doc_tree (dtree_of_expr expr)



  let pp_field w = !^ (ansi_format [Bold; Green] w)


  let dtree_of_tagDefs xs =
    let aux (sym, tagDef) =
      Pp_ail_ast.dtree_of_tag_definition (sym, (Annot.no_attributes, tagDef)) in
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
      | M_GlobalDef (ct, e) ->
          Dnode ( pp_field "GlobalDef" ^^^ pp_symbol sym
                , [Dleaf (Pp_typ.pp_ct ct); dtree_of_expr e] )
      | M_GlobalDecl ct ->
          Dnode ( pp_field "GlobalDecl" ^^^ pp_symbol sym
                , [Dleaf (Pp_typ.pp_ct ct)] )
    in
    Dnode (pp_field ".globs", List.map aux xs)


  let dtree_of_label l def =
    match def with
    | M_Return (loc) -> 
       (Dleaf (!^"return" ^^^ Cerb_location.pp_location ~clever:false loc))
    | M_Label (loc, args_and_body, _, _) ->
       Dnode (pp_symbol l ^^^ Cerb_location.pp_location ~clever:false loc
             , [dtree_of_mu_arguments dtree_of_expr args_and_body])

  let dtrees_of_labels labels = 
    Pmap.fold (fun l def acc ->
        acc @ [dtree_of_label l def]
      ) labels []

  let dtree_of_funs xs =
    let aux (sym, decl) =
      match decl with
        | M_Proc (loc, args_and_body, _, _) ->
            Dnode ( pp_field "Proc" ^^^ pp_symbol sym
                  , [ dtree_of_mu_arguments (fun (body, labels, rt) ->
                      Dnode ( !^"proc_body"
                            , [ Dnode (pp_field ".body", [dtree_of_expr body])
                              ; Dnode (pp_field ".labels", dtrees_of_labels labels) ] ))
                      args_and_body] )
        | M_ProcDecl (loc, ft) ->
            (* TODO: loc*)
            Dleaf ( pp_field "ProcDecl" ^^^ pp_symbol sym (* TODO: spec *))
    in
    Dnode ( pp_field ".funs"
          , List.map aux (Pmap.bindings_list xs) )


  let pp_file file =
    pp_doc_tree begin
      Dnode ( pp_field "CoreFile" ^^ (P.optional (fun sym -> P.space ^^ P.parens (!^ "startup:" ^^^ pp_symbol sym)) file.mu_main)
            (* todo *)
            , [ (* dtree_of_tagDefs file.mu_tagDefs
               * ; dtree_of_funinfo file.mu_funinfo
               * ;  *)dtree_of_globs file.mu_globs
              ; dtree_of_funs file.mu_funs ] )
    end

  let pp_pexpr pexpr = pp_doc_tree (dtree_of_pexpr pexpr)

end

let pp_expr = PP.pp_expr
let pp_pexpr = PP.pp_pexpr

let pp_file = PP.pp_file

