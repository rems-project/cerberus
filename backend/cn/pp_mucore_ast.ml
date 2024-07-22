(* stealing from pp_core_ast *)

open Cerb_pp_prelude
module CF = Cerb_frontend
open CF
open Pp_ast
open Cerb_colour
module P = PPrint

module PP = struct
  let pp_symbol a = !^(ansi_format [ Blue ] (Pp_symbol.to_string_pretty a))

  let pp_keyword w = !^(ansi_format [ Green ] w)

  let pp_pure_ctor w = !^(ansi_format [ Bold; Cyan ] w)

  let pp_eff_ctor w = !^(ansi_format [ Bold; Magenta ] w)

  open Mucore
  module Pp_typ = Pp_mucore.Pp_typ

  let pp_act act = Pp_typ.pp_ct act.ct ^^^ Cerb_location.pp_location ~clever:false act.loc

  let dtree_of_act act = Pp_ast.Dleaf (pp_act act)

  let rec dtree_of_object_value (M_OV (_bty, ov)) =
    match ov with
    | M_OVinteger ival ->
      Dleaf (pp_pure_ctor "OVinteger" ^^^ Impl_mem.pp_integer_value_for_core ival)
    | M_OVfloating fval ->
      Dleaf
        (pp_pure_ctor "OVfloating"
         ^^^ Impl_mem.case_fval
               fval
               (fun () -> !^"unspec(floating)")
               (fun fval -> !^(string_of_float fval)))
    | M_OVpointer ptrval ->
      Dleaf (pp_pure_ctor "OVpointer" ^^^ Impl_mem.pp_pointer_value ptrval)
    | M_OVarray lvals ->
      Dnode (pp_pure_ctor "OVarray", List.map dtree_of_object_value lvals)
    | M_OVstruct (_tag_sym, _xs) ->
      Dleaf (pp_pure_ctor "OVstruct" ^^^ !^(ansi_format [ Red ] "TODO"))
    | M_OVunion (_tag_sym, _membr_ident, _mval) ->
      Dleaf (pp_pure_ctor "OVunion" ^^^ !^(ansi_format [ Red ] "TODO"))


  and dtree_of_value (M_V (_bty, v)) =
    match v with
    | M_Vobject oval -> Dnode (pp_pure_ctor "Vobject", [ dtree_of_object_value oval ])
    | M_Vunit -> Dleaf (pp_pure_ctor "Vunit")
    | M_Vtrue -> Dleaf (pp_pure_ctor "Vtrue")
    | M_Vfalse -> Dleaf (pp_pure_ctor "Vfalse")
    | M_Vlist (_bTy, _cvals) ->
      Dleaf (pp_pure_ctor "Vlist" ^^^ !^(ansi_format [ Red ] "TODO"))
    | M_Vtuple _cvals -> Dleaf (pp_pure_ctor "Vtuple" ^^^ !^(ansi_format [ Red ] "TODO"))
    | M_Vctype _ctype -> Dleaf (pp_pure_ctor "Vctype" ^^^ !^(ansi_format [ Red ] "TODO"))
    | M_Vfunction_addr _sym ->
      Dleaf (pp_pure_ctor "Vfunction_addr" ^^^ !^(ansi_format [ Red ] "TODO"))


  let string_of_bop = Pp_core_ast.string_of_bop

  let dtree_of_pexpr (pexpr : 'ty mu_pexpr) =
    let rec self (M_Pexpr (loc, annot, _, pexpr_)) =
      let pp_ctor str =
        pp_pure_ctor str ^^^ Cerb_location.pp_location ~clever:false loc
      in
      let without_annot =
        match pexpr_ with
        | M_PEsym sym -> Dleaf (pp_ctor "PEsym" ^^^ pp_symbol sym)
        | M_PEval cval -> Dnode (pp_ctor "PEval", [ dtree_of_value cval ])
        | M_PEconstrained _xs ->
          Dleaf (pp_ctor "PEconstrained" ^^^ !^(ansi_format [ Red ] "TODO"))
        | M_PEctor (ctor, pes) ->
          Dnode
            ( pp_ctor "PEctor",
              [ Dleaf (Pp_mucore.Basic.pp_ctor ctor) ] @ List.map self pes )
        | M_PEarray_shift (_pe1, _ty, _pe2) ->
          Dleaf (pp_ctor "PEarray_shift" ^^^ !^(ansi_format [ Red ] "TODO"))
        | M_PEmember_shift (_pe, _sym, _ident) ->
          Dleaf (pp_ctor "PEmember_shift" ^^^ !^(ansi_format [ Red ] "TODO"))
        | M_PEnot pe -> Dnode (pp_ctor "PEnot", [ self pe ])
        | M_PEop (bop, pe1, pe2) ->
          Dnode
            (pp_ctor "PEop" ^^^ P.squotes !^(string_of_bop bop), [ self pe1; self pe2 ])
        | M_PElet (_pat, pe1, pe2) -> Dnode (pp_ctor "PElet", [ self pe1; self pe2 ])
        | M_PEif (pe1, pe2, pe3) ->
          Dnode (pp_ctor "PEif", [ self pe1; self pe2; self pe3 ])
        | M_PEundef (_loc, _ub) ->
          Dleaf (pp_ctor "PEundef" ^^^ !^(ansi_format [ Red ] "TODO"))
        | M_PEerror (str, pe) ->
          Dnode (pp_ctor "PEerror" ^^^ P.dquotes !^(ansi_format [ Red ] str), [ self pe ])
        | _ -> Dnode (pp_ctor "Pexpr(TODO)", [ Dleaf (Pp_mucore.pp_pexpr pexpr) ])
      in
      match (annot, without_annot) with
      | [], dtree -> dtree
      | annots, Dnode (nm, xs) ->
        Dnode
          ( nm,
            xs
            @ [ Dnode
                  ( pp_ctor "Annot",
                    List.map
                      (fun ann -> Dleaf ann)
                      (List.concat_map Pp_mucore.Basic.pp_str_annot annots) )
              ] )
      | _, dtree -> dtree
    in
    self pexpr


  let pp_action_ctor act =
    pp_keyword
      (match act with
       | M_Create _ -> "create"
       | M_CreateReadOnly _ -> "create_readonly"
       | M_Alloc _ -> "alloc"
       | M_Kill _ -> "kill"
       | M_Store _ -> "store"
       | M_Load _ -> "load"
       | M_RMW _ -> "rmw"
       | M_Fence _ -> "fence"
       | M_CompareExchangeStrong _ -> "cmpxchg_strong"
       | M_CompareExchangeWeak _ -> "cmpxchg_weak"
       | M_LinuxFence _ -> "linux_fence"
       | M_LinuxLoad _ -> "linux_load"
       | M_LinuxStore _ -> "linux_store"
       | M_LinuxRMW _ -> "linux_rmw")


  let dtree_of_action act =
    let str, dtrees =
      match act with
      | M_Create _ -> ("create", [])
      | M_CreateReadOnly _ -> ("create_readonly", [])
      | M_Alloc _ -> ("alloc", [])
      | M_Kill _ -> ("kill", [])
      | M_Store _ -> ("store", [])
      | M_Load (pe1, pe2, _mo) -> ("load", [ dtree_of_act pe1; dtree_of_pexpr pe2 ])
      | M_RMW _ -> ("rmw", [])
      | M_Fence _ -> ("fence", [])
      | M_CompareExchangeStrong _ -> ("cmpxchg_strong", [])
      | M_CompareExchangeWeak _ -> ("cmpxchg_weak", [])
      | M_LinuxFence _ -> ("linux_fence", [])
      | M_LinuxLoad _ -> ("linux_load", [])
      | M_LinuxStore _ -> ("linux_store", [])
      | M_LinuxRMW _ -> ("linux_rmw", [])
    in
    Dnode (!^(ansi_format [ Bold; Magenta ] "Eaction") ^^^ pp_keyword str, dtrees)


  let rec dtree_of_expr (M_Expr (loc, _annot, _ty, expr_) as expr) =
    let pp_ctor str = pp_eff_ctor str ^^^ Cerb_location.pp_location ~clever:true loc in
    match expr_ with
    | M_Epure pe -> Dnode (pp_ctor "Epure", (*add_std_annot*) [ dtree_of_pexpr pe ])
    | M_Eskip -> Dleaf (pp_ctor "Eskip")
    | M_Eaction (M_Paction (_p, M_Action (_act_loc, act))) -> dtree_of_action act
    | M_Eif (pe, e1, e2) ->
      Dnode
        ( pp_ctor "Eif",
          (*add_std_annot*) [ dtree_of_pexpr pe; dtree_of_expr e1; dtree_of_expr e2 ] )
    | M_Elet (_pat, e1, e2) ->
      Dnode
        ( pp_ctor "Elet" (* ^^^ P.group (Pp_core.Basic.pp_pattern pat) *),
          (*add_std_annot*)
          [ (* Dleaf (pp_ctor "TODO_pattern") ; *) dtree_of_pexpr e1; dtree_of_expr e2 ]
        )
    | M_Ewseq (_pat, e1, e2) ->
      Dnode
        ( pp_ctor "Ewseq" (* ^^^ P.group (Pp_core.Basic.pp_pattern pat) *),
          (*add_std_annot*)
          [ (* Dleaf (pp_ctor "TODO_pattern") ; *) dtree_of_expr e1; dtree_of_expr e2 ] )
    | M_Esseq (_pat, e1, e2) ->
      Dnode
        ( pp_ctor "Esseq" (* ^^^ P.group (Pp_core.Basic.pp_pattern pat) *),
          (*add_std_annot*)
          [ (* Dleaf (pp_ctor "TODO_pattern") ; *) dtree_of_expr e1; dtree_of_expr e2 ] )
    | M_Erun (_l, asyms) -> Dnode (pp_pure_ctor "Erun", List.map dtree_of_pexpr asyms)
    | M_Ebound e -> Dnode (pp_ctor "Ebound", [ dtree_of_expr e ])
    | M_Ememop _ | M_Eccall (_, _, _) | M_Eunseq _ | M_End _ | M_CN_progs (_, _) ->
      Dnode (pp_ctor "TExpr(TODO)", [ Dleaf (Pp_mucore.pp_expr expr) ])


  let pp_expr expr = pp_doc_tree (dtree_of_expr expr)

  let pp_field w = !^(ansi_format [ Bold; Green ] w)

  let dtree_of_tagDefs xs =
    let aux (sym, tagDef) =
      Pp_ail_ast.dtree_of_tag_definition
        (sym, (Cerb_location.unknown, Annot.no_attributes, tagDef))
    in
    Dnode (pp_field ".tagDefs", List.map aux (Pmap.bindings_list xs))


  let dtree_of_funinfo xs =
    let pp_ctype (Ctype.Ctype (annots, _) as ty) =
      (match Annot.get_typedef annots with
       | Some sym ->
         P.brackets (P.string "typedef" ^^ P.colon ^^^ pp_symbol sym) ^^ P.space
       | None -> P.empty)
      ^^ Pp_ail.pp_ctype Ctype.no_qualifiers ty
    in
    let aux (sym, (_loc, _attrs, ty, params, is_variadic, has_proto)) =
      Dleaf
        (pp_symbol sym
         ^^ P.colon
         ^^^ (if has_proto then
                P.string "PROTO" ^^ P.space
              else
                P.empty)
         ^^ (if is_variadic then
               P.string "variadic" ^^ P.space
             else
               P.empty)
         ^^ P.parens
              (P.separate_map
                 (P.comma ^^ P.space)
                 (fun (sym_opt, ty) ->
                   (match sym_opt with None -> P.underscore | Some sym -> pp_symbol sym)
                   ^^ P.colon
                   ^^^ pp_ctype ty)
                 params)
         ^^^ P.string "->"
         ^^^ pp_ctype ty)
    in
    Dnode (pp_field ".funinfo", List.map aux (Pmap.bindings_list xs))


  let dtree_of_globs xs =
    let aux (sym, glob) =
      match glob with
      | M_GlobalDef (ct, e) ->
        Dnode
          ( pp_field "GlobalDef" ^^^ pp_symbol sym,
            [ Dleaf (Pp_typ.pp_ct ct); dtree_of_expr e ] )
      | M_GlobalDecl ct ->
        Dnode (pp_field "GlobalDecl" ^^^ pp_symbol sym, [ Dleaf (Pp_typ.pp_ct ct) ])
    in
    Dnode (pp_field ".globs", List.map aux xs)


  let dtree_of_label l def =
    match def with
    | M_Return loc -> Dleaf (!^"return" ^^^ Cerb_location.pp_location ~clever:false loc)
    | M_Label (loc, args_and_body, _, _) ->
      Dnode
        ( pp_symbol l ^^^ Cerb_location.pp_location ~clever:false loc,
          [ dtree_of_mu_arguments dtree_of_expr args_and_body ] )


  let dtrees_of_labels labels =
    Pmap.fold (fun l def acc -> acc @ [ dtree_of_label l def ]) labels []


  let dtree_of_funs xs =
    let aux (sym, decl) =
      match decl with
      | M_Proc (_loc, args_and_body, _, _) ->
        Dnode
          ( pp_field "Proc" ^^^ pp_symbol sym,
            [ dtree_of_mu_arguments
                (fun (body, labels, _rt) ->
                  Dnode
                    ( !^"proc_body",
                      [ Dnode (pp_field ".body", [ dtree_of_expr body ]);
                        Dnode (pp_field ".labels", dtrees_of_labels labels)
                      ] ))
                args_and_body
            ] )
      | M_ProcDecl (_loc, _ft) ->
        (* TODO: loc*)
        Dleaf (pp_field "ProcDecl" ^^^ pp_symbol sym (* TODO: spec *))
    in
    Dnode (pp_field ".funs", List.map aux (Pmap.bindings_list xs))


  let pp_file file =
    pp_doc_tree
      (Dnode
         ( pp_field "CoreFile"
           ^^ P.optional
                (fun sym -> P.space ^^ P.parens (!^"startup:" ^^^ pp_symbol sym))
                file.mu_main
           (* todo *),
           [ (* dtree_of_tagDefs file.mu_tagDefs * ; dtree_of_funinfo file.mu_funinfo *
                ; *)
             dtree_of_globs file.mu_globs;
             dtree_of_funs file.mu_funs
           ] ))


  let pp_pexpr pexpr = pp_doc_tree (dtree_of_pexpr pexpr)
end

let pp_expr = PP.pp_expr

let pp_pexpr = PP.pp_pexpr

let pp_file = PP.pp_file
