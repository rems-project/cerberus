open Core
open Milicore
open List
open Cerb_pp_prelude
open PPrint

let inline_label oannots (label_loc, label_sym, label_arg_syms_bts, label_body) args =
  Cerb_debug.output_string2 (Pp_symbol.to_string label_sym ^ ": " ^ Pp_utils.to_plain_string (Cerb_location.pp_location label_loc));
  if ((List.length label_arg_syms_bts) <> (List.length args)) 
  then begin
      PPrint.ToChannel.compact stdout
        (!^"label:"  ^^^ !^(Pp_symbol.to_string_pretty_cn label_sym));
      PPrint.ToChannel.compact stdout
        (!^"label params:"  ^^^ Pp_core.Basic.pp_params label_arg_syms_bts);
      PPrint.ToChannel.compact stdout
        (!^", args:" ^^^ parens (separate_map comma Pp_core.Basic.pp_pexpr args));
      failwith "Different argument numbers"
    end 
  else
  let arguments = (Lem_list.list_combine label_arg_syms_bts args) in
  let (Expr(annots2, e_)) = 
    let label_annot = Option.get (Annot.get_label_annot oannots) in
    let label_body' = match label_body with
      | Expr (body_annots, body) ->
          Expr ((Annot.Ainlined_label (label_loc, label_sym, label_annot)) :: body_annots, body)    
    in
    (List.fold_right (fun ((spec_arg, spec_bt), expr_arg) body ->
         match expr_arg with
         | Pexpr (_, _, PEsym s) when Symbol.symbolEquality s spec_arg ->
            body
         | _ ->
            let pat = (Pattern ([], CaseBase (Some spec_arg, spec_bt))) in
            Expr([], (Elet (pat, expr_arg, body)))
       ) arguments label_body')
  in
  (* this combines annotations *)
  Expr (annots2 @ oannots , e_)


(* looking at how remove_unspecs.ml works, copying, and adjusting *)

open Core_rewriter
module RW = Rewriter(Identity_monad)

let rewriter label : 'bty RW.rewriter =
  let (label_loc, label_sym, label_arg_syms_bts, label_body) = label in
  {
    rw_pexpr= RW.RW (fun _ _ -> Traverse);
    rw_action= RW.RW (fun _ act -> Traverse);    
    rw_expr=
      RW.RW (fun _ (Expr (annots, expr_)) ->
        match expr_ with
        | Erun (_, l, args) when Symbol.symbolEquality l label_sym ->
           Update (inline_label annots label args)
        | _ ->
           Traverse
      )
   }



let rewrite_expr label expr =
  Identity_monad.unwrap (RW.rewriteExpr (rewriter label) expr)



(* todo: ensure CN does not loop when inlining *)
let should_be_inlined annots = 
  let warn lk = Cerb_debug.warn [] (fun () -> "inlining"^lk^"label") in
  match Annot.get_label_annot annots with
  | Some (LAloop_break _) -> true
  | Some (LAloop_continue _) -> true
  | Some (LAloop_body _) -> true
  | Some LAswitch -> warn "switch"; true
  | Some LAcase -> warn "case"; true
  | Some LAdefault -> warn "default"; true
  | Some _ -> false
  | None -> warn "(generic)"; true


(* TODO: check about largs *)
let rec inline_label_labels_and_body ~to_inline ~to_keep body = 
  match to_inline with
  | [] -> 
     (to_keep, body)
  | l :: to_inline' ->
     let to_inline' = 
       List.map (fun (lloc, lname, arg_syms, lbody) -> 
           (lloc, lname, arg_syms, rewrite_expr l lbody)
         ) to_inline'
     in
     let to_keep = 
       Pmap.map (function
           | Mi_Return loc -> 
              Mi_Return loc
           | Mi_Label (loc, lt, args, lbody, annot) -> 
              Mi_Label (loc, lt, args, rewrite_expr l lbody, annot)
         ) to_keep
     in
     let body = rewrite_expr l body in
     inline_label_labels_and_body ~to_inline:to_inline' ~to_keep body



let rewrite_fun_map_decl = function
  | Mi_Proc (loc, mrk, rbt, arg_bts, body, label_defs) -> 
     let to_keep, to_inline = 
       Pmap.fold (fun label def (to_keep, to_inline) ->
           match def with
           | Mi_Label(l_loc, _lt, args, lbody, annot) when should_be_inlined annot ->
              to_keep, 
              ((l_loc, label, args, lbody) :: to_inline)
           | Mi_Label _
           | Mi_Return _ -> 
              (Pmap.add label def to_keep), 
              to_inline
         ) 
         label_defs 
         (Pmap.empty Symbol.symbol_compare, [])
     in
     let (label_defs, body) = inline_label_labels_and_body ~to_inline ~to_keep body in
     Mi_Proc (loc, mrk, rbt, arg_bts, body, label_defs)
  | d -> d




let rewrite_file file = 
  { file with mi_funs = Pmap.map rewrite_fun_map_decl file.mi_funs }


