open Core
open Milicore
open List

let inline_label oannots (label_sym, label_arg_syms_bts, label_body) args =
  assert ((List.length label_arg_syms_bts) = (List.length args));
  let arguments = (Lem_list.list_combine label_arg_syms_bts args) in
  let (Expr(annots2, e_)) = 
    (List.fold_right (fun ((spec_arg, spec_bt), expr_arg) body ->
         match expr_arg with
         | Pexpr (_, _, PEsym s) when Symbol.symbolEquality s spec_arg ->
            body
         | _ ->
            let pat = (Pattern ([], CaseBase (Some spec_arg, spec_bt))) in
            Expr([], (Elet (pat, expr_arg, body)))
       ) arguments label_body)
  in
  (* this combines annotations *)
  Expr (annots2 @ oannots, e_)


(* looking at how remove_unspecs.ml works, copying, and adjusting *)

open Core_rewriter
module RW = Rewriter(Identity_monad)

let rewriter label : 'bty RW.rewriter =
  let (label_sym, label_arg_syms_bts, label_body) = label in
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
  match Annot.get_label_annot annots with
  | Some (LAloop_break _) -> true
  | Some (LAloop_continue _) -> true
  | Some (LAloop_body _) -> true
  | Some LAswitch -> 
     Debug_ocaml.warn [] (fun () -> "inlining switch label"); 
     true
  | Some LAcase -> 
     Debug_ocaml.warn [] (fun () -> "inlining case label"); 
     true
  | Some LAdefault -> 
     Debug_ocaml.warn [] (fun () -> "inlining default label"); 
     true
  | _ -> false


(* TODO: check about largs *)
let rec inline_label_labels_and_body ~to_inline ~to_keep body = 
  match to_inline with
  | [] -> 
     (to_keep, body)
  | l :: to_inline' ->
     let to_inline' = 
       List.map (fun (lname, arg_syms, lbody) -> 
           (lname, arg_syms, rewrite_expr l lbody)
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
  | Mi_Proc (loc, rbt, arg_bts, body, label_defs) -> 
     let to_keep, to_inline = 
       Pmap.fold (fun label def (to_keep, to_inline) ->
           match def with
           | Mi_Label(_loc, _lt, args, lbody, annot) when should_be_inlined annot ->
              to_keep, 
              ((label, args, lbody) :: to_inline)
           | Mi_Label _
           | Mi_Return _ -> 
              (Pmap.add label def to_keep), 
              to_inline
         ) 
         label_defs 
         (Pmap.empty Symbol.symbol_compare, [])
     in
     let (label_defs, body) = inline_label_labels_and_body ~to_inline ~to_keep body in
     Mi_Proc (loc, rbt, arg_bts, body, label_defs)
  | d -> d




let rewrite_file file = 
  { file with mi_funs = Pmap.map rewrite_fun_map_decl file.mi_funs }


