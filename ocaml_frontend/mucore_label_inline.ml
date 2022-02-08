open Lem_pervasives
open Ctype
open Lem_assert_extra

open Core
open Annot

open Mucore
module Mu = Core_anormalise.Mu
open Mu




let rec ib_texpr label e = 

  let (M_TExpr(loc, oannots, e_)) = e in
  let wrap e_= M_TExpr(loc, oannots, e_) in
  let taux = ib_texpr label in
  match e_ with
  | M_Ecase( asym2, pats_es) ->
     let pats_es = 
       (Lem_list.map (fun (pat,e) -> 
            (pat, taux e)
          ) pats_es)
     in
     wrap (M_Ecase( asym2, pats_es))
  | M_Elet( sym_or_pat, pe, e) ->
     wrap (M_Elet( sym_or_pat, pe, (taux e)))
  | M_Eif( asym2, e1, e2) ->
     wrap (M_Eif( asym2, taux e1, taux e2))
  | M_Ewseq( pat, e1, e2) -> 
     wrap (M_Ewseq( pat, e1, taux e2))
  | M_Esseq( pat, e1, e2) ->
     wrap (M_Esseq( pat, e1, taux e2))
  | M_Ebound( n, e) ->
     wrap (M_Ebound( n, taux e))
  | M_End es ->
     wrap (M_End (map taux es))
  | M_Edone asym ->
     wrap (M_Edone asym)
  | M_Eundef (uloc, undef) ->
     wrap (M_Eundef (uloc, undef))
  | M_Erun(l, args) -> 
     let (label_sym, label_arg_syms, label_body) = label in
     if not (Symbol.symbolEquality l label_sym) then 
       e
     else if not ((List.length label_arg_syms) = (List.length args)) then
       failwith "M_Erun supplied wrong number of arguments"
     else
       let () = 
         Debug_ocaml.print_debug 1 [] 
           (fun () -> ("REPLACING LABEL " ^ Symbol.show_symbol l))
       in
       let arguments = (Lem_list.list_combine label_arg_syms args) in
       let (M_TExpr(_, annots2, e_)) = 
         (List.fold_right (fun (spec_arg, (asym : 'TY asym)) body ->
              if Symbol.symbolEquality asym.sym spec_arg then
                body
              else
                let pe = M_Pexpr (asym.loc, asym.annot, asym.type_annot, M_PEsym asym.sym) in
                M_TExpr(loc, [], (M_Elet (M_Symbol spec_arg, pe, body)))
            ) arguments label_body)
       in
       (* this combines annotations *)
       M_TExpr (loc, annots2 @ oannots, e_)


    


let rec inline_label_labels_and_body to_inline to_keep body = 
   ((match to_inline with
  | [] -> (to_keep, body)
  | l :: to_inline' ->
     let to_inline' = 
       (map (fun (lname,arg_syms,lbody) -> 
           (lname,arg_syms,ib_texpr l lbody)
         ) to_inline')
     in
     let to_keep' = 
       (Pmap.map (fun def -> (match def with
         | M_Return _ -> def
         | M_Label(loc, lt, args, lbody, annot) -> 
            M_Label(loc, lt, args, (ib_texpr l lbody), annot)
         )) to_keep)
     in
     let body' = (ib_texpr l body) in
     inline_label_labels_and_body to_inline' to_keep' body'
  ))


let ib_fun_map_decl 
      (name1: symbol)
      (d : unit mu_fun_map_decl) 
    : unit mu_fun_map_decl=
   (try ((match d with
     | M_Proc( loc, rbt, arg_bts, body, label_defs) -> 
        let (to_keep, to_inline) =
          (let aux label def (to_keep, to_inline)=
             ((match def with
            | M_Return _ -> (Pmap.add label def to_keep, to_inline)
            | M_Label(_loc, lt1, args, lbody, annot2) ->
               match get_label_annot annot2 with
               | Some (LAloop_break _)
               | Some (LAloop_continue _) 
                 -> 
                  (to_keep, ((label, map fst args, lbody) :: to_inline))
               | _ -> 
                  (Pmap.add label def to_keep, to_inline)
            )) 
          in
          Pmap.fold aux label_defs ((Pmap.empty Symbol.symbol_compare), []))
        in
        let (label_defs, body) = 
          (inline_label_labels_and_body to_inline to_keep body)
        in
        M_Proc( loc, rbt, arg_bts, body, label_defs)
     | _ -> d
     )) with | Failure error -> failwith (Symbol.show_symbol name1 ^ ": "  ^ error) )

let ib_fun_map (fmap1 : unit mu_fun_map) : unit mu_fun_map = 
   (Pmap.mapi ib_fun_map_decl fmap1)
  

let ib_globs (g : unit mu_globs) 
    : unit mu_globs= 
   ((match g with
  | M_GlobalDef(s, bt1, e) -> M_GlobalDef(s, bt1, e)
  | M_GlobalDecl (s, bt1) -> M_GlobalDecl (s, bt1)
  ))

let ib_globs_list (gs : unit mu_globs_list)
    : unit mu_globs_list= 
   (map (fun (sym1,g) -> (sym1, ib_globs g)) gs)


let ib_file file1 = 
   ({ file1 with mu_stdlib = (ib_fun_map file1.mu_stdlib)
             ; mu_globs = (ib_globs_list file1.mu_globs)
             ; mu_funs = (ib_fun_map file1.mu_funs)
  })

