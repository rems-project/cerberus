open Lem_pervasives
open Ctype
open Lem_assert_extra

open Core
open Annot

open Mucore
module Mu = Core_anormalise.Mu
open Mu


let rec ib_expr 
          (label : symbol * symbol list * unit mu_expr)
          (e : unit mu_expr) 
           : unit mu_expr=
  let (M_Expr(loc, oannots, e_)) = e in
  let wrap e_= M_Expr(loc, oannots, e_) in
  let aux = (ib_expr label) in
  match e_ with
  | M_Epure _ -> wrap e_
  | M_Ememop _ -> wrap e_
  | M_Eaction _ -> wrap e_
  | M_Ecase( asym2, pats_es) ->
     let pats_es = 
       (Lem_list.map (fun (pat,e) -> 
           (pat, aux e)
         ) pats_es)
     in
     wrap (M_Ecase( asym2, pats_es))
 | M_Elet( sym_or_pat, pe, e) ->
    wrap (M_Elet( sym_or_pat, pe, (aux e)))
 | M_Eif( asym2, e1, e2) ->
    let e1 = (aux e1) in
    let e2 = (aux e2) in
    wrap (M_Eif( asym2, e1, e2))
 | M_Eskip -> wrap e_
 | M_Eccall( _, _, _) -> wrap e_
 | M_Eproc( _, _) -> wrap e_
 | M_Ewseq( pat, e1, e2) -> 
    let e1 = (aux e1) in
    let e2 = (aux e2) in
    wrap (M_Ewseq( pat, e1, e2))
 | M_Esseq( pat, e1, e2) ->
    let e1 = (aux e1) in
    let e2 = (aux e2) in
    wrap (M_Esseq( pat, e1, e2))
 | M_Ebound( n, e) ->
    let e = (aux e) in
    wrap (M_Ebound( n, e))
 | M_End es ->
    let es = (map aux es) in
    wrap (M_End es)
 | M_Erun(l, args) -> 
    let (label_sym, label_arg_syms, label_body) = label in
    if not (Symbol.symbolEquality l label_sym) then e
    else if not ((List.length label_arg_syms) = (List.length args)) then
      failwith "M_Erun supplied wrong number of arguments"
    else
      let () = (Debug_ocaml.print_debug 1 [] (fun () -> ("REPLACING LABEL " ^ (let Symbol.Symbol( d, n, str_opt) = l in
    "Symbol" ^ (stringFromPair string_of_int (fun x_opt->stringFromMaybe (fun s->"\"" ^ (s ^ "\"")) x_opt) (n, str_opt)))))) in
      let arguments = (Lem_list.list_combine label_arg_syms args) in
      let (M_Expr(_, annots2, e_)) = 
        (List.fold_right (fun (spec_arg, (asym : 'TY asym)) body ->
            let pe = M_Pexpr (asym.loc, asym.annot, asym.type_annot, M_PEsym asym.sym) in
            M_Expr(loc, [], (M_Elet (M_Symbol spec_arg, pe, body)))
          ) arguments label_body)
      in
      (* this combines annotations *)
      M_Expr(loc, annots2 @ oannots, e_)

    


let rec inline_label_labels_and_body to_inline to_keep body = 
   ((match to_inline with
  | [] -> (to_keep, body)
  | l :: to_inline' ->
     let to_inline' = 
       (map (fun (lname,arg_syms,lbody) -> 
           (lname,arg_syms,ib_expr l lbody)
         ) to_inline')
     in
     let to_keep' = 
       (Pmap.map (fun def -> (match def with
         | M_Return _ -> def
         | M_Label(loc, lt, args, lbody, annot, mapping) -> 
            M_Label(loc, lt, args, (ib_expr l lbody), annot, mapping)
         )) to_keep)
     in
     let body' = (ib_expr l body) in
     inline_label_labels_and_body to_inline' to_keep' body'
  ))


let ib_fun_map_decl 
      (name1: symbol)
      (d : unit mu_fun_map_decl) 
    : unit mu_fun_map_decl=
   (try ((match d with
     | M_Proc( loc, rbt, arg_bts, body, label_defs, mapping) -> 
        let (to_keep, to_inline) =
          (let aux label def (to_keep, to_inline)=
             ((match def with
            | M_Return _ -> (Pmap.add label def to_keep, to_inline)
            | M_Label(_loc, lt1, args, lbody, annot2, _) ->
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
        M_Proc( loc, rbt, arg_bts, body, label_defs, mapping)
     | _ -> d
     )) with | Failure error -> failwith ( (let Symbol.Symbol( d, n, str_opt) = name1 in
    "Symbol" ^ (stringFromPair string_of_int (fun x_opt->stringFromMaybe (fun s->"\"" ^ (s ^ "\"")) x_opt) (n, str_opt)))  ^ error) )

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

