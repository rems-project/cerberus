open Annot
type symbol = Symbol.sym

(* copying some types and logic from an earlier version of mucore.ml
   and from the Core module *)

type loc = Cerb_location.t

type bt = Core.core_base_type
type ft = Ctype.ctype * (Symbol.sym * Ctype.ctype) list * bool
type lt = (Symbol.sym option * (Ctype.ctype * Core.pass_by_value_or_pointer)) list

type 'TY mi_label_def = 
  | Mi_Return of loc
  | Mi_Label of loc * lt * ((symbol * bt) list) * 'TY Core.expr * annot list

type 'TY mi_label_defs = (symbol, ('TY mi_label_def)) Pmap.map

type 'TY mi_fun_map_decl =
  | Mi_Fun of bt * (symbol * bt) list * Core.pexpr
  | Mi_Proc of Cerb_location.t * int option * bt * (symbol * bt) list * 'TY Core.expr * 'TY mi_label_defs
  | Mi_ProcDecl of Cerb_location.t * bt * bt list
  | Mi_BuiltinDecl of Cerb_location.t * bt * bt list

type 'TY mi_fun_map = (symbol, ('TY mi_fun_map_decl)) Pmap.map


type mi_funinfo = (Symbol.sym, (Cerb_location.t * Annot.attributes * Ctype.ctype * (Symbol.sym option * Ctype.ctype) list * bool * bool)) Pmap.map

(* a Core file is just a set of named functions *)
type ('a, 'TY) mi_file = {
  mi_main    : symbol option;
  mi_tagDefs : Core.core_tag_definitions;
  mi_stdlib  : 'TY mi_fun_map;
  mi_impl    : 'TY Core.generic_impl;
  mi_globs   : (Symbol.sym * ('a, 'TY) Core.generic_globs) list;
  mi_funs    : 'TY mi_fun_map;
  mi_extern  : Core.extern_map;
  mi_funinfo :  mi_funinfo;
  mi_loop_attributes : Annot.loop_attributes;
  mi_visible_objects_env : Core.visible_objects_env;
}






let rec remove_save expr =
  let open Core in
  let (Expr (annots, expr_)) = expr in
  let wrap e_ = Expr (annots, e_) in
  match expr_ with
  | Epure _ -> expr
  | Ememop _ -> expr
  | Eaction _ -> expr
  | Ecase (pe, cases) -> 
     let cases = 
       List.map (fun (pat, e) ->
           (pat, remove_save e)
         ) cases
     in
     wrap (Ecase (pe, cases))
  | Elet (pat, pe, body) ->
     wrap (Elet (pat, pe, remove_save body))
  | Eif (pe, e1, e2) ->
     wrap (Eif (pe, remove_save e1, remove_save e2))
  | Eccall _ -> expr
  | Eproc _ -> expr
  | Eunseq es -> 
     wrap (Eunseq (List.map remove_save es))
  | Ewseq (pat, e1, e2) ->
     wrap (Ewseq (pat, remove_save e1, remove_save e2))
  | Esseq (pat, e1, e2) ->
     wrap (Esseq (pat, remove_save e1, remove_save e2))
  | Ebound e -> 
     wrap (Ebound (remove_save e))
  | Esave ((sym, cbt), args, body) ->
     (* have to check *)
     let args = List.map (fun (_, (_, pe)) -> pe) args in
     wrap (Erun ((), sym, args))
  | Erun _ -> expr
  | Epar es -> wrap (Epar (List.map remove_save es))
  | Ewait _ -> expr
  | Eannot (fps, e) -> wrap (Eannot (fps, remove_save e))
  | Eexcluded _ -> expr
  | End es ->
      wrap (End (List.map remove_save es))


let core_to_micore__funmap_decl update_loc = function
  | Core.Fun (bt, args, pe) -> Mi_Fun (bt, args, pe)
  | Core.ProcDecl (loc, bt, bts) -> Mi_ProcDecl (loc, bt, bts)
  | Core.BuiltinDecl (loc, bt, bts) -> Mi_BuiltinDecl (loc, bt, bts)
  | Core.Proc (loc, mrk, bt, args, e) ->
     let saves =
       Pmap.map (fun (_,params,body,annots) ->
           let param_tys = 
             (List.map (fun (sym1,(((_,mctb),_))) -> 
                  (match mctb with
                   | Some (ct1,b) -> (Some sym1, (ct1,b))
                   | None -> 
                      Cerb_debug.error "core_to_micore: label without c-type argument annotation"
                  )
                ) params) 
           in
           let params = List.map (fun (sym, (((bt, _), _))) -> (sym,bt)) params in
           let lloc = (Annot.get_loc_ annots) in
           if is_return annots
           then 
             (* bogus: *)
             (* let () =  *)
             (*   if not (List.equal Core.eq_core_base_type (List.map snd args) (List.map snd params)) then *)
             (*     let open Cerb_pp_prelude.P in *)
             (*     let err =  *)
             (*       string *)
             (*       string "mismatch:" ^^ space ^^ *)
             (*       Pp_core.Basic.pp_params args ^^ space ^^ *)
             (*       string "vs" ^^ space ^^ *)
             (*       Pp_core.Basic.pp_params params *)
             (*     in *)
             (*     Cerb_debug.error (Pp_utils.to_plain_pretty_string err) *)
             (* in *)
             Mi_Return (lloc(* , param_tys *))
           else Mi_Label (lloc, param_tys, params, remove_save body, annots)
         ) (Core_aux.m_collect_saves e)
     in
     Mi_Proc(loc, mrk, bt, args, remove_save e, saves)




let core_to_micore__funmap update_loc funmap =
  Pmap.map (core_to_micore__funmap_decl update_loc) funmap


let core_to_micore__file update_loc (file : ('a, 'TY) Core.generic_file) : ('a, 'TY) mi_file =
  {
    mi_main = file.main;
    mi_tagDefs = file.tagDefs;
    mi_stdlib = core_to_micore__funmap update_loc file.stdlib;
    mi_impl = file.impl;
    mi_globs = file.globs;
    mi_funs = core_to_micore__funmap update_loc file.funs;
    mi_extern = file.extern;
    mi_funinfo = file.funinfo;
    mi_loop_attributes = file.loop_attributes0;
    mi_visible_objects_env = file.visible_objects_env;
  }
