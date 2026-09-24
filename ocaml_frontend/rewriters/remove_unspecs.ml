open Core_rewriter
open Core


module RW = Rewriter(Identity_monad)




let rec contains_unspec (Pattern (annots, pattern_)) = 
  match pattern_ with
  | CaseBase _ -> false
  | CaseDtor (Dunspecified, pats) -> true
  | CaseDtor (_, pats) -> List.exists contains_unspec pats

let rec always_matches (Pattern (_, pat_)) =
  match pat_ with
  | CaseBase _ -> true
  | CaseDtor (Dspecified, [pat']) -> always_matches pat'
  | CaseDtor (Dtuple, pats) -> List.for_all always_matches pats
  | _ -> false

let rec cleanup_cases = function
  | [] -> []
  | (pat, e) :: cases when always_matches pat -> [(pat, e)]
  | (pat, e) :: cases when contains_unspec pat -> cleanup_cases cases
  | (pat, e) :: cases -> (pat, e) :: cleanup_cases cases




let rewriter : RW.rewriter =
  let open RW in {
    rw_pexpr=
      RW.RW begin fun _ _ ->
        DoChildrenPost begin fun (Pexpr (annots, bTy, pexpr_) as pexpr) ->
          match pexpr_ with
            | PEcase (pe, xs) ->
                begin match cleanup_cases xs with
                | [] -> assert false
                | [(pat,pe2)] -> Pexpr (annots, bTy, PElet (pat, pe, pe2))
                | xs' -> Pexpr (annots, bTy, PEcase (pe, xs'))
                end
            | PElet (pat, pe1, pe2) ->
               assert (not (contains_unspec pat));
               pexpr
            | _ ->
                pexpr
        end
      end;
    rw_action=
      RW.RW begin fun _ act ->
        Traverse
      end;
    
    rw_expr=
      RW.(RW begin fun _ _ ->
        DoChildrenPost begin fun (Expr (annots, expr_) as expr) ->
          match expr_ with
            | Ecase (pe, xs) ->
                begin match cleanup_cases xs with
                | [] -> assert false
                | [(pat, e2)] -> Expr (annots, Elet (pat, pe, e2))
                | xs' -> Expr (annots, Ecase (pe, xs'))
                end
            | Elet (pat, _, _)
            | Ewseq (pat, _, _)
            | Esseq (pat, _, _) ->
               assert (not (contains_unspec pat));
               expr
            | _ ->
                expr
        end
      end)
   }

let rewrite_pexpr pexpr =
    Identity_monad.unwrap RW.(rewritePexpr rewriter pexpr)

let rewrite_expr expr =
  Identity_monad.unwrap RW.(rewriteExpr rewriter expr)

let rewrite_file file =
  let rewrite_impl_decl = function
    | Def (bTy, pe) ->
        Def (bTy, rewrite_pexpr pe)
    | IFun (bTy, args, pe) ->
        IFun (bTy, args, rewrite_pexpr pe) in
  
  let rewrite_fun_map_decl = function
    | Fun (bTy, args, pe) ->
        Fun (bTy, args, rewrite_pexpr pe)
    | Proc (loc, mrk, bTy, args, e) ->
        Proc (loc, mrk, bTy, args, rewrite_expr e)
    | decl ->
        decl in
  
  let rewrite_globs = function
    | GlobalDef (bTy, e) ->
        GlobalDef (bTy, rewrite_expr e)
    | decl ->
        decl in
  
  { main = file.main
  ; calling_convention = file.calling_convention
  ; tagDefs = file.tagDefs
  ; stdlib = Pmap.map rewrite_fun_map_decl file.stdlib
  ; impl = Pmap.map rewrite_impl_decl file.impl
  ; globs = List.map (fun (sym, glob) -> (sym, rewrite_globs glob)) file.globs
  ; funs = Pmap.map rewrite_fun_map_decl file.funs
  ; extern = file.extern
  ; funinfo = file.funinfo 
  ; loop_attributes0 = file.loop_attributes0
  ; visible_objects_env = file.visible_objects_env
  }
