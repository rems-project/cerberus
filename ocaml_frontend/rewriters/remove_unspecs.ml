open Core_rewriter
open Core


module Identity = struct
  type 'a t = 'a
  let return = fun z -> z
  let bind m f = f m
  let (>>=) = bind
  let mapM = List.map
  let foldlM f xs init =
    List.fold_left (fun acc x ->
      f x acc
    ) init xs
  
  let unwrap (x: 'a t) : 'a = x
end

module RW = Rewriter(Identity)


let rec always_matches (Pattern (_, pat_)) =
  match pat_ with
    | CaseBase _ ->
        `ALWAYS
    | CaseCtor (Cspecified, [pat']) ->
        always_matches pat'
    | CaseCtor(Cunspecified, _) ->
        `NEVER
    | CaseCtor (Ctuple, pats) ->
        List.fold_left (fun acc pat' ->
          match acc, always_matches pat' with
            | `ALWAYS, `ALWAYS ->
                `ALWAYS
            | `NEVER, _
            | _, `NEVER ->
                `NEVER
            | _ ->
                `UNKNOWN
        ) `ALWAYS pats
    | _ ->
        `UNKNOWN

let rec select_case = function
  | [] ->
      None
  | (pat, z) :: xs ->
      begin match always_matches pat with
        | `ALWAYS ->
            Some (pat, z)
        | `NEVER ->
            select_case xs
        | `UNKNOWN ->
            None
      end

let rewriter : 'bty RW.rewriter =
  let open RW in {
    rw_pexpr=
      RW.RW begin fun _ ->
        DoChildrenPost begin fun (Pexpr (annots, bTy, pexpr_) as pexpr) ->
          match pexpr_ with
            | PEcase (pe, xs) ->
                begin match select_case xs with
                  | None ->
                      pexpr
                  | Some (pat, pe2) ->
                      Pexpr (annots, bTy, PElet (pat, pe, pe2))
                end
            | _ ->
                pexpr
        end
      end;
    rw_action=
      RW.RW begin fun act ->
        Traverse
      end;
    
    rw_expr=
      RW.(RW begin fun _ ->
        DoChildrenPost begin fun (Expr (annots, expr_) as expr) ->
          match expr_ with
            | Ecase (pe, xs) ->
                begin match select_case xs with
                  | None ->
                      expr
                  | Some (pat, e2) ->
                      Expr (annots, Elet (pat, pe, e2))
                end
            | _ ->
                expr
        end
      end)
   }

let rewrite_pexpr pexpr =
    Identity.unwrap RW.(rewritePexpr rewriter pexpr)

let rewrite_expr expr =
  Identity.unwrap RW.(rewriteExpr rewriter expr)

let rewrite_file file =
  let rewrite_impl_decl = function
    | Def (bTy, pe) ->
        Def (bTy, rewrite_pexpr pe)
    | IFun (bTy, args, pe) ->
        IFun (bTy, args, rewrite_pexpr pe) in
  
  let rewrite_fun_map_decl = function
    | Fun (bTy, args, pe) ->
        Fun (bTy, args, rewrite_pexpr pe)
    | Proc (loc, bTy, args, e) ->
        Proc (loc, bTy, args, rewrite_expr e)
    | decl ->
        decl in
  
  let rewrite_globs = function
    | GlobalDef (bTy, e) ->
        GlobalDef (bTy, rewrite_expr e)
    | decl ->
        decl in
  
  { main = file.main
  ; tagDefs = file.tagDefs
  ; stdlib = Pmap.map rewrite_fun_map_decl file.stdlib
  ; impl = Pmap.map rewrite_impl_decl file.impl
  ; globs = List.map (fun (sym, glob) -> (sym, rewrite_globs glob)) file.globs
  ; funs = Pmap.map rewrite_fun_map_decl file.funs
  ; extern = file.extern
  ; funinfo = file.funinfo 
  ; loop_attributes0 = file.loop_attributes0
  }
