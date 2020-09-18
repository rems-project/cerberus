module E = Environment
module IT = IndexTerms
module Loc = Locations
module BT = BaseTypes
module LS = LogicalSorts
open Resultat
open BT
open LS
open TypeErrors
open Local
open Environment


let rec infer_index_term (loc: Loc.t) {local;global} (it: IT.t) : LS.t m = 
  match it with
  | Num _ -> return (Base Int)
  | Bool _ -> return (Base Bool)
  | Add (t,t') | Sub (t,t') | Mul (t,t') | Div (t,t') 
  | Exp (t,t') | Rem_t (t,t') | Rem_f (t,t') 
  | Min (t,t') | Max (t,t') ->
     let* () = check_index_term loc {local;global} (Base Int) t in
     let* () = check_index_term loc {local;global} (Base Int) t' in
     return (Base Int)
  | EQ (t,t') | NE (t,t') | LT (t,t')
  | GT (t,t') | LE (t,t') | GE (t,t') ->
     let* () = check_index_term loc {local;global} (Base Int) t in
     let* () = check_index_term loc {local;global} (Base Int) t' in
     return (Base Bool)
  | Null t ->
     let* () = check_index_term loc {local;global} (Base Loc) t in
     return (Base Bool)
  | And ts | Or ts ->
     let* () = ListM.iterM (check_index_term loc {local;global} (Base Bool)) ts in
     return (Base Bool)
  | Impl (t,t') ->
     let* () = check_index_term loc {local;global} (Base Bool) t in
     let* () = check_index_term loc {local;global} (Base Bool) t' in
     return (Base Bool)
  | Not t ->
     let* () = check_index_term loc {local;global} (Base Bool) t in
     return (Base Bool)
  | ITE (t,t',t'') ->
     let* () = check_index_term loc {local;global} (Base Bool) t in
     let* () = check_index_term loc {local;global} (Base Int) t' in
     let* () = check_index_term loc {local;global} (Base Int) t'' in
     return (Base Int)
  | Tuple its ->
     let* ts = 
       ListM.mapM (fun it -> 
           let* (Base bt) = infer_index_term loc {local;global} it in
           return bt
         ) its in
     return (Base (BT.Tuple ts))
  | Nth (bt, n, it') ->
     let* t = check_index_term loc {local;global} (Base bt) it' in
     begin match bt with
     | Tuple ts ->
        begin match List.nth_opt ts n with
        | Some t -> return (Base t)
        | None -> fail loc (Illtyped_it it)
        end
     | _ -> fail loc (Illtyped_it it)
     end
  | Member (tag, it', member) ->
     let* () = check_index_term loc {local;global} (Base (Struct tag)) it' in
     let* decl = Global.get_struct_decl loc global.struct_decls tag in
     let* bt = Tools.assoc_err loc member decl.raw (Illtyped_it it) in
     return (Base bt)
  | MemberOffset (tag, it', member) ->
     let* () = check_index_term loc {local;global} (Base (Struct tag)) it' in
     let* decl = Global.get_struct_decl loc global.struct_decls tag in
     let* _ = Tools.assoc_err loc member decl.raw (Illtyped_it it) in
     return (Base Loc)
  | Nil bt -> 
     return (Base bt)
  | Cons (it1,it2) ->
     let* (Base item_bt) = infer_index_term loc {local;global} it1 in
     let* () = check_index_term loc {local;global} (Base (List item_bt)) it2 in
     return (Base (List item_bt))
  | List (its,bt) ->
     let* _ = ListM.mapM (check_index_term loc {local;global} (Base bt)) its in
     return (Base bt)
  | Head it' ->
     let* ls = infer_index_term loc {local;global} it' in
     begin match ls with
     | Base (List bt) -> return (Base bt)
     | _ -> fail loc (Illtyped_it it)
     end
  | Tail it' ->
     let* ls = infer_index_term loc {local;global} it in
     begin match ls with
     | Base (List bt) -> return (Base (List bt))
     | _ -> fail loc (Illtyped_it it)
     end
  | S s ->
     get_l loc s local

and check_index_term loc env (ls: LS.t) (it: IT.t) : unit m = 
  let* ls' = infer_index_term loc env it in
  if LS.equal ls ls' then return ()
  else fail loc (Illtyped_it it)
