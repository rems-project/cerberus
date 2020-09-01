module E = Environment
module IT = IndexTerms
module Loc = Locations
module BT = BaseTypes
module LS = LogicalSorts
open Result
open BT
open LS
open TypeErrors
open Local


let rec infer_index_term (loc: Loc.t) (env: E.t) (it: IT.t) : LS.t m = 
  match it with
  | Num _ -> return (Base Int)
  | Bool _ -> return (Base Bool)
  | Add (t,t') | Sub (t,t') | Mul (t,t') | Div (t,t') 
  | Exp (t,t') | Rem_t (t,t') | Rem_f (t,t')  ->
     let* () = check_index_term loc env (Base Int) t in
     let* () = check_index_term loc env (Base Int) t' in
     return (Base Int)
  | EQ (t,t') | NE (t,t') | LT (t,t')
  | GT (t,t') | LE (t,t') | GE (t,t') ->
     let* () = check_index_term loc env (Base Int) t in
     let* () = check_index_term loc env (Base Int) t' in
     return (Base Bool)
  | Null t ->
     let* () = check_index_term loc env (Base Loc) t in
     return (Base Bool)
  | And ts | Or ts ->
     let* () = ListM.iterM (check_index_term loc env (Base Bool)) ts in
     return (Base Bool)
  | Impl (t,t') ->
     let* () = check_index_term loc env (Base Bool) t in
     let* () = check_index_term loc env (Base Bool) t' in
     return (Base Bool)
  | Not t ->
     let* () = check_index_term loc env (Base Bool) t in
     return (Base Bool)
  | Tuple its ->
     let* ts = 
       ListM.mapM (fun it -> 
           let* (Base bt) = infer_index_term loc env it in
           return bt
         ) its in
     return (Base (BT.Tuple ts))
  | Nth (n,it') ->
     let* t = infer_index_term loc env it' in
     begin match t with
     | Base (Tuple ts) ->
        begin match List.nth_opt ts n with
        | Some t -> return (Base t)
        | None -> fail loc (Illtyped_it it)
        end
     | _ -> fail loc (Illtyped_it it)
     end
  | Member (tag, it', member) ->
     let* () = check_index_term loc env (Base (Struct tag)) it' in
     let* decl = Global.get_struct_decl loc env.global.struct_decls tag in
     let* bt = Tools.assoc_err loc member decl.raw (Illtyped_it it) in
     return (Base bt)
  | MemberOffset (tag, it', member) ->
     let* () = check_index_term loc env (Base (Struct tag)) it' in
     let* decl = Global.get_struct_decl loc env.global.struct_decls tag in
     let* _ = Tools.assoc_err loc member decl.raw (Illtyped_it it) in
     return (Base Loc)
  | Nil bt -> 
     return (Base bt)
  | Cons (it1,it2) ->
     let* (Base item_bt) = infer_index_term loc env it1 in
     let* () = check_index_term loc env (Base (List item_bt)) it2 in
     return (Base (List item_bt))
  | List (its,bt) ->
     let* _ = ListM.mapM (check_index_term loc env (Base bt)) its in
     return (Base bt)
  | Head it' ->
     let* ls = infer_index_term loc env it' in
     begin match ls with
     | Base (List bt) -> return (Base bt)
     | _ -> fail loc (Illtyped_it it)
     end
  | Tail it' ->
     let* ls = infer_index_term loc env it in
     begin match ls with
     | Base (List bt) -> return (Base (List bt))
     | _ -> fail loc (Illtyped_it it)
     end
  | S s ->
     get_l loc env.local s

and check_index_term loc env (ls: LS.t) (it: IT.t) : unit m = 
  let* ls' = infer_index_term loc env it in
  if LS.equal ls ls' then return ()
  else fail loc (Illtyped_it it)
