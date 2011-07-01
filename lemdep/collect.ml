module A = Ast

let collect_id (Id ()) l =

let collect_def_aux d l =
  match d with
  | A.Type_def (_, (td, _) list)
  | A.Val_def (val_def)
  | A.Module (_, x_l, _, _, defs, _)
  | A.Rename (_, x_l, _, id)
  | A.Open (_, id) -> collect_id id l
  | A.Indreln (_, targets option, (rule, _) list)
  | A.Spec_def (val_spec)
  | A.Subst (_, _, target, _, v_l, (v_l) list, _, exp)
  | A.Class (_, _, x_l, a_l, _, ((_, v_l, _, typ, l)) list, _)
  | A.Instance (_, instschm, ((val_def, l)) list, _A.Tydef)

and collect_def (A.Def_l (d, _)) l = collect_def_aux d l

and collect_defs (A.Defs defs) =
  List.fold_left (fun (d, _, _) l -> collect_def d l) defs []
