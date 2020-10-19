open Resultat
open TypeErrors
open Pp

open Rc_annot
module LC = LogicalConstraints
module LS = LogicalSorts
module RE = Resources
module BT = BaseTypes
module RT = ReturnTypes
module FT = ArgumentTypes.Make(ReturnTypes)
module LT = ArgumentTypes.Make(False)

module StringMap = Map.Make(String)

open Conversions




let pp_list pp_item xs = 
  brackets (Pp.separate_map (semi ^^ space) pp_item xs)

let pp_tuple pped = parens (separate (comma ^^ space) pped)

let pp_pattern = pp_list (Pp.string)

let pp_option pp_item = function
  | Some x -> parens (!^"Some" ^^^ pp_item x)
  | None -> !^"None"

let pp_quot_elt pp_elt = function
  | Quot_plain s -> parens (!^"Quot_plain" ^^^ parens !^s)
  | Quot_anti a -> pp_elt a

let pp_quoted pp_elt = pp_list (pp_quot_elt pp_elt)

let rec pp_coq_term coq_term = pp_quoted pp_type_expr coq_term
and pp_iris_term iris_term = pp_quoted pp_type_expr iris_term

and pp_coq_expr coq_expr = 
  parens 
    begin match coq_expr with
    | Coq_ident s -> !^"Coq_ident" ^^^ !^s
    | Coq_all coq_term -> !^"Coq_all" ^^^ pp_coq_term coq_term
    end

and pp_constr constr =
  parens
    begin match constr with
    | Constr_Iris iris_term -> 
       !^"Constr_Iris" ^^^ pp_iris_term iris_term
    | Constr_exist (string,o_coq_expr,constr) ->
       !^"Constr_exist" ^^^ 
         pp_tuple [!^string;
                   pp_option pp_coq_expr o_coq_expr;
                   pp_constr constr]
    | Constr_own (string,ptr_kind,type_expr) ->
       !^"Constr_own" ^^^
         pp_tuple [!^string;
                   pp_ptr_kind ptr_kind;
                   pp_type_expr type_expr]
    | Constr_Coq coq_expr ->
       !^"Constr_Coq" ^^^ pp_coq_expr coq_expr
    end

and pp_ptr_kind = function
  | Own -> !^"Own"
  | Shr -> !^"Shr"
  | Frac coq_expr -> parens (!^"Frac" ^^^ pp_coq_expr coq_expr)

and pp_type_expr type_expr = 
  parens
    begin match type_expr with
    | Ty_refine (coq_expr,type_expr) ->
       !^"Ty_refine" ^^^
         pp_tuple [pp_coq_expr coq_expr; pp_type_expr type_expr]
    | Ty_ptr (ptr_kind, type_expr) ->
       !^"Ty_ptr" ^^^ 
         pp_tuple [pp_ptr_kind ptr_kind; 
                   pp_type_expr type_expr]
    | Ty_dots ->
       !^"Ty_dots"
    | Ty_exists (pattern,o_coq_expr,type_expr) ->
       !^"Ty_exists" ^^^
         pp_tuple [pp_pattern pattern; 
                   pp_option pp_coq_expr o_coq_expr;
                   pp_type_expr type_expr]
    | Ty_constr (type_expr, constr) ->
       !^"Ty_constr" ^^^
         pp_tuple [pp_type_expr type_expr; 
                   pp_constr constr]
    | Ty_params (ident,type_expr_args) ->
       !^"Ty_params" ^^^
         pp_tuple [!^ident;
                   pp_list pp_type_expr_arg type_expr_args]
    | Ty_Coq coq_expr ->
       !^"Ty_Coq" ^^^ pp_coq_expr coq_expr
    end

and pp_type_expr_arg type_expr_arg = 
  parens
    begin match type_expr_arg with
    | Ty_arg_expr type_expr ->
       !^"Ty_arg_expr" ^^^ pp_type_expr type_expr
    | Ty_arg_lambda (pattern, o_coq_expr, type_expr_arg) ->
       !^"Ty_arg_lambda" ^^^
         pp_tuple [pp_pattern pattern;
                   pp_option pp_coq_expr o_coq_expr;
                   pp_type_expr_arg type_expr_arg]
    end










let get_name loc names ident : Sym.t m = 
  match StringMap.find_opt ident names with
  | Some sym -> return sym
  | None -> fail loc (Generic !^("unknown name " ^ ident))

let parse_it loc names s context_pp : IT.t m = 
  match IndexTermParser.parse loc names s with
  | Ok r -> return r
  | Error (loc,msg) -> 
     let err = 
       !^"cannot process coq term" ^^^ 
         parens (!^"returned" ^^^ squotes !^msg) ^^ colon ^/^ 
           (Lazy.force context_pp)
     in
     fail loc (Unsupported err)

let cannot_process loc pp_f to_pp = 
  fail loc (Unsupported (!^"cannot process term:" ^/^ pp_f to_pp))




let bytes_of_integer_type_expr loc te =
  match te with
  | Ty_Coq (Coq_ident "u32") -> return (Z.of_int 4)
  | Ty_params ("u32", []) -> return (Z.of_int 4)
  | Ty_Coq (Coq_ident "i32") -> return (Z.of_int 4)
  | Ty_params ("i32", []) -> return (Z.of_int 4)
  | _ -> cannot_process loc pp_type_expr te

let bits_of_integer_type_expr loc te = 
  match te with
  | Ty_Coq (Coq_ident "u32") -> return 32
  | Ty_params ("u32", []) -> return 32
  | Ty_Coq (Coq_ident "i32") -> return 32
  | Ty_params ("i32", []) -> return 32
  | _ -> cannot_process loc pp_type_expr te

let sign_of_integer_type_expr loc te = 
  match te with
  | Ty_Coq (Coq_ident "u32") -> return `Unsigned
  | Ty_params ("u32", []) -> return `Unsigned
  | Ty_Coq (Coq_ident "i32") -> return `Signed
  | Ty_params ("i32", []) -> return `Signed
  | _ -> cannot_process loc pp_type_expr te


let maybe_refinement = function
  | Ty_refine (coq_expr,type_expr) -> (Some coq_expr, type_expr)
  | te -> (None, te)


type bnew = New | Old

type tb =
  | B of (bnew * Sym.t * BT.t * RE.size option) * RT.l

let rec of_coq_expr_typ loc names coq_expr name =
  match coq_expr with
  | Coq_ident ident ->
     begin match ident with
     | "Z" -> 
        return (BT.Integer, None, RT.I)
     | "nat" -> 
        let c = LC.LC (IT.GE (S name, Num Z.zero)) in
        return (BT.Integer, None, RT.Constraint (c, I))
     | "loc" -> 
        return (BT.Loc, None, RT.I)
     | _ -> 
        cannot_process loc pp_coq_expr coq_expr
     end
  | Coq_all coq_term -> 
     begin match coq_term with
     | [Quot_plain "Z"] -> 
        return (BT.Integer, None, RT.I)
     | [Quot_plain "nat"] -> 
        let c = LC.LC (IT.GE (S name, Num Z.zero)) in
        return (BT.Integer, None, RT.Constraint (c, I))
     | _ -> 
        cannot_process loc pp_coq_expr coq_expr
     end

and of_coq_term loc names coq_term =
  match coq_term with
  | [Quot_plain s] -> parse_it loc names s (lazy (pp_coq_term coq_term))
  | _ -> cannot_process loc pp_coq_term coq_term

and of_coq_expr loc names coq_expr = 
  match coq_expr with
  | Coq_ident ident -> 
     let* sym = get_name loc names ident in
     return (IT.S sym)
  | Coq_all coq_term -> 
     of_coq_term loc names coq_term


and of_constr loc names constr : RT.l m =
  let open RT in
  match constr with
  | Constr_Iris _ ->
     fail loc (Unsupported !^"Constr_Iris")
  | Constr_exist _ ->
     fail loc (Unsupported !^"Constr_exist")
  | Constr_own (ident,ptr_kind,type_expr) ->
     let* name = get_name loc names ident in
     let impl = CF.Ocaml_implementation.get () in
     let* psize = match impl.sizeof_pointer with
       | Some n -> return (Some (Z.of_int n))
       | None -> fail loc (Generic !^"sizeof_pointer returned None")
     in
     begin match ptr_kind, is_uninit_type_expr type_expr with
       | Own, Some integer_type_expr -> 
          let* size = bytes_of_integer_type_expr loc integer_type_expr in
          let r = RE.Uninit {pointer = S name; size} in
          return (Resource (r, I))
       | Own, None -> 
          let* B ((bnew, pointee, bt, osize), lrt) = 
            of_type_expr loc names type_expr in
          let* points = match osize with
            | Some size -> return (RE.Points {pointer = S name; pointee; size})
            | None -> fail loc (Generic !^"pointer to non-object")
          in
          let lrt = match bnew with
            | New -> Logical ((pointee, LS.Base bt), Resource (points, I)) 
            | Old -> Resource (points, I)
          in
          return lrt
       | Shr, _ -> 
          fail loc (Generic !^"Shared pointers not supported yet")
       | Frac _, _ -> 
          fail loc (Generic !^"Fractional pointers not supported yet")
     end
  | Constr_Coq coq_expr ->
     let* it = of_coq_expr loc names coq_expr in
     let c = LC.LC it in
     return (RT.Constraint (c, I))

and is_uninit_type_expr = function
  | Ty_params ("uninit", [Ty_arg_expr arg]) -> Some arg
  | _ -> None

and of_type_expr loc names te : tb m =
  let open RT in
  let name = Sym.fresh () in
  let (mrefinement, te') = maybe_refinement te in
  match maybe_refinement te' with
  | None, Ty_ptr (ptr_kind, type_expr) ->
     (* from impl_mem *)
     let impl = CF.Ocaml_implementation.get () in
     let* psize = match impl.sizeof_pointer with
       | Some n -> return (Some (Z.of_int n))
       | None -> fail loc (Generic !^"sizeof_pointer returned None")
     in
     begin match ptr_kind, is_uninit_type_expr type_expr with
       | Own, Some integer_type_expr -> 
          let* size = bytes_of_integer_type_expr loc integer_type_expr in
          let r = RE.Uninit {pointer = S name; size} in
          return (B ((New, name, BT.Loc, psize), Resource (r, I)))
       | Own, None -> 
          let* B ((bnew, pointee, bt, osize), lrt) = 
            of_type_expr loc names type_expr in
          let* points = match osize with
            | Some size -> return (RE.Points {pointer = S name; pointee; size})
            | None -> fail loc (Generic !^"pointer to non-object")
          in
          let lrt = match bnew with
            | New -> Logical ((pointee, LS.Base bt), Resource (points, I)) 
            | Old -> Resource (points, I)
          in
          return (B ((New, name, BT.Loc, osize), lrt))
       | Shr, _ -> 
          fail loc (Generic !^"Shared pointers not supported yet")
       | Frac _, _ -> 
          fail loc (Generic !^"Fractional pointers not supported yet")
     end
  | None, Ty_dots ->
     fail loc (Generic !^"Recursive types not supported yet")
  | None, Ty_exists _ ->
     fail loc (Unsupported !^"existential types")
  | None, Ty_constr (type_expr,constr) ->
     let* B ((bnew, pointee, bt, osize), lrt) = 
       of_type_expr loc names type_expr in
     let* lrt' = of_constr loc names constr in
     return (B ((bnew, pointee, bt, osize), lrt @@ lrt'))
  | _, Ty_params ("int",[Ty_arg_expr arg]) ->
     let* size = bytes_of_integer_type_expr loc arg in
     let* sign = sign_of_integer_type_expr loc arg in
     let* bits = bits_of_integer_type_expr loc arg in
     let* constr = 
       let open IT in
       match bits, sign with
       | 32, `Signed -> return (fun s -> (in_range (S s) (int 0) max_u32))
       | 32, `Unsigned -> return (fun s -> (in_range (S s) min_i32 max_i32))
       | _ -> cannot_process loc pp_type_expr te
     in
     begin match mrefinement with
     | None ->
        let lrt = Constraint (LC.LC (constr name), I) in
        return (B ((New, name, BT.Integer, Some size), lrt))
     | Some (Coq_ident ident) ->
        let* s = get_name loc names ident in
        let lrt = Constraint (LC.LC (constr s), I) in
        return (B ((Old, s, BT.Integer, Some size), lrt))
     | Some (Coq_all coq_term) -> 
        let* it = of_coq_term loc names coq_term in
        let lc = LC.LC (IT.EQ (it, S name)) in
        let lrt = Constraint (LC.LC (constr name), Constraint (lc, I)) in
        return (B ((New, name, BT.Integer, Some size), lrt))
     end
  | None, Ty_params ("void", []) ->
     return (B ((New, name, BT.Unit, None), RT.I))
  | None, Ty_Coq coq_expr ->
     let* (bt, osize, lrt) = 
       of_coq_expr_typ loc names coq_expr name in
     return (B ((New, name, bt, osize), lrt))
  | _, _ ->
     cannot_process loc pp_type_expr te'


(* let log_name_add sym = Pp.d 6 (lazy (!^"adding name" ^^^ Sym.pp sym)) *)
let log_name_add sym = ()

let (@@) = RT.(@@)

let make_fun_spec_annot loc struct_decls attrs args ret_ctype = 
  let (annot: function_annot) = function_annot attrs in
  (* in order to to the List.combine below *)
  let* () = 
    let nargs = List.length args in
    let nargs_spec = List.length annot.fa_args in
    if nargs <> nargs_spec 
    then fail loc (Number_arguments {has = nargs; expect = nargs_spec})
    else return ()
  in
  let names = StringMap.empty in
  let* (names, params_lrt) = 
    ListM.fold_leftM (fun (names, acc_lrt) (ident, coq_expr) : (Sym.t StringMap.t * RT.l) m ->
        let s = Sym.fresh_pretty ident in
        let names = StringMap.add ident s names in
        log_name_add s;
        let* (bt,_,lrt) = of_coq_expr_typ loc names coq_expr s in
        return (names, acc_lrt @@ (RT.Logical ((s, LS.Base bt), lrt)))
      ) (names, RT.I) annot.fa_parameters
  in
  let* (names, args_rts, ret_lrt) =
    ListM.fold_leftM (fun (names, args_rts, rets_lrt) ((msym,_), type_expr) ->
        let mname = Option.bind (Option.map Sym.symbol_name msym) (fun x -> x) in
        let s = Sym.fresh_fancy mname in
        let names = match mname with
          | Some ident -> StringMap.add ident s names 
          | None -> names
        in
        log_name_add s;
        let* (B ((bnew, pointee, bt, osize), lrt)) = 
          of_type_expr loc names type_expr in
        let sa = pointee in
        let sr = Sym.fresh () in
        let* size = match osize with
          | Some size -> return size
          | None -> fail loc (Generic !^"argument type without size")
        in
        let pointsa = RE.Points {pointer = S s; pointee = sa; size} in
        let pointsr = RE.Points {pointer = S s; pointee = sr; size} in
        let arg_lrt = match bnew with
          | New -> RT.Logical ((sa, LS.Base bt), RT.Resource (pointsa, lrt))
          | Old -> RT.Resource (pointsa, lrt)
        in
        let arg_rt = RT.Computational ((s, BT.Loc), arg_lrt) in
        let ret_rt = RT.Logical ((sr, LS.Base bt), Resource (pointsr, I)) in
        return (names, args_rts @ [(mname, arg_rt)], rets_lrt @@ ret_rt)
      ) (names, [], RT.I) (List.combine args annot.fa_args)
  in
  let args_ftt = 
    List.fold_left (fun acc (_,arg_rt) -> 
        Tools.comp acc (FT.of_rt arg_rt)
      ) (fun ft -> ft) args_rts
  in
  let* ret_rt =
    let type_expr = annot.fa_returns in
    let* (B ((bnew, name, bt, osize), lrt)) = 
      of_type_expr loc names type_expr in
    if bnew = Old
    then fail loc (Unconstrained_logical_variable name) 
    else return (RT.Computational ((name, bt), lrt))
  in
  let* (names, exists_lrt) = 
    ListM.fold_leftM (fun (names, lrt) (ident,coq_expr) ->
        let s = Sym.fresh_pretty ident in
        let names = StringMap.add ident s names in
        log_name_add s;
        let* (bt, _, lrt') = of_coq_expr_typ loc names coq_expr s in
        return (names, lrt @@ RT.Logical ((s, LS.Base bt), lrt))
      ) (names, RT.I) annot.fa_exists
  in
  let* requires_lrt = 
    ListM.fold_leftM (fun lrt constr ->
        let* lrt' = of_constr loc names constr in
        return (lrt @@ lrt')
      ) RT.I annot.fa_requires
  in
  let* ensure_lrt = 
    ListM.fold_leftM (fun lrt constr ->
        let* lrt' = of_constr loc names constr in
        return (lrt @@ lrt')
      ) RT.I annot.fa_ensures
  in
  let ft = 
    Tools.comps
      [FT.of_lrt params_lrt; 
       args_ftt;
       FT.of_lrt requires_lrt]
      (FT.I (RT.concat ret_rt (ret_lrt @@ exists_lrt @@ ensure_lrt)))
  in
  return (names, ft, args_rts)



let make_loop_label_spec_annot (loc : Loc.t) 
                               names
                               structs 
                               (fargs : (string option * RT.t) list) 
                               (args : (Sym.t option * CF.Ctype.ctype) list) attrs = 
  let (annot: loop_annot) = loop_annot attrs in
  let* (names, exists_lrt) = 
    ListM.fold_leftM (fun (names, lrt) (ident,coq_expr) ->
        let s = Sym.fresh_pretty ident in
        let names = StringMap.add ident s names in
        log_name_add s;
        let* (bt, _, lrt') = of_coq_expr_typ loc names coq_expr s in
        return (names, lrt @@ RT.Logical ((s, LS.Base bt), lrt))
      ) (names, RT.I) annot.la_exists
  in
  let* (names, fargs_lrts) = 
    ListM.fold_leftM (fun (names,args_lrts) ((mname : string option), rt) ->
        match Option.map (fun n -> (n, List.assoc_opt n annot.la_inv_vars)) mname with
        | None
        | Some (_,None) ->
           let (RT.Computational (_, lrt)) = rt in
           let arg_lrt = update_values_lrt lrt in
           return (names,args_lrts @ [arg_lrt])
        | Some (ident, Some type_expr) ->
           Pp.d 6 (lazy (item ("invariant type " ^ ident) (pp_type_expr type_expr)));
           let* s = match StringMap.find_opt ident names with
           | Some sym -> return sym
           | None -> fail loc (Generic !^("unknown name " ^ ident))
           in
           let* (B ((bnew, pointee, bt, osize), lrt)) = 
             of_type_expr loc names type_expr in
           let sa = pointee in
           let* size = match osize with
             | Some size -> return size
             | None -> fail loc (Generic !^"argument type without size")
           in
           let pointsa = RE.Points {pointer = S s; pointee = sa; size} in
           let arg_lrt = match bnew with
             | New -> RT.Logical ((sa, LS.Base bt), RT.Resource (pointsa, lrt))
             | Old -> RT.Resource (pointsa, lrt)
           in
        return (names, args_lrts @ [arg_lrt])
      )
      (names, []) fargs
  in
  let* (names, args_rts) = 
    ListM.fold_leftM (fun (names, args_rts) (msym, ct) ->
        let mname = Option.bind (Option.map Sym.symbol_name msym) (fun x -> x) in
        match Option.map (fun n -> (n, List.assoc_opt n annot.la_inv_vars)) mname with
        | None
        | Some (_,None) ->
           let mname = Option.bind (Option.map Sym.symbol_name msym) (fun x -> x) in
           let s = Sym.fresh_fancy mname in
           let* arg_rt = rt_of_ctype loc structs s (lift ct) in
           return (names,args_rts @ [arg_rt])
        | Some (ident, Some type_expr) ->
           let mname = Option.bind (Option.map Sym.symbol_name msym) (fun x -> x) in
           let s = Sym.fresh_fancy mname in
           let names = StringMap.add ident s names in
           log_name_add s;
           let* (B ((bnew, pointee, bt, osize), lrt)) = 
             of_type_expr loc names type_expr in
           let sa = pointee in
           let* size = match osize with
             | Some size -> return size
             | None -> fail loc (Generic !^"argument type without size")
           in
           let pointsa = RE.Points {pointer = S s; pointee = sa; size} in
           let arg_lrt = match bnew with
             | New -> RT.Logical ((sa, LS.Base bt), RT.Resource (pointsa, lrt))
             | Old -> RT.Resource (pointsa, lrt)
           in
           let arg_rt = RT.Computational ((s, BT.Loc), arg_lrt) in
           return (names, args_rts @ [arg_rt])
      )
      (names, []) args
  in    
  let fargs_ltt = 
    List.fold_left (fun acc lrt -> 
        Tools.comp acc (LT.of_lrt lrt)
      ) (fun ft -> ft) fargs_lrts
  in
  let args_ltt = 
    List.fold_left (fun acc lrt -> 
        Tools.comp acc (LT.of_lrt lrt)
      ) (fun ft -> ft) fargs_lrts
  in
  let* constrs_lrt = 
    ListM.fold_leftM (fun lrt constr ->
        let* lrt' = of_constr loc names constr in
        return (lrt @@ lrt')
      ) RT.I annot.la_constrs
  in
  let lt = 
    Tools.comps 
      [LT.of_lrt exists_lrt;
       fargs_ltt;
       args_ltt;
       LT.of_lrt constrs_lrt] 
      (LT.I False.False) 
  in
  return (names, lt)
