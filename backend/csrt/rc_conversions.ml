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









let rec of_coq_expr_typ loc names newname coq_expr =
  match coq_expr with
  | Coq_ident ident ->
     begin match ident with
     | "Z" -> 
        return ((BT.Integer, None), [], [], [])
     | "nat" -> 
        return ((BT.Integer, None), [], [], [LC.LC (IT.GE (S newname, Num Num.zero))])
     | "loc" -> 
        return ((BT.Loc, None), [], [], [])
     | _ -> 
        fail loc (Unsupported (!^"cannot process coq type term:" ^/^ 
                                 pp_coq_expr coq_expr))
     end
  | Coq_all coq_term -> 
     begin match coq_term with
     | [Quot_plain "Z"] -> 
        return ((BT.Integer, None), [], [], [])
     | [Quot_plain "nat"] -> 
        return ((BT.Integer, None), [], [], [LC.LC (IT.GE (S newname, Num Num.zero))])
     | _ -> 
        fail loc (Unsupported (!^"cannot process coq type term:" ^/^ 
                                 pp_coq_expr coq_expr))
     end

and of_coq_term loc names coq_term =
  match coq_term with
  | [Quot_plain s] ->
     begin match IndexTermParser.parse loc names s with
     | Ok r -> return ([],r)
     | Error (loc,msg) -> 
        let err = 
          !^"cannot process coq term" ^^^ 
          parens (!^"returned" ^^^ squotes !^msg) ^^ colon ^/^ 
          (pp_coq_term coq_term)
        in
        fail loc (Unsupported err)
     end
  | _ ->
     fail loc (Unsupported (!^"cannot process coq term:" ^/^ 
                              pp_coq_term coq_term))

and of_coq_expr loc names coq_expr = 
  match coq_expr with
  | Coq_ident ident ->
     begin match StringMap.find_opt ident names with
     | Some sym -> return ([], IT.S sym)
     | None -> fail loc (Generic !^("unknown name" ^ ident))
     end
  | Coq_all coq_term -> 
     of_coq_term loc names coq_term


and of_coq_expr_refinement loc names newname coq_expr = 
  let* (l,it) = of_coq_expr loc names coq_expr in
  return (l, LC.LC (IT.EQ (IT.S newname, it)))

and of_coq_expr_constraint loc names coq_expr = 
  let* (l,it) = of_coq_expr loc names coq_expr in
  return (l, LC.LC it)

and of_constr loc names constr : ((Sym.t * LS.t) list * RE.t list * LC.t list) m =
  match constr with
  | Constr_Iris _ ->
     fail loc (Unsupported !^"Constr_Iris")
  | Constr_exist _ ->
     fail loc (Unsupported !^"Constr_exist")
  | Constr_own (ident,ptr_kind,type_expr) ->
     let* sym = match StringMap.find_opt ident names with
     | Some sym -> return sym
     | None -> fail loc (Generic !^("unknown name" ^ ident))
     in
     make_owned_pointer loc names sym ptr_kind type_expr
  | Constr_Coq coq_expr ->
     let* (l, c) = of_coq_expr_constraint loc names coq_expr in
     return (l, [], [c])

and is_uninit_type_expr = function
  | Ty_params ("uninit", [Ty_arg_expr arg]) -> Some arg
  | _ -> None

and of_integer_type_expr loc te = 
  match te with
  | Ty_Coq (Coq_ident "u32") -> return (32, `Unsigned, 4)
  | Ty_params ("u32", []) -> return (32, `Unsigned, 4)
  | Ty_Coq (Coq_ident "i32") -> return (32, `Signed, 4)
  | Ty_params ("i32", []) -> return (32, `Signed, 4)
  | _ -> 
     fail loc (Generic (!^"This integer type is not supported yet:" ^/^
                          pp_type_expr te))

and make_owned_pointer loc names existing_pointer ptr_kind type_expr =
  let newname' = Sym.fresh () in
  (* from impl_mem *)
  begin match ptr_kind, is_uninit_type_expr type_expr with
  | Own, Some integer_type_expr -> 
     let* (_, _, bytes) = of_integer_type_expr loc integer_type_expr in
     let size = Num.of_int bytes in
     let points = RE.Uninit {pointer = S existing_pointer; size} in
     return ([], [points], [])
  | Own, None -> 
     let* ((bt,osize),l,r,c) = of_type_expr loc names newname' type_expr in
     let* points = match osize with
       | Some size ->
          return (RE.Points {pointer = S existing_pointer; 
                             pointee = newname'; size})
       | None -> fail loc (Generic !^"pointer to non-object")
     in
     return ((newname', LS.Base bt) :: l, r @ [points], c)
  | Shr, _ -> 
     fail loc (Generic !^"Shared pointers not supported yet")
  | Frac _, _ -> 
     fail loc (Generic !^"Fractional pointers not supported yet")
  end

and of_type_expr loc names newname te =
  match te with
  | Ty_refine (coq_expr,type_expr) ->
     let* ((bt,size),l,r,c) = of_type_expr loc names newname type_expr in
     let* (l',constr) = of_coq_expr_refinement loc names newname coq_expr in
     return ((bt,size),l @ l', r, c @ [constr])
  | Ty_ptr (ptr_kind, type_expr) ->
       (* from impl_mem *)
     let* pointer_size = match (CF.Ocaml_implementation.get ()).sizeof_pointer with
       | Some n -> return (Num.of_int n)
       | None -> fail loc (Generic !^"sizeof_pointer returned None")
     in
     let* (l,r,c) = make_owned_pointer loc names newname ptr_kind type_expr in
     return ((BT.Loc, Some pointer_size), l, r, c)
  | Ty_dots ->
     fail loc (Generic !^"Recursive types not supported yet")
  | Ty_exists _ ->
     fail loc (Unsupported !^"existential types")
  | Ty_constr (type_expr,constr) ->
     let* ((bt,size),l,r,c) = of_type_expr loc names newname type_expr in
     let* (l',r',c') = of_constr loc names constr in
     return((bt,size), l @ l', r @ r', c @ c')
  | Ty_params (ident,args) ->
     let open IT in
     begin match ident, args with
     | "int", [Ty_arg_expr arg] -> 
        let* (bits,signedness,bytes) = of_integer_type_expr loc arg in
        begin match bits, signedness with
        | 32, `Signed ->
           let constr = LC.LC (in_range (S newname) (int 0) max_u32) in
           return ((BT.Integer, Some (Num.of_int bytes)), [], [], [constr])
        | 32, `Unsigned ->
           let constr = LC.LC (in_range (S newname) min_i32 max_i32) in
           return ((BT.Integer, Some (Num.of_int bytes)), [], [], [constr])
        | _ -> 
           fail loc (Generic (!^"This type application is not supported yet:" ^/^
                                pp_type_expr te))
        end
     | "void", [] ->
        return ((BT.Unit, None), [], [], [])
     | _ -> 
        fail loc (Generic (!^"This type application is not supported yet:" ^/^
                             pp_type_expr te))
     end
  | Ty_Coq coq_expr ->
     of_coq_expr_typ loc names newname coq_expr


(* let log_name_add sym = Pp.d 6 (lazy (!^"adding name" ^^^ Sym.pp sym)) *)
let log_name_add sym = ()

let make_fun_spec_annot loc struct_decls attrs args ret_ctype = 
  let (annot: function_annot) = function_annot attrs in
  let a, l, r, c = [], [], [], [] in
  let rl, rr, rc = [], [], [] in
  let names = StringMap.empty in
  let* (names, (a, l, r, c)) = 
    ListM.fold_leftM (fun (names, (a, l, r, c)) (ident, coq_expr) ->
        let s = Sym.fresh_pretty ident in
        let names = StringMap.add ident s names in
        log_name_add s;
        let* ((bt,_),l',r',c') = of_coq_expr_typ loc names s coq_expr in
        return (names, (a, l @ [(s, LS.Base bt)] @ l', r @ r', c @ c'))
      ) (names, (a, l, r, c)) annot.fa_parameters
  in
  let* ((a, l, r, c), (rl, rr, rc)) =
    ListM.fold_leftM (fun ((a, l, r, c), (rl, rr, rc)) type_expr ->
        let s = Sym.fresh () in
        let sa, sr = Sym.fresh (), Sym.fresh () in
        let* ((bt, osize), l', r', c') = of_type_expr loc names sa type_expr in
        let* size = match osize with
          | Some size -> return size
          | None -> fail loc (Generic !^"argument type without size")
        in
        let pointsa = RE.Points {pointer = S s; pointee = sa; size} in
        let pointsr = RE.Points {pointer = S s; pointee = sr; size} in
        return ((a @ [(s,BT.Loc)], l @ [(sa, LS.Base bt)] @ l', r @ [pointsa] @ r', c @ c'),
                (rl @ [(sr, LS.Base bt)], rr @ [pointsr], rc))
      ) ((a, l, r, c), (rl, rr, rc)) annot.fa_args
  in
  let* (ra, rl, rr, rc) =
    let type_expr = annot.fa_returns in
    let s = Sym.fresh () in
    let* ((bt, size), rl', rr', rc') = of_type_expr loc names s type_expr in
    return ((s,bt), rl @ rl', rr @ rr', rc @ rc')
  in
  let* (names, (rl, rr, rc)) = 
    ListM.fold_leftM (fun (names, (rl, rr, rc)) (ident,coq_expr) ->
        let s = Sym.fresh_pretty ident in
        let names = StringMap.add ident s names in
        log_name_add s;
        let* ((bt,_), rl', rr', rc') = of_coq_expr_typ loc names s coq_expr in
        return (names, (rl @ [(s, LS.Base bt)] @ rl', rr @ rr', rc @ rc'))
      ) (names, (rl, rr, rc)) annot.fa_exists
  in
  let* (a, l, r, c) = 
    ListM.fold_leftM (fun (a, l, r, c) constr ->
        let* (l',r',c') = of_constr loc names constr in
        return (a, l @ l', r @ r', c @ c')
      ) (a, l, r, c) annot.fa_requires
  in
  let* (rl, rr, rc) = 
    ListM.fold_leftM (fun (rl, rr, rc) constr ->
        let* (rl', rr', rc') = of_constr loc names constr in
        return (rl @ rl', rr @ rr', rc @ rc')
      ) (rl, rr, rc) annot.fa_ensures
  in
  let rt = 
    RT.mComputational ra
      (Tools.comps 
         (List.map RT.mLogical rl @ 
          List.map RT.mResource rr @ 
          List.map RT.mConstraint rc)
         RT.I)
  in
  let ft =
    Tools.comps 
      (List.map FT.mComputational a @
       List.map FT.mLogical l @ 
       List.map FT.mResource r @ 
       List.map FT.mConstraint c)
      (FT.I rt)
  in
  return (names,ft)



let make_loop_label_spec_annot (loc : Loc.t) 
                               names
                               structs 
                               (fargs : (Sym.t option * CF.Ctype.ctype) list) 
                               (args : (Sym.t option * CF.Ctype.ctype) list) attrs = 
  let (annot: loop_annot) = loop_annot attrs in
  let* (names, ltt) = 
    ListM.fold_leftM (fun (names, ltt) (ident, coq_expr) ->
        let s = Sym.fresh_pretty ident in
        let names = StringMap.add ident s names in
        log_name_add s;
        let* ((bt,_),l',r',c') = of_coq_expr_typ loc names s coq_expr in
        let l = [(s, LS.Base bt)] @ l' in
        let r = r' in
        let c = c' in
        let arg_rt = 
          (Tools.comps 
             (List.map RT.mLogical l @ 
                List.map RT.mResource r @ 
                  List.map RT.mConstraint c)
               RT.I)
        in
        let arg = LT.of_lrt arg_rt in
        let ltt = Tools.comp ltt arg in
        return (names,ltt)
      ) (names, fun t -> t) annot.la_exists
  in
  let* (names, ltt) = 
    ListM.fold_leftM (fun (names,(ltt : LT.t -> LT.t)) (msym, ct) ->
        let mname = Option.bind (Option.map Sym.symbol_name msym) (fun x -> x) in
        match Option.map (fun n -> (n, List.assoc_opt n annot.la_inv_vars)) mname with
        | None
        | Some (_,None) ->
           let mname = Option.bind (Option.map Sym.symbol_name msym) (fun x -> x) in
           let s = Sym.fresh_fancy mname in
           let* size = Memory.size_of_ctype loc ct in
           let* RT.Computational ((la,bt), lrt) = 
             rt_of_ctype loc structs (Sym.fresh ()) ct in
           let arg_rt = RT.Resource (Points {pointer=S s; pointee=la; size}, lrt) in
           let arg = LT.of_lrt arg_rt in
           let ltt = Tools.comp ltt arg in
           return (names,ltt)
        | Some (ident, Some type_expr) ->
           let mname = Option.bind (Option.map Sym.symbol_name msym) (fun x -> x) in
           let s = Sym.fresh_fancy mname in
           let names = StringMap.add ident s names in
           log_name_add s;
           let sa = Sym.fresh () in
           let* ((bt, osize), l', r', c') = of_type_expr loc names sa type_expr in
           let* size = match osize with
             | Some size -> return size
             | None -> fail loc (Generic !^"argument type without size")
           in
           let points = RE.Points {pointer = S s; pointee = sa; size} in
           let l = [(sa, LS.Base bt)] @ l' in
           let r = [points] @ r' in
           let c = c' in
           let arg_rt = 
             Tools.comps 
               (List.map RT.mLogical l @ 
                  List.map RT.mResource r @ 
                    List.map RT.mConstraint c)
               RT.I
           in
           let arg = LT.of_lrt arg_rt in
           let ltt = Tools.comp ltt arg in
           return (names,ltt)
      )
      (names, ltt) fargs
  in
  let* (names, ltt) = 
    ListM.fold_leftM (fun (names,(ltt : LT.t -> LT.t)) (msym, ct) ->
        let mname = Option.bind (Option.map Sym.symbol_name msym) (fun x -> x) in
        match Option.map (fun n -> (n, List.assoc_opt n annot.la_inv_vars)) mname with
        | None
        | Some (_,None) ->
           let mname = Option.bind (Option.map Sym.symbol_name msym) (fun x -> x) in
           let s = Sym.fresh_fancy mname in
           let* arg_rt = rt_of_ctype loc structs s (lift ct) in
           let arg = LT.of_rt arg_rt in
           let ltt = Tools.comp ltt arg in
           return (names,ltt)
        | Some (ident, Some type_expr) ->
           let mname = Option.bind (Option.map Sym.symbol_name msym) (fun x -> x) in
           let s = Sym.fresh_fancy mname in
           let names = StringMap.add ident s names in
           log_name_add s;
           let sa = Sym.fresh () in
           let* ((bt, osize), l', r', c') = of_type_expr loc names sa type_expr in
           let* size = match osize with
             | Some size -> return size
             | None -> fail loc (Generic !^"argument type without size")
           in
           let points = RE.Points {pointer = S s; pointee = sa; size} in
           let l = [(sa, LS.Base bt)] @ l' in
           let r = [points] @ r' in
           let c = c' in
           let arg_rt = 
             RT.mComputational (s,bt)
               (Tools.comps 
                  (List.map RT.mLogical l @ 
                     List.map RT.mResource r @ 
                       List.map RT.mConstraint c)
                  RT.I)
           in
           let arg = LT.of_rt arg_rt in
           let ltt = Tools.comp ltt arg in
           return (names,ltt)
      )
      (names, ltt) args
  in    
  let* ltt = 
    ListM.fold_leftM (fun ltt constr ->
        let* (l, r, c) = of_constr loc names constr in
        let arg_rt = 
          (Tools.comps 
             (List.map RT.mLogical l @ 
                List.map RT.mResource r @ 
                  List.map RT.mConstraint c)
             RT.I)
        in
        let arg = LT.of_lrt arg_rt in
        let ltt = Tools.comp ltt arg in
        return ltt
      ) ltt annot.la_constrs
  in
  return (names, ltt (LT.I False.False))
