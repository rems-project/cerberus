open Format
open Extra
open Panic
open Coq_ast
open Rc_annot

let pp_str = pp_print_string

let pp_as_tuple : 'a pp -> 'a list pp = fun pp ff xs ->
  match xs with
  | []      -> pp_str ff "()"
  | [x]     -> pp ff x
  | x :: xs -> fprintf ff "(%a" pp x;
               List.iter (fprintf ff ", %a" pp) xs;
               pp_str ff ")"

let pp_as_tuple_pat : 'a pp -> 'a list pp = fun pp ff xs ->
  if List.length xs > 1 then pp_str ff "'";
  pp_as_tuple pp ff xs

let pp_sep : string -> 'a pp -> 'a list pp = fun sep pp ff xs ->
  match xs with
  | []      -> ()
  | x :: xs -> pp ff x; List.iter (fprintf ff "%s%a" sep pp) xs

let pp_as_prod : 'a pp -> 'a list pp = fun pp ff xs ->
  match xs with
  | [] -> pp_str ff "()"
  | _  -> pp_sep " * " pp ff xs

let pp_id_args : bool -> string -> string list pp = fun need_paren id ff xs ->
  if xs <> [] && need_paren then pp_str ff "(";
  pp_str ff id; List.iter (fprintf ff " %s") xs;
  if xs <> [] && need_paren then pp_str ff ")"

let pp_coq_expr : bool -> coq_expr pp = fun wrap ff e ->
  match e with
  | Coq_ident(x) -> pp_str ff x
  | Coq_all(s)   -> if wrap then fprintf ff "(%s)" s else pp_str ff s

let pp_int_type : Coq_ast.int_type pp = fun ff it ->
  let pp fmt = Format.fprintf ff fmt in
  match it with
  | ItSize_t(true)      -> pp "ssize_t"
  | ItSize_t(false)     -> pp "size_t"
  | ItI8(true)          -> pp "i8"
  | ItI8(false)         -> pp "u8"
  | ItI16(true)         -> pp "i16"
  | ItI16(false)        -> pp "u16"
  | ItI32(true)         -> pp "i32"
  | ItI32(false)        -> pp "u32"
  | ItI64(true)         -> pp "i64"
  | ItI64(false)        -> pp "u64"
  | ItBool              -> pp "bool_it"

let rec pp_layout : Coq_ast.layout pp = fun ff layout ->
  let pp fmt = Format.fprintf ff fmt in
  match layout with
  | LVoid              -> pp "LVoid"
  | LPtr               -> pp "LPtr"
  | LStruct(id, false) -> pp "layout_of struct_%s" id
  | LStruct(id, true ) -> pp "ul_layout union_%s" id
  | LInt(i)            -> pp "it_layout %a" pp_int_type i
  | LArray(layout, n)  -> pp "mk_array_layout (%a) %s" pp_layout layout n

let pp_op_type : Coq_ast.op_type pp = fun ff ty ->
  let pp fmt = Format.fprintf ff fmt in
  match ty with
  | OpInt(i) -> pp "IntOp %a" pp_int_type i
  | OpPtr(_) -> pp "PtrOp" (* FIXME *)

let pp_un_op : Coq_ast.un_op pp = fun ff op ->
  let pp fmt = Format.fprintf ff fmt in
  match op with
  | NotBoolOp  -> pp "NotBoolOp"
  | NotIntOp   -> pp "NotIntOp"
  | NegOp      -> pp "NegOp"
  | CastOp(ty) -> pp "(CastOp $ %a)" pp_op_type ty

let pp_bin_op : Coq_ast.bin_op pp = fun ff op ->
  pp_str ff @@
  match op with
  | AddOp       -> "+"
  | SubOp       -> "-"
  | MulOp       -> "×"
  | DivOp       -> "/"
  | ModOp       -> "%"
  | AndOp       -> "..." (* TODO *)
  | OrOp        -> "..." (* TODO *)
  | XorOp       -> "..." (* TODO *)
  | ShlOp       -> "..." (* TODO *)
  | ShrOp       -> "..." (* TODO *)
  | EqOp        -> "="
  | NeOp        -> "!="
  | LtOp        -> "<"
  | GtOp        -> ">"
  | LeOp        -> "≤"
  | GeOp        -> "≥"
  | RoundDownOp -> "..." (* TODO *)
  | RoundUpOp   -> "..." (* TODO *)

let rec pp_expr : Coq_ast.expr pp = fun ff e ->
  let pp fmt = Format.fprintf ff fmt in
  match e with
  | Var(None   ,_)                ->
      pp "\"_\""
  | Var(Some(x),g)                ->
      if g then pp_str ff x else fprintf ff "\"%s\"" x
  | Val(Null)                     ->
      pp "NULL"
  | Val(Void)                     ->
      pp "VOID"
  | Val(Int(s,it))                ->
      pp "i2v %s %a" s pp_int_type it
  | UnOp(op,ty,e)                 ->
      pp "UnOp %a (%a) (%a)" pp_un_op op pp_op_type ty pp_expr e
  | BinOp(op,ty1,ty2,e1,e2)       ->
      begin
        match (ty1, ty2, op) with
        | (OpPtr(l), OpInt(_), AddOp) ->
            pp "(%a) at_offset{%a, PtrOp, %a} (%a)" pp_expr e1
              pp_layout l pp_op_type ty2 pp_expr e2
        | (OpPtr(_), OpInt(_), _) ->
            panic_no_pos "Binop [%a] not supported on pointers." pp_bin_op op
        | (OpInt(_), OpPtr(_), _) ->
            panic_no_pos "Wrong ordering of integer pointer binop [%a]."
              pp_bin_op op
        | _                 ->
            pp "(%a) %a{%a, %a} (%a)" pp_expr e1 pp_bin_op op
              pp_op_type ty1 pp_op_type ty2 pp_expr e2
      end
  | Deref(lay,e)                  ->
      pp "!{%a} (%a)" pp_layout lay pp_expr e
  | CAS(ty,e1,e2,e3)              ->
      pp "CAS@ (%a)@ (%a)@ (%a)@ (%a)" pp_op_type ty
        pp_expr e1 pp_expr e2 pp_expr e3
  | SkipE(e)                      ->
      pp "SkipE (%a)" pp_expr e
  | Use(lay,e)                    ->
      pp "use{%a} (%a)" pp_layout lay pp_expr e
  | AddrOf(e)                     ->
      pp "&(%a)" pp_expr e
  | GetMember(e,name,false,field) ->
      pp "(%a) at{struct_%s} %S" pp_expr e name field
  | GetMember(e,name,true ,field) ->
      pp "(%a) at_union{union_%s} %S" pp_expr e name field
  | AnnotExpr(i,coq_e,e)          ->
      pp "AnnotExpr %i%%nat %a (%a)" i (pp_coq_expr true) coq_e pp_expr e

let rec pp_stmt : Coq_ast.stmt pp = fun ff stmt ->
  let pp fmt = Format.fprintf ff fmt in
  match stmt with
  | Goto(id)               ->
      pp "Goto %S" id
  | Return(e)              ->
      pp "Return @[<hov 0>(%a)@]" pp_expr e
  | Assign(lay,e1,e2,stmt) ->
      pp "@[<hov 2>%a <-{ %a }@ %a ;@]@;%a"
        pp_expr e1 pp_layout lay pp_expr e2 pp_stmt stmt
  | Call(ret_id,e,es,stmt) ->
      let pp_args _ es =
        let n = List.length es in
        let fn i e =
          pp (if i = n - 1 then "%a" else "%a ;@;") pp_expr e
        in
        List.iteri fn es
      in
      pp "@[<hov 2>%S <- %a with@ [ %a ] ;@]@;%a"
        (Option.get "_" ret_id) pp_expr e pp_args es pp_stmt stmt
  | SkipS(stmt)            ->
      pp_stmt ff stmt
  | If(e,stmt1,stmt2)      ->
      pp "if: @[<hov 0>%a@]@;then@;@[<v 2>%a@]@;else@;@[<v 2>%a@]"
        pp_expr e pp_stmt stmt1 pp_stmt stmt2
  | Assert(e, stmt)        ->
      pp "assert: (%a) ;@;%a" pp_expr e pp_stmt stmt
  | ExprS(annot, e, stmt)  ->
      Option.iter (Option.iter (pp "annot: (%s) ;@;")) annot;
      pp "expr: (%a) ;@;%a" pp_expr e pp_stmt stmt

type import = string * string

let pp_import ff (from, mod_name) =
  Format.fprintf ff "From %s Require Import %s.@;" from mod_name

let pp_code : import list -> Coq_ast.t pp = fun imports ff ast ->
  (* Formatting utilities. *)
  let pp fmt = Format.fprintf ff fmt in

  (* Printing some header. *)
  pp "@[<v 0>From refinedc.lang Require Export notation.@;";
  pp "From refinedc.lang Require Import tactics.@;";
  pp "From refinedc.typing Require Import annotations.@;";
  List.iter (pp_import ff) imports;
  pp "Set Default Proof Using \"Type\".@;@;";

  (* Printing generation data in a comment. *)
  pp "(* Generated from [%s]. *)@;" ast.source_file;

  (* Opening the section. *)
  pp "@[<v 2>Section code.";

  (* Printing for struct/union members. *)
  let pp_members members =
    let n = List.length members in
    let fn i (id, (attrs, layout)) =
      let sc = if i = n - 1 then "" else ";" in
      pp "@;(%S, %a)%s" id pp_layout layout sc
    in
    List.iteri fn members
  in

  (* Definition of structs/unions. *)
  let pp_struct (id, decl) =
    pp "\n@;(* Definition of struct [%s]. *)@;" id;
    pp "@[<v 2>Program Definition struct_%s := {|@;" id;

    pp "@[<v 2>sl_members := [";
    pp_members decl.struct_members;
    pp "@]@;];@]@;|}.@;";
    pp "Solve Obligations with solve_struct_obligations."
  in
  let pp_union (id, decl) =
    pp "\n@;(* Definition of union [%s]. *)@;" id;
    pp "@[<v 2>Program Definition union_%s := {|@;" id;

    pp "@[<v 2>ul_members := [";
    pp_members decl.struct_members;
    pp "@]@;];@]@;|}.@;";
    pp "Solve Obligations with solve_struct_obligations."
  in
  let rec sort_structs found strs =
    match strs with
    | []                     -> []
    | (id, s) as str :: strs ->
    if List.for_all (fun id -> List.mem id found) s.struct_deps then
      str :: sort_structs (id :: found) strs
    else
      sort_structs found (strs @ [str])
  in
  let pp_struct_union ((_, {struct_is_union; _}) as s) =
    if struct_is_union then pp_union s else pp_struct s
  in
  List.iter pp_struct_union (sort_structs [] ast.structs);

  (* Definition of functions. *)
  let pp_function (id, def) =
    let deps = fst def.func_deps @ snd def.func_deps in
    pp "\n@;(* Definition of function [%s]. *)@;" id;
    pp "@[<v 2>Definition impl_%s " id;
    if deps <> [] then begin
      pp "(";
      List.iter (pp "%s ") deps;
      pp ": loc)";
    end;
    pp ": function := {|@;";

    pp "@[<v 2>f_args := [";
    begin
      let n = List.length def.func_args in
      let fn i (id, layout) =
        let sc = if i = n - 1 then "" else ";" in
        pp "@;(%S, %a)%s" id pp_layout layout sc
      in
      List.iteri fn def.func_args
    end;
    pp "@]@;];@;";

    pp "@[<v 2>f_local_vars := [";
    begin
      let n = List.length def.func_vars in
      let fn i (id, layout) =
        let sc = if i = n - 1 then "" else ";" in
        pp "@;(%S, %a)%s" id pp_layout layout sc
      in
      List.iteri fn def.func_vars
    end;
    pp "@]@;];@;";

    pp "f_init := \"#0\";@;";

    pp "@[<v 2>f_code := (";
    begin
      let fn id (attrs, stmt) =
        pp "@;@[<v 2><[ \"%s\" :=@;" id;

        pp_stmt ff stmt;
        pp "@]@;]> $";
      in
      SMap.iter fn def.func_blocks;
      pp "∅"
    end;
    pp "@]@;)%%E";
    pp "@]@;|}.";
  in
  List.iter pp_function ast.functions;

  (* Closing the section. *)
  pp "@]@;End code.@]"

type guard_mode =
  | Guard_none
  | Guard_in_def of string
  | Guard_in_lem of string

let (reset_nroot_counter, with_uid) : (unit -> unit) * string pp =
  let counter = ref (-1) in
  let with_uid ff s = incr counter; fprintf ff "\"%s_%i\"" s !counter in
  let reset _ = counter := -1 in
  (reset, with_uid)

let rec pp_constr_guard : unit pp option -> guard_mode -> bool -> constr pp =
    fun pp_dots guard wrap ff c ->
  let pp_type_expr = pp_type_expr_guard pp_dots guard in
  let pp_constr = pp_constr_guard pp_dots guard in
  let pp_kind ff k =
    match k with
    | Own     -> pp_str ff "◁ₗ"
    | Shr     -> pp_str ff "◁ₗ{Shr}"
    | Frac(e) -> fprintf ff "◁ₗ{%a}" (pp_coq_expr false) e
  in
  match c with
  (* Needs no wrapping. *)
  | Constr_Coq(e)      -> fprintf ff "⌜%a⌝" (pp_coq_expr false) e
  (* Apply wrapping. *)
  | _ when wrap        -> fprintf ff "(%a)" (pp_constr false) c
  (* No need for wrappin now. *)
  | Constr_Iris(s)     -> pp_str ff s
  | Constr_exist(x,c)  -> fprintf ff "∃ %s, %a" x (pp_constr false) c
  | Constr_own(x,k,ty) -> fprintf ff "%s %a %a" x pp_kind k pp_type_expr ty

and pp_type_expr_guard : unit pp option -> guard_mode -> type_expr pp =
    fun pp_dots guard ff ty ->
  let pp_constr = pp_constr_guard pp_dots guard in
  let pp_kind ff k =
    match k with
    | Own     -> pp_str ff "&own"
    | Shr     -> pp_str ff "&shr"
    | Frac(e) -> fprintf ff "&frac{%a}" (pp_coq_expr false) e
  in
  let rec pp_patt ff p =
    match p with
    | Pat_var(x)    -> pp_str ff x
    | Pat_tuple(ps) -> fprintf ff "%a" (pp_as_tuple_pat pp_patt) ps
  in
  let rec pp wrap ff ty =
    match ty with
    (* Don't need explicit wrapping. *)
    | Ty_Coq(e)         -> (pp_coq_expr wrap) ff e
    | Ty_params(id,[])  -> pp_str ff id
    (* Always wrapped. *)
    | Ty_lambda(p,ty)   -> fprintf ff "(λ %a, %a)" pp_patt p (pp false) ty
    (* Insert wrapping if needed. *)
    | _ when wrap       -> fprintf ff "(%a)" (pp false) ty
    (* Remaining constructors (no need for explicit wrapping). *)
    | Ty_dots           ->
        begin
          match pp_dots with
          | None     -> Panic.panic_no_pos "Unexpected ellipsis."
          | Some(pp) -> pp ff ()
        end
    | Ty_refine(e,ty)   ->
        begin
          let normal () =
            fprintf ff "%a @@ %a" (pp_coq_expr true) e (pp true) ty
          in
          match (guard, ty) with
          | (Guard_in_def(s), Ty_params(c,_)) when c = s ->
              fprintf ff "guarded (nroot.@%a) " with_uid s;
              fprintf ff "(apply_dfun self %a)" (pp_coq_expr true) e
          | (Guard_in_lem(s), Ty_params(c,tys)) when c = s ->
              fprintf ff "guarded (nroot.@%a) (" with_uid s;
              normal (); pp_str ff ")"
          | (_              , _               )            -> normal ()
        end
    | Ty_ptr(k,ty)      -> fprintf ff "%a %a" pp_kind k (pp true) ty
    | Ty_exists(x,ty)   ->
        fprintf ff "tyexists (λ %s, %a)" x (pp false) ty
    | Ty_constr(ty,c)   ->
        fprintf ff "constrained %a %a" (pp true) ty (pp_constr true) c
    | Ty_params(id,tys) ->
    pp_str ff id;
    match (id, tys) with
    | ("optional", [ty]) | ("optionalO", [ty]) -> fprintf ff " %a null" (pp true) ty
    | (_         , _   ) -> List.iter (fprintf ff " %a" (pp true)) tys
  in
  pp true ff ty

let pp_type_expr = pp_type_expr_guard None Guard_none
let pp_constr = pp_constr_guard None Guard_none true

let pp_constrs : constr list pp = fun ff cs ->
  match cs with
  | []      -> pp_str ff "True"
  | c :: cs -> pp_constr ff c; List.iter (fprintf ff " ∗ %a" pp_constr) cs

let pp_struct_def guard annot fields ff id =
  let pp fmt = fprintf ff fmt in
  (* Printing of the "exists". *)
  pp "@[<v 0>";
  if annot.st_exists <> [] then
    begin
      let pp_exist (x, e) =
        pp "tyexists (λ %s : %a,@;" x (pp_coq_expr false) e
      in
      List.iter pp_exist annot.st_exists;
    end;
  (* Opening the "constrained". *)
  pp "@[<v 2>"; (* Open box for struct fields. *)
  if annot.st_constrs <> [] then pp "constrained (";
  (* Part that may stand for dots in case of "ptr_type". *)
  let pp_dots ff () =
    let pp fmt = fprintf ff fmt in
    (* Printing the "padded". *)
    Option.iter (fun _ -> pp "padded (") annot.st_size;
    (* Printing the struct fields. *)
    pp "struct struct_%s [" id;
    begin
      match fields with
      | []               -> ()
      | (_,ty) :: fields ->
      reset_nroot_counter ();
      let pp_type_expr = pp_type_expr_guard None guard in
      pp "@;%a : type" pp_type_expr ty;
      List.iter (fun (_,ty) -> pp " ;@;%a" pp_type_expr ty) fields
    end;
    pp "@]@;]"; (* Close box for struct fields. *)
    Option.iter (pp ") struct_%s %a" id (pp_coq_expr true)) annot.st_size;
  in
  begin
    match annot.st_ptr_type with
    | None        -> pp_dots ff ()
    | Some(_, ty) -> pp_type_expr_guard (Some(pp_dots)) Guard_none ff ty
  end;
  (* Printing of constraints. *)
  if annot.st_constrs <> [] then
    begin
      pp ") (@;  @[<v 0>";
      let (c, cs) = (List.hd annot.st_constrs, List.tl annot.st_constrs) in
      pp "%a" pp_constr c;
      List.iter (pp " ∗@;%a" pp_constr) cs;
      pp "@]@;)"
    end;
  (* Closing the "exists". *)
  List.iter (fun _ -> pp ")") annot.st_exists;
  pp "@]@]"

(* Functions for looking for recursive occurences of a type. *)

let in_coq_expr : string -> coq_expr -> bool = fun s e ->
  match e with
  | Coq_ident(x) -> x = s
  | Coq_all(e)   -> e = s (* In case of [{s}]. *)

let rec in_patt : string -> pattern -> bool = fun s p ->
  match p with
  | Pat_var(x)    -> x = s
  | Pat_tuple(ps) -> List.exists (in_patt s) ps

let rec in_type_expr : string -> type_expr -> bool = fun s ty ->
  match ty with
  | Ty_refine(e,ty)  -> in_coq_expr s e || in_type_expr s ty
  | Ty_ptr(_,ty)     -> in_type_expr s ty
  | Ty_dots          -> false
  | Ty_exists(x,ty)  -> x <> s && in_type_expr s ty
  | Ty_lambda(p,ty)  -> not (in_patt s p) && in_type_expr s ty
  | Ty_constr(ty,c)  -> in_type_expr s ty || in_constr s c
  | Ty_params(x,tys) -> x = s || List.exists (in_type_expr s) tys
  | Ty_Coq(e)        -> in_coq_expr s e

and in_constr : string -> constr -> bool = fun s c ->
  match c with
  | Constr_Coq(e)      -> in_coq_expr s e
  | Constr_Iris(s)     -> false
  | Constr_exist(x,c)  -> x <> s && in_constr s c
  | Constr_own(_,_,ty) -> in_type_expr s ty

let pp_spec : import list -> Coq_ast.t pp = fun imports ff ast ->
  (* Stuff for import of the code. *)
  let basename =
    let name = Filename.basename ast.source_file in
    try Filename.chop_extension name with Invalid_argument(_) -> name
  in
  let import_path = "refinedc.examples." ^ basename in (* FIXME generic? *)

  (* Formatting utilities. *)
  let pp fmt = Format.fprintf ff fmt in

  (* Printing some header. *)
  pp "@[<v 0>From refinedc.typing Require Import typing.@;";
  pp "From %s Require Import %s_code.@;" import_path basename;
  List.iter (pp_import ff) imports;
  pp "Set Default Proof Using \"Type\".@;@;";

  (* Printing generation data in a comment. *)
  pp "(* Generated from [%s]. *)@;" ast.source_file;

  (* Opening the section. *)
  pp "@[<v 2>Section spec.@;";
  pp "Context `{typeG Σ}.";

  (* Definition of types. *)
  let pp_struct (struct_id, s) =
    let annot =
      match s.struct_annot with
      | Some(annot) -> annot
      | None        ->
      Panic.panic_no_pos "Annotations on struct [%s] are invalid." struct_id
    in
    let fields =
      let fn (x, (ty_opt, _)) =
        match ty_opt with
        | Some(ty) -> (x, ty)
        | None     ->
        Panic.panic_no_pos
          "Annotation on field [%s] (struct [%s])] is invalid." x struct_id
      in
      List.map fn s.struct_members
    in
    let (ref_names, ref_types) = List.split annot.st_refined_by in
    let pp_params ff =
      List.iter (fun (x,e) -> fprintf ff "(%s : %a) " x (pp_coq_expr false) e)
    in
    let params = annot.st_parameters in
    let param_names = List.map fst params in
    let id =
      match annot.st_ptr_type with
      | None       -> struct_id
      | Some(id,_) -> id
    in
    let is_rec = List.exists (fun (_,ty) -> in_type_expr id ty) fields in
    let pp_prod = pp_as_prod (pp_coq_expr true) in
    if is_rec then begin
      pp "@[<v 2>Definition %s_rec %a:" id pp_params params;
      pp " (%a -d> typeO) → (%a -d> typeO) := " pp_prod
        ref_types (pp_as_prod (pp_coq_expr true)) ref_types;
      pp "(λ self %a,@;" (pp_as_tuple pp_str) ref_names;
      pp_struct_def (Guard_in_def(id)) annot fields ff struct_id;
      pp "@;)%%I.@;Arguments %s_rec /.\n" id;

      pp "@;Global Instance %s_rec_ne %a: Contractive %a." id pp_params params
        (pp_id_args true (id ^ "_rec")) param_names;
      pp "@;Proof. solve_type_proper. Qed.\n@;";

      pp "@[<v 2>Definition %s %a: rtype := {|@;"
        id pp_params params;
      pp "rty_type := %a;@;" pp_prod ref_types;
      pp "rty := fixp %a" (pp_id_args true (id ^ "_rec")) param_names;
      pp "@]@;|}.\n";

      (* Generation of the unfolding lemma. *)
      pp "@;@[<v 2>Lemma %s_unfold %a%a:@;"
        id pp_params params pp_params annot.st_refined_by;
      pp "(%a @@ %a)%%I ≡@@{type}@;(" (pp_as_tuple pp_str) ref_names
        (pp_id_args false id) param_names;
      pp_struct_def (Guard_in_lem(id)) annot fields ff struct_id;
      pp ")%%I.@;";
      pp "Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.\n";

      (* Generation of the global instances. *)
      let pp_instance inst_name type_name =
        pp "@;Global Instance %s_%s_inst l_ β_ %a%a:@;" id inst_name
          pp_params params pp_params annot.st_refined_by;
        pp "  %s l_ β_ (%a @@ %a)%%I (Some 100%%N) :=@;" type_name
          (pp_as_tuple pp_str) ref_names (pp_id_args false id) param_names;
        pp "  λ T, i2p (%s_eq l_ β_ _ _ T (%s_unfold" inst_name id;
        List.iter (fun _ -> pp " _") param_names;
        List.iter (fun _ -> pp " _") ref_names; pp "))."
      in
      pp_instance "simplify_hyp_place" "SimplifyHypPlace";
      pp_instance "simplify_goal_place" "SimplifyGoalPlace";

      pp "\n@;Global Program Instance %s_rmovable %a: RMovable %a :=@;"
        id pp_params params (pp_id_args true id) param_names;
      pp "  {| rmovable arg := movable_eq _ _ (%s_unfold" id;
      List.iter (fun _ -> pp " _") param_names;
      List.iter (fun _ -> pp " _") ref_names;
      pp ") |}.@;Next Obligation. done. Qed."
    end else begin
      (* Definition of the [rtype]. *)
      pp "@[<v 2>Definition %s %a: rtype := {|@;" id pp_params params;
      pp "rty_type := %a;@;" pp_prod ref_types;
      pp "rty %a := (@;  @[<hov 0>" (pp_as_tuple_pat pp_str) ref_names;
      pp_struct_def Guard_none annot fields ff id;
      pp "@;)%%I@]@;|}.\n";
      (* Typeclass stuff. *)
      pp "@;Global Program Instance %s_movable %a:" id pp_params params;
      pp " RMovable %a :=" (pp_id_args true id) param_names;
      pp "@;  {| rmovable %a := _ |}." (pp_as_tuple pp_str) ref_names;
      pp "@;Next Obligation. unfold with_refinement => /= ?. ";
      pp "apply _. Defined.";
      pp "@;Next Obligation. solve_typing. Qed."
    end
  in
  let pp_union s =
    pp "(* Printing for Unions not implemented. *)" (* TODO *)
  in
  let pp_struct_union ((_, {struct_is_union; struct_name; _}) as s) =
    pp "\n@;(* Definition of type [%s]. *)@;" struct_name;
    if struct_is_union then pp_union s else pp_struct s
  in
  List.iter pp_struct_union ast.structs;

  (* Function specs. *)
  let pp_spec (id, def) =
    pp "\n@;(* Specifications for function [%s]. *)" id;
    let annot =
      match def.func_annot with
      | Some(annot) -> annot
      | None        ->
      Panic.panic_no_pos "Annotations on function [%s] are invalid." id
    in
    let (param_names, param_types) = List.split annot.fa_parameters in
    let (exist_names, exist_types) = List.split annot.fa_exists in
    let pp_args ff tys =
      match tys with
      | [] -> ()
      | _  -> pp "; "; pp_sep ", " pp_type_expr ff tys
    in
    pp "@;Definition type_of_%s " id;
    List.iter (pp "%s ") (fst def.func_deps);
    pp ":=@;  @[<hov 2>";
    let pp_prod = pp_as_prod (pp_coq_expr true) in
    pp "fn(∀ %a : %a%a; %a)@;→ ∃ %a : %a, %a; %a.@]"
      (pp_as_tuple pp_str) param_names pp_prod param_types
      pp_args annot.fa_args pp_constrs annot.fa_requires (pp_as_tuple pp_str)
      exist_names pp_prod exist_types pp_type_expr
      annot.fa_returns pp_constrs annot.fa_ensures
  in
  List.iter pp_spec ast.functions;

  (* Typing proofs. *)
  let pp_proof (id, def) =
    let annot =
      match def.func_annot with
      | Some(annot) -> annot
      | None        -> assert false (* Unreachable. *)
    in
    let (used_globals, used_functions) = def.func_deps in
    let deps =
      (* This includes global variables on which the used function depend. *)
      let fn acc (id, def) =
        if List.mem id used_functions then fst def.func_deps @ acc else acc
      in
      let all_used_globals = List.fold_left fn used_globals ast.functions in
      let transitive_used_globals =
        (* Use filter to preserve definition order. *)
        List.filter (fun x -> List.mem x all_used_globals) ast.global_vars
      in
      transitive_used_globals @ used_functions
    in
    let pp_args ff xs =
      match xs with
      | [] -> ()
      | _  -> fprintf ff " (%a : loc)" (pp_sep " " pp_str) xs
    in
    pp "\n@;(* Typing proof for [%s]. *)@;" id;
    pp "@[<v 2>Lemma type_%s%a :@;" id pp_args deps;
    begin
      match used_functions with
      | [] -> pp "⊢ typed_function impl_%s type_of_%s." id id
      | _  ->
      let pp_impl ff id =
        let wrap = used_globals <> [] || used_functions <> [] in
        if wrap then fprintf ff "(";
        fprintf ff "impl_%s" id;
        List.iter (fprintf ff " %s") used_globals;
        List.iter (fprintf ff " %s") used_functions;
        if wrap then fprintf ff ")"
      in
      let pp_type ff id =
        let used_globals =
          try fst (List.assoc id ast.functions).func_deps
          with Not_found -> assert false (* Unreachable. *)
        in
        if used_globals <> [] then fprintf ff "(";
        fprintf ff "type_of_%s" id;
        List.iter (fprintf ff " %s") used_globals;
        if used_globals <> [] then fprintf ff ")"
      in
      let pp_dep f = pp "%s ◁ᵥ %s @@ function_ptr %a -∗@;" f f pp_type f in
      List.iter pp_dep used_functions;
      pp "typed_function %a %a." pp_impl id pp_type id
    end;
    let pp_intros ff xs =
      let pp_intro ff (x,_) = pp_str ff x in
      match xs with
      | []      -> fprintf ff "[]"
      | [x]     -> pp_intro ff x
      | x :: xs -> List.iter (fun _ -> pp_str ff "[") xs;
                   pp_intro ff x;
                   List.iter (fprintf ff " %a]" pp_intro) xs
    in
    pp "@]@;@[<v 2>Proof.@;";
    pp "start_function (%a)" pp_intros annot.fa_parameters;
    if def.func_vars <> [] || def.func_args <> [] then
      begin
        pp " =>";
        List.iter (fun (x,_) -> pp " arg_%s" x) def.func_args;
        List.iter (fun (x,_) -> pp " local_%s" x) def.func_vars
      end;
    pp ".@;split_blocks (∅ : gmap block_id (iProp Σ)).";
    pp "@;repeat do_step; do_finish.";
    pp "@;Unshelve. all: try solve_goal.";
    pp "@]@;Qed."
  in
  List.iter pp_proof ast.functions;

  (* Closing the section. *)
  pp "@]@;End spec.@]"

type mode = Code | Spec

let write : import list -> mode -> string -> Coq_ast.t -> unit =
    fun imports mode fname ast ->
  let oc = open_out fname in
  let ff = Format.formatter_of_out_channel oc in
  let pp = match mode with Code -> pp_code | Spec -> pp_spec in
  Format.fprintf ff "%a@." (pp imports) ast;
  close_out oc
