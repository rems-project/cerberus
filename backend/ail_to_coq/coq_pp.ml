open Format
open Extra
open Panic
open Coq_ast
open Rc_annot

(* Flags set by CLI. *)
let print_expr_locs = ref true
let print_stmt_locs = ref true

let pp_str = pp_print_string

let pp_as_tuple : 'a pp -> 'a list pp = fun pp ff xs ->
  match xs with
  | []      -> pp_str ff "()"
  | [x]     -> pp ff x
  | x :: xs -> fprintf ff "(%a" pp x;
               List.iter (fprintf ff ", %a" pp) xs;
               pp_str ff ")"

let pp_encoded_patt_name : string list pp = fun ff xs ->
  match xs with
  | []  -> pp_str ff "_"
  | [x] -> pp_str ff x
  | _   -> pp_str ff "patt__"

(* Print projection to get the [i]-th element of a tuple with [n] elements. *)
let rec pp_projection : int -> int pp = fun n ff i ->
  match n with
  | 1                -> ()
  | _ when i = n - 1 -> fprintf ff ".2"
  | _                -> fprintf ff ".1%a" (pp_projection (n - 1)) i

let pp_encoded_patt_bindings : string list pp = fun ff xs ->
  let nb = List.length xs in
  if nb <= 1 then () else
  let pp_let i x =
    fprintf ff "let %s := patt__%a in@;" x (pp_projection nb) i
  in
  List.iteri pp_let xs

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

let rec pp_layout : bool -> Coq_ast.layout pp = fun wrap ff layout ->
  let pp fmt = Format.fprintf ff fmt in
  match layout with
  | LVoid              -> pp "LVoid"
  | LPtr               -> pp "LPtr"
  | _ when wrap        -> pp "(%a)" (pp_layout false) layout
  | LStruct(id, false) -> pp "layout_of struct_%s" id
  | LStruct(id, true ) -> pp "ul_layout union_%s" id
  | LInt(i)            -> pp "it_layout %a" pp_int_type i
  | LArray(layout, n)  -> pp "al_layout (mk_array_layout %a %s)" (pp_layout true) layout n

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
  let pp_expr_body ff e =
    match Location.(e.elt) with
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
    | Val(SizeOf(ly))                ->
        pp "i2v (%a).(ly_size) %a" (pp_layout false) ly pp_int_type (ItSize_t false)
    | UnOp(op,ty,e)                 ->
        pp "UnOp %a (%a) (%a)" pp_un_op op pp_op_type ty pp_expr e
    | BinOp(op,ty1,ty2,e1,e2)       ->
        begin
          match (ty1, ty2, op) with
          | (OpPtr(l), OpInt(_), AddOp) ->
              pp "(%a) at_offset{%a, PtrOp, %a} (%a)" pp_expr e1
                (pp_layout false) l pp_op_type ty2 pp_expr e2
          | (OpPtr(_), OpInt(_), _) ->
              panic_no_pos "Binop [%a] not supported on pointers."
                pp_bin_op op
          | (OpInt(_), OpPtr(_), _) ->
              panic_no_pos "Wrong ordering of integer pointer binop [%a]."
                pp_bin_op op
          | _                 ->
              pp "(%a) %a{%a, %a} (%a)" pp_expr e1 pp_bin_op op
                pp_op_type ty1 pp_op_type ty2 pp_expr e2
        end
    | Deref(atomic,lay,e)           ->
        if atomic then panic_no_pos "Operations on atomics not supported.";
        pp "!{%a} (%a)" (pp_layout false) lay pp_expr e
    | CAS(ty,e1,e2,e3)              ->
        pp "CAS@ (%a)@ (%a)@ (%a)@ (%a)" pp_op_type ty
          pp_expr e1 pp_expr e2 pp_expr e3
    | SkipE(e)                      ->
        pp "SkipE (%a)" pp_expr e
    | Use(atomic,lay,e)             ->
        if atomic then panic_no_pos "Operations on atomics not supported.";
        pp "use{%a} (%a)" (pp_layout false) lay pp_expr e
    | AddrOf(e)                     ->
        pp "&(%a)" pp_expr e
    | GetMember(e,name,false,field) ->
        pp "(%a) at{struct_%s} %S" pp_expr e name field
    | GetMember(e,name,true ,field) ->
        pp "(%a) at_union{union_%s} %S" pp_expr e name field
    | AnnotExpr(i,coq_e,e)          ->
        pp "AnnotExpr %i%%nat %a (%a)" i (pp_coq_expr true) coq_e pp_expr e
    | Struct(id, fs)                ->
        pp "@[@[<hov 2>Struct struct_%s [" id;
        let fn i (id, e) =
          let s = if i = List.length fs - 1 then "" else " ;" in
          pp "@;(%S, %a)%s" id pp_expr e s
        in
        List.iteri fn fs;
        pp "@]@;]@]"
  in
  match Location.get e.loc with
  | Some(d) when !print_expr_locs ->
      pp "LocInfoE loc_%i (%a)" d.loc_key pp_expr_body e
  | _                             ->
      pp "%a" pp_expr_body e

let rec pp_stmt : Coq_ast.stmt pp = fun ff stmt ->
  let pp fmt = Format.fprintf ff fmt in
  if !print_stmt_locs then
    begin
      match Location.get stmt.loc with
      | None    -> ()
      | Some(d) -> pp "locinfo: loc_%i ;@;" d.loc_key
    end;
  match stmt.elt with
  | Goto(id)                      ->
      pp "Goto %S" id
  | Return(e)                     ->
      pp "Return @[<hov 0>(%a)@]" pp_expr e
  | Assign(atomic,lay,e1,e2,stmt) ->
      if atomic then panic_no_pos "Operations on atomics not supported.";
      pp "@[<hov 2>%a <-{ %a }@ %a ;@]@;%a"
        pp_expr e1 (pp_layout false) lay pp_expr e2 pp_stmt stmt
  | Call(ret_id,e,es,stmt)        ->
      let pp_args _ es =
        let n = List.length es in
        let fn i e =
          pp (if i = n - 1 then "%a" else "%a ;@;") pp_expr e
        in
        List.iteri fn es
      in
      pp "@[<hov 2>%S <- %a with@ [ %a ] ;@]@;%a"
        (Option.get "_" ret_id) pp_expr e pp_args es pp_stmt stmt
  | SkipS(stmt)                   ->
      pp_stmt ff stmt
  | If(e,stmt1,stmt2)             ->
      pp "if: @[<hov 0>%a@]@;then@;@[<v 2>%a@]@;else@;@[<v 2>%a@]"
        pp_expr e pp_stmt stmt1 pp_stmt stmt2
  | Assert(e, stmt)               ->
      pp "assert: (%a) ;@;%a" pp_expr e pp_stmt stmt
  | ExprS(annot, e, stmt)         ->
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

  (* Printing of location data. *)
  if !print_expr_locs || !print_stmt_locs then
    begin
      let (all_locations, all_files) =
        let open Location in
        let locs = ref [] in
        let files = ref [] in
        let fn ({loc_file = file; _} as d) =
          locs := d :: !locs;
          if not (List.mem file !files) then files := file :: !files
        in
        Location.Pool.iter fn coq_locs;
        let locs = List.sort (fun d1 d2 -> d1.loc_key - d2.loc_key) !locs in
        let files = List.mapi (fun i s -> (s, i)) !files in
        (locs, files)
      in
      let pp_file_def (file, key) =
        fprintf ff "@;Definition file_%i : string := \"%s\"." key file
      in
      List.iter pp_file_def all_files;
      let pp_loc_def d =
        let open Location in
        pp "@;Definition loc_%i : location_info := " d.loc_key;
        pp "LocationInfo file_%i %i %i %i %i."
          (List.assoc d.loc_file all_files)
          d.loc_line1 d.loc_col1 d.loc_line2 d.loc_col2
      in
      List.iter pp_loc_def all_locations;
    end;

  (* Printing for struct/union members. *)
  let pp_members members =
    let n = List.length members in
    let fn i (id, (attrs, layout)) =
      let sc = if i = n - 1 then "" else ";" in
      pp "@;(%S, %a)%s" id (pp_layout false) layout sc
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
  let pp_function_def (id, def) =
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
        pp "@;(%S, %a)%s" id (pp_layout false) layout sc
      in
      List.iteri fn def.func_args
    end;
    pp "@]@;];@;";

    pp "@[<v 2>f_local_vars := [";
    begin
      let n = List.length def.func_vars in
      let fn i (id, layout) =
        let sc = if i = n - 1 then "" else ";" in
        pp "@;(%S, %a)%s" id (pp_layout false) layout sc
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
  let pp_function (id, def_or_decl) =
    match def_or_decl with
    | FDef(def) -> pp_function_def (id, def)
    | _         -> ()
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

let pp_type_annot : coq_expr option pp = fun ff eo ->
  Option.iter (fprintf ff " : %a" (pp_coq_expr false)) eo

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
  | Constr_Coq(e)       ->
      fprintf ff "⌜%a⌝" (pp_coq_expr false) e
  (* Apply wrapping. *)
  | _ when wrap         ->
      fprintf ff "(%a)" (pp_constr false) c
  (* No need for wrappin now. *)
  | Constr_Iris(s)      ->
      pp_str ff s
  | Constr_exist(x,a,c) ->
      fprintf ff "∃ %s%a, %a" x pp_type_annot a (pp_constr false) c
  | Constr_own(x,k,ty)  ->
      fprintf ff "%s %a %a" x pp_kind k pp_type_expr ty

and pp_type_expr_guard : unit pp option -> guard_mode -> type_expr pp =
    fun pp_dots guard ff ty ->
  let pp_constr = pp_constr_guard pp_dots guard in
  let pp_kind ff k =
    match k with
    | Own     -> pp_str ff "&own"
    | Shr     -> pp_str ff "&shr"
    | Frac(e) -> fprintf ff "&frac{%a}" (pp_coq_expr false) e
  in
  let rec pp wrap rfnd ff ty =
    match ty with
    (* Don't need explicit wrapping. *)
    | Ty_Coq(e)          -> (pp_coq_expr wrap) ff e
    | Ty_params(id,[])   -> pp_str ff id
    (* Always wrapped. *)
    | Ty_lambda(xs,a,ty) ->
        fprintf ff "(λ %a%a,@;  @[<v 0>%a%a@]@;)" pp_encoded_patt_name xs
          pp_type_annot a pp_encoded_patt_bindings xs (pp false false) ty
    (* Remaining constructors (no need for explicit wrapping). *)
    | Ty_dots            ->
        begin
          match pp_dots with
          | None     -> Panic.panic_no_pos "Unexpected ellipsis."
          | Some(pp) ->
          fprintf ff (if wrap then "(@;  %a@;)" else "%a") pp ()
        end
    (* Insert wrapping if needed. *)
    | _ when wrap        -> fprintf ff "(%a)" (pp false rfnd) ty
    | Ty_refine(e,ty)    ->
        begin
          let normal () =
            fprintf ff "%a @@ %a" (pp_coq_expr true) e (pp true true) ty
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
    | Ty_ptr(k,ty)       -> fprintf ff "%a %a" pp_kind k (pp true false) ty
    | Ty_exists(x,a,ty)  ->
        fprintf ff "tyexists (λ %s%a, %a)" x pp_type_annot a
          (pp false false) ty
    | Ty_constr(ty,c)    ->
        fprintf ff "constrained %a %a" (pp true false) ty (pp_constr true) c
    | Ty_params(id,tys)  ->
        match id with
        | "optional" when not rfnd ->
            let ty =
              match tys with [ty] -> ty | _    ->
              Panic.panic_no_pos "[%s] expects exactly one argument." id
            in
            let ty = Ty_lambda([], Some(Coq_ident("unit")), ty) in
            fprintf ff "optionalO %a null" (pp true false) ty
        | "optional" | "optionalO" ->
            let ty =
              match tys with [ty] -> ty | _    ->
              Panic.panic_no_pos "[%s] expects exactly one argument." id
            in
            fprintf ff "%s %a null" id (pp true false) ty
        | "struct"                 ->
            let (ty, tys) =
              match tys with ty :: tys -> (ty, tys) | [] ->
              Panic.panic_no_pos "[%s] expects at least one argument." id
            in
            fprintf ff "struct %a [@@{type} %a ]" (pp true false) ty
              (pp_sep " ; " (pp false false)) tys
        | _                        ->
            pp_str ff id;
            List.iter (fprintf ff " %a" (pp true false)) tys
  in
  pp true false ff ty

let pp_type_expr = pp_type_expr_guard None Guard_none
let pp_constr = pp_constr_guard None Guard_none true

let pp_constrs : constr list pp = fun ff cs ->
  match cs with
  | []      -> pp_str ff "True"
  | c :: cs -> pp_constr ff c; List.iter (fprintf ff " ∗ %a" pp_constr) cs

let gather_fields s_id s =
  let fn (x, (ty_opt, layout)) =
    match ty_opt with
    | Some(Some(ty)) -> (x, ty, layout)
    | Some(None)     ->
        Panic.panic_no_pos "Weird error on field [%s] of struct [%s]." x s_id
    | None           ->
    Panic.panic_no_pos
      "Annotation on field [%s] (struct [%s])] is invalid." x s_id
  in
  List.map fn s.struct_members

let rec pp_struct_def_np structs guard annot fields ff id =
  let pp fmt = fprintf ff fmt in
  (* Print the part that may stand for dots in case of "ptr_type". *)
  let pp_dots ff () =
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
    let pp fmt = fprintf ff fmt in
    (* Printing the "padded". *)
    Option.iter (fun _ -> pp "padded (") annot.st_size;
    (* Printing the struct fields. *)
    pp "struct struct_%s [@@{type}" id;
    let pp_field ff (_, ty, layout) =
      match layout with
      | LStruct(s_id, false) ->
          let (s, structs) =
            try (List.assoc s_id structs, List.remove_assoc s_id structs)
            with Not_found -> Panic.panic_no_pos "Unknown struct [%s]." s_id
          in
          let annot =
            match s.struct_annot with
            | Some(annot) -> annot
            | None        ->
            Panic.panic_no_pos "Annotations on struct [%s] are invalid." s_id
          in
          if annot = no_struct_annot then
            (* Fall back to normal printing in case of unannotated struct. *)
            pp_type_expr_guard None guard ff ty
          else
          let annot =
            match annot.st_ptr_type with
            | None    -> {annot with st_ptr_type = Some((s_id,ty))}
            | Some(_) ->
            Panic.panic_no_pos "[rc::ptr_type] in nested struct [%s]." s_id
          in
          let fields = gather_fields s_id s in
          pp "(%a)" (pp_struct_def_np structs Guard_none annot fields) s_id
      | LStruct(_   , true ) -> assert false (* TODO *)
      | _                    -> pp_type_expr_guard None guard ff ty
    in
    begin
      match fields with
      | []              -> ()
      | field :: fields ->
      reset_nroot_counter ();
      pp "@;%a" pp_field field;
      List.iter (pp " ;@;%a" pp_field) fields
    end;
    pp "@]@;]"; (* Close box for struct fields. *)
    Option.iter (pp ") struct_%s %a" id (pp_coq_expr true)) annot.st_size;
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
    pp "@]"
  in
  match annot.st_ptr_type with
  | None        -> pp_dots ff ()
  | Some(_, ty) -> pp_type_expr_guard (Some(pp_dots)) Guard_none ff ty

(* Wrapper to print pattern desugaring. *)
let pp_struct_def ref_names structs guard annot fields ff id =
  pp_encoded_patt_bindings ff ref_names;
  pp_struct_def_np structs guard annot fields ff id

(* Functions for looking for recursive occurences of a type. *)

let in_coq_expr : string -> coq_expr -> bool = fun s e ->
  match e with
  | Coq_ident(x) -> x = s
  | Coq_all(e)   -> e = s (* In case of [{s}]. *)

let in_type_annot : string -> coq_expr option -> bool = fun s a ->
  match a with
  | None    -> false
  | Some(e) -> in_coq_expr s e

let in_patt : string -> pattern -> bool = List.mem

let rec in_type_expr : string -> type_expr -> bool = fun s ty ->
  match ty with
  | Ty_refine(e,ty)   -> in_coq_expr s e || in_type_expr s ty
  | Ty_ptr(_,ty)      -> in_type_expr s ty
  | Ty_dots           -> false
  | Ty_exists(x,a,ty) -> in_type_annot s a || (x <> s && in_type_expr s ty)
  | Ty_lambda(p,a,ty) -> in_type_annot s a ||
                         (not (in_patt s p) && in_type_expr s ty)
  | Ty_constr(ty,c)   -> in_type_expr s ty || in_constr s c
  | Ty_params(x,tys)  -> x = s || List.exists (in_type_expr s) tys
  | Ty_Coq(e)         -> in_coq_expr s e

and in_constr : string -> constr -> bool = fun s c ->
  match c with
  | Constr_Coq(e)       -> in_coq_expr s e
  | Constr_Iris(s)      -> false
  | Constr_exist(x,a,c) -> in_type_annot s a || (x <> s && in_constr s c)
  | Constr_own(_,_,ty)  -> in_type_expr s ty

let collect_invs : func_def -> (string * block_annot) list = fun def ->
  let fn id (annot, _) acc =
    match annot with
    | Some(annot) when annot = no_block_annot -> acc
    | Some(annot)                             -> (id, annot) :: acc
    | None                                    ->
    Panic.panic_no_pos "Bad block annotation in function [%s]." def.func_name
  in
  SMap.fold fn def.func_blocks []

let pp_spec : import list -> string list -> Coq_ast.t pp =
    fun imports ctxt ff ast ->
  (* Stuff for import of the code. *)
  let basename =
    let name = Filename.basename ast.source_file in
    try Filename.chop_extension name with Invalid_argument(_) -> name
  in
  let import_path = "refinedc" in (* FIXME generic? Do something smarter? *)

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
  pp "Context `{!typeG Σ} `{!globalG Σ}.";
  List.iter (pp "@;%s.") ctxt;

  (* Definition of types. *)
  let pp_struct (struct_id, s) =
    let annot =
      match s.struct_annot with
      | Some(annot) -> annot
      | None        ->
      Panic.panic_no_pos "Annotations on struct [%s] are invalid." struct_id
    in
    (* Check if a type must be generated. *)
    if annot.st_refined_by = [] && annot.st_ptr_type = None then () else
    (* Gather the field annotations. *)
    let fields = gather_fields struct_id s in
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
    pp "\n@;(* Definition of type [%s]. *)@;" id;
    let is_rec = List.exists (fun (_,ty, _) -> in_type_expr id ty) fields in
    let pp_prod = pp_as_prod (pp_coq_expr true) in
    if is_rec then begin
      pp "@[<v 2>Definition %s_rec %a:" id pp_params params;
      pp " (%a -d> typeO) → (%a -d> typeO) := " pp_prod
        ref_types (pp_as_prod (pp_coq_expr true)) ref_types;
      pp "(λ self %a,@;" pp_encoded_patt_name ref_names;
      let guard = Guard_in_def(id) in
      pp_struct_def ref_names ast.structs guard annot fields ff struct_id;
      pp "@]@;)%%I.@;Typeclasses Opaque %s_rec.\n" id;

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
      pp "@[<v 2>(%a @@ %a)%%I ≡@@{type} (@;" (pp_as_tuple pp_str) ref_names
        (pp_id_args false id) param_names;
      let guard = Guard_in_lem(id) in
      pp_struct_def_np ast.structs guard annot fields ff struct_id;
      pp "@]@;)%%I.@]@;";
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
      pp "rty %a := (@;  @[<v 0>%a@]@;)%%I" pp_encoded_patt_name ref_names
        (pp_struct_def ref_names ast.structs Guard_none annot fields) id;
      pp "@]@;|}.\n";
      (* Typeclass stuff. *)
      pp "@;Global Instance %s_movable %a:" id pp_params params;
      pp " RMovable %a." (pp_id_args true id) param_names;
      pp "@;Proof. solve_rmovable. Defined."
    end
  in
  let pp_union (id, _) =
    pp "\n@;(* Printing for Unions not implemented [%s]. *)" id (* TODO *)
  in
  let pp_struct_union ((_, {struct_is_union; struct_name; _}) as s) =
    if struct_is_union then pp_union s else pp_struct s
  in
  List.iter pp_struct_union ast.structs;

  (* Function specs. *)
  let pp_spec (id, def_or_decl) =
    pp "\n@;(* Specifications for function [%s]. *)" id;
    let annot =
      match def_or_decl with
      | FDef({func_annot=Some(annot); _}) -> annot
      | FDec(Some(annot))                 -> annot
      | _                                 ->
      Panic.panic_no_pos "Annotations on function [%s] are invalid." id
    in
    let (param_names, param_types) = List.split annot.fa_parameters in
    let (exist_names, exist_types) = List.split annot.fa_exists in
    let pp_args ff tys =
      match tys with
      | [] -> ()
      | _  -> pp "; "; pp_sep ", " pp_type_expr ff tys
    in
    pp "@;Definition type_of_%s :=@;  @[<hov 2>" id;
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
    pp "\n@;(* Typing proof for [%s]. *)@;" id;
    if annot.fa_trust_me then
      pp "(* Let's skip that, you seem to have some faith. *)"
    else
    let (used_globals, used_functions) = def.func_deps in
    let deps =
      used_globals @ used_functions
    in
    let pp_args ff xs =
      match xs with
      | [] -> ()
      | _  -> fprintf ff " (%a : loc)" (pp_sep " " pp_str) xs
    in
    pp "@[<v 2>Lemma type_%s%a :@;" id pp_args deps;
    begin
      let prefix = if used_functions = [] then "⊢ " else "" in
      let pp_impl ff id =
        let wrap = used_globals <> [] || used_functions <> [] in
        if wrap then fprintf ff "(";
        fprintf ff "impl_%s" id;
        List.iter (fprintf ff " %s") used_globals;
        List.iter (fprintf ff " %s") used_functions;
        if wrap then fprintf ff ")"
      in
      let pp_global f = pp "global_locs !! \"%s\" = Some %s →@;" f f in
      List.iter pp_global used_globals;
      let pp_global_type f =
        match List.find_opt (fun (name, _) -> name = f) ast.global_vars with
        | Some (_, Some ty) -> pp "global_initialized_types !! \"%s\" = Some (%a : type) →@;" f (pp_type_expr_guard None Guard_none) ty
        | _ -> ()
      in
      List.iter pp_global_type used_globals;
      let pp_dep f = pp "%s ◁ᵥ %s @@ function_ptr type_of_%s -∗@;" f f f in
      List.iter pp_dep used_functions;
      pp "%styped_function %a type_of_%s." prefix pp_impl id id
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
    pp "start_function \"%s\" (%a)" id pp_intros annot.fa_parameters;
    if def.func_vars <> [] || def.func_args <> [] then
      begin
        pp " =>";
        List.iter (fun (x,_) -> pp " arg_%s" x) def.func_args;
        List.iter (fun (x,_) -> pp " local_%s" x) def.func_vars
      end;
    pp ".@;@[<v 2>split_blocks ((";
    let pp_inv (id, annot) =
      (* Opening a box and printing the existentials. *)
      pp "@;@[<v 2><[ \"%s\" :=" id;
      let pp_exists (id, e) = pp "@;∃ %s : %a," id (pp_coq_expr false) e in
      List.iter pp_exists annot.bl_exists;
      (* Compute the used and unused arguments and variables. *)
      let used =
        let fn (id, ty) =
          (* Check if [id_var] is a function argument. *)
          try
            let layout = List.assoc id def.func_args in
            (* Check for name clash with local variables. *)
            if List.mem_assoc id def.func_vars then
              Panic.panic_no_pos "[%s] denotes both an argument and a local \
                variable of function [%s]." id def.func_name;
            ("arg_" ^ id, (layout, Some(ty)))
          with Not_found ->
          (* Not a function argument, check that it is a local variable. *)
          try
            let layout = List.assoc id def.func_vars in
            ("local_" ^ id, (layout, Some(ty)))
          with Not_found ->
            Panic.panic_no_pos "[%s] is neither a local variable nor an \
              argument." id
        in
        List.map fn annot.bl_inv_vars
      in
      let unused =
        let unused_args =
          let pred (id, _) =
            let id = "arg_" ^ id in
            List.for_all (fun (id_var, _) -> id <> id_var) used
          in
          let args = List.filter pred def.func_args in
          List.map (fun (id, layout) -> ("arg_" ^ id, layout)) args
        in
        let unused_vars =
          let pred (id, _) =
            let id = "local_" ^ id in
            List.for_all (fun (id_var, _) -> id <> id_var) used
          in
          let vars = List.filter pred def.func_vars in
          List.map (fun (id, layout) -> ("local_" ^ id, layout)) vars
        in
        let unused = unused_args @ unused_vars in
        List.map (fun (id, layout) -> (id, (layout, None))) unused
      in
      let all_vars = unused @ used in
      let pp_var ff (id, (layout, ty_opt)) =
        match ty_opt with
        | None     -> fprintf ff "%s ◁ₗ uninit %a" id (pp_layout true) layout
        | Some(ty) -> fprintf ff "%s ◁ₗ %a" id pp_type_expr ty
      in
      begin
        match (all_vars, annot.bl_constrs) with
        | ([]     , []     ) ->
            Panic.panic_no_pos "Ill-formed block annotation in function [%s]."
              def.func_name
        | ([]     , c :: cs) ->
            pp "@;%a" pp_constr c;
            List.iter (pp " ∗@;%a" pp_constr) cs
        | (v :: vs, cs     ) ->
            pp "@;%a" pp_var v;
            List.iter (pp " ∗@;%a" pp_var) vs;
            List.iter (pp " ∗@;%a" pp_constr) cs
      end;
      (* Closing the box. *)
      pp "@]@;]> $"
    in
    let invs = collect_invs def in
    List.iter pp_inv invs;
    pp "@;∅@]@;)%%I : gmap block_id (iProp Σ)).";
    let pp_do_step id =
      pp "@;- repeat do_step; do_finish.";
      pp "@;  all: print_typesystem_goal \"%s\" \"%s\"." def.func_name id
    in
    List.iter pp_do_step (List.cons "#0" (List.map fst invs));
    pp "@;Unshelve. all: prepare_sideconditions; try solve_goal.";
    let tactics_items =
      let is_all t = String.length t >= 4 && String.sub t 0 4 = "all:" in
      let rec pp_tactics_all tactics =
        match tactics with
        | t :: ts when is_all t -> pp "@;%s" t; pp_tactics_all ts
        | ts                    -> ts
      in
      pp_tactics_all annot.fa_tactics
    in
    List.iter (pp "@;+ %s") tactics_items;
    pp "@;all: print_sidecondition_goal \"%s\"." def.func_name;
    pp "@]@;Qed."
  in
  let pp_proof (id, def_or_decl) =
    match def_or_decl with
    | FDef(def) -> pp_proof (id, def)
    | FDec(_)   -> ()
  in
  List.iter pp_proof ast.functions;

  (* Closing the section. *)
  pp "@]@;End spec.@]"

type mode =
  | Code of import list
  | Spec of import list * string list

let write : mode -> string -> Coq_ast.t -> unit = fun mode fname ast ->
  let oc = open_out fname in
  let ff = Format.formatter_of_out_channel oc in
  let pp =
    match mode with
    | Code(imports)       -> pp_code imports
    | Spec(imports, ctxt) -> pp_spec imports ctxt
  in
  Format.fprintf ff "%a@." pp ast;
  close_out oc
