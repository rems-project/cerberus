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

let pp_simple_coq_expr wrap ff coq_e =
  match coq_e with
  | Coq_ident(x)             -> pp_str ff x
  | Coq_all([Quot_plain(s)]) -> fprintf ff (if wrap then "(%s)" else "%s") s
  | _                        ->
  Panic.panic_no_pos "Antiquotation forbidden here." (* FIXME location *)

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
  | LArray(layout, n)  -> pp "mk_array_layout %a %s"
                            (pp_layout true) layout n

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
        pp "i2v (%a).(ly_size) %a" (pp_layout false) ly
          pp_int_type (ItSize_t false)
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
        if atomic then panic_no_pos "Deref on atomics not supported.";
        pp "!{%a} (%a)" (pp_layout false) lay pp_expr e
    | CAS(ty,e1,e2,e3)              ->
        pp "CAS@ (%a)@ (%a)@ (%a)@ (%a)" pp_op_type ty
          pp_expr e1 pp_expr e2 pp_expr e3
    | SkipE(e)                      ->
        pp "SkipE (%a)" pp_expr e
    | Use(atomic,lay,e)             ->
        if atomic then panic_no_pos "Use on atomics not supported.";
        pp "use{%a} (%a)" (pp_layout false) lay pp_expr e
    | AddrOf(e)                     ->
        pp "&(%a)" pp_expr e
    | GetMember(e,name,false,field) ->
        pp "(%a) at{struct_%s} %S" pp_expr e name field
    | GetMember(e,name,true ,field) ->
        pp "(%a) at_union{union_%s} %S" pp_expr e name field
    | AnnotExpr(i,coq_e,e)          ->
        pp "AnnotExpr %i%%nat %a (%a)" i
          (pp_simple_coq_expr true) coq_e pp_expr e
    | Struct(id, fs)                ->
        pp "@[@[<hov 2>StructInit struct_%s [" id;
        let fn i (id, e) =
          let s = if i = List.length fs - 1 then "" else " ;" in
          pp "@;(%S, %a : expr)%s" id pp_expr e s
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
  | Switch(it,e,map,bs,def)       ->
      pp "@[<v 2>Switch %a@;" pp_int_type it;
      pp "(%a)@;" pp_expr e;
      begin
        match map with
        | []         -> pp "∅@;"
        | (k,v)::map ->
        pp "@[<v 2>(@;<[ %s := %i%%nat ]> " k v;
        List.iter (fun (k,v) -> pp "$@;<[ %s := %i%%nat ]> " k v) map;
        pp "∅@]@;)@;"
      end;
      begin
        match bs with
        | []    -> pp "[]@;"
        | b::bs ->
        pp "@[<v 2>(@;(%a)" pp_stmt b;
        List.iter (pp " ::@;(%a)" pp_stmt) bs;
        pp " :: []@]@;)@;"
      end;
      pp "(%a)@]" pp_stmt def
  | Assign(atomic,lay,e1,e2,stmt) ->
      let order = if atomic then ", ScOrd" else "" in
      pp "@[<hov 2>%a <-{ %a%s }@ %a ;@]@;%a"
        pp_expr e1 (pp_layout false) lay order pp_expr e2 pp_stmt stmt
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
  let pp_members members is_struct =
    let nb_bytes = ref 0 in
    let n = List.length members in
    let fn i (id, (attrs, (align, size), layout)) =
      (* Insert padding for field alignment (for structs). *)
      if is_struct && !nb_bytes mod align <> 0 then
        begin
          let pad = align - !nb_bytes mod align in
          pp "@;(None, mk_layout %i%%nat 0%%nat);" pad;
          nb_bytes := !nb_bytes + pad;
        end;
      let sc = if i = n - 1 then "" else ";" in
      let some = if is_struct then "Some " else "" in
      pp "@;(%s%S, %a)%s" some id (pp_layout false) layout sc;
      nb_bytes := !nb_bytes + size
    in
    List.iteri fn members;
    (* Insert final padding if necessary. *)
    if is_struct then
      begin
        let max_align =
          let fn acc (_,(_,(align,_),_)) = max acc align in
          List.fold_left fn 1 members
        in
        let r = !nb_bytes mod max_align in
        if r <> 0 then pp ";@;(None, mk_layout %i%%nat 0%%nat)" (max_align - r)
      end
  in

  (* Definition of structs/unions. *)
  let pp_struct (id, decl) =
    pp "\n@;(* Definition of struct [%s]. *)@;" id;
    pp "@[<v 2>Program Definition struct_%s := {|@;" id;

    pp "@[<v 2>sl_members := [";
    pp_members decl.struct_members true;
    pp "@]@;];@]@;|}.@;";
    pp "Solve Obligations with solve_struct_obligations."
  in
  let pp_union (id, decl) =
    pp "\n@;(* Definition of union [%s]. *)@;" id;
    pp "@[<v 2>Program Definition union_%s := {|@;" id;

    pp "@[<v 2>ul_members := [";
    pp_members decl.struct_members false;
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

let rec pp_quoted : type_expr pp -> type_expr quoted pp = fun pp_ty ff l ->
  let pp_quoted_elt ff e =
    match e with
    | Quot_plain(s) -> pp_str ff s
    | Quot_anti(ty) -> fprintf ff "(%a)" pp_ty ty
  in
  match l with
  | []     -> assert false (* Unreachable. *)
  | [e]    -> pp_quoted_elt ff e
  | e :: l -> fprintf ff "%a " pp_quoted_elt e; pp_quoted pp_ty ff l

and pp_coq_expr : bool -> type_expr pp -> coq_expr pp = fun wrap pp_ty ff e ->
  match e with
  | Coq_ident(x) -> pp_str ff x
  | Coq_all(l)   ->
      fprintf ff (if wrap then "(%a)" else "%a") (pp_quoted pp_ty) l

and pp_type_annot : type_expr pp -> coq_expr option pp = fun pp_ty ff eo ->
  Option.iter (fprintf ff " : %a" (pp_coq_expr false pp_ty)) eo

and pp_constr_guard : unit pp option -> guard_mode -> bool -> constr pp =
    fun pp_dots guard wrap ff c ->
  let pp_ty = pp_type_expr_guard pp_dots guard in
  let pp_coq_expr wrap = pp_coq_expr wrap pp_ty in
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
  | Constr_Iris(l)      ->
      pp_quoted pp_ty ff l
  | Constr_exist(x,a,c) ->
      fprintf ff "∃ %s%a, %a" x (pp_type_annot pp_ty) a (pp_constr false) c
  | Constr_own(x,k,ty)  ->
      fprintf ff "%s %a %a" x pp_kind k pp_ty ty

and pp_type_expr_guard : unit pp option -> guard_mode -> type_expr pp =
    fun pp_dots guard ff ty ->
  let pp_constr = pp_constr_guard pp_dots guard in
  let rec pp_kind ff k =
    match k with
    | Own     -> pp_str ff "&own"
    | Shr     -> pp_str ff "&shr"
    | Frac(e) -> fprintf ff "&frac{%a}"
                   (pp_coq_expr false (pp false false false)) e
  and pp_ty_annot ff a =
    pp_type_annot (pp false false false) ff a
  and pp wrap rfnd guarded ff ty =
    let pp_coq_expr wrap = pp_coq_expr wrap (pp false rfnd guarded) in
    match ty with
    (* Don't need explicit wrapping. *)
    | Ty_Coq(e)          -> (pp_coq_expr wrap) ff e
    (* Remaining constructors (no need for explicit wrapping). *)
    | Ty_dots            ->
        begin
          match pp_dots with
          | None     -> Panic.panic_no_pos "Unexpected ellipsis."
          | Some(pp) ->
          fprintf ff (if wrap then "(@;  %a@;)" else "%a") pp ()
        end
    (* Insert wrapping if needed. *)
    | _ when wrap        -> fprintf ff "(%a)" (pp false rfnd guarded) ty
    | Ty_refine(e,ty)    ->
        begin
          match (guard, ty) with
          | (Guard_in_def(s), Ty_params(c,tys)) when c = s ->
              if not guarded then fprintf ff "guarded (%a) (" with_uid s;
              fprintf ff "apply_dfun self (%a" (pp_coq_expr true) e;
              List.iter (fprintf ff ", %a" (pp_arg true guarded)) tys;
              fprintf ff ")"; if not guarded then fprintf ff ")"
          | (Guard_in_lem(s), Ty_params(c,tys)) when c = s ->
              if not guarded then fprintf ff "guarded %a (" with_uid s;
              fprintf ff "%a @@ " (pp_coq_expr true) e;
              if tys <> [] then pp_str ff "(";
              pp_str ff c;
              List.iter (fprintf ff " %a" (pp_arg true guarded)) tys;
              if tys <> [] then pp_str ff ")";
              if not guarded then fprintf ff ")"
          | (_              , _               )            ->
              fprintf ff "%a @@ %a" (pp_coq_expr true) e
                (pp true true guarded) ty
        end
    | Ty_ptr(k,ty)       ->
        fprintf ff "%a %a" pp_kind k (pp true false guarded) ty
    | Ty_exists(xs,a,ty) ->
        fprintf ff "tyexists (λ %a%a, %a%a)" pp_encoded_patt_name xs
          pp_ty_annot a pp_encoded_patt_bindings xs
          (pp false false guarded) ty
    | Ty_constr(ty,c)    ->
        fprintf ff "constrained %a %a" (pp true false guarded) ty
          (pp_constr true) c
    | Ty_params(id,tyas) ->
        let default () =
          pp_str ff id;
          List.iter (fprintf ff " %a" (pp_arg true guarded)) tyas
        in
        match guard with
        | Guard_in_def(s) when id = s ->
            fprintf ff "tyexists (λ rfmt__, ";
            if not guarded then fprintf ff "guarded (%a) (" with_uid s;
            fprintf ff "apply_dfun self (rfmt__";
            List.iter (fprintf ff ", %a" (pp_arg true guarded)) tyas;
            fprintf ff "))"; if not guarded then fprintf ff ")"
        | Guard_in_lem(s) when id = s ->
            fprintf ff "tyexists (λ rfmt__, rfmt__ @@ ";
            if not guarded then fprintf ff "guarded %a (" with_uid s;
            default (); fprintf ff ")";
            if not guarded then fprintf ff ")"
        | _                           ->
        match id with
        | "optional" when not rfnd ->
            let (tya1, tya2) =
              match tyas with
              | [tya]        -> (tya, Ty_arg_expr(Ty_Coq(Coq_ident("null"))))
              | [tya1; tya2] -> (tya1, tya2)
              | _            ->
                 Panic.panic_no_pos "[%s] expects one or two arguments." id
            in
            let tya1 =
              Ty_arg_lambda([], Some(Coq_ident("unit")), tya1)
            in
            fprintf ff "optionalO %a %a" (pp_arg true guarded) tya1
              (pp_arg true guarded) tya2
        | "optional" | "optionalO" ->
           (match tyas with
           | [tya]        ->
               fprintf ff "%s %a null" id (pp_arg true guarded) tya
           | [tya1; tya2] ->
               fprintf ff "%s %a %a" id (pp_arg true guarded) tya1
                 (pp_arg true guarded) tya2
           | _            ->
               Panic.panic_no_pos "[%s] expects one or two arguments." id)
        | "struct"                 ->
            let (tya, tyas) =
              match tyas with tya :: tyas -> (tya, tyas) | [] ->
              Panic.panic_no_pos "[%s] expects at least one argument." id
            in
            fprintf ff "struct %a [@@{type} %a ]"
              (pp_arg true guarded) tya
              (pp_sep " ; " (pp_arg false guarded)) tyas
        | "guarded"                ->
            let (s, ty) =
              match (guard, tyas) with
              | (Guard_in_def(s), [ty])
              | (Guard_in_lem(s), [ty]) -> (s, ty)
              | (Guard_none     , [_ ]) ->
                  Panic.panic_no_pos "[%s] not expected here." id
              | (_              , _   ) ->
                  Panic.panic_no_pos "[%s] expects exactly one argument." id
            in
            fprintf ff "guarded %a %a" with_uid s (pp_arg true true) ty;
        | _                        ->
            default ()
  and pp_arg wrap guarded ff tya =
    match tya with
    | Ty_arg_expr(ty)         ->
        pp wrap false guarded ff ty
    | Ty_arg_lambda(xs,a,tya) ->
        fprintf ff "(λ %a%a,@;  @[<v 0>%a%a@]@;)" pp_encoded_patt_name xs
          pp_ty_annot a pp_encoded_patt_bindings xs (pp_arg false guarded) tya
  in
  pp true false false ff ty

let pp_type_expr = pp_type_expr_guard None Guard_none
let pp_constr = pp_constr_guard None Guard_none true

let pp_constrs : constr list pp = fun ff cs ->
  match cs with
  | []      -> pp_str ff "True"
  | c :: cs -> pp_constr ff c; List.iter (fprintf ff " ∗ %a" pp_constr) cs

let gather_struct_fields id s =
  let fn (x, (ty_opt, _, layout)) =
    match ty_opt with
    | Some(MA_field(ty)) -> (x, ty, layout)
    | Some(MA_utag(_))
    | Some(MA_none)      ->
        Panic.panic_no_pos "Bad annotation on field [%s] of struct [%s]." x id
    | None           ->
        Panic.panic_no_pos "No annotation on field [%s] of struct [%s]." x id
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
          pp "tyexists (λ %s : %a,@;" x (pp_simple_coq_expr false) e
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
          begin
            match annot with
            | SA_union        ->
                Panic.panic_no_pos "Annotations on struct [%s] are invalid \
                  since it is not a union." s_id
            | SA_tagged_u(_)  ->
                Panic.panic_no_pos "Annotations on struct [%s] are invalid \
                  since it is not a tagged union." s_id
            | SA_basic(annot) ->
            if annot = default_basic_struct_annot then
              (* No annotation on struct, fall back to normal printing. *)
              pp_type_expr_guard None guard ff ty
            else
            let annot =
              match annot.st_ptr_type with
              | None    -> {annot with st_ptr_type = Some((s_id,ty))}
              | Some(_) ->
              Panic.panic_no_pos "[rc::ptr_type] in nested struct [%s]." s_id
            in
            let fields = gather_struct_fields s_id s in
            pp "(%a)" (pp_struct_def_np structs Guard_none annot fields) s_id
          end
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
    let fn = pp ") struct_%s %a" id (pp_simple_coq_expr true) in
    Option.iter fn annot.st_size;
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

let collect_invs : func_def -> (string * loop_annot) list = fun def ->
  let fn id (annot, _) acc =
    match annot with
    | BA_none              -> acc
    | BA_loop(Some(annot)) -> (id, annot) :: acc
    | BA_loop(None)        ->
    Panic.panic_no_pos "Bad block annotation in function [%s]." def.func_name
  in
  SMap.fold fn def.func_blocks []

let pp_spec : string -> import list -> string list -> typedef list ->
      string list -> Coq_ast.t pp =
    fun import_path imports inlined typedefs ctxt ff ast ->
  (* Stuff for import of the code. *)
  let basename =
    let name = Filename.basename ast.source_file in
    try Filename.chop_extension name with Invalid_argument(_) -> name
  in

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

  (* Printing inlined code (from comments). *)
  if inlined <> [] then pp "\n@;(* Inlined code. *)\n";
  List.iter (fun s -> if s = "" then pp "\n" else pp "@;%s" s) inlined;

  (* [Typeclass Opaque] stuff that needs to be repeated after the section. *)
  let opaque = ref [] in

  (* Definition of types. *)
  let pp_struct struct_id annot s =
    (* Check if a type must be generated. *)
    if annot.st_refined_by = [] && annot.st_ptr_type = None then () else
    (* Gather the field annotations. *)
    let fields = gather_struct_fields struct_id s in
    let (ref_names, ref_types) = List.split annot.st_refined_by in
    let (par_names, par_types) = List.split annot.st_parameters in
    let ref_and_par_types = ref_types @ par_types in
    let ref_and_par_names = ref_names @ par_names in
    let pp_params ff =
      let fn (x,e) = fprintf ff "(%s : %a) " x (pp_simple_coq_expr false) e in
      List.iter fn
    in
    let params = annot.st_parameters in
    let id =
      match annot.st_ptr_type with
      | None       -> struct_id
      | Some(id,_) -> id
    in
    pp "\n@;(* Definition of type [%s]. *)@;" id;
    let pp_prod = pp_as_prod (pp_simple_coq_expr true) in
    pp "@[<v 2>Definition %s_rec : (%a -d> typeO) → (%a -d> typeO) := " id
      pp_prod ref_and_par_types pp_prod ref_and_par_types;
    pp "(λ self %a,@;" pp_encoded_patt_name ref_and_par_names;
    pp_encoded_patt_bindings ff ref_and_par_names;
    let guard = Guard_in_def(id) in
    pp_struct_def_np ast.structs guard annot fields ff struct_id;
    pp "@]@;)%%I.@;Typeclasses Opaque %s_rec.\n" id;
    opaque := !opaque @ [id ^ "_rec"];

    pp "@;Global Instance %s_rec_ne : Contractive %s_rec." id id;
    pp "@;Proof. solve_type_proper. Qed.\n@;";

    pp "@[<v 2>Definition %s %a: rtype := {|@;" id pp_params params;
    pp "rty_type := %a;@;" pp_prod ref_types;
    pp "rty r__ := fixp %s %a@]@;|}.\n" (id ^ "_rec")
      (pp_as_tuple pp_str) ("r__" :: par_names);

    (* Generation of the unfolding lemma. *)
    pp "@;@[<v 2>Lemma %s_unfold %a%a:@;"
      id pp_params params pp_params annot.st_refined_by;
    pp "@[<v 2>(%a @@ %a)%%I ≡@@{type} (@;" (pp_as_tuple pp_str) ref_names
      (pp_id_args false id) par_names;
    let guard = Guard_in_lem(id) in
    pp_struct_def_np ast.structs guard annot fields ff struct_id;
    pp "@]@;)%%I.@]@;";
    pp "Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.\n";

    pp "\n@;Global Program Instance %s_rmovable %a: RMovable %a :=@;"
      id pp_params params (pp_id_args true id) par_names;
    pp "  {| rmovable '%a := movable_eq _ _ (%s_unfold"
      (pp_as_tuple pp_str) ref_names id;
    List.iter (fun n -> pp " %s" n) par_names;
    List.iter (fun n -> pp " %s" n) ref_names;
    pp ") |}.@;Next Obligation. solve_ty_layout_eq. Qed.\n";

    (* Generation of the global instances. *)
    let pp_instance_place inst_name type_name =
      pp "@;Global Instance %s_%s_inst l_ β_ %a%a:@;" id inst_name
        pp_params params pp_params annot.st_refined_by;
      pp "  %s l_ β_ (%a @@ %a)%%I (Some 100%%N) :=@;" type_name
        (pp_as_tuple pp_str) ref_names (pp_id_args false id) par_names;
      pp "  λ T, i2p (%s_eq l_ β_ _ _ T (%s_unfold" inst_name id;
      List.iter (fun _ -> pp " _") par_names;
      List.iter (fun _ -> pp " _") ref_names; pp "))."
    in
    let pp_instance_val inst_name type_name =
      pp "@;Global Program Instance %s_%s_inst v_ %a%a:@;" id inst_name
        pp_params params pp_params annot.st_refined_by;
      pp "  %s v_ (%a @@ %a)%%I (Some 100%%N) :=@;" type_name
        (pp_as_tuple pp_str) ref_names (pp_id_args false id) par_names;
      pp "  λ T, i2p (%s_eq v_ _ _ (%s_unfold" inst_name id;
      List.iter (fun _ -> pp " _") par_names;
      List.iter (fun _ -> pp " _") ref_names; pp ") T _).";
      pp "@;Next Obligation. done. Qed."
    in
    pp_instance_place "simplify_hyp_place" "SimplifyHypPlace";
    pp_instance_place "simplify_goal_place" "SimplifyGoalPlace";
    pp "\n";
    pp_instance_val "simplify_hyp_val" "SimplifyHypVal";
    pp_instance_val "simplify_goal_val" "SimplifyGoalVal"
  in
  let pp_tagged_union id tag_type_e s =
    if s.struct_is_union then
      Panic.panic_no_pos "Tagged union annotations used on [%s] should \
        rather be placed on a struct definition." id;
    (* Extract the two fields of the wrapping structure (tag and union). *)
    let (tag_field, union_field) =
      match s.struct_members with
      | [tag_field ; union_field] -> (tag_field, union_field)
      | _                         ->
      Panic.panic_no_pos "Tagged union [%s] is ill-formed: it should have \
        exactly two fields (tag and union)." id
    in
    (* Obtain the name of the tag field and check its type. *)
    let tag_field =
      let (tag_field, (annot, _, layout)) = tag_field in
      if annot <> Some(MA_none) then
        Panic.wrn None "Annotation ignored on the tag field [%s] of \
          the tagged union [%s]." tag_field id;
      if layout <> LInt(ItSize_t(false)) then
        Panic.panic_no_pos "The tag field [%s] of tagged union [%s] does \
          not have the expected [size_t] type." tag_field id;
      tag_field
    in
    (* Obtain the name of the union field and the name of the actual union. *)
    let (union_field, union_name) =
      let (union_field, (annot, _, layout)) = union_field in
      if annot <> Some(MA_none) then
        Panic.wrn None "Annotation ignored on the union field [%s] of \
          the tagged union [%s]." union_field id;
      match layout with
      | LStruct(union_name, true) -> (union_field, union_name)
      | _                         ->
      Panic.panic_no_pos "The union field [%s] of tagged union [%s] is \
        expected to be a union." union_field id
    in
    (* Find the union and extract its fields and corresponding annotations. *)
    let union_cases =
      let union =
        try List.assoc union_name ast.structs
        with Not_found -> assert false (* Unreachable thanks to Cerberus. *)
      in
      (* Some sanity checks. *)
      if not union.struct_is_union then
        Panic.panic_no_pos "[%s] was expected to be a union." union_name;
      assert (union.struct_annot = Some(SA_union));
      (* Extracting data from the fields. *)
      let fn (name, (annot, _, layout)) =
        match annot with
        | Some(MA_utag(ts)) ->
            let id_struct =
              match layout with
              | LStruct(id, false) -> id
              | _                  ->
              Panic.panic_no_pos "Field [%s] of union [%s] is not a struct."
                name union_name
            in
            (name, ts, id_struct)
        | Some(MA_none    ) ->
            Panic.panic_no_pos "Union tag annotation expected on field [%s] \
              of union [%s]." name union_name
        | Some(MA_field(_)) ->
            Panic.panic_no_pos "Unexpected field annotation on [%s] in the \
              union [%s]." name union_name
        | None              ->
            Panic.panic_no_pos "Invalid annotation on field [%s] in the \
              union [%s]." name union_name
      in
      List.map fn union.struct_members
    in
    (* Starting to do the printing. *)
    pp "\n@;(* Definition of type [%s] (tagged union). *)@;" id;
    (* Definition of the tag function. *)
    pp "@[<v 2>Definition %s_tag (c : %a) : nat :=@;"
      id (pp_simple_coq_expr false) tag_type_e;
    pp "match c with@;";
    let pp_tag_case i (_, (c, args), _) =
      pp "| %s" c; List.iter (fun _ -> pp " _") args; pp " => %i%%nat@;" i
    in
    List.iteri pp_tag_case union_cases;
    pp "end.@]\n@;";
    (* Simplifications hints for inversing the tag function. *)
    let pp_inversion_hint i (_, (c, args), _) =
      pp "Global Instance simpl_%s_tag_%s c :@;" id c;
      pp "  SimplBothRel (=) (%s_tag c) %i%%nat (" id i;
      if args <> [] then pp "∃";
      let fn (x,e) = pp " (%s : %a)" x (pp_simple_coq_expr false) e in
      List.iter fn args;
      if args <> [] then pp ", ";
      pp "c = %s" c; List.iter (fun (x,_) -> pp " %s" x) args; pp ").@;";
      pp "Proof. split; destruct c; naive_solver. Qed.\n@;";
    in
    List.iteri pp_inversion_hint union_cases;
    (* Definition for the tagged union info. *)
    pp "@[<v 2>Program Definition %s_tunion_info : tunion_info := {|@;" id;
    pp "ti_rtype := %a;@;" (pp_simple_coq_expr false) tag_type_e;
    pp "ti_base_layout := struct_%s;@;" id;
    pp "ti_tag_field_name := \"%s\";@;" tag_field;
    pp "ti_union_field_name := \"%s\";@;" union_field;
    pp "ti_union_layout := union_%s;@;" union_name;
    pp "ti_tag := %s_tag;@;" id;
    pp "ti_type c :=@;";
    pp "  match c with@;";
    let fn (name, (c, args), struct_id) =
      pp "  | %s" c; List.iter (fun (x,_) -> pp " %s" x) args;
      pp " => struct struct_%s [@@{type} " name;
      begin
        let s =
          try List.assoc struct_id ast.structs
          with Not_found -> assert false (* Unreachable thanks to Cerberus. *)
        in
        let fields = gather_struct_fields struct_id s in
        let pp_field ff (_, ty, _) = fprintf ff "%a" pp_type_expr ty in
        match fields with
        | []      -> ()
        | f :: fs -> pp "%a" pp_field f; List.iter (pp "; %a" pp_field) fs
      end;
      pp "]%%I@;"
    in
    List.iter fn union_cases;
    pp "  end;@]@;";
    pp "|}.@;";
    pp "Next Obligation. done. Qed.@;";
    pp "Next Obligation. by case; eauto. Qed.\n@;";
    (* Movable instance. *)
    pp "Global Program Instance movable_%s_tunion_info : MovableTUnion \
      %s_tunion_info := {|@;" id id;
    pp "  mti_movable c :=@;";
    pp "    match c with@;";
    let fn (_, (c, args), _) =
      pp "    | %s" c; List.iter (fun (x,_) -> pp " %s" x) args; pp " => _@;"
    in
    List.iter fn union_cases;
    pp "    end;@;";
    pp "|}.@;";
    let fn _ = pp "Next Obligation. simpl. apply _. Defined.@;" in
    List.iter fn union_cases;
    pp "Next Obligation. by case => /=; apply _. Qed.\n@;";
    (* Actual definition of the type. *)
    pp "Program Definition %s : rtype := tunion %s_tunion_info." id id
  in
  let pp_struct_or_tagged_union (id, s) =
    match s.struct_annot with
    | Some(SA_basic(annot)) -> pp_struct id annot s
    | Some(SA_tagged_u(e))  -> pp_tagged_union id e s
    | Some(SA_union)        -> ()
    | None                  ->
        Panic.panic_no_pos "Annotations on struct [%s] are invalid." id
  in
  List.iter pp_struct_or_tagged_union ast.structs;

  (* Type definitions (from comments). *)
  pp "\n@;(* Type definitions. *)";
  let pp_typedef (id, args, ty) =
    pp "\n@;Definition %s" id;
    let pp_arg (id, eo) =
      let pp_coq_expr = pp_coq_expr false pp_type_expr in
      match eo with
      | None    -> pp " %s" id
      | Some(e) -> pp " (%s : %a)" id pp_coq_expr e
    in
    List.iter pp_arg args;
    pp " := %a." pp_type_expr ty
  in
  List.iter pp_typedef typedefs;

  (* Function specs. *)
  let pp_spec (id, def_or_decl) =
    let annot =
      match def_or_decl with
      | FDef({func_annot=Some(annot); _}) -> annot
      | FDec(Some(annot))                 -> annot
      | _                                 ->
      Panic.panic_no_pos "Annotations on function [%s] are invalid." id
    in
    match annot.fa_proof_kind with
    | Proof_skipped ->
        pp "\n@;(* Function [%s] has been skipped. *)" id
    | _             ->
    pp "\n@;(* Specifications for function [%s]. *)" id;
    let (param_names, param_types) = List.split annot.fa_parameters in
    let (exist_names, exist_types) = List.split annot.fa_exists in
    let pp_args ff tys =
      match tys with
      | [] -> ()
      | _  -> pp "; "; pp_sep ", " pp_type_expr ff tys
    in
    pp "@;Definition type_of_%s :=@;  @[<hov 2>" id;
    let pp_prod = pp_as_prod (pp_simple_coq_expr true) in
    pp "fn(∀ %a : %a%a; %a)@;→ ∃ %a : %a, %a; %a.@]"
      (pp_as_tuple pp_str) param_names pp_prod param_types
      pp_args annot.fa_args pp_constrs annot.fa_requires (pp_as_tuple pp_str)
      exist_names pp_prod exist_types pp_type_expr
      annot.fa_returns pp_constrs annot.fa_ensures
  in
  List.iter pp_spec ast.functions;

  (* Closing the section. *)
  pp "@]@;End spec.";

  (* [Typeclass Opaque] stuff. *)
  if !opaque <> [] then pp "@;";
  let pp_opaque = pp "@;Typeclasses Opaque %s." in
  List.iter pp_opaque !opaque;
  pp "@]"

let pp_proof : string -> func_def -> import list -> string list -> proof_kind
    -> Coq_ast.t pp = fun import_path def imports ctxt proof_kind ff ast ->
  (* Formatting utilities. *)
  let pp fmt = Format.fprintf ff fmt in

  (* Only print a comment if the function is trusted. *)
  match proof_kind with
  | Proof_trusted ->
      pp "(* Let's skip that, you seem to have some faith. *)"
  | Proof_skipped ->
      pp "(* You were too lazy to even write a spec for this function. *)"
  | _             ->

  (* Add the extra import in case of manual proof. *)
  let imports =
    match proof_kind with
    | Proof_manual(from,file,_) -> imports @ [(from,file)]
    | _                         -> imports
  in

  (* Stuff for import of the code. *)
  let basename =
    let name = Filename.basename ast.source_file in
    try Filename.chop_extension name with Invalid_argument(_) -> name
  in

  (* Printing some header. *)
  pp "@[<v 0>From refinedc.typing Require Import typing.@;";
  pp "From %s Require Import %s_code.@;" import_path basename;
  pp "From %s Require Import %s_spec.@;" import_path basename;
  List.iter (pp_import ff) imports;
  pp "Set Default Proof Using \"Type\".@;@;";

  (* Printing generation data in a comment. *)
  pp "(* Generated from [%s]. *)@;" ast.source_file;

  (* Opening the section. *)
  pp "@[<v 2>Section proof_%s.@;" def.func_name;
  pp "Context `{!typeG Σ} `{!globalG Σ}.";
  List.iter (pp "@;%s.") ctxt;

  (* Statement of the typing proof. *)
  let func_annot =
    match def.func_annot with
    | Some(annot) -> annot
    | None        -> assert false (* Unreachable. *)
  in
  if List.length def.func_args <> List.length func_annot.fa_args then
    Panic.panic_no_pos "Argument number missmatch between code and spec.";
  pp "\n@;(* Typing proof for [%s]. *)@;" def.func_name;
  let (used_globals, used_functions) = def.func_deps in
  let deps =
    used_globals @ used_functions
  in
  let pp_args ff xs =
    match xs with
    | [] -> ()
    | _  -> fprintf ff " (%a : loc)" (pp_sep " " pp_str) xs
  in
  pp "@[<v 2>Lemma type_%s%a :@;" def.func_name pp_args deps;
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
    let pp_prod = pp_as_prod (pp_simple_coq_expr true) in
    let pp_global_type f =
      match List.find_opt (fun (name, _) -> name = f) ast.global_vars with
      | Some(_, Some(global_type)) ->
         let (param_names, param_types) = List.split global_type.ga_parameters in
          pp "global_initialized_types !! \"%s\" = Some (GT %a (λ '%a, %a : type)) →@;"
            f pp_prod param_types (pp_as_tuple pp_str) param_names (pp_type_expr_guard None Guard_none) global_type.ga_type
      | _                 -> ()
    in
    List.iter pp_global_type used_globals;
    let pp_dep f = pp "%s ◁ᵥ %s @@ function_ptr type_of_%s -∗@;" f f f in
    List.iter pp_dep used_functions;
    pp "%styped_function %a type_of_%s.@]@;" prefix pp_impl
      def.func_name def.func_name
  end;

  (* We have a manual proof. *)
  match proof_kind with
  | Proof_manual(_,_,thm) ->
      pp "Proof. refine %s. Qed." thm;
      pp "@]@;End proof_%s.@]" def.func_name (* Section closing. *)
  | _                     ->

  (* We output a normal proof. *)
  let pp_intros ff xs =
    let pp_intro ff (x,_) = pp_str ff x in
    match xs with
    | []      -> fprintf ff "[]"
    | [x]     -> pp_intro ff x
    | x :: xs -> List.iter (fun _ -> pp_str ff "[") xs;
                 pp_intro ff x;
                 List.iter (fprintf ff " %a]" pp_intro) xs
  in
  pp "@[<v 2>Proof.@;";
  pp "start_function \"%s\" (%a)" def.func_name
    pp_intros func_annot.fa_parameters;
  if def.func_vars <> [] || def.func_args <> [] then
    begin
      pp " =>";
      List.iter (fun (x,_) -> pp " arg_%s" x) def.func_args;
      List.iter (fun (x,_) -> pp " local_%s" x) def.func_vars
    end;
  pp ".@;split_blocks ((";
  let pp_inv (id, annot) =
    (* Opening a box and printing the existentials. *)
    pp "@;  @[<v 2><[ \"%s\" :=" id;
    let pp_exists (id, e) =
      pp "@;∃ %s : %a," id (pp_simple_coq_expr false) e
    in
    List.iter pp_exists annot.la_exists;
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
          (* Check if the type is different for the toplevel one. *)
          let toplevel_ty =
            try
              let i = List.find_index (fun (s,_) -> s = id) def.func_args in
              List.nth func_annot.fa_args i
            with Not_found | Failure(_) -> assert false (* Unreachable. *)
          in
          if ty = toplevel_ty then
            Panic.wrn None "Useless annotation for argument [%s]." id;
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
      List.map fn annot.la_inv_vars
    in
    let unused =
      let unused_args =
        let pred (id, _) =
          let id = "arg_" ^ id in
          List.for_all (fun (id_var, _) -> id <> id_var) used
        in
        let args = List.filter pred def.func_args in
        let fn (id, layout) =
          let ty =
            try
              let i = List.find_index (fun (s,_) -> s = id) def.func_args in
              List.nth func_annot.fa_args i
            with Not_found | Failure(_) -> assert false (* Unreachable. *)
          in
          ("arg_" ^ id, (layout, Some(ty)))
        in
        List.map fn args
      in
      let unused_vars =
        let pred (id, _) =
          let id = "local_" ^ id in
          List.for_all (fun (id_var, _) -> id <> id_var) used
        in
        let vars = List.filter pred def.func_vars in
        List.map (fun (id, layout) -> ("local_" ^ id, (layout, None))) vars
      in
      unused_args @ unused_vars
    in
    let all_vars = unused @ used in
    let pp_var ff (id, (layout, ty_opt)) =
      match ty_opt with
      | None     -> fprintf ff "%s ◁ₗ uninit %a" id (pp_layout true) layout
      | Some(ty) -> fprintf ff "%s ◁ₗ %a" id pp_type_expr ty
    in
    begin
      match (all_vars, annot.la_constrs) with
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
  let (invs_fb, invs_b) = List.partition (fun (_,la) -> la.la_full) invs in
  List.iter pp_inv invs_fb;
  pp "@;  ∅@;)%%I : gmap block_id (iProp Σ)) ((";
  List.iter pp_inv invs_b;
  pp "@;  ∅@;)%%I : gmap block_id (iProp Σ)).";
  let pp_do_step id =
    pp "@;- repeat liRStep; liShow.";
    pp "@;  all: print_typesystem_goal \"%s\" \"%s\"." def.func_name id
  in
  List.iter pp_do_step (List.cons "#0" (List.map fst invs_fb));
  pp "@;Unshelve. all: prepare_sideconditions; ";
  pp "normalize_and_simpl_goal; try solve_goal.";
  let tactics_items =
    let is_all t =
      let is_selector s =
        s = "all" ||
        let ok c = ('0' <= c && c <= '9') || List.mem c [' '; ','; '-'] in
        String.for_all ok s
      in
      match String.split_on_char ':' t with
      | []     -> false
      | s :: _ -> is_selector (String.trim s)
    in
    let rec pp_tactics_all tactics =
      match tactics with
      | t :: ts when is_all t -> pp "@;%s" t; pp_tactics_all ts
      | ts                    -> ts
    in
    pp_tactics_all func_annot.fa_tactics
  in
  List.iter (pp "@;+ %s") tactics_items;
  pp "@;all: print_sidecondition_goal \"%s\"." def.func_name;
  pp "@]@;Qed.";

  (* Closing the section. *)
  pp "@]@;End proof_%s.@]" def.func_name

type mode =
  | Code of import list
  | Spec of string * import list * string list * typedef list * string list
  | Fprf of string * func_def * import list * string list * proof_kind

let write : mode -> string -> Coq_ast.t -> unit = fun mode fname ast ->
  let pp =
    match mode with
    | Code(imports)                          ->
        pp_code imports
    | Spec(path,imports,inlined,tydefs,ctxt) ->
        pp_spec path imports inlined tydefs ctxt
    | Fprf(path,def,imports,ctxt,kind)       ->
        pp_proof path def imports ctxt kind
  in
  (* We write to a buffer. *)
  let buffer = Buffer.create 4096 in
  Format.fprintf (Format.formatter_of_buffer buffer) "%a@." pp ast;
  (* Check if we should write the file (inexistent / contents different). *)
  let must_write =
    try Buffer.contents (Buffer.from_file fname) <> Buffer.contents buffer
    with Sys_error(_) -> true
  in
  if must_write then Buffer.to_file fname buffer
