open Format
open Extra
open Panic
open Coq_ast
open Rc_annot

let pp_as_tuple : 'a pp -> 'a list pp = fun pp ff xs ->
  match xs with
  | []      -> pp_print_string ff "()"
  | [x]     -> pp ff x
  | x :: xs -> fprintf ff "(%a" pp x;
               List.iter (fprintf ff ", %a" pp) xs;
               pp_print_string ff ")"

let pp_sep : string -> 'a pp -> 'a list pp = fun sep pp ff xs ->
  match xs with
  | []      -> invalid_arg "Coq_pp.pp_sep"
  | x :: xs -> pp ff x; List.iter (fprintf ff "%s%a" sep pp) xs

let pp_as_prod : 'a pp -> 'a list pp = fun pp ff xs ->
  match xs with
  | [] -> pp_print_string ff "()"
  | _  -> pp_sep " * " pp ff xs

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
  Format.pp_print_string ff @@
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
      let x = if g then x else Printf.sprintf "\"%s\"" x in
      Format.pp_print_string ff x
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
          let sc = if i = n - 1 then "" else " ;" in
          pp "%a%s@;" pp_expr e sc
        in
        List.iteri fn es
      in
      pp "@[<hov 2>%S <- %a with@ [ @[<hov 2>%a@] ] ;@]@;%a"
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
  pp "@[<v 2>Section code.@;";

  (* Declaration of objects (global variable) in the context. *)
  pp "(* Global variables. *)@;";
  let pp_global_var = pp "Context (%s : loc).@;" in
  List.iter pp_global_var ast.global_vars;

  (* Declaration of functions in the context. *)
  pp "@;(* Functions. *)@;";
  let pp_func_decl (id, _) = pp "Context (%s : loc).@;" id in
  List.iter pp_func_decl ast.functions;

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
    pp "@;(* Definition of struct [%s]. *)@;" id;
    pp "@[<v 2>Program Definition struct_%s := {|@;" id;

    pp "@[<v 2>sl_members := [";
    pp_members decl.struct_members;
    pp "@]@;];@]@;|}.@;";
    pp "Solve Obligations with solve_struct_obligations.@;"
  in
  let pp_union (id, decl) =
    pp "@;(* Definition of union [%s]. *)@;" id;
    pp "@[<v 2>Program Definition union_%s := {|@;" id;

    pp "@[<v 2>ul_members := [";
    pp_members decl.struct_members;
    pp "@]@;];@]@;|}.@;";
    pp "Solve Obligations with solve_struct_obligations.@;"
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
    pp "\n@;(* Definition of function [%s]. *)@;" id;
    pp "@[<v 2>Definition impl_%s : function := {|@;" id;

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

let pp_coq_expr : coq_expr pp = fun ff e ->
  match e with
  | Coq_ident(x) -> pp_print_string ff x
  | Coq_all(s)   -> fprintf ff "(%s)" s

let rec pp_constr : constr pp = fun ff c ->
  let pp_kind ff k =
    match k with
    | Own     -> pp_print_string ff "◁ₗ"
    | Shr     -> pp_print_string ff "◁ₗ{Shr}"
    | Frac(e) -> fprintf ff "◁ₗ{%a}" pp_coq_expr e
  in
  match c with
  | Constr_Iris(s)     -> pp_print_string ff s
  | Constr_exist(x,c)  -> fprintf ff "(∃ %s, %a)" x pp_constr c
  | Constr_own(x,k,ty) -> fprintf ff "%s %a %a" x pp_kind k pp_type_expr ty
  | Constr_Coq(e)      -> fprintf ff "⌜%a⌝" pp_coq_expr e

and pp_type_expr : type_expr pp = fun ff ty ->
  let pp_kind ff k =
    match k with
    | Own     -> pp_print_string ff "&own"
    | Shr     -> pp_print_string ff "&shr"
    | Frac(e) -> fprintf ff "&frac{%a}" pp_coq_expr e
  in
  let rec pp_patt ff p =
    match p with
    | Pat_var(x)    -> pp_print_string ff x
    | Pat_tuple(ps) -> fprintf ff "`%a" (pp_as_tuple pp_patt) ps
  in
  let rec pp wrap ff ty =
    match ty with
    (* Don't need wrapping. *)
    | Ty_direct(id)     -> pp_print_string ff id
    | Ty_Coq(e)         -> pp_coq_expr ff e
    | Ty_dots           -> Panic.panic_no_pos "Unexpected ellipsis."
    (* Always wrapped. *)
    | Ty_lambda(p,ty)   -> fprintf ff "(λ %a, %a)" pp_patt p (pp false) ty
    (* Insert wrapping if needed. *)
    | _ when wrap       -> fprintf ff "(%a)" (pp false) ty
    (* Remaining constructors (no need for explicit wrapping). *)
    | Ty_refine(e,ty)   -> fprintf ff "%a @@ %a" pp_coq_expr e (pp true) ty
    | Ty_ptr(k,ty)      -> fprintf ff "%a %a" pp_kind k (pp true) ty
    | Ty_exists(x,ty)   -> fprintf ff "∃ %s, %a" x (pp false) ty
    | Ty_constr(ty,c)   -> assert false
    | Ty_params(id,tys) ->
    pp_print_string ff id;
    match (id, tys) with
    | ("optional", [ty]) -> fprintf ff " %a null" (pp true) ty
    | (_         , _   ) -> List.iter (fprintf ff " %a" (pp true)) tys
  in
  pp true ff ty

let pp_constrs : constr list pp = fun ff cs ->
  match cs with
  | []      -> pp_print_string ff "True"
  | c :: cs -> pp_constr ff c; List.iter (fprintf ff ", %a" pp_constr) cs

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
  let pp_struct s =
    pp "(* Not implemented. *)" (* TODO *)
  in
  let pp_union s =
    pp "(* Not implemented. *)" (* TODO *)
  in
  let pp_struct_union ((_, {struct_is_union; struct_name; _}) as s) =
    pp "\n@;(* Definition of type [%s]. *)@;" struct_name;
    if struct_is_union then pp_union s else pp_struct s
  in
  List.iter pp_struct_union ast.structs;

  (* Function specs. *)
  let pp_spec (id, def) =
    pp "\n@;(* Specifications for function [%s]. *)" id;
    match def.func_annot with None -> assert false | Some(annot) ->
    let (param_names, param_types) = List.split annot.fa_parameters in
    let (exist_names, exist_types) = List.split annot.fa_exists in
    let pp_args ff tys =
      match tys with
      | [] -> ()
      | _  -> pp "; "; pp_sep ", " pp_type_expr ff tys
    in
    pp "@;Definition type_of_%s :=@;  @[<hov 2>" id;
    pp "fn(∀ %a : %a%a; %a)@;→ ∃ %a : %a, %a; %a.@]"
      (pp_as_tuple pp_print_string) param_names
      (pp_as_prod pp_coq_expr) param_types pp_args annot.fa_args
      pp_constrs annot.fa_requires (pp_as_tuple pp_print_string) exist_names
      (pp_as_prod pp_coq_expr) exist_types pp_type_expr annot.fa_returns
      pp_constrs annot.fa_ensures
  in
  List.iter pp_spec ast.functions;

  (* Typing proofs. *)
  let pp_proof (id, def) =
    pp "\n@;(* Typing proof for [%s]. *)@;" id;
    pp "(* Not implemented. *)" (* TODO *)
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
