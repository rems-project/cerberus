open Printf
open Syntax
(*open Ssa_lib*)
open Llvm

(** Coq Pretty Printer *)
let getRealName (id:LLVMsyntax.id) =
    if String.length id <= 1
    then id
    else 
      if String.get id 0 = '@' or String.get id 0 = '%'
      then String.sub id 1 (String.length id-1)
      else id

let rec string_of_floating_point fp =
  match fp with
  | LLVMsyntax.Coq_fp_float -> "float" 
  | LLVMsyntax.Coq_fp_double -> "double" 
  | LLVMsyntax.Coq_fp_fp128 -> "fp128" 
  | LLVMsyntax.Coq_fp_x86_fp80 -> "x86_fp80" 
  | LLVMsyntax.Coq_fp_ppc_fp128 -> "ppc_fp128"

let rec string_of_typ ty =
  match ty with
  | LLVMsyntax.Coq_typ_int sz -> "i"^(string_of_int sz)
  | LLVMsyntax.Coq_typ_floatpoint fp -> string_of_floating_point fp
  | LLVMsyntax.Coq_typ_void -> "void"
  | LLVMsyntax.Coq_typ_label -> "label"
  | LLVMsyntax.Coq_typ_metadata -> "metadata"
  | LLVMsyntax.Coq_typ_array (sz, t) ->
                     "["   ^ (string_of_int sz) ^
                      " x " ^ (string_of_typ t) ^ "]"
  | LLVMsyntax.Coq_typ_function (t, ts, va) ->
      string_of_typ t ^ " (" ^ string_of_list_typ ts ^ 
        (if va then " ... " else "") ^ ")"
  | LLVMsyntax.Coq_typ_struct ts ->
                     "{ " ^ string_of_list_typ ts ^ " }"
  | LLVMsyntax.Coq_typ_pointer t -> (string_of_typ t) ^ "*"
  | LLVMsyntax.Coq_typ_opaque -> "opaque"
  | LLVMsyntax.Coq_typ_namedt id -> id
and string_of_list_typ ts =
  match ts with
  | LLVMsyntax.Cons_list_typ (t, ts') ->  
      (string_of_typ t)^" "^(string_of_list_typ ts')
  | LLVMsyntax.Nil_list_typ -> ""

let string_of_bop bop =
  match bop with
  | LLVMsyntax.Coq_bop_add -> "add"       
  | LLVMsyntax.Coq_bop_sub -> "sub"
  | LLVMsyntax.Coq_bop_mul -> "mul"
  | LLVMsyntax.Coq_bop_udiv -> "udiv"
  | LLVMsyntax.Coq_bop_sdiv -> "sdiv"
  | LLVMsyntax.Coq_bop_urem -> "urem"
  | LLVMsyntax.Coq_bop_srem -> "srem"
  | LLVMsyntax.Coq_bop_shl -> "shl"
  | LLVMsyntax.Coq_bop_lshr -> "lshr"       
  | LLVMsyntax.Coq_bop_ashr -> "ashr"
  | LLVMsyntax.Coq_bop_and -> "and"
  | LLVMsyntax.Coq_bop_or -> "or"       
  | LLVMsyntax.Coq_bop_xor -> "xor"  
                  
let string_of_fbop fbop =
  match fbop with
  | LLVMsyntax.Coq_fbop_fadd -> "fadd"       
  | LLVMsyntax.Coq_fbop_fsub -> "fsub"
  | LLVMsyntax.Coq_fbop_fmul -> "fmul"
  | LLVMsyntax.Coq_fbop_fdiv -> "fdiv"
  | LLVMsyntax.Coq_fbop_frem -> "frem"

let string_of_cond cond =
  match cond with
  | LLVMsyntax.Coq_cond_eq -> "eq"       
  | LLVMsyntax.Coq_cond_ne -> "ne"       
  | LLVMsyntax.Coq_cond_ugt -> "ugt"       
  | LLVMsyntax.Coq_cond_uge -> "uge"       
  | LLVMsyntax.Coq_cond_ult -> "ult"       
  | LLVMsyntax.Coq_cond_ule -> "ule"       
  | LLVMsyntax.Coq_cond_sgt -> "sgt"       
  | LLVMsyntax.Coq_cond_sge -> "sge"       
  | LLVMsyntax.Coq_cond_slt -> "slt"       
  | LLVMsyntax.Coq_cond_sle -> "sle"       

let string_of_fcond fcond =
  match fcond with
  | LLVMsyntax.Coq_fcond_false -> "false"       
  | LLVMsyntax.Coq_fcond_oeq -> "oeq"
  | LLVMsyntax.Coq_fcond_ogt -> "ogt"       
  | LLVMsyntax.Coq_fcond_oge -> "oge"       
  | LLVMsyntax.Coq_fcond_olt -> "olt"       
  | LLVMsyntax.Coq_fcond_ole -> "ole"       
  | LLVMsyntax.Coq_fcond_one -> "one"       
  | LLVMsyntax.Coq_fcond_ord -> "ord"       
  | LLVMsyntax.Coq_fcond_ueq -> "ueq"       
  | LLVMsyntax.Coq_fcond_ugt -> "ugt"       
  | LLVMsyntax.Coq_fcond_uge -> "uge"       
  | LLVMsyntax.Coq_fcond_ult -> "ult"       
  | LLVMsyntax.Coq_fcond_ule -> "ule"       
  | LLVMsyntax.Coq_fcond_une -> "une"
  | LLVMsyntax.Coq_fcond_uno -> "uno"       
  | LLVMsyntax.Coq_fcond_true -> "true"       
  
let string_of_extop extop =
  match extop with
  | LLVMsyntax.Coq_extop_s -> "sext"       
  | LLVMsyntax.Coq_extop_z -> "zext"
  | LLVMsyntax.Coq_extop_fp -> "fpext"

let string_of_castop castop =
  match castop with
  | LLVMsyntax.Coq_castop_fptoui -> "fptoui"       
  | LLVMsyntax.Coq_castop_fptosi -> "fptosi"   
  | LLVMsyntax.Coq_castop_uitofp -> "uitofp"
  | LLVMsyntax.Coq_castop_sitofp -> "sitofp"
  | LLVMsyntax.Coq_castop_ptrtoint -> "ptrtoint"
  | LLVMsyntax.Coq_castop_inttoptr -> "inttoptr"
  | LLVMsyntax.Coq_castop_bitcast -> "bitcast"

let string_of_truncop truncop =
  match truncop with
  | LLVMsyntax.Coq_truncop_int -> "trunc"       
  | LLVMsyntax.Coq_truncop_fp -> "fptrunc"

let rec string_of_constant c = 
  match c with
  | LLVMsyntax.Coq_const_int (sz, i) -> APInt.to_string i^":"^string_of_int sz
  | LLVMsyntax.Coq_const_undef _ -> "undef"
  | LLVMsyntax.Coq_const_null _ -> "null"
  | LLVMsyntax.Coq_const_arr (_, cs) -> string_of_list_constant cs
  | LLVMsyntax.Coq_const_struct cs -> string_of_list_constant cs
  | LLVMsyntax.Coq_const_gid (_,id) -> id
  | LLVMsyntax.Coq_const_zeroinitializer _ -> "zeroinitializer"
  | LLVMsyntax.Coq_const_floatpoint (_, f) -> APFloat.to_string f
  | LLVMsyntax.Coq_const_truncop (op, c, t) -> 
    string_of_truncop op^" ("^string_of_constant c^" to "^string_of_typ t^")" 
  | LLVMsyntax.Coq_const_extop (op, c, t) -> 
    string_of_extop op^" ("^string_of_constant c^" to "^string_of_typ t^")" 
  | LLVMsyntax.Coq_const_castop (op, c, t) -> 
    string_of_castop op^" ("^string_of_constant c^" to "^string_of_typ t^")" 
  | LLVMsyntax.Coq_const_gep (ib, c, cs) -> 
    (
    match ib with
    | true ->  "gepelementptr inbounds ("^string_of_constant c^" "^
        string_of_list_constant cs^")"
    | false ->  "gepelementptr ("^string_of_constant c^" "^
        string_of_list_constant cs^")"
    )
  |  LLVMsyntax.Coq_const_select (c0, c1, c2) -> 
    "select ("^string_of_constant c0^" "^string_of_constant c1^" "^
       string_of_constant c2^")"  
  |  LLVMsyntax.Coq_const_icmp (cond, c1, c2) ->
    "icmp "^string_of_cond cond^" ("^string_of_constant c1^" "^
       string_of_constant c2^")"  
  |  LLVMsyntax.Coq_const_fcmp (cond, c1, c2) ->
    "fcmp "^string_of_fcond cond^" ("^string_of_constant c1^" "^
      string_of_constant c2^")"  
  | LLVMsyntax.Coq_const_extractvalue (c, cs) ->
    "extractvalue ("^string_of_constant c^" "^string_of_list_constant cs^")"
  | LLVMsyntax.Coq_const_insertvalue (c1, c2, cs) ->
    "insertvalue ("^string_of_constant c1^" "^string_of_constant c2^" "^
      string_of_list_constant cs^")"
  | LLVMsyntax.Coq_const_bop (op, c1, c2) ->  
    string_of_bop op^" ("^string_of_constant c1^" to "^string_of_constant c2^")" 
  | LLVMsyntax.Coq_const_fbop (op, c1, c2) ->  
    string_of_fbop op^" ("^string_of_constant c1^" to "^string_of_constant c2^")"
            
and string_of_list_constant cs =
  match cs with
  | LLVMsyntax.Cons_list_const (c, cs') ->  
      (string_of_constant c)^" "^(string_of_list_constant cs')
  | LLVMsyntax.Nil_list_const -> ""
  
let string_of_value v =
  match v with
  | LLVMsyntax.Coq_value_id id -> id
  | LLVMsyntax.Coq_value_const c -> string_of_constant c

let rec string_of_params ps =
  match ps with
  | [] -> ""
  | ((t, _), v)::ps' -> 
      "("^(string_of_typ t)^","^(string_of_value v)^")"^(string_of_params ps')

let rec string_of_list_value vs =
  match vs with
  | LLVMsyntax.Nil_list_sz_value -> ""
  | LLVMsyntax.Cons_list_sz_value (sz0, v, vs') -> 
     "i"^(string_of_int sz0)^" "^(string_of_value v)^", "^
     (string_of_list_value vs')

let rec string_of_list_value_l vls =
  match vls with
  | LLVMsyntax.Cons_list_value_l (v, l, vls') ->  
      "("^(string_of_value v)^","^l^")"^(string_of_list_value_l vls')
  | LLVMsyntax.Nil_list_value_l -> ""

let rec string_of_args args =
  match args with
  | [] -> ""
  | ((t, _), id)::args' -> 
      "("^(string_of_typ t)^","^id^")"^(string_of_args args')

let travel_terminator i =
  match i with 
  | LLVMsyntax.Coq_insn_br (id, v, l1, l2) -> 
      eprintf "  %s = br %s %s %s\n" id (string_of_value v) l1 l2
  | LLVMsyntax.Coq_insn_br_uncond (id, l) -> 
      eprintf "  %s = br %s \n" id l
  | LLVMsyntax.Coq_insn_return (id, t, v) ->
      eprintf "  %s = ret %s %s\n" id (string_of_typ t) (string_of_value v)
  | LLVMsyntax.Coq_insn_return_void id ->
      eprintf "  %s = ret void\n" id
  | LLVMsyntax.Coq_insn_unreachable id -> 
      eprintf "  %s = unreachable\n" id
  ;
  flush_all ()      

let travel_cmd i =
  match i with
  | LLVMsyntax.Coq_insn_bop (id, bop, sz, v1, v2) ->
      eprintf "  %s = %s i%d %s %s\n" id (string_of_bop bop) sz 
        (string_of_value v1) (string_of_value v2)
  | LLVMsyntax.Coq_insn_fbop (id, fbop, fp, v1, v2) ->
      eprintf "  %s = %s %s %s %s\n" id (string_of_fbop fbop) 
        (string_of_floating_point fp) (string_of_value v1) (string_of_value v2)
  | LLVMsyntax.Coq_insn_extractvalue (id, t, v, cs) ->
      eprintf "  %s = extractvalue %s %s %s\n" id (string_of_typ t) 
        (string_of_value v) (string_of_list_constant cs)
  | LLVMsyntax.Coq_insn_insertvalue (id, t1, v1, t2, v2, cs) ->
      eprintf "  %s = insertvalue %s %s %s %s %s\n" id (string_of_typ t1) 
        (string_of_value v1) (string_of_typ t2) (string_of_value v2) 
        (string_of_list_constant cs)
  | LLVMsyntax.Coq_insn_malloc (id, t, v, align) ->
      eprintf "  %s = malloc %s %s %d\n" id (string_of_typ t) (string_of_value v)
        align
  | LLVMsyntax.Coq_insn_alloca (id, t, v, align) ->
      eprintf "  %s = alloca %s %s %d\n" id (string_of_typ t) (string_of_value v)
        align
  | LLVMsyntax.Coq_insn_free (id, t, v) ->
      eprintf "  %s = free %s %s\n" id (string_of_typ t) (string_of_value v)
  | LLVMsyntax.Coq_insn_load (id, t, v, a) ->
      eprintf "  %s = load %s* %s %d\n" id (string_of_typ t) (string_of_value v) 
        a
  | LLVMsyntax.Coq_insn_store (id, t, v1, v2, a) ->
      eprintf "  %s = store %s %s %s %d\n" id (string_of_typ t) 
        (string_of_value v1) (string_of_value v2) a
  | LLVMsyntax.Coq_insn_gep (id, inbounds, t, v, vs) ->
      eprintf "  %s = gep %s %s %s %s\n" id (string_of_bool inbounds) 
       (string_of_typ t) (string_of_value v) (string_of_list_value vs)
  | LLVMsyntax.Coq_insn_trunc (id, truncop, t1, v, t2) ->
      eprintf "  %s = %s %s %s %s\n" id (string_of_truncop truncop) 
        (string_of_typ t1) (string_of_value v) (string_of_typ t2)
  | LLVMsyntax.Coq_insn_ext (id, extop, t1, v, t2) ->
      eprintf "  %s = %s %s %s %s\n" id (string_of_extop extop) 
        (string_of_typ t1) (string_of_value v) (string_of_typ t2)
  | LLVMsyntax.Coq_insn_cast (id, castop, t1, v, t2) ->
      eprintf "  %s = %s %s %s %s\n" id (string_of_castop castop) 
        (string_of_typ t1) (string_of_value v) (string_of_typ t2)
  | LLVMsyntax.Coq_insn_icmp (id, cond, t, v1, v2) ->
      eprintf "  %s = icmp %s %s %s %s\n" id (string_of_cond cond) 
        (string_of_typ t) (string_of_value v1) (string_of_value v2)
  | LLVMsyntax.Coq_insn_fcmp (id, fcond, fp, v1, v2) ->
      eprintf "  %s = fcmp %s %s %s %s\n" id (string_of_fcond fcond) 
        (string_of_floating_point fp) (string_of_value v1) (string_of_value v2)
  | LLVMsyntax.Coq_insn_select (id, v, t, v1, v2) ->
      eprintf "  %s = select %s %s %s %s\n" id (string_of_value v) 
        (string_of_typ t) (string_of_value v1) (string_of_value v2)
  | LLVMsyntax.Coq_insn_call (id, noret, 
        LLVMsyntax.Coq_clattrs_intro (tailc, cc, ra, ca), t, fv, ps) ->
      eprintf "  %s = call %s %s %s %s %s\n" id (string_of_bool noret) 
        (string_of_bool tailc) (string_of_typ t) (string_of_value fv) 
        (string_of_params ps)
  ;
  flush_all ()        
          
let travel_phi i =
  match i with
  | LLVMsyntax.Coq_insn_phi (id, t, list_v_l) -> 
      eprintf "  %s = phi %s %s\n" id (string_of_typ t) 
       (string_of_list_value_l list_v_l)
  ;      
  flush_all ()      
  
let travel_block b =
  match b with
  | LLVMsyntax.Coq_block_intro (l, ps, cs, tmn) ->
    eprintf "label: %s\n" l; flush_all ();
    List.iter travel_phi ps;
    List.iter travel_cmd cs;
    travel_terminator tmn

let travel_fdec f =
  match f with
  | LLVMsyntax.Coq_fheader_intro (_, t, fid, args, va) ->
    eprintf "declare %s %s %s %s\n" (string_of_typ t) fid (string_of_args args)
      (if va then "..." else "");
    flush_all ()

let travel_fdef f =
  match f with
  | LLVMsyntax.Coq_fdef_intro 
      (LLVMsyntax.Coq_fheader_intro (_, t, fid, args, va), bs) ->
    eprintf "define %s %s %s %s\n" (string_of_typ t) fid (string_of_args args)
      (if va then "..." else ""); 
    flush_all ();
    List.iter travel_block bs
          
let string_of_gvar_spec gs =
  match gs with
  | LLVMsyntax.Coq_gvar_spec_global -> "global"           
  | LLVMsyntax.Coq_gvar_spec_constant -> "constant"

let string_of_linkage lk =
match lk with
  | LLVMsyntax.Coq_linkage_external -> "external"
  | LLVMsyntax.Coq_linkage_available_externally -> "available_externally"
  | LLVMsyntax.Coq_linkage_link_once -> "linkonce"
  | LLVMsyntax.Coq_linkage_link_once_odr -> "linkonce_odr"
  | LLVMsyntax.Coq_linkage_weak -> "weak"
  | LLVMsyntax.Coq_linkage_weak_odr -> "weak_odr"
  | LLVMsyntax.Coq_linkage_appending -> "appending"
  | LLVMsyntax.Coq_linkage_internal -> "internal"
  | LLVMsyntax.Coq_linkage_private -> "private"
  | LLVMsyntax.Coq_linkage_linker_private -> "linker_private"
  | LLVMsyntax.Coq_linkage_dllimport -> "dllimport"
  | LLVMsyntax.Coq_linkage_dllexport -> "dllexport"
  | LLVMsyntax.Coq_linkage_external_weak -> "external_weak"
  | LLVMsyntax.Coq_linkage_ghost -> "ghost"
  | LLVMsyntax.Coq_linkage_common -> "common"
          
let travel_product g =
  match g with
  | LLVMsyntax.Coq_product_gvar (LLVMsyntax.Coq_gvar_intro 
      (id, lk, spec, t, c, a)) -> 
    eprintf "%s = %s %s %s %s %d\n" id (string_of_linkage lk) 
     (string_of_gvar_spec spec) (string_of_typ t) 
     (string_of_constant c) a; 
    flush_all ()
  | LLVMsyntax.Coq_product_gvar (LLVMsyntax.Coq_gvar_external (id, spec, t)) -> 
    eprintf "%s = external %s %s\n" id (string_of_gvar_spec spec) 
      (string_of_typ t); 
    flush_all ()
  | LLVMsyntax.Coq_product_fdec f -> travel_fdec f
  | LLVMsyntax.Coq_product_fdef f -> travel_fdef f

let travel_layout dlt =
  match dlt with
  | LLVMsyntax.Coq_layout_be -> eprintf "E\n"
  | LLVMsyntax.Coq_layout_le -> eprintf "e\n"
  | LLVMsyntax.Coq_layout_ptr (sz, a1, a2) -> eprintf "p:%d:%d:%d\n" sz a1 a2 
  | LLVMsyntax.Coq_layout_int (sz, a1, a2) -> eprintf "i%d:%d:%d\n" sz a1 a2  
  | LLVMsyntax.Coq_layout_float (sz, a1, a2) -> eprintf "f%d:%d:%d\n" sz a1 a2  
  | LLVMsyntax.Coq_layout_aggr (sz, a1, a2) -> eprintf "a%d:%d:%d\n" sz a1 a2
  | LLVMsyntax.Coq_layout_stack (sz, a1, a2) -> eprintf "s%d:%d:%d\n" sz a1 a2
  | LLVMsyntax.Coq_layout_vector (sz, a1, a2) -> eprintf "v%d:%d:%d\n" sz a1 a2
  ;
  flush_all ()

let travel_namedt nt =
  match nt with
  | (LLVMsyntax.Coq_namedt_intro (id, t)) ->
    eprintf "%s = type %s\n" id (string_of_typ t); 
    flush_all ()

let travel_module m =
  prerr_endline "Travel Coq module:";
  match m with
  | LLVMsyntax.Coq_module_intro (dlts, nts, ps) -> 
    List.iter travel_layout dlts;
    List.iter travel_namedt nts;
    List.iter travel_product ps



