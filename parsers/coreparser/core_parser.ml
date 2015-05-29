module Make
           (M : sig
                  val sym_counter: int ref
                  val std: (Core_parser_util._sym, Core.sym) Pmap.map
                end)
= struct

  exception Error
  
  type _menhir_env = {
    _menhir_lexer: Lexing.lexbuf -> Core_parser_util.token;
    _menhir_lexbuf: Lexing.lexbuf;
    mutable _menhir_token: Core_parser_util.token;
    mutable _menhir_startp: Lexing.position;
    mutable _menhir_endp: Lexing.position;
    mutable _menhir_shifted: int
  }
  
  and _menhir_state = 
    | MenhirState440
    | MenhirState430
    | MenhirState428
    | MenhirState424
    | MenhirState422
    | MenhirState419
    | MenhirState416
    | MenhirState414
    | MenhirState411
    | MenhirState406
    | MenhirState403
    | MenhirState402
    | MenhirState393
    | MenhirState390
    | MenhirState388
    | MenhirState382
    | MenhirState378
    | MenhirState375
    | MenhirState373
    | MenhirState364
    | MenhirState352
    | MenhirState347
    | MenhirState344
    | MenhirState341
    | MenhirState339
    | MenhirState337
    | MenhirState335
    | MenhirState333
    | MenhirState331
    | MenhirState328
    | MenhirState326
    | MenhirState322
    | MenhirState320
    | MenhirState318
    | MenhirState315
    | MenhirState313
    | MenhirState309
    | MenhirState307
    | MenhirState303
    | MenhirState285
    | MenhirState283
    | MenhirState279
    | MenhirState275
    | MenhirState271
    | MenhirState269
    | MenhirState267
    | MenhirState265
    | MenhirState263
    | MenhirState259
    | MenhirState251
    | MenhirState249
    | MenhirState247
    | MenhirState245
    | MenhirState241
    | MenhirState239
    | MenhirState235
    | MenhirState233
    | MenhirState231
    | MenhirState229
    | MenhirState227
    | MenhirState225
    | MenhirState223
    | MenhirState221
    | MenhirState219
    | MenhirState213
    | MenhirState209
    | MenhirState207
    | MenhirState205
    | MenhirState203
    | MenhirState201
    | MenhirState199
    | MenhirState197
    | MenhirState195
    | MenhirState193
    | MenhirState191
    | MenhirState189
    | MenhirState186
    | MenhirState184
    | MenhirState179
    | MenhirState176
    | MenhirState174
    | MenhirState172
    | MenhirState170
    | MenhirState168
    | MenhirState166
    | MenhirState164
    | MenhirState162
    | MenhirState158
    | MenhirState154
    | MenhirState152
    | MenhirState149
    | MenhirState147
    | MenhirState145
    | MenhirState143
    | MenhirState141
    | MenhirState139
    | MenhirState138
    | MenhirState135
    | MenhirState128
    | MenhirState125
    | MenhirState123
    | MenhirState121
    | MenhirState120
    | MenhirState118
    | MenhirState116
    | MenhirState106
    | MenhirState102
    | MenhirState100
    | MenhirState98
    | MenhirState95
    | MenhirState90
    | MenhirState86
    | MenhirState77
    | MenhirState72
    | MenhirState63
    | MenhirState51
    | MenhirState49
    | MenhirState47
    | MenhirState44
    | MenhirState40
    | MenhirState38
    | MenhirState33
    | MenhirState31
    | MenhirState29
    | MenhirState23
    | MenhirState20
    | MenhirState9
    | MenhirState8
    | MenhirState5
    | MenhirState3
    | MenhirState0
  
    
open Lem_pervasives
open Either
open Global

open Core_parser_util

module Mem = Naive_memory

module Cmm = Cmm_master

let symbol_compare =
  Symbol.instance_Basic_classes_Ord_Symbol_t_dict.compare_method

let implementation_constant_compare =
  compare


type name =
  | Sym of _sym
  | Impl of Implementation_.implementation_constant


type expr =
  | Vunit
  | Vtrue | Vfalse
  | Vlist of expr list (* value *)
(*  | Vtuple of list value *)
  | Vctype of Core_ctype.ctype0
  | Vunspecified of Core_ctype.ctype0
  | Vinteger of Nat_big_num.num
  | Vfloating of string
(* RUNTIME  | Vsymbolic of Symbolic.symbolic *)
(* RUNTIME  | Vpointer of Mem.pointer_value *)
(*  | Varray of list Mem.mem_value *)
  | PEundef of Undefined.undefined_behaviour
  | PEerror of string
  | PEsym of _sym
  | PEimpl of Implementation_.implementation_constant
  | PEcons of expr (* pexpr *) * expr (* pexpr *)
  | PEcase_list of expr (* pexpr *) * expr (* pexpr *) * name
  | PEcase_ctype of expr (* pexpr *) * expr (* pexpr *) * name * name * name * name *
                    name * name * name * name
  | PEshift of expr (* pexpr *) * (Core_ctype.ctype0 * expr (* pexpr *)) list
  | PEnot of expr (* pexpr *)
  | PEop of Core.binop * expr (* pexpr *) * expr (* pexpr *)
  | PEtuple of expr list (* pexpr *)
  | PEarray of expr list (* ((Mem.mem_value, _sym) either) list *)
  | PEcall of name * expr list (* pexpr *)
(*
  | PElet of sym * pexpr * pexpr
  | PEif of pexpr * pexpr * pexpr
*)
  | PEis_scalar of expr (* pexpr *)
  | PEis_integer of expr (* pexpr *)
  | PEis_signed of expr (* pexpr *)
  | PEis_unsigned of expr (* pexpr *)
  | Eraise of _sym
  | Eregister of _sym * name
  | Eskip
  | Elet of _sym * expr (* pexpr *) * expr
  | Eif of expr (* pexpr *) * expr * expr
  | Eproc of name * expr list (* pexpr *)
  | Eaction of paction
  | Eunseq of expr list
  | Ewseq of (_sym option) list * expr * expr
  | Esseq of (_sym option) list * expr * expr
  | Easeq of _sym option * action * paction
  | Eindet of expr
  | Ebound of int * expr
  | Esave of _sym * (_sym * Core_ctype.ctype0) list * expr
  | Erun of _sym * (_sym * expr (* pexpr *)) list
  | Eret of expr (* pexpr *)
  | End of expr list
  | Epar of expr list
(* RUNTIME  | Ewait of Thread.thread_id *)

and action =
  | Create of expr (* pexpr *) * expr (* pexpr *)
  | Alloc of expr (* pexpr *) * expr (* pexpr *)
  | Kill of expr (* pexpr *)
  | Store of expr (* pexpr *) * expr (* pexpr *) * expr (* pexpr *) * Cmm.memory_order
  | Load of expr (* pexpr *) * expr (* pexpr *) * Cmm.memory_order
  | CompareExchangeStrong of expr (* pexpr *) * expr (* pexpr *) * expr (* pexpr *) * expr (* pexpr *) * Cmm.memory_order * Cmm.memory_order
  | CompareExchangeWeak of expr (* pexpr *) * expr (* pexpr *) * expr (* pexpr *) * expr (* pexpr *) * Cmm.memory_order * Cmm.memory_order
and paction = Core.polarity * action


type declaration =
  | Def_decl  of Implementation_.implementation_constant * Core.core_base_type * expr
  | IFun_decl of Implementation_.implementation_constant * (Core.core_base_type * (_sym * Core.core_base_type) list * expr)
  | Glob_decl of _sym * Core.core_type * expr
  | Fun_decl  of _sym * (Core.core_base_type * (_sym * Core.core_base_type) list * expr)
  | Proc_decl of _sym * (Core.core_base_type * (_sym * Core.core_base_type) list * expr)




let fresh_symbol (str, _) =
  let n = !M.sym_counter in
  M.sym_counter := n+1;
  Symbol.Symbol (n, Some str)


let lookup_symbol ((str, loc) as _sym) syms =
  (* TODO: print location *)
  Debug.print_debug 7 ("[Core_parser.convert_expr] LOOKING FOR: " ^ str);
  begin try
    Pmap.find _sym syms (* TODO: Error handling *)
  with
    | e -> print_endline (pp_pos _sym ^ " [Core_parser.convert_expr] Failed to find: " ^ str);
           Pmap.iter (fun (str, _) _ ->
             Printf.printf "DEBUG, in sigma: %s\n" str
           ) syms;
           raise e
  end


let register_cont_symbols expr =
  let rec f (st : (_sym, Core.sym) Pmap.map) = function
    | Vunit
    | Vtrue
    | Vfalse
    | Vlist _
    | Vctype _
    | Vunspecified _
    | Vinteger _
    | Vfloating _
    | PEundef _
    | PEerror _
    | PEsym _
    | PEimpl _
    | PEcons _
    | PEcase_list _
    | PEcase_ctype _
    | PEshift _
    | PEnot _
    | PEop _
    | PEtuple _
    | PEarray _
    | PEcall _
    | PEis_scalar _
    | PEis_integer _
    | PEis_signed _
    | PEis_unsigned _
    | Eraise _
    | Eregister _
    | Eskip
    | Elet _
    | Eproc _
    | Eaction _
    | Eunseq _
    | Easeq _
    | Erun _
    | Eret _ ->
        st
    | Eif (_, _e1, _e2)
    | Ewseq (_, _e1, _e2)
    | Esseq (_, _e1, _e2) ->
        f (f st _e1) _e2
    | Eindet _e
    | Ebound (_, _e) ->
        f st _e
    | End _es
    | Epar _es ->
        List.fold_left f st _es
    | Esave (_sym, _, _e) ->
        f (Pmap.add _sym (fresh_symbol _sym) st) _e
  
  in f (Pmap.empty _sym_compare) expr


let symbolify_name _Sigma : name -> Core.name = function
  | Impl iCst ->
      Core.Impl iCst
  | Sym _sym ->
      let sym = try Pmap.find _sym _Sigma
      with Not_found -> try Pmap.find _sym M.std
      with Not_found ->
        prerr_endline (Colour.ansi_format [Colour.Red] ("PARSING ERROR: the function `" ^ fst _sym ^ "' was not declared."));
        exit 1 in
      Core.Sym sym


type _core =
  | Value of Core.value
  | Pure of Core.pexpr
  | Expr of unit Core.expr

let to_value = function
  | Value cval ->
      Some cval
  | _ ->
      None

let to_values xs =
  List.fold_right (fun x acc_opt ->
    match to_value x, acc_opt with
      | Some cval, Some acc ->
          Some (cval :: acc)
      | _ ->
          None
  ) xs (Some [])

let to_pure = function
  | Value cval ->
      Left (Core.PEval cval)
  | Pure pe ->
      Left pe
  | Expr e ->
      Right e

let to_pures xs =
  List.fold_right (fun x acc_opt ->
    match to_pure x, acc_opt with
      | Left pe, Left acc ->
          Left (pe :: acc)
      | Left pe, Right acc ->
          Right (Core.Epure pe :: acc)
      | Right e, Left acc ->
          Right (e :: List.map (fun pe -> Core.Epure pe) acc)
      | Right e, Right acc ->
          Right (e :: acc)
  ) xs (Left [])

let to_expr = function
  | Value cval ->
      Core.Epure (Core.PEval cval)
  | Pure pe ->
      Core.Epure pe
  | Expr e ->
      e


(* NOTE: the second argument is the map of non-filescoped symbols *)
let symbolify_expr _Sigma st (expr: expr) : _core =
  let fnm = symbolify_name _Sigma in
  let rec f (st : (_sym, Core.sym) Pmap.map) = function
    | Vunit ->
        Value (Core.Vunit)
    | Vtrue ->
        Value (Core.Vtrue)
    | Vfalse ->
        Value (Core.Vfalse)
    | Vlist _es ->
        (match to_values (List.map (f st) _es) with
          | Some cvals ->
              Value (Core.Vlist cvals)
          | None ->
              failwith "TODO(MSG) type-error: symbolify_expr, Vlist")
    | Vctype ty ->
        Value (Core.Vctype ty)
    | Vunspecified ty ->
        Value (Core.Vunspecified ty)
    | Vinteger n ->
        Value (Core.Vinteger (Mem.mk_integer_value n))
    | Vfloating str ->
        Value (Core.Vfloating str)
    | PEundef ub ->
        Pure (Core.PEundef ub)
    | PEerror str ->
        Pure (Core.PEerror str)
    | PEsym _sym ->
        Pure (Core.PEsym (lookup_symbol _sym st))
    | PEimpl iCst ->
        Pure (Core.PEimpl iCst)
    | PEcons (_e1, _e2) ->
        (match to_pure (f st _e1), to_pure (f st _e2) with
          | Left pe1, Left pe2 ->
              Pure (Core.PEcons (pe1, pe2))
          | _ ->
              failwith "TODO(MSG) type-error: symbolify_expr, PEcons")
    | PEcase_list (_e1, _e2, nm) ->
        (match to_pure (f st _e1), to_pure (f st _e2) with
          | Left pe1, Left pe2 ->
              Pure (Core.PEcase_list (pe1, pe2, fnm nm))
          | _ ->
              failwith "TODO(MSG) type-error: symbolify_expr, PEcase_list")
    | PEcase_ctype (_e1, _e2, nm1, nm2, nm3, nm4, nm5, nm6, nm7, nm8) ->
        (match to_pure (f st _e1), to_pure (f st _e2) with
          | Left pe1, Left pe2 ->
              Pure (Core.PEcase_ctype (pe1, pe2, fnm nm1, fnm nm2, fnm nm3, fnm nm4, fnm nm5, fnm nm6, fnm nm7, fnm nm8))
          | _ ->
              failwith "TODO(MSG) type-error: symbolify_expr, PEcase_ctype")
    | PEshift (_e1, ty_es) ->
        let ty_es_opt = List.fold_right (fun (ty, _e) acc_opt ->
          match to_pure (f st _e), acc_opt with
            | Left pe, Some acc ->
                Some ((ty, pe) :: acc)
            | _ ->
                None
        ) ty_es (Some []) in
        (match to_pure (f st _e1), ty_es_opt with
          | Left pe1, Some ty_pes ->
              Pure (Core.PEshift (pe1, ty_pes))
          | _ ->
              failwith "TODO(MSG) type-error: symbolify_expr, PEshift")
    | PEnot _e ->
        (match to_pure (f st _e) with
          | Left pe ->
              Pure (Core.PEnot pe)
          | _ ->
              failwith "TODO(MSG) type-error: symbolify_expr, PEnot")
    | PEop (bop, _e1, _e2) ->
        (match to_pure (f st _e1), to_pure (f st _e2) with
          | Left pe1, Left pe2 ->
              Pure (Core.PEop (bop, pe1, pe2))
          | _ ->
              failwith "TODO(MSG) type-error: symbolify_expr, PEop")
    | PEtuple _es ->
        (match to_pures (List.map (f st) _es) with
          | Left pes ->
              Pure (Core.PEtuple pes)
          | _ ->
              failwith "TODO(MSG) type-error: symbolify_expr, PEtuple")
    | PEarray _es ->
        (match to_pures (List.map (f st) _es) with
          | Left pes ->
              Pure (Core.PEarray pes)
          | _ ->
              failwith "TODO(MSG) type-error: symbolify_expr, PEarray")

(*
    | PEarray _xs ->
        let xs = List.map (function
          | Left mem_val ->
              Left mem_val
          | Right _sym ->
              Right (lookup_symbol _sym st)
        ) _xs in
        Pure (Core.PEarray xs)
*)
    | PEcall (_nm, _es) ->
        let nm = fnm _nm in
        (match to_pures (List.map (f st) _es) with
          | Left pes ->
              Pure (Core.PEcall (nm, pes))
          | _ ->
              failwith "TODO(MSG) type-error: symbolify_expr, PEcall")
    | PEis_scalar _e ->
        (match to_pure (f st _e) with
          | Left pe ->
              Pure (Core.PEis_scalar pe)
          | _ ->
              failwith "TODO(MSG) type-error: symbolify_expr, PEis_scalar")
    | PEis_integer _e ->
        (match to_pure (f st _e) with
          | Left pe ->
              Pure (Core.PEis_integer pe)
          | _ ->
              failwith "TODO(MSG) type-error: symbolify_expr, PEis_integer")
    | PEis_signed _e ->
        (match to_pure (f st _e) with
          | Left pe ->
              Pure (Core.PEis_signed pe)
          | _ ->
              failwith "TODO(MSG) type-error: symbolify_expr, PEis_signed")
    | PEis_unsigned _e ->
        (match to_pure (f st _e) with
          | Left pe ->
              Pure (Core.PEis_unsigned pe)
          | _ ->
              failwith "TODO(MSG) type-error: symbolify_expr, PEis_unsigned")
    | Eraise _sym ->
        Expr (Core.Eraise (fst _sym))
    | Eregister (_sym, nm) ->
        Expr (Core.Eregister (fst _sym, fnm nm))
    | Eskip ->
        Expr (Core.Eskip)
    | Elet (_sym, _e1, _e2) ->
        let sym = fresh_symbol _sym in
        let _e2' = f (Pmap.add _sym sym st) _e2 in
        (match to_pure (f st _e1), to_pure _e2' with
          | Left pe1, Left pe2 ->
              Pure (Core.PElet (sym, pe1, pe2))
          | Left pe1, Right e2 ->
              Expr (Core.Elet (sym, pe1, e2))
          | _ ->
              failwith "TODO(MSG) type-error: symbolify_expr, Elet")
    | Eif (_e1, _e2, _e3) ->
        let _e2' = f st _e2 in
        let _e3' = f st _e3 in
        (match to_pure (f st _e1), to_pure _e2', to_pure _e3' with
          | Left pe1, Left pe2, Left pe3 ->
              Pure (Core.PEif (pe1, pe2, pe3))
          | Left pe1, Left pe2, Right e3 ->
              Expr (Core.Eif (pe1, Core.Epure pe2, e3))
          | Left pe1, Right e2, Left pe3 ->
              Expr (Core.Eif (pe1, e2, Core.Epure pe3))
          | Left pe1, Right e2, Right e3 ->
              Expr (Core.Eif (pe1, e2, e3))
          | _ ->
              failwith "TODO(MSG) type-error: symbolify_expr, Eif")
    | Eproc (nm, _es) ->
        (match to_pures (List.map (f st) _es) with
          | Left pes ->
              Expr (Core.Eproc ((), fnm nm, pes))
          | _ ->
              failwith "TODO(MSG) type-error: symbolify_expr, Eproc")
    | Eaction (p, act) ->
        Expr (Core.Eaction (Core.Paction (p, Core.Action ((), g st act))))
    | Eunseq _es ->
        Expr (Core.Eunseq (List.map (fun z -> to_expr (f st z)) _es))
    | Ewseq (_as, _e1, _e2) ->
        let (_as', st') = List.fold_left (fun (_as, st) _sym_opt ->
          match _sym_opt with
            | Some _sym ->
                let sym = fresh_symbol _sym in
                (Some sym :: _as, Pmap.add _sym sym st)
            | None ->
                (None :: _as, st)
        ) ([], st) _as in
        Expr (Core.Ewseq (List.rev _as', to_expr (f st _e1), to_expr (f st' _e2)))
    | Esseq (_as, _e1, _e2) ->
        let (_as', st') = List.fold_left (fun (_as, st) _sym_opt ->
          match _sym_opt with
            | Some _sym ->
                let sym = fresh_symbol _sym in
                (Some sym :: _as, Pmap.add _sym sym st)
            | None ->
                (None :: _as, st)
        ) ([], st) _as in
        Expr (Core.Esseq (List.rev _as', to_expr (f st _e1), to_expr (f st' _e2)))
    | Easeq (_sym_opt, act1, (p, act2)) ->
        Expr (match _sym_opt with
          | Some _sym ->
              let sym = fresh_symbol _sym in
              Core.Easeq (Some sym, Core.Action ((), g st act1), Core.Paction (p, Core.Action ((), g (Pmap.add _sym sym st) act2)))
          | None ->
              Core.Easeq (None, Core.Action ((), g st act1), Core.Paction (p, Core.Action ((), g st act2))))
    | Eindet _e ->
        Expr (Core.Eindet (to_expr (f st _e)))
    | Ebound (n, _e) ->
        Expr (Core.Ebound (n, to_expr (f st _e)))
    | Esave (_sym, _sym_tys, _e) ->
        let sym_tys =
          List.map (fun (_sym, ty) -> (lookup_symbol _sym st, ty)) _sym_tys in
        Expr (Core.Esave (lookup_symbol _sym st, sym_tys, to_expr (f st _e)))
    | Erun (_sym, _sym__es) ->
        let sym_pes_opt = List.fold_right (fun (_sym, _e) acc_opt ->
          match (to_pure (f st _e), acc_opt) with
            | (Left pe, Some acc) ->
                Some ((lookup_symbol _sym st, pe) :: acc)
            | _ ->
                None
        ) _sym__es (Some []) in
        (match sym_pes_opt with
          | Some sym_pes ->
              Expr (Core.Erun ((), lookup_symbol _sym st, sym_pes))
          | None ->
              failwith "TODO(MSG) type-error: symbolify_expr, Erun")
    | Eret _e ->
        (match to_pure (f st _e) with
          | Left pe ->
              Expr (Core.Eret pe)
          | _ ->
              failwith "TODO(MSG) type-error: symbolify_expr, Eret")
    | End _es ->
        Expr (Core.End (List.map (fun z -> to_expr (f st z)) _es))
    | Epar _es ->
        Expr (Core.Epar (List.map (fun z -> to_expr (f st z)) _es))
  
  and g st = function
    | Create (_e1, _e2) ->
        (match to_pure (f st _e1), to_pure (f st _e2) with
          | Left pe1, Left pe2 ->
              Core.Create (pe1, pe2, [])
          | _ ->
            failwith "TODO(MSG) type-error: symbolify_expr, Create")
    | Alloc (_e1, _e2) ->
        (match to_pure (f st _e1), to_pure (f st _e2) with
          | Left pe1, Left pe2 ->
              Core.Alloc0 (pe1, pe2, [])
          | _ ->
            failwith "TODO(MSG) type-error: symbolify_expr, Alloc")
    | Kill _e ->
        (match to_pure (f st _e) with
          | Left pe ->
              Core.Kill pe
          | _ ->
            failwith "TODO(MSG) type-error: symbolify_expr, Kill")
    | Store (_e1, _e2, _e3, mo) ->
        (match to_pure (f st _e1), to_pure (f st _e2), to_pure (f st _e3) with
          | Left pe1, Left pe2, Left pe3 ->
              Core.Store0 (pe1, pe2, pe3, mo)
          | _ ->
            failwith "TODO(MSG) type-error: symbolify_expr, Store")
    | Load (_e1, _e2, mo) ->
        (match to_pure (f st _e1), to_pure (f st _e2) with
          | Left pe1, Left pe2 ->
              Core.Load0 (pe1, pe2, mo)
          | _ ->
            failwith "TODO(MSG) type-error: symbolify_expr, Load")
        
    | CompareExchangeStrong (_e1, _e2, _e3, _e4, mo1, mo2) ->
        (match to_pure (f st _e1), to_pure (f st _e2), to_pure (f st _e3), to_pure (f st _e4) with
          | Left pe1, Left pe2, Left pe3, Left pe4 ->
              Core.CompareExchangeStrong (pe1, pe2, pe3, pe4, mo1, mo2)
          | _ ->
            failwith "TODO(MSG) type-error: symbolify_expr, CompareExchangeStrong")
    | CompareExchangeWeak (_e1, _e2, _e3, _e4, mo1, mo2) ->
        (match to_pure (f st _e1), to_pure (f st _e2), to_pure (f st _e3), to_pure (f st _e4) with
          | Left pe1, Left pe2, Left pe3, Left pe4 ->
              Core.CompareExchangeWeak (pe1, pe2, pe3, pe4, mo1, mo2)
          | _ ->
            failwith "TODO(MSG) type-error: symbolify_expr, CompareExchangeWeak") in
  f st expr


(* let symbolify_ *)




let symbolify_expr_ (_Sigma, fsyms) (expr: expr) : unit Core.expr =
  failwith "WIP"
(* TODO: WIP
  let lookup_symbol str syms =
    Debug.print_debug 7 ("[Core_parser.convert_expr] LOOKING FOR: " ^ str);
    begin try
        Pmap.find str syms (* TODO: Error handling *)
      with
        | e -> print_endline ("[Core_parser.convert_expr] Failed to find: " ^ str);
               raise e
    end in
  
  let rec f st = function
    | Eunit ->
        Core.Epure (Core.PEval Core.Vunit)
(*
    | Enull ->
        Core.Enull Core_ctype.Void0 (* TODO *)
*)
    | Etrue ->
        Core.Epure (Core.PEval Core.Etrue)
    | Efalse ->
        Core.Epure (Core.PEval Core.Efalse)
    | Econst c ->
        Core.Econst c
    | Elist es ->
        Core.Elist (List.map (f st) es)
    | Econs (pe1, pe2) ->
        Core.Econs (f st pe1, f st pe2)
    | Ectype ty ->
        Core.Ectype ty
    | Esym a ->
        Core.Esym (lookup_symbol a st)
    | Eimpl ic ->
        Core.Eimpl ic
    | Etuple es ->
        Core.Etuple (List.map (f st) es)
    | Enot e ->
        Core.Enot (f st e)
    | Eop (binop, e1, e2) ->
        Core.Eop (binop, f st e1, f st e2)
    | Ecall (Impl func, params) ->
        Core.Ecall (Core.Impl func, List.map (f st) params)
    | Ecall (Sym func, params) ->
        let fsym = try
            Pmap.find func fsyms
          with Not_found -> try
              Pmap.find func M.std
            with Not_found ->
              prerr_endline (Colour.ansi_format [Colour.Red] ("PARSING ERROR: the function `" ^ func ^ "' was not declared."));
              exit 1 in
        Core.Ecall (Core.Sym fsym, List.map (f st) params)
    | Eundef ub ->
        Core.Eundef ub
    | Eerror str ->
        Core.Eerror str
    | Eraise evnt ->
        Core.Eraise evnt
    | Eregister (evnt, nm) ->
        let nm' = match nm with
          | Impl f ->
              Core.Impl f
          | Sym str ->
              Core.Sym (Pmap.find str fsyms) in
        Core.Eregister (evnt, nm')
(*
    | Etry (e, str_es) ->
        Core.Etry (f st e, List.map (fun (str, e) -> (str, f st e)) str_es)
*)
    | Eshift (pe, sh) ->
        Core.Eshift (f st pe, List.map (fun (ty, e) -> (ty, f st e)) sh)

    | Eskip ->
        Core.Eskip
    | Elet (a, e1, e2) ->
        let sym_n = fresh_symbol a in
        Core.Elet (sym_n, f st e1, f (Pmap.add a sym_n st) e2)
    | Eif (e1, e2, e3) ->
        Core.Eif (f st e1, f st e2, f st e3)
    | Eproc (Impl func, params) ->
        Core.Eproc ((), Core.Impl func, List.map (f st) params)
    | Eproc (Sym func, params) ->
        Core.Eproc ((), Core.Sym (Pmap.find func fsyms), List.map (f st) params)

    | Ecase (e, nm1, nm2, nm3, nm4, nm5, nm6, nm7, nm8, nm9) ->
        let g = (function
          | Impl f -> Core.Impl f
          | Sym f  ->
              begin try
                Core.Sym (Pmap.find f fsyms)
              with
                | e -> print_endline ("[Core_parser.symbolify, Ecase] Failed to find: " ^ f);
                    raise e
              end) in
        Core.Ecase (f st e, g nm1, g nm2, g nm3, g nm4, g nm5, g nm6, g nm7, g nm8, g nm9)


(*
    | Esame (e1, e2) ->
        Core.Esame (f st e1, f st e2)
*)
    | Eaction pact ->
        let (p, (s, act)) = g st pact in
        Core.Eaction (Core.Paction (p, Core.Action (s, act)))
    | Eunseq es ->
        Core.Eunseq (List.map (f st) es)
    | Ewseq (_as, e1, e2) ->
        let (_as', st') = List.fold_left (fun (_as, st) str_opt ->
          match str_opt with
            | Some str ->
                let sym_n = fresh_symbol str in
                (Some sym_n :: _as, Pmap.add str sym_n st)
            | None ->
                (None :: _as, st)
        ) ([], st) _as in
        Core.Ewseq (List.rev _as', f st e1, f st' e2)
(*
        let (count', _as', syms') = List.fold_left (fun (c, _as, syms) sym_opt ->
          match sym_opt with
            | Some sym -> let _a = Symbol.Symbol (c, Some sym) in
                          (c+1, Some _a :: _as, Pmap.add sym _a syms)
            | None     -> (c+1, None :: _as, syms)) (count, [], syms) _as in
        Core.Ewseq (List.rev _as', f st e1, f (count', syms') e2)
*)
    | Esseq (_as, e1, e2) ->
        let (_as', st') = List.fold_left (fun (_as, st) str_opt ->
          match str_opt with
            | Some str ->
                let sym_n = fresh_symbol str in
                (Some sym_n :: _as, Pmap.add str sym_n st)
            | None ->
                (None :: _as, st)
        ) ([], st) _as in
        Core.Esseq (List.rev _as', f st e1, f st' e2)

(*
        let (count', _as', syms') = List.fold_left (fun (c, _as, syms) sym_opt ->
          match sym_opt with
            | Some sym -> let _a = Symbol.Symbol (c, Some sym) in
                          (c+1, Some _a :: _as, Pmap.add sym _a syms)
            | None     -> (c+1, None :: _as, syms)) (count, [], syms) _as in
        Core.Esseq (List.rev _as', f st e1, f (count', syms') e2)
 *)
    | Easeq (_a_opt, act, pact) ->
        begin match _a_opt with
                | Some _a ->
                    let sym_n = !M.sym_counter in
                    let _a' = Symbol.Symbol (sym_n, Some _a) in
                    M.sym_counter := sym_n+1;
                    let (_, (s1, act1)) = g st (Core.Pos, act) in
                    let (p2, (s2, act2)) = g (Pmap.add _a _a' st) pact in
                    Core.Easeq (Some _a', Core.Action (s1, act1), Core.Paction (p2, Core.Action (s2, act2)))
                | None ->
                    let (_, (s1, act1)) = g st (Core.Pos, act) in
                    let (p2, (s2, pact2)) = g st pact in
                    Core.Easeq (None, Core.Action (s1, act1), Core.Paction (p2, Core.Action (s2, pact2)))
        end
    | Eindet e ->
        Core.Eindet (f st e)
    | Ebound (j, e) ->
        failwith "[Core_parser.symbolify] #Ebound: TODO"
    | Esave (k, a_tys, e) ->
        let a_tys' = List.map (fun (a, ty) -> (lookup_symbol a st, ty)) a_tys in
        Core.Esave (lookup_symbol k st, a_tys', f st e)
(* HIP
        let (st', a_tys') = List.fold_left (fun ((count, syms) as st, acc) (a, ty) ->
          let _a = Symbol.Symbol (count, Some a) in
          ((count+1, Pmap.add a _a syms), (_a, ty) :: acc)
        ) (st, []) a_tys in
        Core.Esave (lookup_symbol k syms, List.rev a_tys', f st' e)
 *)
    | Erun (k, a_es) ->
        let a_es' = List.map (fun (a, e) -> (lookup_symbol a st, f st e)) a_es in
        Core.Erun ((), lookup_symbol k st, a_es')
    | Eret e ->
        Core.Eret (f st e)
    | End es ->
        Core.End (List.map (f st) es)
    | Epar es ->
        Core.Epar (List.map (f st) es)
    | Eis_scalar e ->
        Core.Eis_scalar (f st e)
    | Eis_integer e ->
        Core.Eis_integer (f st e)
    | Eis_signed e ->
        Core.Eis_signed (f st e)
    | Eis_unsigned e ->
        Core.Eis_unsigned (f st e)
  
  and g st (p, act) =(p,
    match act with
      | Create (e_al, e_ty) ->
          ((), Core.Create (f st e_al, f st e_ty, []))
      | Alloc (e_al, e_n) ->
          ((), Core.Alloc0 (f st e_al, f st e_n, []))
      | Kill e_o ->
          ((), Core.Kill (f st e_o))
      | Store (e_ty, e_o, e_n, mo) ->
          ((), Core.Store0 (f st e_ty, f st e_o, f st e_n, mo))
      | Load (e_ty, e_o, mo) ->
          ((), Core.Load0 (f st e_ty, f st e_o, mo))
      | CompareExchangeStrong (e_ty, e_o, e_e, e_d, mo1, mo2) ->
          ((), Core.CompareExchangeStrong (f st e_ty, f st e_o, f st e_e, f st e_d, mo1, mo2))
      | CompareExchangeWeak (e_ty, e_o, e_e, e_d, mo1, mo2) ->
          ((), Core.CompareExchangeWeak (f st e_ty, f st e_o, f st e_e, f st e_d, mo1, mo2))
    )
  in
  let conts = register_cont_symbols expr in
  f (Pmap.union _Sigma conts) expr
*)


(*


(* symbolify_impl_map: (Implementation_.implementation_constant, Core.core_basic_type * () list) Pmap.map -> unit Core.impl *)
let symbolify_impl_map global_syms xs : Core.impl =
  Pmap.map (function
    | Left (bTy, _e) ->
        (match to_pure (symbolify_expr global_syms (Pmap.empty _sym_compare) _e) with
          | Left pe ->
              Core.Def (bTy, pe)
          | _ ->
              failwith "(TODO msg) Type-error: symbolify_impl_map, Left")
    
    | Right (bTy, params_, _e) ->
        let (_Sigma, params) =
          List.fold_left (fun (_Sigma_acc, params_acc) (param_str, param_ty) ->
            let param_sym = fresh_symbol param_str in
            ( Pmap.add param_str param_sym _Sigma_acc, (param_sym, param_ty) :: params_acc )
          ) (Pmap.empty _sym_compare, []) params_ in
        
        (match to_pure (symbolify_expr global_syms _Sigma _e) with
          | Left pe ->
              Core.IFun (bTy, params, pe)
          | _ ->
              failwith "(TODO msg) Type-error: symbolify_impl_map, Right")
  ) xs
*)






let symbolify_params _params =
  List.fold_right (fun (str, bTy) (params_acc, _Gamma_acc) ->
    let sym = fresh_symbol str in
    ((sym, bTy) :: params_acc, Pmap.add str sym _Gamma_acc)
  ) _params ([], Pmap.empty _sym_compare)


let symbolify_decls _Sigma _decls =
  List.fold_left (fun (impl_acc, globs_acc, funs_acc) -> function
    | Def_decl (iCst, bTy, _e) ->
        (match to_pure (symbolify_expr _Sigma (Pmap.empty _sym_compare) _e) with
          | Left pe ->
              (Pmap.add iCst (Core.Def (bTy, pe)) impl_acc, globs_acc, funs_acc)
          | _ ->
              failwith "TODO(MSG) type-error: symbolify_decls, Def_decl")
    | IFun_decl (iCst, (bTy, _params, _e)) ->
        let (params, _Gamma) = symbolify_params _params in
        (match to_pure (symbolify_expr _Sigma _Gamma _e) with
          | Left pe ->
              (Pmap.add iCst (Core.IFun (bTy, params, pe)) impl_acc, globs_acc, funs_acc)
          | _ ->
              failwith "TODO(MSG) type-error: symbolify_decls, IFun_decl")
    | Glob_decl (_sym, coreTy, _e) ->
        (impl_acc,
         (lookup_symbol _sym _Sigma, coreTy, to_expr (symbolify_expr (Pmap.remove _sym _Sigma) (Pmap.empty _sym_compare) _e)) :: globs_acc,
         funs_acc)
    | Fun_decl (_sym, (bTy, _params, _e)) ->
        let (params, _Gamma) = symbolify_params _params in
        (match to_pure (symbolify_expr _Sigma _Gamma _e) with
           | Left pe ->
               (impl_acc, globs_acc,
                Pmap.add (lookup_symbol _sym _Sigma) (Core.Fun (bTy, params, pe)) funs_acc)
           | _ ->
               failwith "TODO(MSG) type-error: symbolify_decls, Fun_decl")
    | Proc_decl (_sym, (bTy, _params, _e)) ->
        let (params, _Gamma) = symbolify_params _params in
        (impl_acc, globs_acc,
         Pmap.add (lookup_symbol _sym _Sigma) (Core.Proc (bTy, params, to_expr (symbolify_expr _Sigma _Gamma _e))) funs_acc)
  ) (Pmap.empty implementation_constant_compare, [], Pmap.empty symbol_compare) _decls



let mk_file _decls =
  (* this first pass collect all the file scope symbol names to allow mutually recursive definitions *)
  (* TODO: check for exhaustivity of iCst definition *)
  let (sym_opt, _, _Sigma) = List.fold_left (fun (sym_opt_acc, iCsts, _Sigma_acc) -> function
    | Def_decl (iCst, _, _)
    | IFun_decl (iCst, _) ->
        if List.mem iCst iCsts then
          failwith ("duplicate definition of '" ^ Implementation_.string_of_implementation_constant iCst ^ "'")
        else
          (sym_opt_acc, iCst :: iCsts, _Sigma_acc)
    | Glob_decl ((str, _) as _sym, _, _) ->
        if Pmap.mem _sym _Sigma_acc then
          failwith ("duplicate definition of '" ^ str ^ "'")
        else if str = "main" then
          failwith "a global cannot be named 'main'"
        else
          (sym_opt_acc, iCsts, Pmap.add _sym (fresh_symbol _sym) _Sigma_acc)
    | Fun_decl  ((str, _) as _sym, _)
    | Proc_decl  ((str, _) as _sym, _) ->
        if Pmap.mem _sym _Sigma_acc then
          failwith ("duplicate definition of '" ^ str ^ "'")
        else
          let sym = fresh_symbol _sym in
          ((if str = "main" then Some sym else sym_opt_acc), iCsts, Pmap.add _sym sym _Sigma_acc)
  ) (None, [], Pmap.empty _sym_compare) _decls in
  
  if List.exists (function Glob_decl _ -> true | _ -> false) _decls then
    (* CASE: this must be program file *)
    if List.exists (function IFun_decl _ | Def_decl _ -> true | _ -> false) _decls then
      failwith "TODO(msg): globals are not allowed in implementation files"
    else
      let (_, globs, funs) = symbolify_decls _Sigma _decls in
      match sym_opt with
        | Some sym ->
            Core_parser_util.Rfile (sym, globs, funs)
        | None ->
            failwith "TODO(msg): program file should define the startup function/procedure 'main'"
  else if List.exists (function IFun_decl _ | Def_decl _ -> true | _ -> false) _decls then
    (* CASE: this has to be an implementation file *)
    match sym_opt with
      | Some _ ->
          failwith "TODO(msg): the file-scope name 'main' is reserved for the startup function/procedure in program files"
      | None ->
          let (impl, _, funs) = symbolify_decls _Sigma _decls in
          Core_parser_util.Rimpl (impl, funs)
  else
    (* CASE: program or std file (latter in absence of a main function/procedure *)
    let (_, globs, funs) = symbolify_decls _Sigma _decls in
    match sym_opt with
      | Some sym ->
          Core_parser_util.Rfile (sym, globs, funs)
      | None ->
          Core_parser_util.Rstd funs


(*
              match coreTy with
                | Core.TyBase bTy ->
                    match to_pure (symbolify_expr global_syms _Sigma_acc' _e)
                    (sym_opt_acc, _Sigma_acc', Core.Fun_decl (bTy, [], ) :: fun_map_acc)
                     
*)




(*

  if List.for_all (function Fun_decl _ -> true | _ -> false) decls then
    (* CASE: this is not an implementation file. *)
    let (main_opt, _Sigma, fun_map_) =
      List.fold_left (fun (main_opt_acc, _Sigma_acc, fun_map_acc) decl ->
        match decl with
          | Fun_decl (fun_str, fun_def) ->
            (* TODO: better error *)
            if Pmap.mem fun_str _Sigma_acc then
              failwith ("duplicate definition of `" ^ fun_str ^ "'")
            else
              let fun_sym = fresh_symbol fun_str in
              ((if fun_str = "main" then Some fun_sym else main_opt_acc),
               Pmap.add fun_str fun_sym _Sigma_acc,
               Pmap.add fun_sym fun_def fun_map_acc)
          | _ -> assert false
      ) (None, Pmap.empty compare, Pmap.empty symbol_compare) decls
    in
    
    let fun_map = symbolify_fun_map _Sigma fun_map_ in
    match main_opt with
      | Some sym_main ->
          Core_parser_util.Rfile (sym_main, fun_map)
      | None ->
          Core_parser_util.Rstd fun_map
  
  else
    (* CASE: this is an implementation file *)
    let (impl_map_, (_Sigma, fun_map_)) =
      List.fold_left (fun (impl_map_acc, ((fsyms, fun_map) as funs_acc)) decl ->
        match decl with
          | Def_decl (i, bty, e) ->
              if Pmap.mem i impl_map_acc then
                failwith ("(TODO_MSG) duplication declaration of " ^ Implementation_.string_of_implementation_constant i)
              else
                (Pmap.add i (Left (bty, e)) impl_map_acc, funs_acc)
          
          | IFun_decl (implConst, decl) ->
              if Pmap.mem implConst impl_map_acc then
                failwith ("multiple declaration of " ^ Implementation_.string_of_implementation_constant implConst)
              else
              (Pmap.add implConst (Right decl) impl_map_acc, funs_acc)
          
          | Glob_decl _ ->
              failwith "(TODO_MSG) found a global declaration in an implementation file."
          
          | Fun_decl (fname, fdef) ->
            (* TODO: better error *)
            if Pmap.mem fname fsyms then
              failwith ("duplicate definition of `" ^ fname ^ "'")
            else
              let fun_sym = fresh_symbol fname in
              (impl_map_acc, (Pmap.add fname fun_sym fsyms, Pmap.add fun_sym fdef fun_map))
      ) (Pmap.empty compare, (Pmap.empty compare, Pmap.empty symbol_compare)) decls in
    
    
    (* We perform the symbolification as a second step to allow mutual recursion *)
    let impl_map = failwith "symbolify_impl_map _Sigma impl_map_" in
    let fun_map = failwith "symbolify_fun_map _Sigma fun_map_" in
    
    (* TODO: add a check for completeness of the impl map *)
    Core_parser_util.Rimpl (impl_map, fun_map)
*)


(* HACK for now (maybe we should just get back to concrete names for ctypes) *)
let ctypes_names = ref (0, Pmap.empty symbol_compare)

(*val subst: string -> Symbol.t *)
let subst name =
  let (z, ns) = !ctypes_names in
  if Pmap.mem name ns then
    Pmap.find name ns
  else
    let n = (z, Some name) in
    ctypes_names := (z+1, Pmap.add name n ns);
    n

let _eRR =
    Error
  
  let rec _menhir_goto_separated_nonempty_list_COMMA_pattern_elem_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Core_parser_util._sym option list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState128 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, _as) = _menhir_stack in
              let _v : (Core_parser_util._sym option list) =     ( _as ) in
              _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState135 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s, x), _, xs) = _menhir_stack in
          let _v : (Core_parser_util._sym option list) =     ( x :: xs ) in
          _menhir_goto_separated_nonempty_list_COMMA_pattern_elem_ _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_ctype__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Core_ctype.ctype0 list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      let _menhir_stack = Obj.magic _menhir_stack in
      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
      let _tok = _menhir_env._menhir_token in
      match _tok with
      | Core_parser_util.RPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _ = _menhir_discard _menhir_env in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s, ty), _, xs00) = _menhir_stack in
          let _v : (Core_ctype.ctype0) = let tys =
            let xs0 = xs00 in
            let x =
              let xs = xs0 in
                  ( xs )
            in
                ( x )
          in
              ( Core_ctype.Function0 (ty, List.map (fun ty -> (AilTypes.no_qualifiers, ty)) tys, false) ) in
          _menhir_goto_ctype _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_goto_option_INT_CONST_ : _menhir_env -> 'ttv_tail -> (Nat_big_num.num option) -> 'ttv_return =
    fun _menhir_env _menhir_stack _v ->
      let _menhir_stack = (_menhir_stack, _v) in
      let _menhir_stack = Obj.magic _menhir_stack in
      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
      let _tok = _menhir_env._menhir_token in
      match _tok with
      | Core_parser_util.RBRACKET ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _ = _menhir_discard _menhir_env in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s, ty), n_opt) = _menhir_stack in
          let _v : (Core_ctype.ctype0) =     ( Core_ctype.Array0 (ty, n_opt) ) in
          _menhir_goto_ctype _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_goto_pattern_elem : _menhir_env -> 'ttv_tail -> _menhir_state -> (Core_parser_util._sym option) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      let _menhir_stack = Obj.magic _menhir_stack in
      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
      let _tok = _menhir_env._menhir_token in
      match _tok with
      | Core_parser_util.COMMA ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.SYM _v ->
              _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _v
          | Core_parser_util.UNDERSCORE ->
              _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState135
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState135)
      | Core_parser_util.RPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, x) = _menhir_stack in
          let _v : (Core_parser_util._sym option list) =     ( [ x ] ) in
          _menhir_goto_separated_nonempty_list_COMMA_pattern_elem_ _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_goto_nonempty_list_declaration_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (declaration list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState0 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.EOF ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, decls) = _menhir_stack in
              let _v : (Core_parser_util.result) =     ( mk_file decls ) in
              let _menhir_stack = Obj.magic _menhir_stack in
              let _menhir_stack = Obj.magic _menhir_stack in
              let _1 = _v in
              Obj.magic _1
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState440 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s, x), _, xs) = _menhir_stack in
          let _v : (declaration list) =     ( x :: xs ) in
          _menhir_goto_nonempty_list_declaration_ _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_memory_order : _menhir_env -> 'ttv_tail -> _menhir_state -> (Cmm.memory_order) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState251 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ACQUIRE ->
                  _menhir_run257 _menhir_env (Obj.magic _menhir_stack) MenhirState259
              | Core_parser_util.ACQ_REL ->
                  _menhir_run256 _menhir_env (Obj.magic _menhir_stack) MenhirState259
              | Core_parser_util.CONSUME ->
                  _menhir_run255 _menhir_env (Obj.magic _menhir_stack) MenhirState259
              | Core_parser_util.RELAXED ->
                  _menhir_run254 _menhir_env (Obj.magic _menhir_stack) MenhirState259
              | Core_parser_util.RELEASE ->
                  _menhir_run253 _menhir_env (Obj.magic _menhir_stack) MenhirState259
              | Core_parser_util.SEQ_CST ->
                  _menhir_run252 _menhir_env (Obj.magic _menhir_stack) MenhirState259
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState259)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState259 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let (((((((_menhir_stack, _menhir_s), _, e1), _, e2), _, e3), _, e4), _, mo1), _, mo2) = _menhir_stack in
              let _v : (action) =     ( CompareExchangeStrong (e1, e2, e3, e4, mo1, mo2) ) in
              _menhir_goto_action _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState269 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ACQUIRE ->
                  _menhir_run257 _menhir_env (Obj.magic _menhir_stack) MenhirState271
              | Core_parser_util.ACQ_REL ->
                  _menhir_run256 _menhir_env (Obj.magic _menhir_stack) MenhirState271
              | Core_parser_util.CONSUME ->
                  _menhir_run255 _menhir_env (Obj.magic _menhir_stack) MenhirState271
              | Core_parser_util.RELAXED ->
                  _menhir_run254 _menhir_env (Obj.magic _menhir_stack) MenhirState271
              | Core_parser_util.RELEASE ->
                  _menhir_run253 _menhir_env (Obj.magic _menhir_stack) MenhirState271
              | Core_parser_util.SEQ_CST ->
                  _menhir_run252 _menhir_env (Obj.magic _menhir_stack) MenhirState271
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState271)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState271 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let (((((((_menhir_stack, _menhir_s), _, e1), _, e2), _, e3), _, e4), _, mo1), _, mo2) = _menhir_stack in
              let _v : (action) =     ( CompareExchangeWeak (e1, e2, e3, e4, mo1, mo2) ) in
              _menhir_goto_action _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState347 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((((_menhir_stack, _menhir_s), _, e1), _, e2), _, mo) = _menhir_stack in
              let _v : (action) =     ( Load (e1, e2, mo) ) in
              _menhir_goto_action _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState393 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let (((((_menhir_stack, _menhir_s), _, e1), _, e2), _, e3), _, mo) = _menhir_stack in
              let _v : (action) =     ( Store (e1, e2, e3, mo) ) in
              _menhir_goto_action _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_paction : _menhir_env -> 'ttv_tail -> _menhir_state -> (paction) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      match _menhir_s with
      | MenhirState430 | MenhirState424 | MenhirState416 | MenhirState406 | MenhirState31 | MenhirState33 | MenhirState390 | MenhirState388 | MenhirState40 | MenhirState378 | MenhirState44 | MenhirState95 | MenhirState100 | MenhirState102 | MenhirState116 | MenhirState118 | MenhirState120 | MenhirState352 | MenhirState121 | MenhirState344 | MenhirState123 | MenhirState328 | MenhirState326 | MenhirState322 | MenhirState320 | MenhirState315 | MenhirState313 | MenhirState309 | MenhirState307 | MenhirState303 | MenhirState138 | MenhirState139 | MenhirState141 | MenhirState143 | MenhirState145 | MenhirState147 | MenhirState149 | MenhirState152 | MenhirState285 | MenhirState283 | MenhirState154 | MenhirState279 | MenhirState162 | MenhirState275 | MenhirState164 | MenhirState267 | MenhirState265 | MenhirState263 | MenhirState166 | MenhirState249 | MenhirState247 | MenhirState245 | MenhirState168 | MenhirState239 | MenhirState170 | MenhirState219 | MenhirState172 | MenhirState174 | MenhirState213 | MenhirState209 | MenhirState207 | MenhirState205 | MenhirState203 | MenhirState201 | MenhirState199 | MenhirState197 | MenhirState195 | MenhirState193 | MenhirState191 | MenhirState189 | MenhirState186 | MenhirState184 | MenhirState179 | MenhirState176 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let pact = _v in
          let _v : (expr) =     ( Eaction pact ) in
          _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
      | MenhirState335 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let pact2 = _v in
          let (((_menhir_stack, _menhir_s), _, str), _, act1) = _menhir_stack in
          let _v : (expr) =     ( Easeq (Some str, act1, pact2) ) in
          _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
      | MenhirState341 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let pact2 = _v in
          let (((_menhir_stack, _menhir_s), _, _), _, act1) = _menhir_stack in
          let _v : (expr) =     ( Easeq (None, act1, pact2) ) in
          _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_separated_pair_SYM_COLON_ctype__ : _menhir_env -> 'ttv_tail -> _menhir_state -> ((Core_parser_util._sym * Core_ctype.ctype0) list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      match _menhir_s with
      | MenhirState90 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let xs = _v in
          let ((_menhir_stack, _menhir_s, x0), _, y0) = _menhir_stack in
          let _v : ((Core_parser_util._sym * Core_ctype.ctype0) list) = let x =
            let y = y0 in
            let x = x0 in
                ( (x, y) )
          in
              ( x :: xs ) in
          _menhir_goto_separated_nonempty_list_COMMA_separated_pair_SYM_COLON_ctype__ _menhir_env _menhir_stack _menhir_s _v
      | MenhirState47 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let x = _v in
          let _v : ((Core_parser_util._sym * Core_ctype.ctype0) list) =     ( x ) in
          _menhir_goto_loption_separated_nonempty_list_COMMA_separated_pair_SYM_COLON_ctype___ _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_ctype_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Core_ctype.ctype0 list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      match _menhir_s with
      | MenhirState77 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let x = _v in
          let _v : (Core_ctype.ctype0 list) =     ( x ) in
          _menhir_goto_loption_separated_nonempty_list_COMMA_ctype__ _menhir_env _menhir_stack _menhir_s _v
      | MenhirState86 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let xs = _v in
          let (_menhir_stack, _menhir_s, x) = _menhir_stack in
          let _v : (Core_ctype.ctype0 list) =     ( x :: xs ) in
          _menhir_goto_separated_nonempty_list_COMMA_ctype_ _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run75 : _menhir_env -> 'ttv_tail * _menhir_state * (Core_ctype.ctype0) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let (_menhir_stack, _menhir_s, ty) = _menhir_stack in
      let _v : (Core_ctype.ctype0) =     ( Core_ctype.Pointer0 (AilTypes.no_qualifiers, ty) ) in
      _menhir_goto_ctype _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run77 : _menhir_env -> 'ttv_tail * _menhir_state * (Core_ctype.ctype0) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ATOMIC ->
          _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState77
      | Core_parser_util.BOOL ->
          _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState77
      | Core_parser_util.CHAR ->
          _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState77
      | Core_parser_util.INT16_T ->
          _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState77
      | Core_parser_util.INT32_T ->
          _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState77
      | Core_parser_util.INT64_T ->
          _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState77
      | Core_parser_util.INT8_T ->
          _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState77
      | Core_parser_util.SIGNED ->
          _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState77
      | Core_parser_util.SYM _v ->
          _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState77 _v
      | Core_parser_util.UINT16_T ->
          _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState77
      | Core_parser_util.UINT32_T ->
          _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState77
      | Core_parser_util.UINT64_T ->
          _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState77
      | Core_parser_util.UINT8_T ->
          _menhir_run58 _menhir_env (Obj.magic _menhir_stack) MenhirState77
      | Core_parser_util.UNSIGNED ->
          _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState77
      | Core_parser_util.VOID ->
          _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState77
      | Core_parser_util.RPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_s = MenhirState77 in
          let _v : (Core_ctype.ctype0 list) =     ( [] ) in
          _menhir_goto_loption_separated_nonempty_list_COMMA_ctype__ _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState77
  
  and _menhir_run82 : _menhir_env -> 'ttv_tail * _menhir_state * (Core_ctype.ctype0) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.INT_CONST _v ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _ = _menhir_discard _menhir_env in
          let _menhir_stack = Obj.magic _menhir_stack in
          let x = _v in
          let _v : (Nat_big_num.num option) =     ( Some x ) in
          _menhir_goto_option_INT_CONST_ _menhir_env _menhir_stack _v
      | Core_parser_util.RBRACKET ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _v : (Nat_big_num.num option) =     ( None ) in
          _menhir_goto_option_INT_CONST_ _menhir_env _menhir_stack _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_goto_integer_base_type : _menhir_env -> 'ttv_tail -> _menhir_state -> (AilTypes.integerBaseType) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      match _menhir_s with
      | MenhirState51 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ibt = _v in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          let _v : (AilTypes.integerType) =     ( AilTypes.Unsigned ibt ) in
          _menhir_goto_integer_type _menhir_env _menhir_stack _menhir_s _v
      | MenhirState63 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ibt = _v in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          let _v : (AilTypes.integerType) =     ( AilTypes.Signed ibt ) in
          _menhir_goto_integer_type _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_pattern : _menhir_env -> 'ttv_tail -> _menhir_state -> (Core_parser_util._sym option list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState125 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.EQ ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState138 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState138
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState138)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState318 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.EQ ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState320 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState320 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState320 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState320
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState320)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_run129 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (Core_parser_util._sym option) =                 ( None   ) in
      _menhir_goto_pattern_elem _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run130 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Core_parser_util._sym) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let a = _v in
      let _v : (Core_parser_util._sym option) =                 ( Some a ) in
      _menhir_goto_pattern_elem _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_goto_empty_pattern : _menhir_env -> 'ttv_tail -> _menhir_state -> (unit) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState125 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.EQ ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState307 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState307 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState307 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState307
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState307)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState318 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.EQ ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState326 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState326 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState326 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState326
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState326)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState331 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.EQ ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState339
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState339
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState339
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState339
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState339
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState339
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState339
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState339)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (expr list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState179 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, nm), _, xs00) = _menhir_stack in
              let _v : (expr) = let _es =
                let xs0 = xs00 in
                let x =
                  let xs = xs0 in
                      ( xs )
                in
                    ( x )
              in
                  ( PEcall (nm, _es) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState209 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RBRACE ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, nm), _, xs00) = _menhir_stack in
              let _v : (expr) = let _es =
                let xs0 = xs00 in
                let x =
                  let xs = xs0 in
                      ( xs )
                in
                    ( x )
              in
                  ( Eproc (nm, _es) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState139 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RBRACKET ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, xs00) = _menhir_stack in
              let _v : (expr) = let _es =
                let xs0 = xs00 in
                let x =
                  let xs = xs0 in
                      ( xs )
                in
                    ( x )
              in
                  ( Vlist _es ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState120 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, xs00) = _menhir_stack in
              let _v : (expr) = let _es =
                let xs0 = xs00 in
                let x =
                  let xs = xs0 in
                      ( xs )
                in
                    ( x )
              in
                  ( End _es ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState116 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, xs00) = _menhir_stack in
              let _v : (expr) = let _es =
                let xs0 = xs00 in
                let x =
                  let xs = xs0 in
                      ( xs )
                in
                    ( x )
              in
                  ( Epar _es ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_name : _menhir_env -> 'ttv_tail -> _menhir_state -> (name) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState106 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let (((_menhir_stack, _menhir_s), str), _, nm) = _menhir_stack in
              let _v : (expr) =     ( Eregister (str, nm) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState430 | MenhirState424 | MenhirState416 | MenhirState406 | MenhirState31 | MenhirState33 | MenhirState390 | MenhirState388 | MenhirState40 | MenhirState378 | MenhirState44 | MenhirState95 | MenhirState100 | MenhirState102 | MenhirState116 | MenhirState118 | MenhirState120 | MenhirState352 | MenhirState121 | MenhirState344 | MenhirState123 | MenhirState328 | MenhirState326 | MenhirState322 | MenhirState320 | MenhirState315 | MenhirState313 | MenhirState309 | MenhirState307 | MenhirState303 | MenhirState138 | MenhirState139 | MenhirState141 | MenhirState143 | MenhirState145 | MenhirState147 | MenhirState149 | MenhirState152 | MenhirState285 | MenhirState283 | MenhirState154 | MenhirState279 | MenhirState162 | MenhirState275 | MenhirState164 | MenhirState267 | MenhirState265 | MenhirState263 | MenhirState166 | MenhirState249 | MenhirState247 | MenhirState245 | MenhirState168 | MenhirState239 | MenhirState170 | MenhirState219 | MenhirState172 | MenhirState174 | MenhirState213 | MenhirState209 | MenhirState207 | MenhirState205 | MenhirState203 | MenhirState201 | MenhirState199 | MenhirState197 | MenhirState195 | MenhirState193 | MenhirState191 | MenhirState189 | MenhirState186 | MenhirState184 | MenhirState179 | MenhirState176 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.LBRACE ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState209 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState209 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState209 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | Core_parser_util.RBRACE ->
                  _menhir_reduce114 _menhir_env (Obj.magic _menhir_stack) MenhirState209
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState209)
          | Core_parser_util.LPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState179 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | Core_parser_util.RPAREN ->
                  _menhir_reduce114 _menhir_env (Obj.magic _menhir_stack) MenhirState179
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState179)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState221 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.IMPL _v ->
                  _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _v
              | Core_parser_util.SYM _v ->
                  _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState223)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState223 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.IMPL _v ->
                  _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState225 _v
              | Core_parser_util.SYM _v ->
                  _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState225 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState225)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState225 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.IMPL _v ->
                  _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _v
              | Core_parser_util.SYM _v ->
                  _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState227 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState227)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState227 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.IMPL _v ->
                  _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState229 _v
              | Core_parser_util.SYM _v ->
                  _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState229 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState229)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState229 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.IMPL _v ->
                  _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState231 _v
              | Core_parser_util.SYM _v ->
                  _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState231 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState231)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState231 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.IMPL _v ->
                  _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState233 _v
              | Core_parser_util.SYM _v ->
                  _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState233 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState233)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState233 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.IMPL _v ->
                  _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState235 _v
              | Core_parser_util.SYM _v ->
                  _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState235 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState235)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState235 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let (((((((((((_menhir_stack, _menhir_s), _, _e1), _, _e2), _, nm1), _, nm2), _, nm3), _, nm4), _, nm5), _, nm6), _, nm7), _, nm8) = _menhir_stack in
              let _v : (expr) =     ( PEcase_ctype (_e1, _e2, nm1, nm2, nm3, nm4, nm5, nm6, nm7, nm8) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState241 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((((_menhir_stack, _menhir_s), _, _e1), _, _e2), _, nm) = _menhir_stack in
              let _v : (expr) =     ( PEcase_list (_e1, _e2, nm) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_declaration : _menhir_env -> 'ttv_tail -> _menhir_state -> (declaration) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      let _menhir_stack = Obj.magic _menhir_stack in
      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
      let _tok = _menhir_env._menhir_token in
      match _tok with
      | Core_parser_util.DEF ->
          _menhir_run426 _menhir_env (Obj.magic _menhir_stack) MenhirState440
      | Core_parser_util.FUN ->
          _menhir_run409 _menhir_env (Obj.magic _menhir_stack) MenhirState440
      | Core_parser_util.GLOB ->
          _menhir_run400 _menhir_env (Obj.magic _menhir_stack) MenhirState440
      | Core_parser_util.PROC ->
          _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState440
      | Core_parser_util.EOF ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, x) = _menhir_stack in
          let _v : (declaration list) =     ( [ x ] ) in
          _menhir_goto_nonempty_list_declaration_ _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState440
  
  and _menhir_goto_separated_nonempty_list_COMMA_shift_elem_ : _menhir_env -> 'ttv_tail -> _menhir_state -> ((Core_ctype.ctype0 * expr) list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState382 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s, x), _, xs) = _menhir_stack in
          let _v : ((Core_ctype.ctype0 * expr) list) =     ( x :: xs ) in
          _menhir_goto_separated_nonempty_list_COMMA_shift_elem_ _menhir_env _menhir_stack _menhir_s _v
      | MenhirState373 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RBRACE ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.RPAREN ->
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let _ = _menhir_discard _menhir_env in
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let (((_menhir_stack, _menhir_s), _, _e), _, x0) = _menhir_stack in
                  let _v : (expr) = let sh =
                    let x = x0 in
                        ( x )
                  in
                      ( PEshift (_e, sh) ) in
                  _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_run374 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.DQUOTE ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ATOMIC ->
              _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState375
          | Core_parser_util.BOOL ->
              _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState375
          | Core_parser_util.CHAR ->
              _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState375
          | Core_parser_util.INT16_T ->
              _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState375
          | Core_parser_util.INT32_T ->
              _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState375
          | Core_parser_util.INT64_T ->
              _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState375
          | Core_parser_util.INT8_T ->
              _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState375
          | Core_parser_util.SIGNED ->
              _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState375
          | Core_parser_util.SYM _v ->
              _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState375 _v
          | Core_parser_util.UINT16_T ->
              _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState375
          | Core_parser_util.UINT32_T ->
              _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState375
          | Core_parser_util.UINT64_T ->
              _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState375
          | Core_parser_util.UINT8_T ->
              _menhir_run58 _menhir_env (Obj.magic _menhir_stack) MenhirState375
          | Core_parser_util.UNSIGNED ->
              _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState375
          | Core_parser_util.VOID ->
              _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState375
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState375)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_goto_separated_nonempty_list_COMMA_separated_pair_SYM_COLON_expr__ : _menhir_env -> 'ttv_tail -> _menhir_state -> ((Core_parser_util._sym * expr) list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      match _menhir_s with
      | MenhirState364 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let xs = _v in
          let ((_menhir_stack, _menhir_s, x0), _, y0) = _menhir_stack in
          let _v : ((Core_parser_util._sym * expr) list) = let x =
            let y = y0 in
            let x = x0 in
                ( (x, y) )
          in
              ( x :: xs ) in
          _menhir_goto_separated_nonempty_list_COMMA_separated_pair_SYM_COLON_expr__ _menhir_env _menhir_stack _menhir_s _v
      | MenhirState98 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let x = _v in
          let _v : ((Core_parser_util._sym * expr) list) =     ( x ) in
          _menhir_goto_loption_separated_nonempty_list_COMMA_separated_pair_SYM_COLON_expr___ _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run252 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (Cmm.memory_order) =           ( Cmm.Seq_cst ) in
      _menhir_goto_memory_order _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run253 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (Cmm.memory_order) =           ( Cmm.Release ) in
      _menhir_goto_memory_order _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run254 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (Cmm.memory_order) =           ( Cmm.Relaxed ) in
      _menhir_goto_memory_order _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run255 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (Cmm.memory_order) =           ( Cmm.Consume ) in
      _menhir_goto_memory_order _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run256 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (Cmm.memory_order) =           ( Cmm.Acq_rel ) in
      _menhir_goto_memory_order _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run257 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (Cmm.memory_order) =           ( Cmm.Acquire ) in
      _menhir_goto_memory_order _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_goto_action : _menhir_env -> 'ttv_tail -> _menhir_state -> (action) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState430 | MenhirState424 | MenhirState416 | MenhirState406 | MenhirState31 | MenhirState33 | MenhirState40 | MenhirState388 | MenhirState390 | MenhirState44 | MenhirState378 | MenhirState95 | MenhirState100 | MenhirState102 | MenhirState116 | MenhirState118 | MenhirState120 | MenhirState121 | MenhirState352 | MenhirState123 | MenhirState344 | MenhirState341 | MenhirState335 | MenhirState326 | MenhirState328 | MenhirState320 | MenhirState322 | MenhirState313 | MenhirState315 | MenhirState307 | MenhirState309 | MenhirState138 | MenhirState303 | MenhirState139 | MenhirState141 | MenhirState143 | MenhirState145 | MenhirState147 | MenhirState149 | MenhirState152 | MenhirState154 | MenhirState283 | MenhirState285 | MenhirState162 | MenhirState279 | MenhirState164 | MenhirState275 | MenhirState166 | MenhirState263 | MenhirState265 | MenhirState267 | MenhirState168 | MenhirState245 | MenhirState247 | MenhirState249 | MenhirState170 | MenhirState239 | MenhirState172 | MenhirState219 | MenhirState174 | MenhirState176 | MenhirState213 | MenhirState209 | MenhirState179 | MenhirState207 | MenhirState205 | MenhirState189 | MenhirState203 | MenhirState201 | MenhirState199 | MenhirState197 | MenhirState193 | MenhirState195 | MenhirState191 | MenhirState184 | MenhirState186 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, act) = _menhir_stack in
          let _v : (paction) =     ( (Core.Pos, act) ) in
          _menhir_goto_paction _menhir_env _menhir_stack _menhir_s _v
      | MenhirState333 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.IN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState335
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState335
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState335
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState335
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState335
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState335
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState335
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState335
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState335)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState339 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.IN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState341
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState341
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState341
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState341
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState341
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState341
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState341
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState341
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState341)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState38 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _, act) = _menhir_stack in
          let _v : (paction) =     ( (Core.Neg, act) ) in
          _menhir_goto_paction _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_expr_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (expr list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState116 | MenhirState120 | MenhirState139 | MenhirState209 | MenhirState179 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, x) = _menhir_stack in
          let _v : (expr list) =     ( x ) in
          _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ _menhir_env _menhir_stack _menhir_s _v
      | MenhirState205 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s, x), _, xs) = _menhir_stack in
          let _v : (expr list) =     ( x :: xs ) in
          _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_env _menhir_stack _menhir_s _v
      | MenhirState174 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, x0) = _menhir_stack in
              let _v : (expr) = let _es =
                let x = x0 in
                    ( x )
              in
                  ( PEarray _es ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState352 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let (((_menhir_stack, _menhir_s), _, _e), _, _es) = _menhir_stack in
              let _v : (expr) =     ( PEtuple (_e::_es) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState33 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, x0) = _menhir_stack in
              let _v : (expr) = let _es =
                let x = x0 in
                    ( x )
              in
                  ( Eunseq _es ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_run184 : _menhir_env -> 'ttv_tail * _menhir_state * (expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ALLOC ->
          _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.ARRAY ->
          _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.CASE_CTYPE ->
          _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.CASE_LIST ->
          _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
          _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
          _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.CONS ->
          _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.CREATE ->
          _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.DQUOTE ->
          _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.ERROR ->
          _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.FALSE ->
          _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.IF ->
          _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.IMPL _v ->
          _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState184 _v
      | Core_parser_util.INDET ->
          _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.INT_CONST _v ->
          _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState184 _v
      | Core_parser_util.IS_INTEGER ->
          _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.IS_SCALAR ->
          _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.IS_SIGNED ->
          _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.IS_UNSIGNED ->
          _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.KILL ->
          _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.LBRACKET ->
          _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.LET ->
          _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.LOAD ->
          _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.LPAREN ->
          _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.ND ->
          _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.NOT ->
          _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.PAR ->
          _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.RAISE ->
          _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.REGISTER ->
          _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.RETURN ->
          _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.RUN ->
          _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.SAVE ->
          _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.SHIFT ->
          _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.SKIP ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.STORE ->
          _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.SYM _v ->
          _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState184 _v
      | Core_parser_util.TILDE ->
          _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.TRUE ->
          _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.UNDEF ->
          _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.UNIT ->
          _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | Core_parser_util.UNSEQ ->
          _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState184
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState184
  
  and _menhir_run189 : _menhir_env -> 'ttv_tail * _menhir_state * (expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ALLOC ->
          _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.ARRAY ->
          _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.CASE_CTYPE ->
          _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.CASE_LIST ->
          _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
          _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
          _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.CONS ->
          _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.CREATE ->
          _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.DQUOTE ->
          _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.ERROR ->
          _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.FALSE ->
          _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.IF ->
          _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.IMPL _v ->
          _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState189 _v
      | Core_parser_util.INDET ->
          _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.INT_CONST _v ->
          _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState189 _v
      | Core_parser_util.IS_INTEGER ->
          _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.IS_SCALAR ->
          _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.IS_SIGNED ->
          _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.IS_UNSIGNED ->
          _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.KILL ->
          _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.LBRACKET ->
          _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.LET ->
          _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.LOAD ->
          _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.LPAREN ->
          _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.ND ->
          _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.NOT ->
          _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.PAR ->
          _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.RAISE ->
          _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.REGISTER ->
          _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.RETURN ->
          _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.RUN ->
          _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.SAVE ->
          _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.SHIFT ->
          _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.SKIP ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.STORE ->
          _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.SYM _v ->
          _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState189 _v
      | Core_parser_util.TILDE ->
          _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.TRUE ->
          _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.UNDEF ->
          _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.UNIT ->
          _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | Core_parser_util.UNSEQ ->
          _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState189
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState189
  
  and _menhir_run191 : _menhir_env -> 'ttv_tail * _menhir_state * (expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ALLOC ->
          _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.ARRAY ->
          _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.CASE_CTYPE ->
          _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.CASE_LIST ->
          _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
          _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
          _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.CONS ->
          _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.CREATE ->
          _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.DQUOTE ->
          _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.ERROR ->
          _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.FALSE ->
          _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.IF ->
          _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.IMPL _v ->
          _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _v
      | Core_parser_util.INDET ->
          _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.INT_CONST _v ->
          _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _v
      | Core_parser_util.IS_INTEGER ->
          _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.IS_SCALAR ->
          _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.IS_SIGNED ->
          _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.IS_UNSIGNED ->
          _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.KILL ->
          _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.LBRACKET ->
          _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.LET ->
          _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.LOAD ->
          _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.LPAREN ->
          _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.ND ->
          _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.NOT ->
          _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.PAR ->
          _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.RAISE ->
          _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.REGISTER ->
          _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.RETURN ->
          _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.RUN ->
          _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.SAVE ->
          _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.SHIFT ->
          _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.SKIP ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.STORE ->
          _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.SYM _v ->
          _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _v
      | Core_parser_util.TILDE ->
          _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.TRUE ->
          _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.UNDEF ->
          _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.UNIT ->
          _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | Core_parser_util.UNSEQ ->
          _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState191
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState191
  
  and _menhir_run193 : _menhir_env -> 'ttv_tail * _menhir_state * (expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ALLOC ->
          _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.ARRAY ->
          _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.CASE_CTYPE ->
          _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.CASE_LIST ->
          _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
          _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
          _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.CONS ->
          _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.CREATE ->
          _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.DQUOTE ->
          _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.ERROR ->
          _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.FALSE ->
          _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.IF ->
          _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.IMPL _v ->
          _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _v
      | Core_parser_util.INDET ->
          _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.INT_CONST _v ->
          _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _v
      | Core_parser_util.IS_INTEGER ->
          _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.IS_SCALAR ->
          _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.IS_SIGNED ->
          _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.IS_UNSIGNED ->
          _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.KILL ->
          _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.LBRACKET ->
          _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.LET ->
          _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.LOAD ->
          _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.LPAREN ->
          _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.ND ->
          _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.NOT ->
          _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.PAR ->
          _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.RAISE ->
          _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.REGISTER ->
          _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.RETURN ->
          _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.RUN ->
          _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.SAVE ->
          _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.SHIFT ->
          _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.SKIP ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.STORE ->
          _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.SYM _v ->
          _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _v
      | Core_parser_util.TILDE ->
          _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.TRUE ->
          _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.UNDEF ->
          _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.UNIT ->
          _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | Core_parser_util.UNSEQ ->
          _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState193
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState193
  
  and _menhir_run195 : _menhir_env -> 'ttv_tail * _menhir_state * (expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ALLOC ->
          _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.ARRAY ->
          _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.CASE_CTYPE ->
          _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.CASE_LIST ->
          _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
          _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
          _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.CONS ->
          _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.CREATE ->
          _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.DQUOTE ->
          _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.ERROR ->
          _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.FALSE ->
          _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.IF ->
          _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.IMPL _v ->
          _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState195 _v
      | Core_parser_util.INDET ->
          _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.INT_CONST _v ->
          _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState195 _v
      | Core_parser_util.IS_INTEGER ->
          _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.IS_SCALAR ->
          _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.IS_SIGNED ->
          _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.IS_UNSIGNED ->
          _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.KILL ->
          _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.LBRACKET ->
          _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.LET ->
          _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.LOAD ->
          _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.LPAREN ->
          _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.ND ->
          _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.NOT ->
          _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.PAR ->
          _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.RAISE ->
          _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.REGISTER ->
          _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.RETURN ->
          _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.RUN ->
          _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.SAVE ->
          _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.SHIFT ->
          _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.SKIP ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.STORE ->
          _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.SYM _v ->
          _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState195 _v
      | Core_parser_util.TILDE ->
          _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.TRUE ->
          _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.UNDEF ->
          _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.UNIT ->
          _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | Core_parser_util.UNSEQ ->
          _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState195
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState195
  
  and _menhir_run197 : _menhir_env -> 'ttv_tail * _menhir_state * (expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ALLOC ->
          _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.ARRAY ->
          _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.CASE_CTYPE ->
          _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.CASE_LIST ->
          _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
          _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
          _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.CONS ->
          _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.CREATE ->
          _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.DQUOTE ->
          _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.ERROR ->
          _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.FALSE ->
          _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.IF ->
          _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.IMPL _v ->
          _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _v
      | Core_parser_util.INDET ->
          _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.INT_CONST _v ->
          _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _v
      | Core_parser_util.IS_INTEGER ->
          _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.IS_SCALAR ->
          _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.IS_SIGNED ->
          _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.IS_UNSIGNED ->
          _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.KILL ->
          _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.LBRACKET ->
          _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.LET ->
          _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.LOAD ->
          _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.LPAREN ->
          _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.ND ->
          _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.NOT ->
          _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.PAR ->
          _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.RAISE ->
          _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.REGISTER ->
          _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.RETURN ->
          _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.RUN ->
          _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.SAVE ->
          _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.SHIFT ->
          _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.SKIP ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.STORE ->
          _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.SYM _v ->
          _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState197 _v
      | Core_parser_util.TILDE ->
          _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.TRUE ->
          _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.UNDEF ->
          _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.UNIT ->
          _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | Core_parser_util.UNSEQ ->
          _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState197
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState197
  
  and _menhir_run199 : _menhir_env -> 'ttv_tail * _menhir_state * (expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ALLOC ->
          _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.ARRAY ->
          _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.CASE_CTYPE ->
          _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.CASE_LIST ->
          _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
          _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
          _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.CONS ->
          _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.CREATE ->
          _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.DQUOTE ->
          _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.ERROR ->
          _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.FALSE ->
          _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.IF ->
          _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.IMPL _v ->
          _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState199 _v
      | Core_parser_util.INDET ->
          _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.INT_CONST _v ->
          _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState199 _v
      | Core_parser_util.IS_INTEGER ->
          _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.IS_SCALAR ->
          _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.IS_SIGNED ->
          _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.IS_UNSIGNED ->
          _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.KILL ->
          _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.LBRACKET ->
          _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.LET ->
          _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.LOAD ->
          _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.LPAREN ->
          _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.ND ->
          _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.NOT ->
          _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.PAR ->
          _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.RAISE ->
          _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.REGISTER ->
          _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.RETURN ->
          _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.RUN ->
          _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.SAVE ->
          _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.SHIFT ->
          _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.SKIP ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.STORE ->
          _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.SYM _v ->
          _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState199 _v
      | Core_parser_util.TILDE ->
          _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.TRUE ->
          _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.UNDEF ->
          _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.UNIT ->
          _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | Core_parser_util.UNSEQ ->
          _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState199
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState199
  
  and _menhir_run201 : _menhir_env -> 'ttv_tail * _menhir_state * (expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ALLOC ->
          _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.ARRAY ->
          _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.CASE_CTYPE ->
          _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.CASE_LIST ->
          _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
          _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
          _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.CONS ->
          _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.CREATE ->
          _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.DQUOTE ->
          _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.ERROR ->
          _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.FALSE ->
          _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.IF ->
          _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.IMPL _v ->
          _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _v
      | Core_parser_util.INDET ->
          _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.INT_CONST _v ->
          _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _v
      | Core_parser_util.IS_INTEGER ->
          _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.IS_SCALAR ->
          _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.IS_SIGNED ->
          _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.IS_UNSIGNED ->
          _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.KILL ->
          _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.LBRACKET ->
          _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.LET ->
          _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.LOAD ->
          _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.LPAREN ->
          _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.ND ->
          _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.NOT ->
          _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.PAR ->
          _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.RAISE ->
          _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.REGISTER ->
          _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.RETURN ->
          _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.RUN ->
          _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.SAVE ->
          _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.SHIFT ->
          _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.SKIP ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.STORE ->
          _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.SYM _v ->
          _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState201 _v
      | Core_parser_util.TILDE ->
          _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.TRUE ->
          _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.UNDEF ->
          _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.UNIT ->
          _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | Core_parser_util.UNSEQ ->
          _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState201
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState201
  
  and _menhir_run203 : _menhir_env -> 'ttv_tail * _menhir_state * (expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ALLOC ->
          _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.ARRAY ->
          _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.CASE_CTYPE ->
          _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.CASE_LIST ->
          _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
          _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
          _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.CONS ->
          _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.CREATE ->
          _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.DQUOTE ->
          _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.ERROR ->
          _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.FALSE ->
          _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.IF ->
          _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.IMPL _v ->
          _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _v
      | Core_parser_util.INDET ->
          _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.INT_CONST _v ->
          _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _v
      | Core_parser_util.IS_INTEGER ->
          _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.IS_SCALAR ->
          _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.IS_SIGNED ->
          _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.IS_UNSIGNED ->
          _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.KILL ->
          _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.LBRACKET ->
          _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.LET ->
          _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.LOAD ->
          _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.LPAREN ->
          _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.ND ->
          _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.NOT ->
          _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.PAR ->
          _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.RAISE ->
          _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.REGISTER ->
          _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.RETURN ->
          _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.RUN ->
          _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.SAVE ->
          _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.SHIFT ->
          _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.SKIP ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.STORE ->
          _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.SYM _v ->
          _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState203 _v
      | Core_parser_util.TILDE ->
          _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.TRUE ->
          _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.UNDEF ->
          _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.UNIT ->
          _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | Core_parser_util.UNSEQ ->
          _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState203
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState203
  
  and _menhir_run186 : _menhir_env -> 'ttv_tail * _menhir_state * (expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ALLOC ->
          _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.ARRAY ->
          _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.CASE_CTYPE ->
          _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.CASE_LIST ->
          _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
          _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
          _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.CONS ->
          _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.CREATE ->
          _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.DQUOTE ->
          _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.ERROR ->
          _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.FALSE ->
          _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.IF ->
          _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.IMPL _v ->
          _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState186 _v
      | Core_parser_util.INDET ->
          _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.INT_CONST _v ->
          _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState186 _v
      | Core_parser_util.IS_INTEGER ->
          _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.IS_SCALAR ->
          _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.IS_SIGNED ->
          _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.IS_UNSIGNED ->
          _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.KILL ->
          _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.LBRACKET ->
          _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.LET ->
          _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.LOAD ->
          _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.LPAREN ->
          _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.ND ->
          _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.NOT ->
          _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.PAR ->
          _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.RAISE ->
          _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.REGISTER ->
          _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.RETURN ->
          _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.RUN ->
          _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.SAVE ->
          _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.SHIFT ->
          _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.SKIP ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.STORE ->
          _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.SYM _v ->
          _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState186 _v
      | Core_parser_util.TILDE ->
          _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.TRUE ->
          _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.UNDEF ->
          _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.UNIT ->
          _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | Core_parser_util.UNSEQ ->
          _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState186
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState186
  
  and _menhir_run207 : _menhir_env -> 'ttv_tail * _menhir_state * (expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ALLOC ->
          _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.ARRAY ->
          _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.CASE_CTYPE ->
          _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.CASE_LIST ->
          _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
          _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
          _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.CONS ->
          _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.CREATE ->
          _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.DQUOTE ->
          _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.ERROR ->
          _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.FALSE ->
          _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.IF ->
          _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.IMPL _v ->
          _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState207 _v
      | Core_parser_util.INDET ->
          _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.INT_CONST _v ->
          _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState207 _v
      | Core_parser_util.IS_INTEGER ->
          _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.IS_SCALAR ->
          _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.IS_SIGNED ->
          _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.IS_UNSIGNED ->
          _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.KILL ->
          _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.LBRACKET ->
          _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.LET ->
          _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.LOAD ->
          _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.LPAREN ->
          _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.ND ->
          _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.NOT ->
          _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.PAR ->
          _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.RAISE ->
          _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.REGISTER ->
          _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.RETURN ->
          _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.RUN ->
          _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.SAVE ->
          _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.SHIFT ->
          _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.SKIP ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.STORE ->
          _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.SYM _v ->
          _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState207 _v
      | Core_parser_util.TILDE ->
          _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.TRUE ->
          _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.UNDEF ->
          _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.UNIT ->
          _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | Core_parser_util.UNSEQ ->
          _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState207
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState207
  
  and _menhir_goto_ctype : _menhir_env -> 'ttv_tail -> _menhir_state -> (Core_ctype.ctype0) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState72 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.LBRACKET ->
              _menhir_run82 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LPAREN ->
              _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, x0) = _menhir_stack in
              let _v : (Core_ctype.ctype0) = let ty =
                let x = x0 in
                    ( x )
              in
                  ( Core_ctype.Atomic0 ty ) in
              _menhir_goto_ctype _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.STAR ->
              _menhir_run75 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState86 | MenhirState77 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ATOMIC ->
                  _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState86
              | Core_parser_util.BOOL ->
                  _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState86
              | Core_parser_util.CHAR ->
                  _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState86
              | Core_parser_util.INT16_T ->
                  _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState86
              | Core_parser_util.INT32_T ->
                  _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState86
              | Core_parser_util.INT64_T ->
                  _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState86
              | Core_parser_util.INT8_T ->
                  _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState86
              | Core_parser_util.SIGNED ->
                  _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState86
              | Core_parser_util.SYM _v ->
                  _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState86 _v
              | Core_parser_util.UINT16_T ->
                  _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState86
              | Core_parser_util.UINT32_T ->
                  _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState86
              | Core_parser_util.UINT64_T ->
                  _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState86
              | Core_parser_util.UINT8_T ->
                  _menhir_run58 _menhir_env (Obj.magic _menhir_stack) MenhirState86
              | Core_parser_util.UNSIGNED ->
                  _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState86
              | Core_parser_util.VOID ->
                  _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState86
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState86)
          | Core_parser_util.LBRACKET ->
              _menhir_run82 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LPAREN ->
              _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run75 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, x) = _menhir_stack in
              let _v : (Core_ctype.ctype0 list) =     ( [ x ] ) in
              _menhir_goto_separated_nonempty_list_COMMA_ctype_ _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState49 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.SYM _v ->
                  _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState90 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState90)
          | Core_parser_util.LBRACKET ->
              _menhir_run82 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LPAREN ->
              _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run75 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, x0), _, y0) = _menhir_stack in
              let _v : ((Core_parser_util._sym * Core_ctype.ctype0) list) = let x =
                let y = y0 in
                let x = x0 in
                    ( (x, y) )
              in
                  ( [ x ] ) in
              _menhir_goto_separated_nonempty_list_COMMA_separated_pair_SYM_COLON_ctype__ _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState158 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.DQUOTE ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, x0) = _menhir_stack in
              let _v : (expr) = let ty =
                let x = x0 in
                    ( x )
              in
                  ( Vctype ty ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.LBRACKET ->
              _menhir_run82 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LPAREN ->
              _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run75 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState375 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.DQUOTE ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.COMMA ->
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let _tok = _menhir_discard _menhir_env in
                  (match _tok with
                  | Core_parser_util.ALLOC ->
                      _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.ARRAY ->
                      _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.CASE_CTYPE ->
                      _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.CASE_LIST ->
                      _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                      _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                      _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.CONS ->
                      _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.CREATE ->
                      _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.DQUOTE ->
                      _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.ERROR ->
                      _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.FALSE ->
                      _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.IF ->
                      _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.IMPL _v ->
                      _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState378 _v
                  | Core_parser_util.INDET ->
                      _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.INT_CONST _v ->
                      _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState378 _v
                  | Core_parser_util.IS_INTEGER ->
                      _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.IS_SCALAR ->
                      _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.IS_SIGNED ->
                      _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.IS_UNSIGNED ->
                      _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.KILL ->
                      _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.LBRACKET ->
                      _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.LET ->
                      _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.LOAD ->
                      _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.LPAREN ->
                      _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.ND ->
                      _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.NOT ->
                      _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.PAR ->
                      _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.RAISE ->
                      _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.REGISTER ->
                      _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.RETURN ->
                      _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.RUN ->
                      _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.SAVE ->
                      _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.SHIFT ->
                      _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.SKIP ->
                      _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.STORE ->
                      _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.SYM _v ->
                      _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState378 _v
                  | Core_parser_util.TILDE ->
                      _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.TRUE ->
                      _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.UNDEF ->
                      _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.UNIT ->
                      _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | Core_parser_util.UNSEQ ->
                      _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState378
                  | _ ->
                      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                      _menhir_env._menhir_shifted <- (-1);
                      _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState378)
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
          | Core_parser_util.LBRACKET ->
              _menhir_run82 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LPAREN ->
              _menhir_run77 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run75 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_run52 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (AilTypes.integerBaseType) =     ( AilTypes.Short ) in
      _menhir_goto_integer_base_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run53 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (AilTypes.integerBaseType) =     ( AilTypes.LongLong ) in
      _menhir_goto_integer_base_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run54 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (AilTypes.integerBaseType) =     ( AilTypes.Long ) in
      _menhir_goto_integer_base_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run55 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (AilTypes.integerBaseType) =     ( AilTypes.Int_ ) in
      _menhir_goto_integer_base_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run56 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (AilTypes.integerBaseType) =     ( AilTypes.Ichar ) in
      _menhir_goto_integer_base_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_goto_integer_type : _menhir_env -> 'ttv_tail -> _menhir_state -> (AilTypes.integerType) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = Obj.magic _menhir_stack in
      let _menhir_stack = Obj.magic _menhir_stack in
      let it = _v in
      let _v : (AilTypes.basicType) =     ( AilTypes.Integer it ) in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _menhir_stack = Obj.magic _menhir_stack in
      let bty = _v in
      let _v : (Core_ctype.ctype0) =     ( Core_ctype.Basic0 bty ) in
      _menhir_goto_ctype _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_reduce128 : _menhir_env -> 'ttv_tail * _menhir_state * (Core_parser_util._sym) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let (_menhir_stack, _menhir_s, _sym) = _menhir_stack in
      let _v : (name) =     ( Sym _sym ) in
      _menhir_goto_name _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_separated_pair_SYM_COLON_ctype___ : _menhir_env -> 'ttv_tail -> _menhir_state -> ((Core_parser_util._sym * Core_ctype.ctype0) list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      let _menhir_stack = Obj.magic _menhir_stack in
      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
      let _tok = _menhir_env._menhir_token in
      match _tok with
      | Core_parser_util.RPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.DOT ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState95 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState95
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState95)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run48 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Core_parser_util._sym) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.COLON ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ATOMIC ->
              _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState49
          | Core_parser_util.BOOL ->
              _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState49
          | Core_parser_util.CHAR ->
              _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState49
          | Core_parser_util.INT16_T ->
              _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState49
          | Core_parser_util.INT32_T ->
              _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState49
          | Core_parser_util.INT64_T ->
              _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState49
          | Core_parser_util.INT8_T ->
              _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState49
          | Core_parser_util.SIGNED ->
              _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState49
          | Core_parser_util.SYM _v ->
              _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState49 _v
          | Core_parser_util.UINT16_T ->
              _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState49
          | Core_parser_util.UINT32_T ->
              _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState49
          | Core_parser_util.UINT64_T ->
              _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState49
          | Core_parser_util.UINT8_T ->
              _menhir_run58 _menhir_env (Obj.magic _menhir_stack) MenhirState49
          | Core_parser_util.UNSIGNED ->
              _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState49
          | Core_parser_util.VOID ->
              _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState49
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState49)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_separated_pair_SYM_COLON_expr___ : _menhir_env -> 'ttv_tail -> _menhir_state -> ((Core_parser_util._sym * expr) list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      let _menhir_stack = Obj.magic _menhir_stack in
      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
      let _tok = _menhir_env._menhir_token in
      match _tok with
      | Core_parser_util.RPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _ = _menhir_discard _menhir_env in
          let _menhir_stack = Obj.magic _menhir_stack in
          let (((_menhir_stack, _menhir_s), d), _, xs00) = _menhir_stack in
          let _v : (expr) = let str__es =
            let xs0 = xs00 in
            let x =
              let xs = xs0 in
                  ( xs )
            in
                ( x )
          in
              ( Erun (d, str__es) ) in
          _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run99 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Core_parser_util._sym) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.COLON ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState100 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState100
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState100)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run107 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Core_parser_util._sym) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      let _ = _menhir_discard _menhir_env in
      _menhir_reduce128 _menhir_env (Obj.magic _menhir_stack)
  
  and _menhir_run108 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Implementation_.implementation_constant) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      let _ = _menhir_discard _menhir_env in
      _menhir_reduce129 _menhir_env (Obj.magic _menhir_stack)
  
  and _menhir_run127 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Core_parser_util._sym) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let sym = _v in
      let _v : (Core_parser_util._sym option list) =     ( [Some sym] ) in
      _menhir_goto_pattern _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run128 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.RPAREN ->
          _menhir_run131 _menhir_env (Obj.magic _menhir_stack) MenhirState128
      | Core_parser_util.SYM _v ->
          _menhir_run130 _menhir_env (Obj.magic _menhir_stack) MenhirState128 _v
      | Core_parser_util.UNDERSCORE ->
          _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState128
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState128
  
  and _menhir_run126 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (unit) =     ( ) in
      _menhir_goto_empty_pattern _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run131 : _menhir_env -> 'ttv_tail * _menhir_state -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let (_menhir_stack, _menhir_s) = _menhir_stack in
      let _v : (unit) =     ( ) in
      _menhir_goto_empty_pattern _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_reduce114 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _v : (expr list) =     ( [] ) in
      _menhir_goto_loption_separated_nonempty_list_COMMA_expr__ _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_reduce129 : _menhir_env -> 'ttv_tail * _menhir_state * (Implementation_.implementation_constant) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let (_menhir_stack, _menhir_s, i) = _menhir_stack in
      let _v : (name) =     ( Impl i ) in
      _menhir_goto_name _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_goto_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> (expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState33 | MenhirState116 | MenhirState120 | MenhirState352 | MenhirState139 | MenhirState174 | MenhirState209 | MenhirState205 | MenhirState179 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState205 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState205 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState205 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState205
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState205)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RBRACE | Core_parser_util.RBRACKET | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, x) = _menhir_stack in
              let _v : (expr list) =     ( [ x ] ) in
              _menhir_goto_separated_nonempty_list_COMMA_expr_ _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState184 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.BACKSLASH_SLASH | Core_parser_util.COMMA | Core_parser_util.DEF | Core_parser_util.ELSE | Core_parser_util.END | Core_parser_util.EOF | Core_parser_util.EQ | Core_parser_util.FUN | Core_parser_util.GLOB | Core_parser_util.IN | Core_parser_util.LE | Core_parser_util.LT | Core_parser_util.MINUS | Core_parser_util.PERCENT | Core_parser_util.PLUS | Core_parser_util.PROC | Core_parser_util.RBRACE | Core_parser_util.RBRACKET | Core_parser_util.RPAREN | Core_parser_util.SLASH | Core_parser_util.SLASH_BACKSLASH | Core_parser_util.STAR | Core_parser_util.THEN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, _e1), _, _e2) = _menhir_stack in
              let _v : (expr) = let bop =
                                  ( Core.OpMul )
              in
                  ( PEop (bop, _e1, _e2) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState186 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH | Core_parser_util.COMMA | Core_parser_util.DEF | Core_parser_util.ELSE | Core_parser_util.END | Core_parser_util.EOF | Core_parser_util.EQ | Core_parser_util.FUN | Core_parser_util.GLOB | Core_parser_util.IN | Core_parser_util.LE | Core_parser_util.LT | Core_parser_util.MINUS | Core_parser_util.PERCENT | Core_parser_util.PLUS | Core_parser_util.PROC | Core_parser_util.RBRACE | Core_parser_util.RBRACKET | Core_parser_util.RPAREN | Core_parser_util.SLASH | Core_parser_util.SLASH_BACKSLASH | Core_parser_util.STAR | Core_parser_util.THEN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, _e1), _, _e2) = _menhir_stack in
              let _v : (expr) = let bop =
                                  ( Core.OpExp )
              in
                  ( PEop (bop, _e1, _e2) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState189 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.BACKSLASH_SLASH | Core_parser_util.COMMA | Core_parser_util.DEF | Core_parser_util.ELSE | Core_parser_util.END | Core_parser_util.EOF | Core_parser_util.FUN | Core_parser_util.GLOB | Core_parser_util.IN | Core_parser_util.PROC | Core_parser_util.RBRACE | Core_parser_util.RBRACKET | Core_parser_util.RPAREN | Core_parser_util.THEN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, _e1), _, _e2) = _menhir_stack in
              let _v : (expr) = let bop =
                                  ( Core.OpAnd )
              in
                  ( PEop (bop, _e1, _e2) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState191 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.BACKSLASH_SLASH | Core_parser_util.COMMA | Core_parser_util.DEF | Core_parser_util.ELSE | Core_parser_util.END | Core_parser_util.EOF | Core_parser_util.EQ | Core_parser_util.FUN | Core_parser_util.GLOB | Core_parser_util.IN | Core_parser_util.LE | Core_parser_util.LT | Core_parser_util.MINUS | Core_parser_util.PERCENT | Core_parser_util.PLUS | Core_parser_util.PROC | Core_parser_util.RBRACE | Core_parser_util.RBRACKET | Core_parser_util.RPAREN | Core_parser_util.SLASH | Core_parser_util.SLASH_BACKSLASH | Core_parser_util.STAR | Core_parser_util.THEN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, _e1), _, _e2) = _menhir_stack in
              let _v : (expr) = let bop =
                                  ( Core.OpDiv )
              in
                  ( PEop (bop, _e1, _e2) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState193 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.BACKSLASH_SLASH | Core_parser_util.COMMA | Core_parser_util.DEF | Core_parser_util.ELSE | Core_parser_util.END | Core_parser_util.EOF | Core_parser_util.EQ | Core_parser_util.FUN | Core_parser_util.GLOB | Core_parser_util.IN | Core_parser_util.LE | Core_parser_util.LT | Core_parser_util.MINUS | Core_parser_util.PLUS | Core_parser_util.PROC | Core_parser_util.RBRACE | Core_parser_util.RBRACKET | Core_parser_util.RPAREN | Core_parser_util.SLASH_BACKSLASH | Core_parser_util.THEN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, _e1), _, _e2) = _menhir_stack in
              let _v : (expr) = let bop =
                                  ( Core.OpAdd )
              in
                  ( PEop (bop, _e1, _e2) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState195 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.BACKSLASH_SLASH | Core_parser_util.COMMA | Core_parser_util.DEF | Core_parser_util.ELSE | Core_parser_util.END | Core_parser_util.EOF | Core_parser_util.EQ | Core_parser_util.FUN | Core_parser_util.GLOB | Core_parser_util.IN | Core_parser_util.LE | Core_parser_util.LT | Core_parser_util.MINUS | Core_parser_util.PERCENT | Core_parser_util.PLUS | Core_parser_util.PROC | Core_parser_util.RBRACE | Core_parser_util.RBRACKET | Core_parser_util.RPAREN | Core_parser_util.SLASH | Core_parser_util.SLASH_BACKSLASH | Core_parser_util.STAR | Core_parser_util.THEN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, _e1), _, _e2) = _menhir_stack in
              let _v : (expr) = let bop =
                                  ( Core.OpMod )
              in
                  ( PEop (bop, _e1, _e2) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState197 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.BACKSLASH_SLASH | Core_parser_util.COMMA | Core_parser_util.DEF | Core_parser_util.ELSE | Core_parser_util.END | Core_parser_util.EOF | Core_parser_util.EQ | Core_parser_util.FUN | Core_parser_util.GLOB | Core_parser_util.IN | Core_parser_util.LE | Core_parser_util.LT | Core_parser_util.MINUS | Core_parser_util.PLUS | Core_parser_util.PROC | Core_parser_util.RBRACE | Core_parser_util.RBRACKET | Core_parser_util.RPAREN | Core_parser_util.SLASH_BACKSLASH | Core_parser_util.THEN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, _e1), _, _e2) = _menhir_stack in
              let _v : (expr) = let bop =
                                  ( Core.OpSub )
              in
                  ( PEop (bop, _e1, _e2) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState199 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.BACKSLASH_SLASH | Core_parser_util.COMMA | Core_parser_util.DEF | Core_parser_util.ELSE | Core_parser_util.END | Core_parser_util.EOF | Core_parser_util.EQ | Core_parser_util.FUN | Core_parser_util.GLOB | Core_parser_util.IN | Core_parser_util.LE | Core_parser_util.LT | Core_parser_util.PROC | Core_parser_util.RBRACE | Core_parser_util.RBRACKET | Core_parser_util.RPAREN | Core_parser_util.SLASH_BACKSLASH | Core_parser_util.THEN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, _e1), _, _e2) = _menhir_stack in
              let _v : (expr) = let bop =
                                  ( Core.OpLt  )
              in
                  ( PEop (bop, _e1, _e2) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState201 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.BACKSLASH_SLASH | Core_parser_util.COMMA | Core_parser_util.DEF | Core_parser_util.ELSE | Core_parser_util.END | Core_parser_util.EOF | Core_parser_util.EQ | Core_parser_util.FUN | Core_parser_util.GLOB | Core_parser_util.IN | Core_parser_util.LE | Core_parser_util.LT | Core_parser_util.PROC | Core_parser_util.RBRACE | Core_parser_util.RBRACKET | Core_parser_util.RPAREN | Core_parser_util.SLASH_BACKSLASH | Core_parser_util.THEN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, _e1), _, _e2) = _menhir_stack in
              let _v : (expr) =     ( PEop (Core.OpOr, PEop (Core.OpLt, _e1, _e2), PEop (Core.OpEq, _e1, _e2)) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState203 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.BACKSLASH_SLASH | Core_parser_util.COMMA | Core_parser_util.DEF | Core_parser_util.ELSE | Core_parser_util.END | Core_parser_util.EOF | Core_parser_util.EQ | Core_parser_util.FUN | Core_parser_util.GLOB | Core_parser_util.IN | Core_parser_util.LE | Core_parser_util.LT | Core_parser_util.PROC | Core_parser_util.RBRACE | Core_parser_util.RBRACKET | Core_parser_util.RPAREN | Core_parser_util.SLASH_BACKSLASH | Core_parser_util.THEN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, _e1), _, _e2) = _menhir_stack in
              let _v : (expr) = let bop =
                                  ( Core.OpEq  )
              in
                  ( PEop (bop, _e1, _e2) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState207 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA | Core_parser_util.DEF | Core_parser_util.ELSE | Core_parser_util.END | Core_parser_util.EOF | Core_parser_util.FUN | Core_parser_util.GLOB | Core_parser_util.IN | Core_parser_util.PROC | Core_parser_util.RBRACE | Core_parser_util.RBRACKET | Core_parser_util.RPAREN | Core_parser_util.THEN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, _e1), _, _e2) = _menhir_stack in
              let _v : (expr) = let bop =
                                  ( Core.OpOr  )
              in
                  ( PEop (bop, _e1, _e2) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState176 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState213 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState213 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState213 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState213
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState213)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState213 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let (((_menhir_stack, _menhir_s), _, e1), _, e2) = _menhir_stack in
              let _v : (action) =     ( Alloc (e1, e2) ) in
              _menhir_goto_action _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState172 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState219 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState219
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState219)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState219 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.IMPL _v ->
                  _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState221 _v
              | Core_parser_util.SYM _v ->
                  _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState221 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState221)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState170 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState239 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState239
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState239)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState239 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.IMPL _v ->
                  _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState241 _v
              | Core_parser_util.SYM _v ->
                  _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState241 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState241)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState168 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState245 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState245 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState245 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState245
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState245)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState245 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState247 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState247 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState247 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState247
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState247)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState247 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState249 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState249 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState249 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState249
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState249)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState249 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ACQUIRE ->
                  _menhir_run257 _menhir_env (Obj.magic _menhir_stack) MenhirState251
              | Core_parser_util.ACQ_REL ->
                  _menhir_run256 _menhir_env (Obj.magic _menhir_stack) MenhirState251
              | Core_parser_util.CONSUME ->
                  _menhir_run255 _menhir_env (Obj.magic _menhir_stack) MenhirState251
              | Core_parser_util.RELAXED ->
                  _menhir_run254 _menhir_env (Obj.magic _menhir_stack) MenhirState251
              | Core_parser_util.RELEASE ->
                  _menhir_run253 _menhir_env (Obj.magic _menhir_stack) MenhirState251
              | Core_parser_util.SEQ_CST ->
                  _menhir_run252 _menhir_env (Obj.magic _menhir_stack) MenhirState251
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState251)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState166 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState263 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState263 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState263 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState263
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState263)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState263 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState265 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState265 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState265 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState265
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState265)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState265 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState267 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState267 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState267 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState267
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState267)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState267 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ACQUIRE ->
                  _menhir_run257 _menhir_env (Obj.magic _menhir_stack) MenhirState269
              | Core_parser_util.ACQ_REL ->
                  _menhir_run256 _menhir_env (Obj.magic _menhir_stack) MenhirState269
              | Core_parser_util.CONSUME ->
                  _menhir_run255 _menhir_env (Obj.magic _menhir_stack) MenhirState269
              | Core_parser_util.RELAXED ->
                  _menhir_run254 _menhir_env (Obj.magic _menhir_stack) MenhirState269
              | Core_parser_util.RELEASE ->
                  _menhir_run253 _menhir_env (Obj.magic _menhir_stack) MenhirState269
              | Core_parser_util.SEQ_CST ->
                  _menhir_run252 _menhir_env (Obj.magic _menhir_stack) MenhirState269
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState269)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState164 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState275 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState275 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState275 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState275
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState275)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState275 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let (((_menhir_stack, _menhir_s), _, _e1), _, _e2) = _menhir_stack in
              let _v : (expr) =     ( PEcons (_e1, _e2) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState162 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState279 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState279 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState279 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState279
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState279)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState279 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let (((_menhir_stack, _menhir_s), _, e1), _, e2) = _menhir_stack in
              let _v : (action) =     ( Create (e1, e2) ) in
              _menhir_goto_action _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState154 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.THEN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState283 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState283 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState283 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState283
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState283)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState283 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.ELSE ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState285 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState285 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState285 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState285
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState285)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState285 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.END ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((((_menhir_stack, _menhir_s), _, _e1), _, _e2), _, _e3) = _menhir_stack in
              let _v : (expr) =     ( Eif (_e1, _e2, _e3) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState152 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, x0) = _menhir_stack in
              let _v : (expr) = let _e =
                let x = x0 in
                    ( x )
              in
                  ( Eindet _e ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState149 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, x0) = _menhir_stack in
              let _v : (expr) = let _e =
                let x = x0 in
                    ( x )
              in
                  ( PEis_integer _e ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState147 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, x0) = _menhir_stack in
              let _v : (expr) = let _e =
                let x = x0 in
                    ( x )
              in
                  ( PEis_scalar _e ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState145 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, x0) = _menhir_stack in
              let _v : (expr) = let _e =
                let x = x0 in
                    ( x )
              in
                  ( PEis_signed _e ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState143 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, x0) = _menhir_stack in
              let _v : (expr) = let _e =
                let x = x0 in
                    ( x )
              in
                  ( PEis_unsigned _e ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState141 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, x0) = _menhir_stack in
              let _v : (action) = let e =
                let x = x0 in
                    ( x )
              in
                  ( Kill e ) in
              _menhir_goto_action _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState138 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.IN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState303 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState303 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState303 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState303
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState303)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState303 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.END ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((((_menhir_stack, _menhir_s), _, _as), _, _e1), _, _e2) = _menhir_stack in
              let _v : (expr) =     ( Ewseq (_as, _e1, _e2) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState307 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.IN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState309 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState309 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState309 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState309
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState309)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState309 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.END ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((((_menhir_stack, _menhir_s), _, _), _, _e1), _, _e2) = _menhir_stack in
              let _v : (expr) =     ( Ewseq ([], _e1, _e2) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState313 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.IN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState315 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState315 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState315 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState315
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState315)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState315 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.END ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((((_menhir_stack, _menhir_s), str), _, _e1), _, _e2) = _menhir_stack in
              let _v : (expr) =     ( Elet (str, _e1, _e2) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState320 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.IN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState322 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState322 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState322 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState322
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState322)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState322 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.END ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((((_menhir_stack, _menhir_s), _, _as), _, _e1), _, _e2) = _menhir_stack in
              let _v : (expr) =     ( Esseq (_as, _e1, _e2) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState326 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.IN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState328 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState328 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState328 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState328
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState328)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState328 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.END ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((((_menhir_stack, _menhir_s), _, _), _, _e1), _, _e2) = _menhir_stack in
              let _v : (expr) =     ( Esseq ([], _e1, _e2) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState123 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState344 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState344 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState344 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState344
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState344)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState344 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ACQUIRE ->
                  _menhir_run257 _menhir_env (Obj.magic _menhir_stack) MenhirState347
              | Core_parser_util.ACQ_REL ->
                  _menhir_run256 _menhir_env (Obj.magic _menhir_stack) MenhirState347
              | Core_parser_util.CONSUME ->
                  _menhir_run255 _menhir_env (Obj.magic _menhir_stack) MenhirState347
              | Core_parser_util.RELAXED ->
                  _menhir_run254 _menhir_env (Obj.magic _menhir_stack) MenhirState347
              | Core_parser_util.RELEASE ->
                  _menhir_run253 _menhir_env (Obj.magic _menhir_stack) MenhirState347
              | Core_parser_util.SEQ_CST ->
                  _menhir_run252 _menhir_env (Obj.magic _menhir_stack) MenhirState347
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState347)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let (((_menhir_stack, _menhir_s), _, e1), _, e2) = _menhir_stack in
              let _v : (action) =     ( Load (e1, e2, Cmm.NA) ) in
              _menhir_goto_action _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState121 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState352 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState352
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState352)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, _e) = _menhir_stack in
              let _v : (expr) =     ( _e ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState118 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, x0) = _menhir_stack in
              let _v : (expr) = let _e =
                let x = x0 in
                    ( x )
              in
                  ( PEnot _e ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState102 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, x0) = _menhir_stack in
              let _v : (expr) = let _e =
                let x = x0 in
                    ( x )
              in
                  ( Eret _e ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState100 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.SYM _v ->
                  _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState364 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState364)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, x0), _, y0) = _menhir_stack in
              let _v : ((Core_parser_util._sym * expr) list) = let x =
                let y = y0 in
                let x = x0 in
                    ( (x, y) )
              in
                  ( [ x ] ) in
              _menhir_goto_separated_nonempty_list_COMMA_separated_pair_SYM_COLON_expr__ _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState95 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.END ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((((_menhir_stack, _menhir_s), str), _, xs00), _, _e) = _menhir_stack in
              let _v : (expr) = let str_tys =
                let xs0 = xs00 in
                let x =
                  let xs = xs0 in
                      ( xs )
                in
                    ( x )
              in
                  ( Esave (str, str_tys, _e) ) in
              _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState44 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.LBRACE ->
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let _tok = _menhir_discard _menhir_env in
                  (match _tok with
                  | Core_parser_util.LPAREN ->
                      _menhir_run374 _menhir_env (Obj.magic _menhir_stack) MenhirState373
                  | _ ->
                      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                      _menhir_env._menhir_shifted <- (-1);
                      _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState373)
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState378 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let (((_menhir_stack, _menhir_s), _, x0), _, _e) = _menhir_stack in
              let _v : (Core_ctype.ctype0 * expr) = let ty =
                let x = x0 in
                    ( x )
              in
                ( (ty, _e) ) in
              let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
              let _menhir_stack = Obj.magic _menhir_stack in
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              let _tok = _menhir_env._menhir_token in
              (match _tok with
              | Core_parser_util.COMMA ->
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let _tok = _menhir_discard _menhir_env in
                  (match _tok with
                  | Core_parser_util.LPAREN ->
                      _menhir_run374 _menhir_env (Obj.magic _menhir_stack) MenhirState382
                  | _ ->
                      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                      _menhir_env._menhir_shifted <- (-1);
                      _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState382)
              | Core_parser_util.RBRACE ->
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let (_menhir_stack, _menhir_s, x) = _menhir_stack in
                  let _v : ((Core_ctype.ctype0 * expr) list) =     ( [ x ] ) in
                  _menhir_goto_separated_nonempty_list_COMMA_shift_elem_ _menhir_env _menhir_stack _menhir_s _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState40 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState388 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState388 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState388 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState388
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState388)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState388 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState390 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState390 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState390 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState390
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState390)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState390 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ACQUIRE ->
                  _menhir_run257 _menhir_env (Obj.magic _menhir_stack) MenhirState393
              | Core_parser_util.ACQ_REL ->
                  _menhir_run256 _menhir_env (Obj.magic _menhir_stack) MenhirState393
              | Core_parser_util.CONSUME ->
                  _menhir_run255 _menhir_env (Obj.magic _menhir_stack) MenhirState393
              | Core_parser_util.RELAXED ->
                  _menhir_run254 _menhir_env (Obj.magic _menhir_stack) MenhirState393
              | Core_parser_util.RELEASE ->
                  _menhir_run253 _menhir_env (Obj.magic _menhir_stack) MenhirState393
              | Core_parser_util.SEQ_CST ->
                  _menhir_run252 _menhir_env (Obj.magic _menhir_stack) MenhirState393
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState393)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((((_menhir_stack, _menhir_s), _, e1), _, e2), _, e3) = _menhir_stack in
              let _v : (action) =     ( Store (e1, e2, e3, Cmm.NA) ) in
              _menhir_goto_action _menhir_env _menhir_stack _menhir_s _v
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState31 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.DEF | Core_parser_util.EOF | Core_parser_util.FUN | Core_parser_util.GLOB | Core_parser_util.PROC ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let (((((_menhir_stack, _menhir_s), _sym), _, xs00), _, bTy), _, fbody) = _menhir_stack in
              let _v : (declaration) = let params =
                let xs0 = xs00 in
                let x =
                  let xs = xs0 in
                      ( xs )
                in
                    ( x )
              in
                  ( Proc_decl (_sym, (bTy, params, fbody)) ) in
              let _menhir_stack = Obj.magic _menhir_stack in
              let _menhir_stack = Obj.magic _menhir_stack in
              let d = _v in
              let _v : (declaration) =     ( d ) in
              _menhir_goto_declaration _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState406 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.DEF | Core_parser_util.EOF | Core_parser_util.FUN | Core_parser_util.GLOB | Core_parser_util.PROC ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((((_menhir_stack, _menhir_s), gname), _, cTy), _, e) = _menhir_stack in
              let _v : (declaration) =   (
   print_endline "GLOB";
   Glob_decl (gname, cTy, e) ) in
              let _menhir_stack = Obj.magic _menhir_stack in
              let _menhir_stack = Obj.magic _menhir_stack in
              let d = _v in
              let _v : (declaration) =     ( d ) in
              _menhir_goto_declaration _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState416 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.DEF | Core_parser_util.EOF | Core_parser_util.FUN | Core_parser_util.GLOB | Core_parser_util.PROC ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let (((((_menhir_stack, _menhir_s), fname), _, xs00), _, bTy), _, fbody) = _menhir_stack in
              let _v : (declaration) = let params =
                let xs0 = xs00 in
                let x =
                  let xs = xs0 in
                      ( xs )
                in
                    ( x )
              in
                  ( Fun_decl (fname, (bTy, params, fbody)) ) in
              let _menhir_stack = Obj.magic _menhir_stack in
              let _menhir_stack = Obj.magic _menhir_stack in
              let d = _v in
              let _v : (declaration) =     ( d ) in
              _menhir_goto_declaration _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState424 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.DEF | Core_parser_util.EOF | Core_parser_util.FUN | Core_parser_util.GLOB | Core_parser_util.PROC ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let (((((_menhir_stack, _menhir_s), fname), _, xs00), _, bTy), _, fbody) = _menhir_stack in
              let _v : (declaration) = let params =
                let xs0 = xs00 in
                let x =
                  let xs = xs0 in
                      ( xs )
                in
                    ( x )
              in
                  ( IFun_decl (fname, (bTy, params, fbody)) ) in
              let _menhir_stack = Obj.magic _menhir_stack in
              let _menhir_stack = Obj.magic _menhir_stack in
              let d = _v in
              let _v : (declaration) =     ( d ) in
              _menhir_goto_declaration _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState430 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.BACKSLASH_SLASH ->
              _menhir_run207 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.CARET ->
              _menhir_run186 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.EQ ->
              _menhir_run203 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LE ->
              _menhir_run201 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.LT ->
              _menhir_run199 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.MINUS ->
              _menhir_run197 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PERCENT ->
              _menhir_run195 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.PLUS ->
              _menhir_run193 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH ->
              _menhir_run191 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.SLASH_BACKSLASH ->
              _menhir_run189 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.STAR ->
              _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
          | Core_parser_util.DEF | Core_parser_util.EOF | Core_parser_util.FUN | Core_parser_util.GLOB | Core_parser_util.PROC ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((((_menhir_stack, _menhir_s), dname), _, bTy), _, e) = _menhir_stack in
              let _v : (declaration) =     ( Def_decl (dname, bTy, e) ) in
              let _menhir_stack = Obj.magic _menhir_stack in
              let _menhir_stack = Obj.magic _menhir_stack in
              let d = _v in
              let _v : (declaration) =     ( d ) in
              _menhir_goto_declaration _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_run50 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (Core_ctype.ctype0) =     ( Core_ctype.Void0 ) in
      _menhir_goto_ctype _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run51 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ICHAR ->
          _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState51
      | Core_parser_util.INT ->
          _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState51
      | Core_parser_util.LONG ->
          _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState51
      | Core_parser_util.LONG_LONG ->
          _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState51
      | Core_parser_util.SHORT ->
          _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState51
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState51
  
  and _menhir_run58 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (AilTypes.integerType) =     ( AilTypes.Unsigned (AilTypes.IBBuiltin "int8_t") ) in
      _menhir_goto_integer_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run59 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (AilTypes.integerType) =     ( AilTypes.Unsigned (AilTypes.IBBuiltin "int64_t") ) in
      _menhir_goto_integer_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run60 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (AilTypes.integerType) =     ( AilTypes.Unsigned (AilTypes.IBBuiltin "int32_t") ) in
      _menhir_goto_integer_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run61 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (AilTypes.integerType) =     ( AilTypes.Unsigned (AilTypes.IBBuiltin "int16_t") ) in
      _menhir_goto_integer_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run62 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Core_parser_util._sym) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let str = _v in
      match try
        Some (    ( match Builtins.translate_builtin_typenames ("__cerbty_" ^ fst str) with
        | Some ty ->
            Core_aux.proj_ctype ty
        | None ->
            (raise _eRR)
    ) : (Core_ctype.ctype0))
      with
      | Error ->
          None with
      | Some _v ->
          _menhir_goto_ctype _menhir_env _menhir_stack _menhir_s _v
      | None ->
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run63 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ICHAR ->
          _menhir_run56 _menhir_env (Obj.magic _menhir_stack) MenhirState63
      | Core_parser_util.INT ->
          _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState63
      | Core_parser_util.LONG ->
          _menhir_run54 _menhir_env (Obj.magic _menhir_stack) MenhirState63
      | Core_parser_util.LONG_LONG ->
          _menhir_run53 _menhir_env (Obj.magic _menhir_stack) MenhirState63
      | Core_parser_util.SHORT ->
          _menhir_run52 _menhir_env (Obj.magic _menhir_stack) MenhirState63
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState63
  
  and _menhir_run65 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (AilTypes.integerType) =     ( AilTypes.Signed (AilTypes.IBBuiltin "int8_t") ) in
      _menhir_goto_integer_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run66 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (AilTypes.integerType) =     ( AilTypes.Signed (AilTypes.IBBuiltin "int64_t") ) in
      _menhir_goto_integer_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run67 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (AilTypes.integerType) =     ( AilTypes.Signed (AilTypes.IBBuiltin "int32_t") ) in
      _menhir_goto_integer_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run68 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (AilTypes.integerType) =     ( AilTypes.Signed (AilTypes.IBBuiltin "int16_t") ) in
      _menhir_goto_integer_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run69 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (AilTypes.integerType) =     ( AilTypes.Char ) in
      _menhir_goto_integer_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run70 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (AilTypes.integerType) =     ( AilTypes.Bool ) in
      _menhir_goto_integer_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run71 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ATOMIC ->
              _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState72
          | Core_parser_util.BOOL ->
              _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState72
          | Core_parser_util.CHAR ->
              _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState72
          | Core_parser_util.INT16_T ->
              _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState72
          | Core_parser_util.INT32_T ->
              _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState72
          | Core_parser_util.INT64_T ->
              _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState72
          | Core_parser_util.INT8_T ->
              _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState72
          | Core_parser_util.SIGNED ->
              _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState72
          | Core_parser_util.SYM _v ->
              _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
          | Core_parser_util.UINT16_T ->
              _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState72
          | Core_parser_util.UINT32_T ->
              _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState72
          | Core_parser_util.UINT64_T ->
              _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState72
          | Core_parser_util.UINT8_T ->
              _menhir_run58 _menhir_env (Obj.magic _menhir_stack) MenhirState72
          | Core_parser_util.UNSIGNED ->
              _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState72
          | Core_parser_util.VOID ->
              _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState72
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState72)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_fail : unit -> 'a =
    fun () ->
      Printf.fprintf Pervasives.stderr "Internal failure -- please contact the parser generator's developers.\n%!";
      assert false
  
  and _menhir_goto_core_type : _menhir_env -> 'ttv_tail -> _menhir_state -> (Core.core_type) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      let _menhir_stack = Obj.magic _menhir_stack in
      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
      let _tok = _menhir_env._menhir_token in
      match _tok with
      | Core_parser_util.COLON_EQ ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState406 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState406 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState406 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState406
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState406)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run32 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState33
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState33)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run34 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (expr) =     ( Vunit ) in
      _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run35 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.UB _v ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _ = _menhir_discard _menhir_env in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ub = _v in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          let _v : (expr) =     ( PEundef ub ) in
          _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run37 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (expr) =     ( Vtrue ) in
      _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run38 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ALLOC ->
          _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState38
      | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
          _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState38
      | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
          _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState38
      | Core_parser_util.CREATE ->
          _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState38
      | Core_parser_util.KILL ->
          _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState38
      | Core_parser_util.LOAD ->
          _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState38
      | Core_parser_util.STORE ->
          _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState38
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState38
  
  and _menhir_run41 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Core_parser_util._sym) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LBRACE | Core_parser_util.LPAREN ->
          _menhir_reduce128 _menhir_env (Obj.magic _menhir_stack)
      | Core_parser_util.BACKSLASH_SLASH | Core_parser_util.CARET | Core_parser_util.COMMA | Core_parser_util.DEF | Core_parser_util.ELSE | Core_parser_util.END | Core_parser_util.EOF | Core_parser_util.EQ | Core_parser_util.FUN | Core_parser_util.GLOB | Core_parser_util.IN | Core_parser_util.LE | Core_parser_util.LT | Core_parser_util.MINUS | Core_parser_util.PERCENT | Core_parser_util.PLUS | Core_parser_util.PROC | Core_parser_util.RBRACE | Core_parser_util.RBRACKET | Core_parser_util.RPAREN | Core_parser_util.SLASH | Core_parser_util.SLASH_BACKSLASH | Core_parser_util.STAR | Core_parser_util.THEN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, str) = _menhir_stack in
          let _v : (expr) =     ( PEsym str ) in
          _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run39 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState40 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState40
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState40)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run42 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (expr) =     ( Eskip ) in
      _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run43 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState44 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState44
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState44)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run45 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.SYM _v ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = (_menhir_stack, _v) in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.LPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.SYM _v ->
                  _menhir_run48 _menhir_env (Obj.magic _menhir_stack) MenhirState47 _v
              | Core_parser_util.RPAREN ->
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let _menhir_s = MenhirState47 in
                  let _v : ((Core_parser_util._sym * Core_ctype.ctype0) list) =     ( [] ) in
                  _menhir_goto_loption_separated_nonempty_list_COMMA_separated_pair_SYM_COLON_ctype___ _menhir_env _menhir_stack _menhir_s _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState47)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run96 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.SYM _v ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = (_menhir_stack, _v) in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.LPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.SYM _v ->
                  _menhir_run99 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
              | Core_parser_util.RPAREN ->
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let _menhir_s = MenhirState98 in
                  let _v : ((Core_parser_util._sym * expr) list) =     ( [] ) in
                  _menhir_goto_loption_separated_nonempty_list_COMMA_separated_pair_SYM_COLON_expr___ _menhir_env _menhir_stack _menhir_s _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState98)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run101 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState102 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState102
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState102)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run103 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.SYM _v ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _menhir_stack = (_menhir_stack, _v) in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.COMMA ->
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let _tok = _menhir_discard _menhir_env in
                  (match _tok with
                  | Core_parser_util.IMPL _v ->
                      _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState106 _v
                  | Core_parser_util.SYM _v ->
                      _menhir_run107 _menhir_env (Obj.magic _menhir_stack) MenhirState106 _v
                  | _ ->
                      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                      _menhir_env._menhir_shifted <- (-1);
                      _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState106)
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run111 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.SYM _v ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _menhir_stack = (_menhir_stack, _v) in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.RPAREN ->
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let _ = _menhir_discard _menhir_env in
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let ((_menhir_stack, _menhir_s), x0) = _menhir_stack in
                  let _v : (expr) = let str =
                    let x = x0 in
                        ( x )
                  in
                      ( Eraise str ) in
                  _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run115 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | Core_parser_util.RPAREN ->
              _menhir_reduce114 _menhir_env (Obj.magic _menhir_stack) MenhirState116
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState116)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run117 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState118 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState118
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState118)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run119 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState120 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | Core_parser_util.RPAREN ->
              _menhir_reduce114 _menhir_env (Obj.magic _menhir_stack) MenhirState120
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState120)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run121 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ALLOC ->
          _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.ARRAY ->
          _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.CASE_CTYPE ->
          _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.CASE_LIST ->
          _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
          _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
          _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.CONS ->
          _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.CREATE ->
          _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.DQUOTE ->
          _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.ERROR ->
          _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.FALSE ->
          _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.IF ->
          _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.IMPL _v ->
          _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
      | Core_parser_util.INDET ->
          _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.INT_CONST _v ->
          _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
      | Core_parser_util.IS_INTEGER ->
          _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.IS_SCALAR ->
          _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.IS_SIGNED ->
          _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.IS_UNSIGNED ->
          _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.KILL ->
          _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.LBRACKET ->
          _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.LET ->
          _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.LOAD ->
          _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.LPAREN ->
          _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.ND ->
          _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.NOT ->
          _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.PAR ->
          _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.RAISE ->
          _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.REGISTER ->
          _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.RETURN ->
          _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.RUN ->
          _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.SAVE ->
          _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.SHIFT ->
          _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.SKIP ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.STORE ->
          _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.SYM _v ->
          _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
      | Core_parser_util.TILDE ->
          _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.TRUE ->
          _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.UNDEF ->
          _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.UNIT ->
          _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | Core_parser_util.UNSEQ ->
          _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState121
  
  and _menhir_run122 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState123 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState123
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState123)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run124 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ATOM ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.LPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _menhir_s = MenhirState331 in
              let _menhir_stack = (_menhir_stack, _menhir_s) in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.RPAREN ->
                  _menhir_run131 _menhir_env (Obj.magic _menhir_stack) MenhirState337
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState337)
          | Core_parser_util.SYM _v ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _menhir_s = MenhirState331 in
              let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.EQ ->
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let _tok = _menhir_discard _menhir_env in
                  (match _tok with
                  | Core_parser_util.ALLOC ->
                      _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState333
                  | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                      _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState333
                  | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                      _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState333
                  | Core_parser_util.CREATE ->
                      _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState333
                  | Core_parser_util.KILL ->
                      _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState333
                  | Core_parser_util.LOAD ->
                      _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState333
                  | Core_parser_util.STORE ->
                      _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState333
                  | _ ->
                      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                      _menhir_env._menhir_shifted <- (-1);
                      _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState333)
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
          | Core_parser_util.UNDERSCORE ->
              _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState331
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState331)
      | Core_parser_util.STRONG ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.LPAREN ->
              _menhir_run128 _menhir_env (Obj.magic _menhir_stack) MenhirState318
          | Core_parser_util.SYM _v ->
              _menhir_run127 _menhir_env (Obj.magic _menhir_stack) MenhirState318 _v
          | Core_parser_util.UNDERSCORE ->
              _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState318
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState318)
      | Core_parser_util.SYM _v ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = (_menhir_stack, _v) in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.EQ ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState313 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState313
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState313)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | Core_parser_util.WEAK ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.LPAREN ->
              _menhir_run128 _menhir_env (Obj.magic _menhir_stack) MenhirState125
          | Core_parser_util.SYM _v ->
              _menhir_run127 _menhir_env (Obj.magic _menhir_stack) MenhirState125 _v
          | Core_parser_util.UNDERSCORE ->
              _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState125
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState125)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run139 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ALLOC ->
          _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.ARRAY ->
          _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.CASE_CTYPE ->
          _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.CASE_LIST ->
          _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
          _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
          _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.CONS ->
          _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.CREATE ->
          _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.DQUOTE ->
          _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.ERROR ->
          _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.FALSE ->
          _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.IF ->
          _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.IMPL _v ->
          _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _v
      | Core_parser_util.INDET ->
          _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.INT_CONST _v ->
          _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _v
      | Core_parser_util.IS_INTEGER ->
          _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.IS_SCALAR ->
          _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.IS_SIGNED ->
          _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.IS_UNSIGNED ->
          _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.KILL ->
          _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.LBRACKET ->
          _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.LET ->
          _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.LOAD ->
          _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.LPAREN ->
          _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.ND ->
          _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.NOT ->
          _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.PAR ->
          _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.RAISE ->
          _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.REGISTER ->
          _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.RETURN ->
          _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.RUN ->
          _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.SAVE ->
          _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.SHIFT ->
          _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.SKIP ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.STORE ->
          _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.SYM _v ->
          _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _v
      | Core_parser_util.TILDE ->
          _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.TRUE ->
          _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.UNDEF ->
          _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.UNIT ->
          _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.UNSEQ ->
          _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | Core_parser_util.RBRACKET ->
          _menhir_reduce114 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState139
  
  and _menhir_run140 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState141 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState141
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState141)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run142 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState143 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState143
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState143)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run144 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState145 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState145 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState145 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState145
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState145)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run146 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState147
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState147)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run148 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState149 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState149
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState149)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run150 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Nat_big_num.num) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let n = _v in
      let _v : (expr) =     ( Vinteger n ) in
      _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run151 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState152
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState152)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run153 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Implementation_.implementation_constant) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LBRACE | Core_parser_util.LPAREN ->
          _menhir_reduce129 _menhir_env (Obj.magic _menhir_stack)
      | Core_parser_util.BACKSLASH_SLASH | Core_parser_util.CARET | Core_parser_util.COMMA | Core_parser_util.DEF | Core_parser_util.ELSE | Core_parser_util.END | Core_parser_util.EOF | Core_parser_util.EQ | Core_parser_util.FUN | Core_parser_util.GLOB | Core_parser_util.IN | Core_parser_util.LE | Core_parser_util.LT | Core_parser_util.MINUS | Core_parser_util.PERCENT | Core_parser_util.PLUS | Core_parser_util.PROC | Core_parser_util.RBRACE | Core_parser_util.RBRACKET | Core_parser_util.RPAREN | Core_parser_util.SLASH | Core_parser_util.SLASH_BACKSLASH | Core_parser_util.STAR | Core_parser_util.THEN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, iCst) = _menhir_stack in
          let _v : (expr) =     ( PEimpl iCst ) in
          _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run154 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ALLOC ->
          _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.ARRAY ->
          _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.CASE_CTYPE ->
          _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.CASE_LIST ->
          _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
          _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
          _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.CONS ->
          _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.CREATE ->
          _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.DQUOTE ->
          _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.ERROR ->
          _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.FALSE ->
          _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.IF ->
          _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.IMPL _v ->
          _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _v
      | Core_parser_util.INDET ->
          _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.INT_CONST _v ->
          _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _v
      | Core_parser_util.IS_INTEGER ->
          _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.IS_SCALAR ->
          _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.IS_SIGNED ->
          _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.IS_UNSIGNED ->
          _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.KILL ->
          _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.LBRACKET ->
          _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.LET ->
          _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.LOAD ->
          _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.LPAREN ->
          _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.ND ->
          _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.NOT ->
          _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.PAR ->
          _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.RAISE ->
          _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.REGISTER ->
          _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.RETURN ->
          _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.RUN ->
          _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.SAVE ->
          _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.SHIFT ->
          _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.SKIP ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.STORE ->
          _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.SYM _v ->
          _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState154 _v
      | Core_parser_util.TILDE ->
          _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.TRUE ->
          _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.UNDEF ->
          _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.UNIT ->
          _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | Core_parser_util.UNSEQ ->
          _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState154
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState154
  
  and _menhir_run155 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (expr) =     ( Vfalse ) in
      _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run156 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.STRING _v ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _ = _menhir_discard _menhir_env in
          let _menhir_stack = Obj.magic _menhir_stack in
          let str = _v in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          let _v : (expr) =     ( PEerror str ) in
          _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run158 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.ATOMIC ->
          _menhir_run71 _menhir_env (Obj.magic _menhir_stack) MenhirState158
      | Core_parser_util.BOOL ->
          _menhir_run70 _menhir_env (Obj.magic _menhir_stack) MenhirState158
      | Core_parser_util.CHAR ->
          _menhir_run69 _menhir_env (Obj.magic _menhir_stack) MenhirState158
      | Core_parser_util.INT16_T ->
          _menhir_run68 _menhir_env (Obj.magic _menhir_stack) MenhirState158
      | Core_parser_util.INT32_T ->
          _menhir_run67 _menhir_env (Obj.magic _menhir_stack) MenhirState158
      | Core_parser_util.INT64_T ->
          _menhir_run66 _menhir_env (Obj.magic _menhir_stack) MenhirState158
      | Core_parser_util.INT8_T ->
          _menhir_run65 _menhir_env (Obj.magic _menhir_stack) MenhirState158
      | Core_parser_util.SIGNED ->
          _menhir_run63 _menhir_env (Obj.magic _menhir_stack) MenhirState158
      | Core_parser_util.SYM _v ->
          _menhir_run62 _menhir_env (Obj.magic _menhir_stack) MenhirState158 _v
      | Core_parser_util.UINT16_T ->
          _menhir_run61 _menhir_env (Obj.magic _menhir_stack) MenhirState158
      | Core_parser_util.UINT32_T ->
          _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState158
      | Core_parser_util.UINT64_T ->
          _menhir_run59 _menhir_env (Obj.magic _menhir_stack) MenhirState158
      | Core_parser_util.UINT8_T ->
          _menhir_run58 _menhir_env (Obj.magic _menhir_stack) MenhirState158
      | Core_parser_util.UNSIGNED ->
          _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState158
      | Core_parser_util.VOID ->
          _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState158
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState158
  
  and _menhir_run161 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState162 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState162 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState162 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState162
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState162)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run163 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState164 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState164
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState164)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run165 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState166 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState166
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState166)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run167 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState168 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState168 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState168 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState168
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState168)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run169 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState170
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState170)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run171 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState172 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState172
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState172)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run173 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState174 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState174 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState174 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState174
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState174)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run175 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.LPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.ALLOC ->
              _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.ARRAY ->
              _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.CASE_CTYPE ->
              _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.CASE_LIST ->
              _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
              _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
              _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.CONS ->
              _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.CREATE ->
              _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.DQUOTE ->
              _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.ERROR ->
              _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.FALSE ->
              _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.IF ->
              _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.IMPL _v ->
              _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _v
          | Core_parser_util.INDET ->
              _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.INT_CONST _v ->
              _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _v
          | Core_parser_util.IS_INTEGER ->
              _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.IS_SCALAR ->
              _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.IS_SIGNED ->
              _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.IS_UNSIGNED ->
              _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.KILL ->
              _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.LBRACKET ->
              _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.LET ->
              _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.LOAD ->
              _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.LPAREN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.ND ->
              _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.NOT ->
              _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.PAR ->
              _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.RAISE ->
              _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.REGISTER ->
              _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.RETURN ->
              _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.RUN ->
              _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.SAVE ->
              _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.SHIFT ->
              _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.SKIP ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.STORE ->
              _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.SYM _v ->
              _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _v
          | Core_parser_util.TILDE ->
              _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.TRUE ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.UNDEF ->
              _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.UNIT ->
              _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | Core_parser_util.UNSEQ ->
              _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState176
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState176)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_goto_separated_nonempty_list_COMMA_separated_pair_SYM_COLON_core_base_type__ : _menhir_env -> 'ttv_tail -> _menhir_state -> ((Core_parser_util._sym * Core.core_base_type) list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      match _menhir_s with
      | MenhirState23 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let xs = _v in
          let ((_menhir_stack, _menhir_s, x0), _, y0) = _menhir_stack in
          let _v : ((Core_parser_util._sym * Core.core_base_type) list) = let x =
            let y = y0 in
            let x = x0 in
                ( (x, y) )
          in
              ( x :: xs ) in
          _menhir_goto_separated_nonempty_list_COMMA_separated_pair_SYM_COLON_core_base_type__ _menhir_env _menhir_stack _menhir_s _v
      | MenhirState419 | MenhirState411 | MenhirState3 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let x = _v in
          let _v : ((Core_parser_util._sym * Core.core_base_type) list) =     ( x ) in
          _menhir_goto_loption_separated_nonempty_list_COMMA_separated_pair_SYM_COLON_core_base_type___ _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_core_base_type_ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Core.core_base_type list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      match _menhir_s with
      | MenhirState8 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let x = _v in
          let _v : (Core.core_base_type list) =     ( x ) in
          _menhir_goto_loption_separated_nonempty_list_COMMA_core_base_type__ _menhir_env _menhir_stack _menhir_s _v
      | MenhirState20 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let xs = _v in
          let (_menhir_stack, _menhir_s, x) = _menhir_stack in
          let _v : (Core.core_base_type list) =     ( x :: xs ) in
          _menhir_goto_separated_nonempty_list_COMMA_core_base_type_ _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_separated_pair_SYM_COLON_core_base_type___ : _menhir_env -> 'ttv_tail -> _menhir_state -> ((Core_parser_util._sym * Core.core_base_type) list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState3 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.COLON ->
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let _tok = _menhir_discard _menhir_env in
                  (match _tok with
                  | Core_parser_util.EFF ->
                      let _menhir_stack = Obj.magic _menhir_stack in
                      let _tok = _menhir_discard _menhir_env in
                      (match _tok with
                      | Core_parser_util.BOOLEAN ->
                          _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState29
                      | Core_parser_util.CFUNCTION ->
                          _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState29
                      | Core_parser_util.CTYPE ->
                          _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState29
                      | Core_parser_util.INTEGER ->
                          _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState29
                      | Core_parser_util.LBRACKET ->
                          _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState29
                      | Core_parser_util.LPAREN ->
                          _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState29
                      | Core_parser_util.POINTER ->
                          _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState29
                      | Core_parser_util.UNIT ->
                          _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState29
                      | _ ->
                          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                          _menhir_env._menhir_shifted <- (-1);
                          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState29)
                  | _ ->
                      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                      _menhir_env._menhir_shifted <- (-1);
                      let _menhir_stack = Obj.magic _menhir_stack in
                      let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                      _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState411 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.COLON ->
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let _tok = _menhir_discard _menhir_env in
                  (match _tok with
                  | Core_parser_util.BOOLEAN ->
                      _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState414
                  | Core_parser_util.CFUNCTION ->
                      _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState414
                  | Core_parser_util.CTYPE ->
                      _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState414
                  | Core_parser_util.INTEGER ->
                      _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState414
                  | Core_parser_util.LBRACKET ->
                      _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState414
                  | Core_parser_util.LPAREN ->
                      _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState414
                  | Core_parser_util.POINTER ->
                      _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState414
                  | Core_parser_util.UNIT ->
                      _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState414
                  | _ ->
                      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                      _menhir_env._menhir_shifted <- (-1);
                      _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState414)
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState419 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.COLON ->
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let _tok = _menhir_discard _menhir_env in
                  (match _tok with
                  | Core_parser_util.BOOLEAN ->
                      _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState422
                  | Core_parser_util.CFUNCTION ->
                      _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState422
                  | Core_parser_util.CTYPE ->
                      _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState422
                  | Core_parser_util.INTEGER ->
                      _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState422
                  | Core_parser_util.LBRACKET ->
                      _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState422
                  | Core_parser_util.LPAREN ->
                      _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState422
                  | Core_parser_util.POINTER ->
                      _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState422
                  | Core_parser_util.UNIT ->
                      _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState422
                  | _ ->
                      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                      _menhir_env._menhir_shifted <- (-1);
                      _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState422)
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_core_base_type__ : _menhir_env -> 'ttv_tail -> _menhir_state -> (Core.core_base_type list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      let _menhir_stack = Obj.magic _menhir_stack in
      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
      let _tok = _menhir_env._menhir_token in
      match _tok with
      | Core_parser_util.RPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _ = _menhir_discard _menhir_env in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _, xs00) = _menhir_stack in
          let _v : (Core.core_base_type) = let baseTys =
            let xs0 = xs00 in
            let x =
              let xs = xs0 in
                  ( xs )
            in
                ( x )
          in
              ( Core.BTy_tuple baseTys ) in
          _menhir_goto_core_base_type _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_goto_core_base_type : _menhir_env -> 'ttv_tail -> _menhir_state -> (Core.core_base_type) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState9 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.RBRACKET ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, x0) = _menhir_stack in
              let _v : (Core.core_base_type) = let baseTy =
                let x = x0 in
                    ( x )
              in
                  ( Core.BTy_list baseTy ) in
              _menhir_goto_core_base_type _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState20 | MenhirState8 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.BOOLEAN ->
                  _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState20
              | Core_parser_util.CFUNCTION ->
                  _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState20
              | Core_parser_util.CTYPE ->
                  _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState20
              | Core_parser_util.INTEGER ->
                  _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState20
              | Core_parser_util.LBRACKET ->
                  _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState20
              | Core_parser_util.LPAREN ->
                  _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState20
              | Core_parser_util.POINTER ->
                  _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState20
              | Core_parser_util.UNIT ->
                  _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState20
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, x) = _menhir_stack in
              let _v : (Core.core_base_type list) =     ( [ x ] ) in
              _menhir_goto_separated_nonempty_list_COMMA_core_base_type_ _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState5 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.SYM _v ->
                  _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState23)
          | Core_parser_util.RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, x0), _, y0) = _menhir_stack in
              let _v : ((Core_parser_util._sym * Core.core_base_type) list) = let x =
                let y = y0 in
                let x = x0 in
                    ( (x, y) )
              in
                  ( [ x ] ) in
              _menhir_goto_separated_nonempty_list_COMMA_separated_pair_SYM_COLON_core_base_type__ _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState29 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.COLON_EQ ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState31 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState31 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState31 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState31
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState31)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState403 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _, baseTy) = _menhir_stack in
          let _v : (Core.core_type) =     ( Core.TyEffect baseTy ) in
          _menhir_goto_core_type _menhir_env _menhir_stack _menhir_s _v
      | MenhirState402 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, baseTy) = _menhir_stack in
          let _v : (Core.core_type) =     ( Core.TyBase baseTy ) in
          _menhir_goto_core_type _menhir_env _menhir_stack _menhir_s _v
      | MenhirState414 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.COLON_EQ ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState416 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState416 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState416 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState416
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState416)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState422 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.COLON_EQ ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState424 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState424 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState424 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState424
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState424)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState428 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | Core_parser_util.COLON_EQ ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.ALLOC ->
                  _menhir_run175 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.ARRAY ->
                  _menhir_run173 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.CASE_CTYPE ->
                  _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.CASE_LIST ->
                  _menhir_run169 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.COMPARE_EXCHANGE_STRONG ->
                  _menhir_run167 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.COMPARE_EXCHANGE_WEAK ->
                  _menhir_run165 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.CONS ->
                  _menhir_run163 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.CREATE ->
                  _menhir_run161 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.DQUOTE ->
                  _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.ERROR ->
                  _menhir_run156 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.FALSE ->
                  _menhir_run155 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.IF ->
                  _menhir_run154 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.IMPL _v ->
                  _menhir_run153 _menhir_env (Obj.magic _menhir_stack) MenhirState430 _v
              | Core_parser_util.INDET ->
                  _menhir_run151 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.INT_CONST _v ->
                  _menhir_run150 _menhir_env (Obj.magic _menhir_stack) MenhirState430 _v
              | Core_parser_util.IS_INTEGER ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.IS_SCALAR ->
                  _menhir_run146 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.IS_SIGNED ->
                  _menhir_run144 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.IS_UNSIGNED ->
                  _menhir_run142 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.KILL ->
                  _menhir_run140 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.LBRACKET ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.LET ->
                  _menhir_run124 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.LOAD ->
                  _menhir_run122 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.LPAREN ->
                  _menhir_run121 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.ND ->
                  _menhir_run119 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.NOT ->
                  _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.PAR ->
                  _menhir_run115 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.RAISE ->
                  _menhir_run111 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.REGISTER ->
                  _menhir_run103 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.RETURN ->
                  _menhir_run101 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.RUN ->
                  _menhir_run96 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.SAVE ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.SHIFT ->
                  _menhir_run43 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.SKIP ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.STORE ->
                  _menhir_run39 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.SYM _v ->
                  _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState430 _v
              | Core_parser_util.TILDE ->
                  _menhir_run38 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.TRUE ->
                  _menhir_run37 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.UNDEF ->
                  _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.UNIT ->
                  _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | Core_parser_util.UNSEQ ->
                  _menhir_run32 _menhir_env (Obj.magic _menhir_stack) MenhirState430
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState430)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_reduce116 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _v : ((Core_parser_util._sym * Core.core_base_type) list) =     ( [] ) in
      _menhir_goto_loption_separated_nonempty_list_COMMA_separated_pair_SYM_COLON_core_base_type___ _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run4 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Core_parser_util._sym) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.COLON ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.BOOLEAN ->
              _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState5
          | Core_parser_util.CFUNCTION ->
              _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState5
          | Core_parser_util.CTYPE ->
              _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState5
          | Core_parser_util.INTEGER ->
              _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState5
          | Core_parser_util.LBRACKET ->
              _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState5
          | Core_parser_util.LPAREN ->
              _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState5
          | Core_parser_util.POINTER ->
              _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState5
          | Core_parser_util.UNIT ->
              _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState5
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState5)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run6 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (Core.core_base_type) =     ( Core.BTy_unit ) in
      _menhir_goto_core_base_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run7 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (Core.core_base_type) =     ( Core.BTy_pointer ) in
      _menhir_goto_core_base_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run8 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.BOOLEAN ->
          _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState8
      | Core_parser_util.CFUNCTION ->
          _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState8
      | Core_parser_util.CTYPE ->
          _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState8
      | Core_parser_util.INTEGER ->
          _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState8
      | Core_parser_util.LBRACKET ->
          _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState8
      | Core_parser_util.LPAREN ->
          _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState8
      | Core_parser_util.POINTER ->
          _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState8
      | Core_parser_util.UNIT ->
          _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState8
      | Core_parser_util.RPAREN ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_s = MenhirState8 in
          let _v : (Core.core_base_type list) =     ( [] ) in
          _menhir_goto_loption_separated_nonempty_list_COMMA_core_base_type__ _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState8
  
  and _menhir_run9 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.BOOLEAN ->
          _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState9
      | Core_parser_util.CFUNCTION ->
          _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState9
      | Core_parser_util.CTYPE ->
          _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState9
      | Core_parser_util.INTEGER ->
          _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState9
      | Core_parser_util.LBRACKET ->
          _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState9
      | Core_parser_util.LPAREN ->
          _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState9
      | Core_parser_util.POINTER ->
          _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState9
      | Core_parser_util.UNIT ->
          _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState9
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState9
  
  and _menhir_run10 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (Core.core_base_type) =     ( Core.BTy_integer ) in
      _menhir_goto_core_base_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run11 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (Core.core_base_type) =     ( Core.BTy_ctype ) in
      _menhir_goto_core_base_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run12 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (Core.core_base_type) =     ( Core.BTy_cfunction ) in
      _menhir_goto_core_base_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run13 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (Core.core_base_type) =     ( Core.BTy_boolean ) in
      _menhir_goto_core_base_type _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_discard : _menhir_env -> Core_parser_util.token =
    fun _menhir_env ->
      let lexbuf = _menhir_env._menhir_lexbuf in
      let _tok = _menhir_env._menhir_lexer lexbuf in
      _menhir_env._menhir_token <- _tok;
      _menhir_env._menhir_startp <- lexbuf.Lexing.lex_start_p;
      _menhir_env._menhir_endp <- lexbuf.Lexing.lex_curr_p;
      let shifted = Pervasives.(+) _menhir_env._menhir_shifted 1 in
      if Pervasives.(>=) shifted 0 then
        _menhir_env._menhir_shifted <- shifted;
      _tok
  
  and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      match _menhir_s with
      | MenhirState440 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState430 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState428 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState424 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState422 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState419 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState416 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState414 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState411 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState406 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState403 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState402 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState393 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState390 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState388 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState382 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState378 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState375 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState373 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState364 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState352 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState347 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState344 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState341 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState339 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState337 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState335 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState333 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState331 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState328 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState326 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState322 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState320 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState318 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState315 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState313 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState309 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState307 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState303 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState285 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState283 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState279 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState275 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState271 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState269 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState267 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState265 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState263 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState259 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState251 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState249 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState247 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState245 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState241 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState239 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState235 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState233 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState231 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState229 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState227 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState225 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState223 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState221 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState219 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState213 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState209 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState207 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState205 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState203 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState201 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState199 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState197 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState195 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState193 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState191 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState189 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState186 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState184 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState179 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState176 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState174 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState172 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState170 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState168 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState166 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState164 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState162 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState158 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState154 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState152 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState149 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState147 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState145 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState143 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState141 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState139 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState138 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState135 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState128 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState125 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState123 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState121 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState120 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState118 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState116 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState106 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState102 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState100 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState98 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState95 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState90 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState86 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState77 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState72 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState63 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState51 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState49 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState47 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState44 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState40 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState38 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState33 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState31 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState29 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState23 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState20 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState9 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState8 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState5 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState3 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState0 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          raise _eRR
  
  and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.SYM _v ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = (_menhir_stack, _v) in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.LPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.SYM _v ->
                  _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v
              | Core_parser_util.RPAREN ->
                  _menhir_reduce116 _menhir_env (Obj.magic _menhir_stack) MenhirState3
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState3)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run400 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.SYM _v ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = (_menhir_stack, _v) in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.COLON ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.BOOLEAN ->
                  _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState402
              | Core_parser_util.CFUNCTION ->
                  _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState402
              | Core_parser_util.CTYPE ->
                  _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState402
              | Core_parser_util.EFF ->
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let _menhir_s = MenhirState402 in
                  let _menhir_stack = (_menhir_stack, _menhir_s) in
                  let _tok = _menhir_discard _menhir_env in
                  (match _tok with
                  | Core_parser_util.BOOLEAN ->
                      _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState403
                  | Core_parser_util.CFUNCTION ->
                      _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState403
                  | Core_parser_util.CTYPE ->
                      _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState403
                  | Core_parser_util.INTEGER ->
                      _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState403
                  | Core_parser_util.LBRACKET ->
                      _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState403
                  | Core_parser_util.LPAREN ->
                      _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState403
                  | Core_parser_util.POINTER ->
                      _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState403
                  | Core_parser_util.UNIT ->
                      _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState403
                  | _ ->
                      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                      _menhir_env._menhir_shifted <- (-1);
                      _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState403)
              | Core_parser_util.INTEGER ->
                  _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState402
              | Core_parser_util.LBRACKET ->
                  _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState402
              | Core_parser_util.LPAREN ->
                  _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState402
              | Core_parser_util.POINTER ->
                  _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState402
              | Core_parser_util.UNIT ->
                  _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState402
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState402)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run409 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.IMPL _v ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = (_menhir_stack, _v) in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.LPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.SYM _v ->
                  _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState419 _v
              | Core_parser_util.RPAREN ->
                  _menhir_reduce116 _menhir_env (Obj.magic _menhir_stack) MenhirState419
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState419)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | Core_parser_util.SYM _v ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = (_menhir_stack, _v) in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.LPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.SYM _v ->
                  _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState411 _v
              | Core_parser_util.RPAREN ->
                  _menhir_reduce116 _menhir_env (Obj.magic _menhir_stack) MenhirState411
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState411)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run426 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | Core_parser_util.IMPL _v ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = (_menhir_stack, _v) in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | Core_parser_util.COLON ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | Core_parser_util.BOOLEAN ->
                  _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState428
              | Core_parser_util.CFUNCTION ->
                  _menhir_run12 _menhir_env (Obj.magic _menhir_stack) MenhirState428
              | Core_parser_util.CTYPE ->
                  _menhir_run11 _menhir_env (Obj.magic _menhir_stack) MenhirState428
              | Core_parser_util.INTEGER ->
                  _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState428
              | Core_parser_util.LBRACKET ->
                  _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState428
              | Core_parser_util.LPAREN ->
                  _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState428
              | Core_parser_util.POINTER ->
                  _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState428
              | Core_parser_util.UNIT ->
                  _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState428
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState428)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and start : (Lexing.lexbuf -> Core_parser_util.token) -> Lexing.lexbuf -> (Core_parser_util.result) =
    fun lexer lexbuf ->
      let _menhir_env = let _tok = lexer lexbuf in
      {
        _menhir_lexer = lexer;
        _menhir_lexbuf = lexbuf;
        _menhir_token = _tok;
        _menhir_startp = lexbuf.Lexing.lex_start_p;
        _menhir_endp = lexbuf.Lexing.lex_curr_p;
        _menhir_shifted = max_int;
        } in
      Obj.magic (let _menhir_stack = () in
      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
      let _tok = _menhir_env._menhir_token in
      match _tok with
      | Core_parser_util.DEF ->
          _menhir_run426 _menhir_env (Obj.magic _menhir_stack) MenhirState0
      | Core_parser_util.FUN ->
          _menhir_run409 _menhir_env (Obj.magic _menhir_stack) MenhirState0
      | Core_parser_util.GLOB ->
          _menhir_run400 _menhir_env (Obj.magic _menhir_stack) MenhirState0
      | Core_parser_util.PROC ->
          _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)
  
  




end
