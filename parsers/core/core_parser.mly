%{
open Cerb_frontend

open Lem_pervasives
open Either

open Core_parser_util

open Errors

open Core

module Caux = Core_aux
module Cmm = Cmm_csem

open Ctype

let sym_compare =
  Symbol.instance_Basic_classes_Ord_Symbol_sym_dict.compare_method

let iCst_compare =
  compare

type parsed_pexpr = (unit, _sym) generic_pexpr
type parsed_expr  = (unit, unit, _sym) generic_expr

type attribute =
  | Attr_ailname of string

type declaration =
  | Def_decl  of Implementation.implementation_constant * Core.core_base_type * parsed_pexpr
  | IFun_decl of Implementation.implementation_constant * (Core.core_base_type * (_sym * Core.core_base_type) list * parsed_pexpr)
  | Glob_decl of _sym * (Core.core_base_type * Ctype.ctype) * parsed_expr
  | Fun_decl  of _sym * (Core.core_base_type * (_sym * Core.core_base_type) list * parsed_pexpr)
  | Proc_decl of _sym * attribute list * (Core.core_base_type * (_sym * Core.core_base_type) list * parsed_expr)
  | Builtin_decl of _sym * (Core.core_base_type * (Core.core_base_type) list)
  | Aggregate_decl of _sym * Ctype.tag_definition
(*
  | WithAttributes_decl of attribute list * declaration
*)



let hasAilname: attribute list -> string option = function
  | [] ->
      None
  | Attr_ailname str :: _ ->
      Some str


(* TODO: move to Caux *)
let rec mk_list_pe bTy = function
  | [] ->
      Pexpr ([], (), PEctor (Cnil bTy, []))
  | _pe::_pes ->
      Pexpr ([], (), PEctor (Ccons, [_pe; mk_list_pe bTy _pes]))

let rec mk_list_pat bTy = function
  | [] ->
      Pattern ([], CaseCtor (Cnil bTy, []))
  | _pat::_pats ->
      Pattern ([], CaseCtor (Ccons, [_pat; mk_list_pat bTy _pats]))

let ensure_list_core_base_type loc = function
  | BTy_list cbt -> cbt
  | _ -> failwith ((Cerb_location.location_to_string loc) ^ 
                     ": list given non-list type")


type symbolify_state = {
  labels: (Core_parser_util._sym, Symbol.sym * Cerb_location.t) Pmap.map;
  sym_scopes: ((Core_parser_util._sym, Symbol.sym * Cerb_location.t) Pmap.map) list;
  ailnames: (string, Symbol.sym) Pmap.map
}

let initial_symbolify_state = {
  labels= Pmap.empty Core_parser_util._sym_compare;
  sym_scopes= [Pmap.map (fun sym -> (sym, Cerb_location.unknown)) M.std];
  ailnames= Pmap.empty Stdlib.compare;
}

module Eff : sig
  type 'a t
  val return: 'a -> 'a t
  val bind: 'a t -> ('a -> 'b t) -> 'b t
  val fmap: ('a -> 'b) -> 'a t -> 'b t
  val app: ('a -> 'b) t -> 'a t -> 'b t
  val mapM: ('a -> 'b t) -> 'a list -> ('b list) t
  val mapM_: ('a -> 'b t) -> 'a list -> unit t
  val foldrM: ('a -> 'b -> 'b t) -> 'b -> 'a list -> 'b t
  val fail: Cerb_location.t -> core_parser_cause -> 'a t
  val runM: 'a t -> symbolify_state -> (Cerb_location.t * core_parser_cause, 'a * symbolify_state) either
  val get: symbolify_state t
  val put: symbolify_state -> unit t
end = struct
  open Either
  type 'a t = symbolify_state -> (Cerb_location.t * core_parser_cause, 'a * symbolify_state) either
  
  let return z =
    fun st -> Right (z, st)
  
  let bind mz f =
    fun st ->
      match mz st with
        | Left err ->
            Left err
        | Right (z, st') ->
            f z st'
  
  let fmap f m =
    bind m (comb return f)
  
  let app mf m =
    bind mf (fun f -> fmap f m)
  
  let sequence ms =
    List.fold_right
      (fun m m' ->
        bind m  (fun x  ->
        bind m' (fun xs ->
        return (x::xs)))
      ) ms (return [])
  
  let listM t xs = sequence (t xs)
  
  let mapM f = listM (List.map f)
  
  let sequence_ ms = List.fold_right (fun m f -> bind m (fun _ -> f)) ms (return ())
  let mapM_ f _as = sequence_ (List.map f _as)
  
  let rec foldrM f a = function
    | [] -> return a
    | x::xs -> bind (foldrM f a xs) (f x)
  
  let fail loc err =
    fun _ -> Left (loc, err)
  
  let runM m st =
    m st
  
  let get =
    fun st -> Right (st, st)
  
  let put st' =
    fun _ -> Right ((), st')
end

let (>>=)    = Eff.bind
let (<$>)    = Eff.fmap
let (<*>)    = Eff.app


let register_ailname str sym =
  Eff.get >>= fun st ->
  Eff.put {st with ailnames= Pmap.add str sym st.ailnames }

let open_scope : unit Eff.t =
  Eff.get >>= fun st ->
  Eff.put {st with sym_scopes= Pmap.empty Core_parser_util._sym_compare :: st.sym_scopes} >>= fun () ->
  Eff.return ()
  
let close_scope : ((Core_parser_util._sym, Symbol.sym * Cerb_location.t) Pmap.map) Eff.t =
  Eff.get >>= fun st ->
  match st.sym_scopes with
    | [] ->
        failwith "Core_parser.close_scope: found open scope"
    | scope :: scopes ->
        Eff.put {st with sym_scopes= scopes} >>= fun () ->
        Eff.return scope

let under_scope (m: 'a Eff.t) : 'a Eff.t =
  open_scope >>= fun () ->
  m >>= fun ret ->
  close_scope >>= fun _ ->
  Eff.return ret


let register_sym ((_, (start_p, end_p)) as _sym) : Symbol.sym Eff.t =
  Eff.get >>= fun st ->
  let sym = Symbol.Symbol (Cerb_fresh.digest(), Cerb_fresh.int(), SD_Id (fst _sym)) in
(*  let sym = Symbol.Symbol (Cerb_global.new_int (), Some (fst _sym)) in *)
  Eff.put {st with
    sym_scopes=
      match st.sym_scopes with
        | [] ->
            failwith "Core_parser.register_sym: found open scope"
        | scope::scopes ->
            Pmap.add _sym (sym, Cerb_location.(region (start_p, end_p) NoCursor)) scope :: scopes
  } >>= fun () ->
  Eff.return sym

let lookup_sym _sym : ((Symbol.sym * Cerb_location.t) option) Eff.t =
  Eff.get >>= fun st ->
  Eff.return (match st.sym_scopes with
    | [] ->
        failwith "Core_parser.lookup_sym: found open scope"
    | scopes ->
        let rec aux = (function
          | [] ->
              None
          | scope::scopes' ->
              (match Pmap.lookup _sym scope with
                | Some sym_loc ->
                    Some sym_loc
                | None ->
                    aux scopes'
              )
        ) in
        aux scopes
  )


let register_label ((_, (start_p, end_p)) as _sym) : unit Eff.t =
  let loc = Cerb_location.(region (start_p, end_p) NoCursor) in
  Eff.get >>= fun st ->
  let sym = Symbol.Symbol (Cerb_fresh.digest(), Cerb_fresh.int(), SD_Id (fst _sym)) in
  Eff.put {st with
    labels= Pmap.add _sym (sym, loc) st.labels
  }

let lookup_label _sym: ((Symbol.sym * Cerb_location.t) option) Eff.t =
  Eff.get >>= fun st ->
  Eff.return (Pmap.lookup _sym st.labels)


let symbolify_name = function
 | Sym _sym ->
     lookup_sym _sym >>= (function
       | Some (sym, _) ->
           Eff.return (Sym sym)
       | None ->
           Eff.fail (Cerb_location.(region (snd _sym) NoCursor)) (Core_parser_unresolved_symbol (fst _sym)))
 | Impl iCst ->
     Eff.return (Impl iCst)

let symbolify_sym _sym =
  lookup_sym _sym >>= function
    | Some (sym, _) ->
        Eff.return sym
    | None ->
       Eff.fail (Cerb_location.(region (snd _sym) NoCursor)) (Core_parser_unresolved_symbol (fst _sym))

let rec symbolify_ctype (Ctype (annots, ty)) =
  let symbolify_symbol = function
    | Symbol.Symbol (_, _, SD_Id str) ->
      begin lookup_sym (str, (Lexing.dummy_pos, Lexing.dummy_pos)) >>= function
        | Some (sym, _) ->
            Eff.return sym
        | None ->
            (* TODO: location *)
            Eff.fail Cerb_location.unknown (Core_parser_unresolved_symbol str)
      end
    | _ -> failwith "symbolify_ctype"
  in
  Eff.fmap (fun ty -> Ctype (annots, ty)) @@ match ty with
  | Void ->
      Eff.return Void
  | Basic bty ->
      Eff.return (Basic bty)
  | Array (ty, n) ->
      symbolify_ctype ty >>= fun ty' ->
      Eff.return (Array (ty', n))
  | Atomic ty ->
      symbolify_ctype ty >>= fun ty' ->
      Eff.return (Atomic ty')
  | Function ((ret_qs, ret_ty), params, isVariadic) ->
      symbolify_ctype ret_ty >>= fun ret_ty' ->
      Eff.mapM (fun (qs, ty, _) -> symbolify_ctype ty >>= fun ty' -> Eff.return (qs, ty', false)) params >>= fun params' ->
      Eff.return (Function ((ret_qs, ret_ty'), params', isVariadic))
  | FunctionNoParams (ret_qs, ret_ty) ->
      symbolify_ctype ret_ty >>= fun ret_ty' ->
      Eff.return (FunctionNoParams (ret_qs, ret_ty'))
  | Pointer (qs, ty) ->
      symbolify_ctype ty >>= fun ty' ->
      Eff.return (Pointer (qs, ty'))
  | Struct tag ->
      symbolify_symbol tag >>= fun tag' ->
      Eff.return (Struct tag')
  | Union tag ->
      symbolify_symbol tag >>= fun tag' ->
      Eff.return (Union tag')

let symbolify_value _cval =
  match _cval with
   | Vunit ->
       Eff.return Vunit
   | Vtrue ->
       Eff.return Vtrue
   | Vfalse ->
       Eff.return Vfalse
   | Vctype ty ->
       symbolify_ctype ty >>= fun ty' ->
       Eff.return (Vctype ty')
   | _ ->
       assert false

let do_esave_arg (sym,(cbt,pe)) = (sym,((cbt,None),pe))



let rec symbolify_pattern (Pattern (annots, _pat)) : pattern Eff.t =
  Eff.get >>= fun st ->
  match _pat with
    | CaseBase (None, bTy) ->
        Eff.return (Pattern (annots, CaseBase (None, bTy)))
    | CaseBase (Some _sym, bTy) ->
        register_sym _sym >>= fun sym ->
        Eff.return (Pattern (annots, CaseBase (Some sym, bTy)))
    | CaseCtor (ctor, _pats) ->
        Eff.mapM symbolify_pattern _pats >>= fun pat ->
        Eff.return (Pattern (annots, CaseCtor (ctor, pat)))

let rec symbolify_pexpr (Pexpr (annot, (), _pexpr): parsed_pexpr) : pexpr Eff.t =
  let loc = Annot.get_loc_ annot in
  match _pexpr with
    | PEsym _sym ->
        Eff.get         >>= fun st ->
        lookup_sym _sym >>= (function
          | Some (sym, _) ->
              Eff.return (Pexpr (annot, (), PEsym sym))
          | None ->
              Eff.fail (Cerb_location.(region (snd _sym) NoCursor)) (Core_parser_unresolved_symbol (fst _sym))
        )
    | PEimpl iCst ->
        Eff.return (Pexpr (annot, (), PEimpl iCst))
    | PEval (Vobject (OVinteger ival)) ->
        Eff.return (Pexpr (annot, (), PEval (Vobject (OVinteger ival))))
    | PEval (Vobject (OVpointer ptrval)) ->
        Eff.return (Pexpr (annot, (), PEval (Vobject (OVpointer ptrval))))
          (*
    | PEval (Vobject (OVcfunction _nm)) ->
        (* TODO(V): CHANGING THE MEANING OF THIS KEYWORD *)
        symbolify_name _nm >>= (function
        | Sym sym ->
          Eff.return (Pexpr (annot, (), PEval (Vobject (OVpointer (Impl_mem.fun_ptrval sym)))))
        | _ -> failwith "PANIC")
             *)
    | PEval Vunit ->
        Eff.return (Pexpr (annot, (), PEval Vunit))
    | PEval Vtrue ->
        Eff.return (Pexpr (annot, (), PEval Vtrue))
    | PEval Vfalse ->
        Eff.return (Pexpr (annot, (), PEval Vfalse))
    | PEval (Vctype ty) ->
        symbolify_ctype ty >>= fun ty' ->
        Eff.return (Pexpr (annot, (), PEval (Vctype ty')))
    | PEval _cval ->
        failwith "WIP: Core parser -> PEval"
    | PEconstrained _ ->
        assert false
    | PEundef (loc, ub) ->
        Eff.return (Pexpr (annot, (), PEundef (loc, ub)))
    | PEerror (str, _pe) ->
        symbolify_pexpr _pe >>= fun pe ->
        Eff.return (Pexpr (annot, (), PEerror (str, pe)))
    | PEctor (Cnil bTy, _pes) ->
        begin match _pes with
          | [] ->
              Eff.return (Pexpr (annot, (), PEctor (Cnil bTy, [])))
          | _ ->
              Eff.fail loc (Core_parser_ctor_wrong_application (0, List.length _pes))
        end
    | PEctor (Ccons, _pes) ->
        begin match _pes with
          | [_pe1; _pe2] ->
              symbolify_pexpr _pe1 >>= fun pe1 ->
              symbolify_pexpr _pe2 >>= fun pe2 ->
              Eff.return (Pexpr (annot, (), PEctor (Ccons, [pe1; pe2])))
          | _ ->
              Eff.fail loc (Core_parser_ctor_wrong_application (2, List.length _pes))
        end
    | PEctor (Ctuple, _pes) ->
        Eff.mapM symbolify_pexpr _pes >>= fun pes ->
        Eff.return (Pexpr (annot, (), PEctor (Ctuple, pes)))
    | PEctor (Carray, _pes) ->
        Eff.mapM symbolify_pexpr _pes >>= fun pes ->
        Eff.return (Pexpr (annot, (), PEctor (Carray, pes)))
    | PEctor (Civmax, _pes) ->
        begin match _pes with
          | [_pe] ->
              symbolify_pexpr _pe >>= fun pe ->
              Eff.return (Pexpr (annot, (), PEctor (Civmax, [pe])))
          | _ ->
              Eff.fail loc (Core_parser_ctor_wrong_application (1, List.length _pes))
        end
    | PEctor (Civmin, _pes) ->
        begin match _pes with
          | [_pe] ->
              symbolify_pexpr _pe >>= fun pe ->
              Eff.return (Pexpr (annot, (), PEctor (Civmin, [pe])))
          | _ ->
              Eff.fail loc (Core_parser_ctor_wrong_application (1, List.length _pes))
        end
    | PEctor (Civsizeof, _pes) ->
        begin match _pes with
          | [_pe] ->
              symbolify_pexpr _pe >>= fun pe ->
              Eff.return (Pexpr (annot, (), PEctor (Civsizeof, [pe])))
          | _ ->
              Eff.fail loc (Core_parser_ctor_wrong_application (1, List.length _pes))
        end
    | PEctor (Civalignof, _pes) ->
        begin match _pes with
          | [_pe] ->
              symbolify_pexpr _pe >>= fun pe ->
              Eff.return (Pexpr (annot, (), PEctor (Civalignof, [pe])))
          | _ ->
              Eff.fail loc (Core_parser_ctor_wrong_application (1, List.length _pes))
        end
    | PEctor (CivCOMPL, _pes) ->
        begin match _pes with
          | [_pe1; _pe2] ->
              symbolify_pexpr _pe1 >>= fun pe1 ->
              symbolify_pexpr _pe2 >>= fun pe2 ->
              Eff.return (Core_aux.bitwise_complement_pe pe1 pe2)
          | _ ->
              Eff.fail loc (Core_parser_ctor_wrong_application (2, List.length _pes))
        end
    | PEctor (CivAND, _pes) ->
        begin match _pes with
          | [_pe1; _pe2; _pe3] ->
              symbolify_pexpr _pe1 >>= fun pe1 ->
              symbolify_pexpr _pe2 >>= fun pe2 ->
              symbolify_pexpr _pe3 >>= fun pe3 ->
              Eff.return (Pexpr (annot, (), PEctor (CivAND, [pe1; pe2; pe3])))
          | _ ->
              Eff.fail loc (Core_parser_ctor_wrong_application (3, List.length _pes))
        end
    | PEctor (CivOR, _pes) ->
        begin match _pes with
          | [_pe1; _pe2; _pe3] ->
              symbolify_pexpr _pe1 >>= fun pe1 ->
              symbolify_pexpr _pe2 >>= fun pe2 ->
              symbolify_pexpr _pe3 >>= fun pe3 ->
              Eff.return (Pexpr (annot, (), PEctor (CivOR, [pe1; pe2; pe3])))
          | _ ->
              Eff.fail loc (Core_parser_ctor_wrong_application (3, List.length _pes))
        end
    | PEctor (CivXOR, _pes) ->
        begin match _pes with
          | [_pe1; _pe2; _pe3] ->
              symbolify_pexpr _pe1 >>= fun pe1 ->
              symbolify_pexpr _pe2 >>= fun pe2 ->
              symbolify_pexpr _pe3 >>= fun pe3 ->
              Eff.return (Pexpr (annot, (), PEctor (CivXOR, [pe1; pe2; pe3])))
          | _ ->
              Eff.fail loc (Core_parser_ctor_wrong_application (3, List.length _pes))
        end
    | PEctor (Cspecified, _pes) ->
        begin match _pes with
          | [_pe] ->
              symbolify_pexpr _pe >>= fun pe ->
              Eff.return (Pexpr (annot, (), (PEctor (Cspecified, [pe]))))
          | _ ->
              Eff.fail loc (Core_parser_ctor_wrong_application (1, List.length _pes))
        end
    | PEctor (Cunspecified, _pes) ->
        begin match _pes with
          | [_pe] ->
              symbolify_pexpr _pe >>= fun pe ->
              Eff.return (Pexpr (annot, (), PEctor (Cunspecified, [pe])))
          | _ ->
              Eff.fail loc (Core_parser_ctor_wrong_application (1, List.length _pes))
        end
    | PEctor (Cfvfromint, _pes) ->
        begin match _pes with
          | [_pe] ->
              symbolify_pexpr _pe >>= fun pe ->
              Eff.return (Pexpr (annot, (), PEctor (Cfvfromint, [pe])))
          | _ ->
              Eff.fail loc (Core_parser_ctor_wrong_application (1, List.length _pes))
        end
    | PEctor (Civfromfloat, _pes) ->
        begin match _pes with
          | [_pe1; _pe2] ->
              symbolify_pexpr _pe1 >>= fun pe1 ->
              symbolify_pexpr _pe2 >>= fun pe2 ->
              Eff.return (Pexpr (annot, (), PEctor (Civfromfloat, [pe1; pe2])))
          | _ ->
              Eff.fail loc (Core_parser_ctor_wrong_application (2, List.length _pes))
        end
    | PEctor (CivNULLcap is_signed, _pes) ->
        begin match _pes with
          | [] ->
              Eff.return (Pexpr (annot, (), PEctor (CivNULLcap is_signed, [])))
          | _ ->
              Eff.fail loc (Core_parser_ctor_wrong_application (0, List.length _pes))
        end
    | PEcase (_pe, _pat_pes) ->
        symbolify_pexpr _pe >>= fun pe ->
        Eff.mapM (fun (_pat, _pe) ->
          under_scope (
            symbolify_pattern _pat >>= fun pat ->
            symbolify_pexpr _pe >>= fun pe ->
            Eff.return (pat, pe)
          )
        ) _pat_pes >>= fun pat_pes ->
        Eff.return (Pexpr (annot, (), PEcase (pe, pat_pes)))
    | PEarray_shift (_pe1, ty, _pe2) ->
        symbolify_pexpr _pe1 >>= fun pe1 ->
        symbolify_pexpr _pe2 >>= fun pe2 ->
        Eff.return (Pexpr (annot, (), PEarray_shift (pe1, ty, pe2)))
    | PEmember_shift (_pe, _tag_sym, member_ident) ->
        symbolify_pexpr _pe >>= fun pe ->
        lookup_sym _tag_sym >>= (function
          | Some (tag_sym, _) ->
              Eff.return (Pexpr (annot, (), PEmember_shift (pe, tag_sym, member_ident)))
          | None ->
             Eff.fail (Cerb_location.(region (snd _tag_sym) NoCursor))
               (Core_parser_unresolved_symbol (fst _tag_sym)))
    | PEmemop (mop, _pes) ->
        Eff.mapM symbolify_pexpr _pes >>= fun pes ->
        Eff.return (Pexpr (annot, (), PEmemop (mop, pes)))
    | PEnot _pe ->
        Caux.mk_not_pe <$> symbolify_pexpr _pe
    | PEop (bop, _pe1, _pe2) ->
        symbolify_pexpr _pe1 >>= fun pe1 ->
        symbolify_pexpr _pe2 >>= fun pe2 ->
        Eff.return (Pexpr (annot, (), PEop (bop, pe1, pe2)))
    | PEconv_int (ity, _pe) ->
        symbolify_pexpr _pe >>= fun pe ->
        Eff.return (Pexpr (annot, (), PEconv_int (ity, pe)))
    | PEwrapI (ity, iop, _pe1, _pe2) ->
        symbolify_pexpr _pe1 >>= fun pe1 ->
        symbolify_pexpr _pe2 >>= fun pe2 ->
        Eff.return (Pexpr (annot, (), PEwrapI (ity, iop, pe1, pe2)))
    | PEcatch_exceptional_condition (ity, iop, _pe1, _pe2) ->
        symbolify_pexpr _pe1 >>= fun pe1 ->
        symbolify_pexpr _pe2 >>= fun pe2 ->
        Eff.return (Pexpr (annot, (), PEcatch_exceptional_condition (ity, iop, pe1, pe2)))
    | PEstruct (_tag_sym, _ident_pes) ->
        symbolify_sym _tag_sym >>= fun tag_sym ->
        Eff.mapM (fun (cid, _pe) -> symbolify_pexpr _pe >>= fun pe -> Eff.return (cid, pe)) _ident_pes >>= fun ident_pes ->
        Eff.return (Pexpr (annot, (), PEstruct (tag_sym, ident_pes)))
    | PEunion (_tag_sym, member_ident, _pe) ->
        symbolify_sym _tag_sym >>= fun tag_sym ->
        symbolify_pexpr _pe >>= fun pe ->
        Eff.return (Pexpr (annot, (), PEunion (tag_sym, member_ident, pe)))
    | PEcfunction _pe ->
        symbolify_pexpr _pe >>= fun pe ->
        Eff.return (Pexpr (annot, (), PEcfunction pe))
    | PEmemberof (tag_sym, member_ident, _pe) ->
        failwith "WIP: PEmemberof"
    | PEcall (_nm, _pes) ->
        symbolify_name _nm >>= fun nm ->
        Eff.mapM symbolify_pexpr _pes >>= fun pes ->
        Eff.return (Pexpr (annot, (), PEcall (nm, pes)))
    | PElet (_pat, _pe1, _pe2) ->
        symbolify_pexpr _pe1   >>= fun pe1 ->
        under_scope begin
          symbolify_pattern _pat >>= fun pat ->
          symbolify_pexpr _pe2   >>= fun pe2 ->
          Eff.return (Caux.mk_let_pe pat pe1 pe2)
        end
    | PEif (_pe1, _pe2, _pe3) ->
        (fun pe1 pe2 pe3 -> Pexpr (annot, (), PEif (pe1, pe2, pe3)))
          <$> symbolify_pexpr _pe1
          <*> symbolify_pexpr _pe2
          <*> symbolify_pexpr _pe3
    | PEis_scalar _pe ->
        symbolify_pexpr _pe >>= fun pe ->
        Eff.return (Pexpr (annot, (), PEis_scalar pe))
    | PEis_integer _pe ->
        symbolify_pexpr _pe >>= fun pe ->
        Eff.return (Pexpr (annot, (), PEis_integer pe))
    | PEis_signed _pe ->
        symbolify_pexpr _pe >>= fun pe ->
        Eff.return (Pexpr (annot, (), PEis_signed pe))
    | PEis_unsigned _pe ->
        symbolify_pexpr _pe >>= fun pe ->
        Eff.return (Pexpr ([], (), PEis_unsigned pe))
    | PEbmc_assume _pe ->
        symbolify_pexpr _pe >>= fun pe ->
        Eff.return (Pexpr ([], (), PEbmc_assume pe))
    | PEare_compatible (_pe1, _pe2) ->
        symbolify_pexpr _pe1 >>= fun pe1 ->
        symbolify_pexpr _pe2 >>= fun pe2 ->
        Eff.return (Pexpr (annot, (), PEare_compatible (pe1, pe2)))


let rec symbolify_expr ((Expr (annot, expr_)) : parsed_expr) : (unit expr) Eff.t  =
  (fun z -> Expr (annot, z)) <$> match expr_ with
   | Epure _pe ->
       symbolify_pexpr _pe >>= fun pe ->
       Eff.return (Epure pe)
   | Ememop (_memop, _pes) ->
       begin
         let open Mem_common in
         match _memop with
          | PtrMemberShift (_tag_sym, membr_ident) ->
              lookup_sym _tag_sym >>= (function
                | Some (tag_sym, _) ->
                    Eff.return (PtrMemberShift (tag_sym, membr_ident))
                | None ->
                    Eff.fail (Cerb_location.(region (snd _tag_sym) NoCursor))
                      (Core_parser_unresolved_symbol (fst _tag_sym)))
          | PtrEq ->
               Eff.return PtrEq
          | PtrNe ->
              Eff.return PtrNe
          | PtrLt ->
              Eff.return PtrLt
          | PtrGt ->
              Eff.return PtrGt
          | PtrLe ->
              Eff.return PtrLe
          | PtrGe ->
              Eff.return PtrGe
          | Ptrdiff ->
              Eff.return Ptrdiff
          | IntFromPtr ->
              Eff.return IntFromPtr
          | PtrFromInt ->
              Eff.return PtrFromInt
          | PtrValidForDeref ->
              Eff.return PtrValidForDeref
          | PtrWellAligned ->
              Eff.return PtrWellAligned
          | PtrArrayShift ->
              Eff.return PtrArrayShift
          | Memcpy ->
              Eff.return Memcpy
          | Memcmp ->
              Eff.return Memcmp
          | Realloc ->
              Eff.return Realloc
          | Va_start ->
              Eff.return Va_start
          | Va_copy ->
              Eff.return Va_copy
          | Va_arg ->
              Eff.return Va_arg
          | Va_end ->
              Eff.return Va_end
          | Copy_alloc_id ->
              Eff.return Copy_alloc_id
          | CHERI_intrinsic _ ->
              assert false
       end >>= fun memop ->
       Eff.mapM symbolify_pexpr _pes >>= fun pes ->
       Eff.return (Ememop (memop, pes))
   | Eaction _pact ->
       symbolify_paction _pact >>= fun pact ->
       Eff.return (Eaction pact)
   | Ecase (_pe, _pat_es) ->
       symbolify_pexpr _pe >>= fun pe ->
       Eff.mapM (fun (_pat, _e) ->
         under_scope (
           symbolify_pattern _pat >>= fun pat ->
           symbolify_expr _e      >>= fun e   ->
           Eff.return (pat, e)
         )
       ) _pat_es >>= fun pat_es ->
       Eff.return (Ecase (pe, pat_es))
   | Elet (_pat, _pe1, _e2) ->
       symbolify_pexpr _pe1 >>= fun pe1 ->
       under_scope (
         symbolify_pattern _pat >>= fun pat ->
         symbolify_expr _e2     >>= fun e2  ->
         Eff.return (Elet (pat, pe1, e2))
       )
   | Eif (_pe1, _e2, _e3) ->
       symbolify_pexpr _pe1 >>= fun pe1 ->
       symbolify_expr _e2   >>= fun e2  ->
       symbolify_expr _e3   >>= fun e3  ->
       Eff.return (
         Eif (pe1, e2, e3)
       )
   | Eccall ((), _pe_ty, _pe, _pes) ->
       symbolify_pexpr _pe_ty        >>= fun pe_ty ->
       symbolify_pexpr _pe           >>= fun pe  ->
       Eff.mapM symbolify_pexpr _pes >>= fun pes ->
       Eff.return (Eccall ((), pe_ty, pe, pes))
   | Eproc ((), _nm, _pes) ->
       symbolify_name _nm            >>= fun nm  ->
       Eff.mapM symbolify_pexpr _pes >>= fun pes ->
       Eff.return (Eproc ((), nm, pes))
   | Eunseq _es ->
       Eff.mapM symbolify_expr _es >>= fun es ->
       Eff.return (Eunseq es)
   | Ewseq (_pat, _e1, _e2) ->
       symbolify_expr _e1 >>= fun e1 ->
       under_scope (
         symbolify_pattern _pat >>= fun pat ->
         symbolify_expr _e2     >>= fun e2  ->
         Eff.return (Ewseq (pat, e1, e2))
       )
   | Esseq (_pat, _e1, _e2) ->
       symbolify_expr _e1 >>= fun e1 ->
       under_scope (
         symbolify_pattern _pat >>= fun pat ->
         symbolify_expr _e2     >>= fun e2  ->
         Eff.return (Esseq (pat, e1, e2))
       )
   | Ebound _e ->
       symbolify_expr _e >>= fun e ->
       Eff.return (Ebound e)
   | End _es ->
       Eff.mapM symbolify_expr _es >>= fun es ->
       Eff.return (End es)
   | Esave ((_sym, bTy), _xs, _e) ->
       (* NOTE: the scope of Esave symbols is the whole function and these are
          therefore registered in a preliminary pass *)
       lookup_label _sym >>= begin function
         | None ->
             Eff.fail (Cerb_location.(region (snd _sym) NoCursor)) (Core_parser_unresolved_symbol (fst _sym))
         | Some (sym, _) ->
             under_scope begin
               Eff.mapM (fun (_sym, ((bTy,mct), _pe)) ->
                 symbolify_pexpr _pe >>= fun pe  ->
                 Eff.return (_sym, ((bTy,mct), pe))
               ) _xs >>= fun _xs' ->
               Eff.mapM (fun (_sym, ((bTy,mct), pe)) ->
                 register_sym _sym   >>= fun sym ->
                 Eff.return (sym, ((bTy,mct), pe))
               ) _xs' >>= fun xs ->
               symbolify_expr _e >>= fun e ->
               Eff.return (Esave ((sym, bTy), xs, e))
             end
       end
   | Erun ((), _sym, _pes) ->
       lookup_label _sym >>= begin function
         | None ->
             Eff.fail (Cerb_location.(region (snd _sym) NoCursor)) (Core_parser_unresolved_symbol (fst _sym))
         | Some (sym, _) ->
             Eff.mapM symbolify_pexpr _pes >>= fun pes ->
             Eff.return (Erun ((), sym, pes))
       end
   | Epar _es ->
       Eff.mapM symbolify_expr _es >>= fun es ->
       Eff.return (Epar es)
   | Ewait _
   | Eannot _
   | Eexcluded _ ->
       assert false

and symbolify_action_ = function
 | Create (_pe1, _pe2, pref) ->
     symbolify_pexpr _pe1 >>= fun pe1 ->
     symbolify_pexpr _pe2 >>= fun pe2 ->
     Eff.return (Create (pe1, pe2, pref))
 | CreateReadOnly (_pe1, _pe2, _pe3, pref) ->
     symbolify_pexpr _pe1 >>= fun pe1 ->
     symbolify_pexpr _pe2 >>= fun pe2 ->
     symbolify_pexpr _pe3 >>= fun pe3 ->
     Eff.return (CreateReadOnly (pe1, pe2, pe3, pref))
 | Alloc0 (_pe1, _pe2, pref) ->
     symbolify_pexpr _pe1 >>= fun pe1 ->
     symbolify_pexpr _pe2 >>= fun pe2 ->
     Eff.return (Alloc0 (pe1, pe2, pref))
 | Kill (kind, _pe) -> 
     symbolify_pexpr _pe >>= fun pe ->
     Eff.return (Kill (kind, pe))
 | Store0 (b, _pe1, _pe2, _pe3, mo) ->
     symbolify_pexpr _pe1 >>= fun pe1 ->
     symbolify_pexpr _pe2 >>= fun pe2 ->
     symbolify_pexpr _pe3 >>= fun pe3 ->
     Eff.return (Store0 (b, pe1, pe2, pe3, mo))
 | SeqRMW (b, _pe1, _pe2, _sym, _pe3) ->
     symbolify_pexpr _pe1 >>= fun pe1 ->
     symbolify_pexpr _pe2 >>= fun pe2 ->
     under_scope (
       register_sym _sym    >>= fun sym ->
       symbolify_pexpr _pe3 >>= fun pe3 ->
       Eff.return (SeqRMW (b, pe1, pe3, sym, pe3))
     )
 | Load0 (_pe1, _pe2, mo) ->
     symbolify_pexpr _pe1 >>= fun pe1 ->
     symbolify_pexpr _pe2 >>= fun pe2 ->
     Eff.return (Load0 (pe1, pe2, mo))
 | RMW0 (_pe1, _pe2, _pe3, _pe4, mo1, mo2) ->
     symbolify_pexpr _pe1 >>= fun pe1 ->
     symbolify_pexpr _pe2 >>= fun pe2 ->
     symbolify_pexpr _pe3 >>= fun pe3 ->
     symbolify_pexpr _pe4 >>= fun pe4 ->
     Eff.return (RMW0 (pe1, pe2, pe3, pe4, mo1, mo2))
 | Fence0 mo ->
     Eff.return (Fence0 mo)
 | CompareExchangeStrong (_pe1, _pe2, _pe3, _pe4, mo1, mo2) ->
     symbolify_pexpr _pe1 >>= fun pe1 ->
     symbolify_pexpr _pe2 >>= fun pe2 ->
     symbolify_pexpr _pe3 >>= fun pe3 ->
     symbolify_pexpr _pe4 >>= fun pe4 ->
     Eff.return (CompareExchangeStrong (pe1, pe2, pe3, pe4, mo1, mo2))
 | CompareExchangeWeak (_pe1, _pe2, _pe3, _pe4, mo1, mo2) ->
     symbolify_pexpr _pe1 >>= fun pe1 ->
     symbolify_pexpr _pe2 >>= fun pe2 ->
     symbolify_pexpr _pe3 >>= fun pe3 ->
     symbolify_pexpr _pe4 >>= fun pe4 ->
     Eff.return (CompareExchangeWeak (pe1, pe2, pe3, pe4, mo1, mo2))
 | LinuxFence mo ->
     Eff.return (LinuxFence mo)
 | LinuxStore (_pe1, _pe2, _pe3, mo) ->
     symbolify_pexpr _pe1 >>= fun pe1 ->
     symbolify_pexpr _pe2 >>= fun pe2 ->
     symbolify_pexpr _pe3 >>= fun pe3 ->
     Eff.return (LinuxStore (pe1, pe2, pe3, mo))
 | LinuxLoad (_pe1, _pe2, mo) ->
     symbolify_pexpr _pe1 >>= fun pe1 ->
     symbolify_pexpr _pe2 >>= fun pe2 ->
     Eff.return (LinuxLoad (pe1, pe2, mo))
 | LinuxRMW (_pe1, _pe2, _pe3, mo) ->
     symbolify_pexpr _pe1 >>= fun pe1 ->
     symbolify_pexpr _pe2 >>= fun pe2 ->
     symbolify_pexpr _pe3 >>= fun pe3 ->
     Eff.return (LinuxRMW (pe1, pe2, pe3, mo))





and symbolify_paction = function
 | Paction (p, Action (loc, (), _act_)) ->
     symbolify_action_ _act_ >>= fun act_ ->
     Eff.return (Paction (p, Action (loc, (), act_)))


let rec register_labels ((Expr (_, expr_)) : parsed_expr) : unit Eff.t  =
  match expr_ with
    | Esave ((_sym, _), _, _e) ->
        lookup_sym _sym >>= (function
          | Some (_, loc) ->
                Eff.fail loc (Core_parser_multiple_declaration (fst _sym))
          | None ->
              register_label _sym >>= fun () ->
              register_labels _e
        )
    | Epure _
    | Ememop _
    | Eaction _
    | Eccall _
    | Eproc _
    | Erun _
    | Ewait _
      ->
        Eff.return ()
    | Ecase (_, _pat_es) ->
        Eff.mapM_ (fun (_, _e) ->
          register_labels _e
        ) _pat_es
    | Elet (_, _, _e2) ->
        register_labels _e2
    | Eif (_, _e2, _e3) ->
        register_labels _e2 >>= fun () ->
        register_labels _e3
    | Eunseq _es ->
        (* TODO: there shouldn't be any Esave/Erun inside an Eunseq *)
        Eff.mapM_ register_labels _es
    | Ewseq (_, _e1, _e2) ->
        register_labels _e1 >>= fun () ->
        register_labels _e2
    | Esseq (_, _e1, _e2) ->
        register_labels _e1 >>= fun () ->
        register_labels _e2
    | Ebound _e ->
        register_labels _e
    | End _es
    | Epar _es ->
        Eff.mapM_ register_labels _es
    | Eannot _ 
    | Eexcluded _ ->
        assert false


let with_labels _e m =
  register_labels _e >>= fun () ->
  m >>= fun ret ->
  Eff.get >>= fun st ->
  Eff.put { st with labels= Pmap.empty Core_parser_util._sym_compare } >>= fun () ->
  Eff.return ret


let symbolify_impl_or_file decls : ((Core.impl, parsed_core_file) either) Eff.t =
  (* Registering all the declaration symbol in first pass (and looking for the startup symbol) *)
  open_scope >>= fun () ->
  Eff.foldrM (fun decl acc ->
    match decl with
      | Glob_decl (_sym, _, _)
      | Fun_decl (_sym, _)
      | Proc_decl (_sym, _, _)
      | Aggregate_decl (_sym, _) ->
          lookup_sym _sym >>= (function
            | Some (_, loc) ->
                Eff.fail loc (Core_parser_multiple_declaration (fst _sym))
            | None ->
                register_sym _sym >>= fun sym ->
                if fst _sym = "main" then
                  Eff.return (Some sym)
                else
                  Eff.return acc
          )
      | _ ->
          Eff.return acc
  ) None decls >>= fun startup_sym_opt ->
  Eff.foldrM (fun decl (impl_acc, globs_acc, fun_map_acc, tagDefs_acc) ->
    match decl with
      | Def_decl (iCst, bTy, _pe) ->
          symbolify_pexpr _pe >>= fun pe ->
          Eff.return (Pmap.add iCst (Def (bTy, pe)) impl_acc, globs_acc, fun_map_acc, tagDefs_acc)
      | IFun_decl (iCst, (bTy, _sym_bTys, _pe)) ->
          under_scope (
            Eff.foldrM (fun (_sym, bTy) acc ->
              register_sym _sym >>= fun sym ->
              Eff.return ((sym, bTy) :: acc)
            ) [] _sym_bTys      >>= fun sym_bTys ->
            symbolify_pexpr _pe >>= fun pe ->
            Eff.return (Pmap.add iCst (IFun (bTy, sym_bTys, pe)) impl_acc, globs_acc, fun_map_acc, tagDefs_acc)
          )
      | Glob_decl (_sym, (bTy, _ct), _e) ->
          lookup_sym _sym >>= (function
            | Some (decl_sym, _) ->
                symbolify_expr _e >>= fun e ->
                symbolify_ctype _ct >>= fun ct ->
                Eff.return (impl_acc, (decl_sym, (bTy, ct), e) :: globs_acc, fun_map_acc, tagDefs_acc)
            | None ->
                assert false
          )
      | Fun_decl (_sym, (bTy, _sym_bTys, _pe)) ->
          lookup_sym _sym >>= (function
            | Some (decl_sym, _) ->
                open_scope >>= fun () ->
                Eff.foldrM (fun (_sym, bTy) acc ->
                  register_sym _sym >>= fun sym ->
                  Eff.return ((sym, bTy) :: acc)
                ) [] _sym_bTys      >>= fun sym_bTys ->
                symbolify_pexpr _pe >>= fun pe ->
                close_scope >>= fun _ ->
                Eff.return (impl_acc, globs_acc, Pmap.add decl_sym (Fun (bTy, sym_bTys, pe)) fun_map_acc, tagDefs_acc)
            | None ->
                assert false
          )
      | Proc_decl (_sym, _, (bTy, _sym_bTys, _e)) ->
          with_labels _e begin
            lookup_sym _sym >>= function
              | Some (decl_sym, decl_loc) ->
                  open_scope >>= fun () ->
                  Eff.foldrM (fun (_sym, bTy) acc ->
                    register_sym _sym >>= fun sym ->
                    Eff.return ((sym, bTy) :: acc)
                  ) [] _sym_bTys    >>= fun sym_bTys ->
                  symbolify_expr _e >>= fun e        ->
                  close_scope >>= fun _ ->
                  Eff.return ( impl_acc, globs_acc
                             , Pmap.add decl_sym (Proc (decl_loc, None, bTy, sym_bTys, e)) fun_map_acc, tagDefs_acc)
            | None ->
                assert false
          end
      | Builtin_decl (_sym, (bTy, bTys)) ->
          begin lookup_sym _sym >>= function
            | Some (decl_sym, decl_loc) ->
                Eff.return (impl_acc, globs_acc, Pmap.add decl_sym (BuiltinDecl (decl_loc, bTy, bTys)) fun_map_acc, tagDefs_acc)
            | None ->
                assert false
          end
      | Aggregate_decl (_sym, tags) ->
          begin lookup_sym _sym >>= function
            | Some (decl_sym, _) ->
                Eff.return (impl_acc, globs_acc, fun_map_acc, Pmap.add decl_sym tags tagDefs_acc)
            | None ->
                assert false
          end
  ) (Pmap.empty iCst_compare, [], Pmap.empty sym_compare, Pmap.empty sym_compare) decls >>= fun (impl, globs, fun_map, tagDefs) ->
  if not (Pmap.is_empty impl) &&  globs = [] && Pmap.is_empty fun_map then
    Eff.return (Left impl)
  else
    (* TODO: check the absence of impl stuff *)
    match startup_sym_opt with
      | Some sym ->
          Eff.return (Right (sym, globs, fun_map, tagDefs))
      | None ->
          Eff.fail Cerb_location.unknown Core_parser_undefined_startup

let symbolify_std decls : (unit Core.fun_map) Eff.t =
  (* Registering all the declaration symbol in first pass (and looking for the startup symbol) *)
  open_scope >>= fun () ->
  Eff.mapM_ (function
    | Glob_decl (_sym, _, _)
    | Fun_decl (_sym, _)
    | Proc_decl (_sym, _, _)
    | Builtin_decl (_sym, _) ->
        lookup_sym _sym >>= (function
          | Some (_, loc) ->
              Eff.fail loc (Core_parser_multiple_declaration (fst _sym))
          | None ->
              register_sym _sym >>= fun sym ->
              Eff.return ()
        )
    | _ ->
        Eff.return ()
  ) decls >>= fun () ->
  Eff.foldrM (fun decl fun_map_acc -> match decl with
    | Def_decl (_, _, Pexpr (annots, _, _))
    | IFun_decl (_, (_, _, Pexpr (annots, _, _))) ->
      let loc = Annot.get_loc_ annots in
       Eff.fail loc Core_parser_wrong_decl_in_std
    | Glob_decl (_sym, _, _)  ->
       Eff.fail (Cerb_location.(region (snd _sym) NoCursor)) Core_parser_wrong_decl_in_std
    | Fun_decl (_sym, (bTy, _sym_bTys, _pe)) ->
        lookup_sym _sym >>= (function
          | Some (decl_sym, _) ->
              open_scope >>= fun () ->
              Eff.foldrM (fun (_sym, bTy) acc ->
                register_sym _sym >>= fun sym ->
                Eff.return ((sym, bTy) :: acc)
              ) [] _sym_bTys      >>= fun sym_bTys ->
              symbolify_pexpr _pe >>= fun pe       ->
              close_scope >>= fun _ ->
              Eff.return (Pmap.add decl_sym (Fun (bTy, sym_bTys, pe)) fun_map_acc)
          | None ->
              assert false
        )
    | Builtin_decl (_sym, (bTy, bTys)) ->
        begin lookup_sym _sym >>= function
          | Some (decl_sym, decl_loc) ->
              Eff.return (Pmap.add decl_sym (BuiltinDecl (decl_loc, bTy, bTys)) fun_map_acc)
          | None ->
              assert false
        end
    | Proc_decl (_sym, attrs, (bTy, _sym_bTys, _e)) ->
        lookup_sym _sym >>= (function
          | Some (decl_sym, decl_loc) ->
              open_scope >>= fun () ->
              Eff.foldrM (fun (_sym, bTy) acc ->
                register_sym _sym >>= fun sym ->
                Eff.return ((sym, bTy) :: acc)
              ) [] _sym_bTys    >>= fun sym_bTys ->
              symbolify_expr _e >>= fun e        ->
              close_scope >>= fun _ ->
              begin match hasAilname attrs with
                | Some str ->
                    register_ailname str decl_sym
                | None ->
                    Eff.return ()
              end >>= fun _ ->
              Eff.return (Pmap.add decl_sym (Proc (decl_loc, None, bTy, sym_bTys, e)) fun_map_acc)
          | None ->
              assert false
        )
      | Aggregate_decl ((_, p), _tags) ->
          Eff.fail (Cerb_location.(region p NoCursor)) Core_parser_wrong_decl_in_std
  ) (Pmap.empty sym_compare) decls

let symbolify_impl decls : impl Eff.t =
  Eff.foldrM (fun decl impl_acc ->
    match decl with
      | Def_decl (iCst, bTy, _pe) ->
          symbolify_pexpr _pe >>= fun pe ->
          Eff.return (Pmap.add iCst (Def (bTy, pe)) impl_acc)
      | IFun_decl (iCst, (bTy, _sym_bTys, _pe)) ->
          failwith "WIP"
      | _ ->
          failwith "ERROR: TODO(msg) this is not a valid impl file"
  ) (Pmap.empty iCst_compare) decls


(* TODO ... *)
let mk_file decls =
  match M.mode with
    | ImplORFileMode ->
        (match Eff.runM (symbolify_impl_or_file decls) initial_symbolify_state with
          | Left err ->
              raise (Core_parser_util.Core_error err)
          | Right (Left impl, _) ->
              Rimpl impl
          | Right (Right parsed_file, _) ->
              Rfile parsed_file)
    | StdMode ->
        (match Eff.runM (symbolify_std decls) initial_symbolify_state with
          | Left err ->
              raise (Core_parser_util.Core_error err)
          | Right (fun_map, st) ->
              Rstd (st.ailnames, fun_map))

%}

%token <Nat_big_num.num> INT_CONST
%token <Core_parser_util._sym> SYM
%token <Implementation.implementation_constant> IMPL
%token <Undefined.undefined_behaviour> UB
%token <Mem_common.pure_memop> PURE_MEMOP_OP
%token <Core_parser_util._sym Mem_common.generic_memop> MEMOP_OP
%token PTRMEMBERSHIFT

(* ctype tokens *)
%token CONST
%token VOID ATOMIC DOTS
%token FLOAT DOUBLE LONG_DOUBLE
%token ICHAR SHORT INT LONG LONG_LONG
%token CHAR BOOL SIGNED UNSIGNED
%token INT8_T INT16_T INT32_T INT64_T UINT8_T UINT16_T UINT32_T UINT64_T
%token INTPTR_T INTMAX_T UINTPTR_T UINTMAX_T
%token SIZE_T PTRDIFF_T
%token STRUCT UNION

(* C11 memory orders *)
%token SEQ_CST RELAXED RELEASE ACQUIRE CONSUME ACQ_REL

(* definition keywords *)
%token DEF GLOB FUN PROC

(* Core types *)
%token INTEGER FLOATING BOOLEAN POINTER CTYPE CFUNCTION UNIT EFF LOADED STORABLE

(* Core constant keywords *)
%token NULL TRUE FALSE UNIT_VALUE
%token ARRAY_SHIFT MEMBER_SHIFT
%token UNDEF ERROR
%token<string> CSTRING STRING
%token IF THEN ELSE
%nonassoc ELSE

(* list expression symbols *)
%token BRACKETS COLON_COLON


(* Core exception operators *)
(* %token RAISE REGISTER *)

(* Core sequencing operators *)
%token LET WEAK STRONG UNSEQ IN END BOUND PURE MEMOP PCALL CCALL
%token SQUOTE LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE COLON_EQ COLON SEMICOLON DOT COMMA NEG


(* SEMICOLON has higher priority than IN *)
%nonassoc IN
%right SEMICOLON



%token IS_INTEGER IS_SIGNED IS_UNSIGNED IS_SCALAR ARE_COMPATIBLE

(* unary operators *)
%token NOT

(* binary operators *)
%token STAR SLASH REM_T REM_F MINUS EQ PLUS CARET

(* boolean operators *)
%token GT LT GE LE

(* logical operators *)
%token SLASH_BACKSLASH BACKSLASH_SLASH

(* memory actions *)
%token CREATE CREATE_READONLY ALLOC STORE STORE_LOCK LOAD SEQ_RMW SEQ_RMW_WITH_FORWARD KILL FREE RMW FENCE (* COMPARE_EXCHANGE_STRONG *)

(* continuation operators *)
%token SAVE RUN

(* binder patterns *)
%token UNDERSCORE

%token ND PAR 


(* integer values *)
%token IVMAX IVMIN IVSIZEOF IVALIGNOF CFUNCTION_VALUE ARRAYCTOR
%token IVCOMPL IVAND IVOR IVXOR
%token IVMAX_ALIGNMENT
%token ARRAY SPECIFIED UNSPECIFIED

%token FVFROMINT IVFROMFLOAT


%token CASE PIPE EQ_GT OF

(* Attributes *)
%token AILNAME


(* used for globs *)
%token AILCTYPE

(* Builtin *)
%token BUILTIN

%token CONV_INT
%token<Core.iop> WRAPI CATCH_EXCEPTIONAL_CONDITION


%right BACKSLASH_SLASH
%right SLASH_BACKSLASH
%left EQ GT LT GE LE
%left PLUS MINUS
%right COLON_COLON
%left STAR SLASH REM_T REM_F
%nonassoc CARET

%token EOF

%type<Core.value>
  value
%type<(unit, Core_parser_util._sym) Core.generic_pexpr>
  pexpr
%type<(unit, unit, Core_parser_util._sym) Core.generic_expr>
  expr


%start <Core_parser_util.result>start
%parameter <M : sig
                  val mode: Core_parser_util.mode
                  val std: (Core_parser_util._sym, Cerb_frontend.Symbol.sym) Pmap.map
                end>

%%

start:
| decls= nonempty_list(declaration) EOF
    { mk_file decls }
;



attribute:
  | attrs= delimited(LBRACKET, separated_list(COMMA, attribute_pair), RBRACKET)
      { attrs }
attribute_pair:
  | AILNAME EQ str= CSTRING
      { Attr_ailname str }
;
















(* BEGIN Ail types *)
integer_base_type:
| ICHAR
    { IntegerType.Ichar }
| SHORT
    { IntegerType.Short }
| INT
    { IntegerType.Int_ }
| LONG
    { IntegerType.Long }
| LONG_LONG
    { IntegerType.LongLong }
;

integer_type:
| CHAR
    { IntegerType.Char }
| BOOL
    { IntegerType.Bool }
| INT8_T
    { IntegerType.Signed (IntegerType.IntN_t 8) }
| INT16_T
    { IntegerType.Signed (IntegerType.IntN_t 16) }
| INT32_T
    { IntegerType.Signed (IntegerType.IntN_t 32) }
| INT64_T
    { IntegerType.Signed (IntegerType.IntN_t 64) }
| UINT8_T
    { IntegerType.Unsigned (IntegerType.IntN_t 8) }
| UINT16_T
    { IntegerType.Unsigned (IntegerType.IntN_t 16) }
| UINT32_T
    { IntegerType.Unsigned (IntegerType.IntN_t 32) }
| UINT64_T
    { IntegerType.Unsigned (IntegerType.IntN_t 64) }
| INTMAX_T
    { IntegerType.(Signed Intmax_t) }
| INTPTR_T
    { IntegerType.(Signed Intptr_t) }
| UINTMAX_T
    { IntegerType.(Unsigned Intmax_t) }
| UINTPTR_T
    { IntegerType.(Unsigned Intptr_t) }
| SIGNED ibty= integer_base_type
    { IntegerType.Signed ibty }
| UNSIGNED ibty= integer_base_type
    { IntegerType.Unsigned ibty }
| SIZE_T
    { IntegerType.Size_t }
| PTRDIFF_T
    { IntegerType.Ptrdiff_t }
;

floating_type:
| FLOAT
    { Ctype.(RealFloating Float) }
| DOUBLE
    { Ctype.(RealFloating Double) }
| LONG_DOUBLE
    { Ctype.(RealFloating LongDouble) }
;

basic_type:
| ity= integer_type
    { Ctype.Integer ity }
| fty= floating_type
    { Ctype.Floating fty }
;

ctype:
| VOID
    { Ctype.void }
| bty= basic_type
  { Ctype ([], Basic bty) }
| ty= ctype LBRACKET n_opt= INT_CONST? RBRACKET
    { Ctype ([], Array (ty, n_opt)) }
| ty= ctype params= delimited(LPAREN, params, RPAREN)
    { let (tys, is_variadic) = params in
      Ctype ([], Function ( (Ctype.no_qualifiers, ty)
                          , List.map (fun ty -> (Ctype.no_qualifiers, ty, false)) tys, false)) }
| CONST ty= ctype STAR
    { Ctype ([], Pointer ({ no_qualifiers with const= true }, ty)) }
| ty= ctype STAR
    { Ctype ([], Pointer (no_qualifiers, ty)) }
| ATOMIC ty= delimited(LPAREN, ctype, RPAREN)
    { Ctype ([], Atomic ty) }
| (* TODO: check the lexing *) str= SYM
    { match Builtins.translate_builtin_typenames ("__cerbty_" ^ fst str) with
        | Some ty ->
            ty
        | None ->
            let loc = (Cerb_location.(region ($startpos, $endpos) NoCursor)) in
            raise (Core_parser_util.Core_error (loc, Errors.Core_parser_unknown_ctype (fst str)))
    }
| STRUCT tag= SYM
    (* NOTE: we only collect the string name here *)
    { Ctype.Ctype ([], Ctype.Struct (Symbol.Symbol ("", -1, SD_Id (fst tag)))) }
| UNION tag= SYM
    (* NOTE: we only collect the string name here *)
    { Ctype.Ctype ([], Ctype.Union (Symbol.Symbol ("", -1, SD_Id (fst tag)))) }
;

params:
| xs= separated_list(COMMA, ctype)
    { (xs, false) }
| xs= separated_list(COMMA, ctype) COMMA DOTS
    { (xs, true) }
;
(* END Ail types *)


core_object_type:
| INTEGER
    { OTy_integer }
| FLOATING
    { OTy_floating }
| POINTER
    { OTy_pointer }
(*
| CFUNCTION LPAREN UNDERSCORE COMMA nparams= INT_CONST RPAREN
    { OTy_cfunction (None, Nat_big_num.to_int nparams, false) }
| CFUNCTION LPAREN UNDERSCORE COMMA nparams= INT_CONST COMMA DOTS RPAREN
    { OTy_cfunction (None, Nat_big_num.to_int nparams, true) }
| CFUNCTION LPAREN ret_oTy= core_object_type COMMA nparams= INT_CONST RPAREN
    { OTy_cfunction (Some ret_oTy, Nat_big_num.to_int nparams, false) }
| CFUNCTION LPAREN ret_oTy= core_object_type COMMA nparams= INT_CONST COMMA DOTS RPAREN
    { OTy_cfunction (Some ret_oTy, Nat_big_num.to_int nparams, true) }
   *)
(*
| CFUNCTION LPAREN UNDERSCORE COMMA oTys= separated_list(COMMA, core_object_type) RPAREN
    { OTy_cfunction (None, oTys) }
| CFUNCTION LPAREN ret_oTy= core_object_type COMMA oTys= separated_list(COMMA, core_object_type) RPAREN
    { OTy_cfunction (Some ret_oTy, oTys) }
*)
| ARRAY oTy= delimited(LPAREN, core_object_type, RPAREN)
    { OTy_array oTy }
(* NOTE: this is a hack to use Symbol.sym instead of _sym!
 * The symbol is checked later, but we lose the location *)
| STRUCT tag= SYM
    { OTy_struct (Symbol.Symbol ("", 0, SD_Id (fst tag))) }
| UNION tag= SYM
    { OTy_union (Symbol.Symbol ("", 0, SD_Id (fst tag))) }
;

core_base_type:
| UNIT
    { BTy_unit }
| BOOLEAN
    { BTy_boolean }
| CTYPE
    { BTy_ctype }
| baseTy= delimited(LBRACKET, core_base_type, RBRACKET)
    { BTy_list baseTy }
| baseTys= delimited(LPAREN, separated_list(COMMA, core_base_type), RPAREN)
    { BTy_tuple baseTys }
| oTy= core_object_type
    { BTy_object oTy }
| LOADED oTy= core_object_type
    { BTy_loaded oTy }
| STORABLE
    { BTy_storable }
;

core_type:
| baseTy = core_base_type
    { (*TyBase*) baseTy }
| EFF baseTy= core_base_type
    { (*TyEffect*) baseTy }
;


%inline binary_operator:
| PLUS            { OpAdd   }
| MINUS           { OpSub   }
| STAR            { OpMul   }
| SLASH           { OpDiv   }
| REM_T           { OpRem_t }
| REM_F           { OpRem_f }
| CARET           { OpExp   }
| EQ              { OpEq    }
| GT              { OpGt    }
| LT              { OpLt    }
| GE              { OpGe    }
| LE              { OpLe    }
| SLASH_BACKSLASH { OpAnd   }
| BACKSLASH_SLASH { OpOr    }
;


name:
| _sym= SYM
    { Sym _sym }
| i= IMPL
    { Impl i }
;

cabs_id:
| n= SYM
  { Symbol.Identifier (Cerb_location.(region (snd n) NoCursor), fst n) }
;

memory_order:
| SEQ_CST { Cmm.Seq_cst }
| RELAXED { Cmm.Relaxed }
| RELEASE { Cmm.Release }
| ACQUIRE { Cmm.Acquire }
| CONSUME { Cmm.Consume }
| ACQ_REL { Cmm.Acq_rel }
;

ctor:
| ARRAYCTOR
    { Carray }
| IVMAX
    { Civmax }
| IVMIN
    { Civmin }
| IVSIZEOF
    { Civsizeof }
| IVALIGNOF
    { Civalignof }
| SPECIFIED
    { Cspecified }
| UNSPECIFIED
    { Cunspecified }
| FVFROMINT
    { Cfvfromint }
| IVFROMFLOAT
    { Civfromfloat }
| IVCOMPL
    { CivCOMPL }
| IVAND
    { CivAND }
| IVOR
    { CivOR }
| IVXOR
    { CivXOR }


list_pattern:
| BRACKETS COLON bTy= core_base_type
  { let loc = (Cerb_location.(region ($startpos, $endpos) NoCursor)) in
    Pattern ([Aloc loc], CaseCtor (Cnil (ensure_list_core_base_type loc bTy), [])) }
|  _pat1= pattern COLON_COLON _pat2= pattern
  { Pattern ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], CaseCtor (Ccons, [_pat1; _pat2])) }
| _pats= delimited(LBRACKET, separated_list(COMMA, pattern) , RBRACKET) COLON bTy= core_base_type
    { let loc = (Cerb_location.(region ($startpos, $endpos) NoCursor)) in
      mk_list_pat (ensure_list_core_base_type loc bTy) _pats }

pattern:
| _sym= SYM COLON bTy= core_base_type
    { Pattern ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], CaseBase (Some _sym, bTy)) }
| UNDERSCORE COLON bTy= core_base_type
    { Pattern ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], CaseBase (None, bTy)) }
(* Syntactic sugar for tuples and lists *)
| _pat= list_pattern
    { _pat }
| LPAREN _pat= pattern COMMA _pats= separated_nonempty_list(COMMA, pattern) RPAREN
    { Pattern ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], CaseCtor (Ctuple, _pat :: _pats)) }
| ctor=ctor _pats= delimited(LPAREN, separated_list(COMMA, pattern), RPAREN)
    { Pattern ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], CaseCtor (ctor, _pats)) }
;

pattern_pair(X):
| PIPE _pat= pattern EQ_GT _body= X
    { (_pat, _body) }

(*
typed_expr:
| _e= expr COLON bTy= core_base_type
  { (_e, bTy) }
*)


core_ctype:
| ty= delimited(SQUOTE, ctype, SQUOTE)
    { ty }

core_integer_type:
| ity= delimited(SQUOTE, integer_type, SQUOTE)
    { ity }

value:
(* TODO:
  | Vconstrained of list (list Mem.mem_constraint * value)
  | Vobject of object_value
  | Vloaded of object_value
  | Vunspecified of ctype
*)
| n= INT_CONST
    { Vobject (OVinteger (Impl_mem.integer_ival n)) }
| IVMAX_ALIGNMENT
    { Vobject (OVinteger (Impl_mem.integer_ival (Z.of_int (Ocaml_implementation.(get ()).max_alignment)))) }
| NULL ty= delimited(LPAREN, ctype, RPAREN)
    { Vobject (OVpointer (Impl_mem.null_ptrval ty)) }
| CFUNCTION_VALUE _nm= delimited(LPAREN, name, RPAREN)
  { (*TODO*) Vobject (OVpointer (Impl_mem.null_ptrval Ctype.void)) }
| UNIT_VALUE
    { Vunit }
| TRUE
    { Vtrue }
| FALSE
    { Vfalse }
| ty= core_ctype
    { Vctype ty }


list_pexpr:
| BRACKETS COLON bTy= core_base_type
    { let loc = (Cerb_location.(region ($startpos, $endpos) NoCursor)) in
      Pexpr ([Aloc loc], (), PEctor (Cnil (ensure_list_core_base_type loc bTy), [])) }
|  _pe1= pexpr COLON_COLON _pe2= pexpr
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEctor (Ccons, [_pe1; _pe2])) }
| _pes= delimited(LBRACKET, separated_list(COMMA, pexpr) , RBRACKET) COLON bTy= core_base_type
    { let loc = (Cerb_location.(region ($startpos, $endpos) NoCursor)) in
      mk_list_pe (ensure_list_core_base_type loc bTy) _pes }

member:
| DOT cid=cabs_id EQ _pe=pexpr
    { (cid, _pe) }
;

pexpr:
| _pe= delimited(LPAREN, pexpr, RPAREN)
    { _pe }
| UNDEF LPAREN ub= UB RPAREN
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEundef (Cerb_location.(region ($startpos, $endpos) NoCursor), ub)) }
| ERROR LPAREN str= STRING COMMA _pe= pexpr RPAREN
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEerror (str, _pe))  }
| _cval= value
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEval _cval) }
| _sym= SYM
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEsym _sym) }
| iCst= IMPL
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEimpl iCst) }
(* Syntactic sugar for tuples and lists *)
| LPAREN _pe= pexpr COMMA _pes= separated_nonempty_list(COMMA, pexpr) RPAREN
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEctor (Ctuple, _pe :: _pes)) }
| _pe= list_pexpr
  { _pe }
| ctor= ctor _pes= delimited(LPAREN, separated_list(COMMA, pexpr), RPAREN)
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEctor (ctor, _pes)) }
| CASE _pe= pexpr OF _pat_pes= list(pattern_pair(pexpr)) END
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) (PointCursor($startpos($1)))))], (), PEcase (_pe, _pat_pes)) }
| ARRAY_SHIFT LPAREN _pe1= pexpr COMMA ty= core_ctype COMMA _pe2= pexpr RPAREN
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEarray_shift (_pe1, ty, _pe2)) }
| MEMBER_SHIFT LPAREN _pe1= pexpr COMMA _sym= SYM COMMA DOT cid= cabs_id RPAREN
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEmember_shift (_pe1, _sym, cid)) }
| NOT _pe= delimited(LPAREN, pexpr, RPAREN)
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1))))], (), PEnot _pe) }
| MINUS _pe= pexpr
    { let loc = Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1))) in
      Pexpr ([Aloc loc], (), PEop (OpSub, Pexpr ([Aloc loc], (), PEval (Vobject (OVinteger (Impl_mem.integer_ival (Nat_big_num.of_int 0))))), _pe)) }
| CFUNCTION _pe = delimited(LPAREN, pexpr, RPAREN)
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1))))], (), PEcfunction _pe) }
| _pe1= pexpr bop= binary_operator _pe2= pexpr
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos(bop))))], (), PEop (bop, _pe1, _pe2)) }
| CONV_INT LPAREN ity= core_integer_type COMMA _pe= pexpr RPAREN
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEconv_int (ity, _pe)) }
| iop= WRAPI LPAREN ity= core_integer_type COMMA _pe1= pexpr COMMA _pe2= pexpr RPAREN
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEwrapI (ity, iop, _pe1, _pe2)) }
| iop= CATCH_EXCEPTIONAL_CONDITION LPAREN ity= core_integer_type COMMA _pe1= pexpr COMMA _pe2= pexpr RPAREN
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEcatch_exceptional_condition (ity, iop, _pe1, _pe2)) }
| MEMOP LPAREN memop= PURE_MEMOP_OP COMMA _pes= separated_list(COMMA, pexpr) RPAREN
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) (PointCursor $startpos($1))))], (), PEmemop (memop, _pes)) }
| LPAREN STRUCT _sym=SYM RPAREN _mems= delimited(LBRACE,separated_list (COMMA, member), RBRACE)
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEstruct (_sym, _mems)) }
| LPAREN UNION _sym=SYM RPAREN LBRACE m=member RBRACE
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEunion (_sym, fst m, snd m)) }
| nm= name _pes= delimited(LPAREN, separated_list(COMMA, pexpr), RPAREN)
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEcall (nm, _pes)) }
| LET _pat= pattern EQ _pe1= pexpr IN _pe2= pexpr
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) (PointCursor($startpos($1)))))], (), PElet (_pat, _pe1, _pe2)) }
| IF _pe1= pexpr THEN _pe2= pexpr ELSE _pe3= pexpr
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) (PointCursor($startpos($1)))))], (), PEif (_pe1, _pe2, _pe3)) }
| IS_SCALAR _pe= delimited(LPAREN, pexpr, RPAREN)
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEis_scalar _pe) }
| IS_INTEGER _pe= delimited(LPAREN, pexpr, RPAREN)
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEis_integer _pe) }
| IS_SIGNED _pe= delimited(LPAREN, pexpr, RPAREN)
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEis_signed _pe) }
| IS_UNSIGNED _pe= delimited(LPAREN, pexpr, RPAREN)
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEis_unsigned _pe) }
| ARE_COMPATIBLE LPAREN _pe1= pexpr COMMA _pe2= pexpr RPAREN
    { Pexpr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], (), PEare_compatible (_pe1, _pe2)) }
;

memop_op:
| memop= MEMOP_OP
    { memop }
| PTRMEMBERSHIFT _sym_cid= delimited(LBRACKET, separated_pair(SYM, COMMA, preceded(DOT, cabs_id)), RBRACKET)
    { let (_sym, cid) = _sym_cid in
      Mem_common.PtrMemberShift (_sym, cid) }

expr:
| e_= delimited(LPAREN, expr, RPAREN)
    { let Expr (annot, expr_) = e_ in
      Expr (Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor)) :: annot, expr_) }
| PURE pe_= delimited(LPAREN, pexpr, RPAREN)
    { Expr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], Epure pe_) }
| MEMOP LPAREN memop= memop_op COMMA pes= separated_list(COMMA, pexpr) RPAREN
    { Expr ([Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))], Ememop (memop, pes)) }
| LET _pat= pattern EQ _pe1= pexpr IN _e2= expr
    { Expr ( [Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))]
           , Elet (_pat, _pe1, _e2) ) }
| IF _pe1= pexpr THEN _e2= expr ELSE _e3= expr
    { Expr ( [Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))]
           , Eif (_pe1, _e2, _e3) ) }
| CASE _pe= pexpr OF _pat_es= list(pattern_pair(expr)) END
    { Expr ( [Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))]
           , Ecase (_pe, _pat_es) ) }
| PCALL LPAREN _nm= name RPAREN
    { Expr ( [Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))]
           , Eproc ((), _nm, []) ) }
| PCALL LPAREN _nm= name COMMA _pes= separated_nonempty_list(COMMA, pexpr) RPAREN
    { Expr ( [Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))]
           , Eproc ((), _nm, _pes) ) }
| CCALL LPAREN  _pe_ty= pexpr COMMA _pe= pexpr RPAREN
    { Expr ( [Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))]
           , Eccall ((), _pe_ty, _pe, []) ) }
| CCALL LPAREN  _pe_ty= pexpr COMMA _pe= pexpr COMMA _pes= separated_nonempty_list(COMMA, pexpr) RPAREN
    { Expr ( [Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))]
           , Eccall ((), _pe_ty, _pe, _pes) ) }
| _pact= paction
    { Expr ( [Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))]
           , Eaction _pact ) }
| UNSEQ _es= delimited(LPAREN, separated_list(COMMA, expr), RPAREN)
    { Expr ( [Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))]
           , Eunseq _es ) }
| LET WEAK _pat= pattern EQ _e1= expr IN _e2= expr
    { Expr ( [Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))]
           , Ewseq (_pat, _e1, _e2) ) }
| _e1= expr SEMICOLON _e2= expr
    { Expr ( [Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))]
           , Esseq (Pattern ([], CaseBase (None, BTy_unit)), _e1, _e2)) }
| LET STRONG _pat= pattern EQ _e1= expr IN _e2= expr
    { Expr ( [Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))]
           , Esseq (_pat, _e1, _e2) ) }
| BOUND _e= delimited(LPAREN, expr, RPAREN)
    { Expr ( [Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))]
           , Ebound _e ) }
| SAVE _sym= SYM COLON bTy= core_base_type
       _xs= delimited(LPAREN,
              separated_list(COMMA,
                separated_pair(SYM, COLON, separated_pair(core_base_type, COLON_EQ, pexpr))),
            RPAREN) IN _e= expr
    { Expr ( [Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))]
           , Esave ((_sym, bTy), map do_esave_arg _xs, _e) ) }
| RUN _sym= SYM _pes= delimited(LPAREN, separated_list(COMMA, pexpr), RPAREN)
    { Expr ( [Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))]
           , Erun ((), _sym, _pes) ) }
| ND _es= delimited(LPAREN, separated_list(COMMA, expr), RPAREN)
    { Expr ( [Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))]
           , End _es ) }
| PAR _es= delimited(LPAREN, separated_list(COMMA, expr), RPAREN)
    { Expr ( [Aloc (Cerb_location.(region ($startpos, $endpos) NoCursor))]
           , Epar _es ) }
;

action:
| CREATE LPAREN _pe1= pexpr COMMA _pe2= pexpr RPAREN
    { Create (_pe1, _pe2, Symbol.PrefOther "Core") }
| CREATE_READONLY LPAREN _pe1= pexpr COMMA _pe2= pexpr COMMA _pe3= pexpr RPAREN
    { CreateReadOnly (_pe1, _pe2, _pe3, Symbol.PrefOther "Core") }
| ALLOC LPAREN _pe1= pexpr COMMA _pe2= pexpr RPAREN
    { Alloc0 (_pe1, _pe2, Symbol.PrefOther "Core") }
| FREE _pe= delimited(LPAREN, pexpr, RPAREN)
    { Kill (Dynamic, _pe) }
| KILL LPAREN _ct = core_ctype COMMA _pe= pexpr RPAREN
    { Kill (Static0 _ct, _pe) }
| STORE LPAREN _pe1= pexpr COMMA _pe2= pexpr COMMA _pe3= pexpr RPAREN
    { Store0 (false, _pe1, _pe2, _pe3, Cmm.NA) }
| STORE_LOCK LPAREN _pe1= pexpr COMMA _pe2= pexpr COMMA _pe3= pexpr RPAREN
    { Store0 (true, _pe1, _pe2, _pe3, Cmm.NA) }
| LOAD LPAREN _pe1= pexpr COMMA _pe2= pexpr RPAREN
    { Load0 (_pe1, _pe2, Cmm.NA) }
| STORE LPAREN _pe1= pexpr COMMA _pe2= pexpr COMMA _pe3= pexpr COMMA mo= memory_order RPAREN
    { Store0 (false, _pe1, _pe2, _pe3, mo) }
| STORE_LOCK LPAREN _pe1= pexpr COMMA _pe2= pexpr COMMA _pe3= pexpr COMMA mo= memory_order RPAREN
    { Store0 (true, _pe1, _pe2, _pe3, mo) }
| LOAD LPAREN _pe1= pexpr COMMA _pe2= pexpr COMMA mo= memory_order RPAREN
    { Load0 (_pe1, _pe2, mo) }
| SEQ_RMW LPAREN _pe1= pexpr COMMA _pe2= pexpr COMMA _sym= SYM EQ_GT _pe3= pexpr (*COMMA mo= memory_order*) RPAREN
    { SeqRMW (false, _pe1, _pe2, _sym, _pe3) }
| SEQ_RMW_WITH_FORWARD LPAREN _pe1= pexpr COMMA _pe2= pexpr COMMA _sym= SYM EQ_GT _pe3= pexpr (*COMMA mo= memory_order*) RPAREN
    { SeqRMW (true, _pe1, _pe2, _sym, _pe3) }

| RMW LPAREN _pe1= pexpr COMMA _pe2= pexpr COMMA _pe3= pexpr COMMA _pe4= pexpr COMMA mo1= memory_order COMMA mo2= memory_order RPAREN
    { RMW0 (_pe1, _pe2, _pe3, _pe4, mo1, mo2) }
| FENCE LPAREN mo= memory_order RPAREN
    { Fence0 mo }
(*
| COMPARE_EXCHANGE_STRONG LPAREN _pe1= pexpr COMMA _pe2= pexpr COMMA _pe3= pexpr COMMA _pe4= pexpr COMMA mo1= memory_order COMMA mo2= memory_order RPAREN
    { CompareExchangeStrong (_pe1, _pe2, _pe3, _pe4, mo1, mo2) }
*)
;

paction:
| _act= action
    { Paction (Pos, Action (Cerb_location.(region ($startpos, $endpos) NoCursor), (), _act)) }
| NEG _act= delimited(LPAREN, action, RPAREN)
    { Paction (Neg, Action (Cerb_location.(region ($startpos, $endpos) NoCursor), (), _act)) }
;

def_declaration:
| DEF dname= IMPL COLON bTy= core_base_type COLON_EQ pe_= pexpr
    { Def_decl (dname, bTy, pe_) }
;

def_field:
| cid=cabs_id COLON ty=core_ctype
  { (cid, (Annot.no_attributes, None(*TODO: add support for alignment specs *), no_qualifiers, ty)) }
;

def_fields:
| f=def_field               { ([], f) }
| f=def_field fs_=def_fields { let (fs, last) = fs_ in (f::fs, last) }
;

def_aggregate_declaration:
| DEF STRUCT name=SYM COLON_EQ fds_=def_fields
    {
      let (membrs, flex_opt) =
        match fds_ with
          | (xs, (ident, (attrs, _, qs, Ctype (_, Array (elem_ty, None))))) ->
              (xs, Some (FlexibleArrayMember (attrs, ident, qs, elem_ty)))
          | (xs, last) ->
              (xs @ [last], None) in
        Aggregate_decl (name, StructDef (membrs, flex_opt))
    }
| DEF UNION name=SYM COLON_EQ fds_=def_fields
  { let (xs, last) = fds_ in
    Aggregate_decl (name, UnionDef (xs @ [last])) }
;

ifun_declaration:
| FUN fname= IMPL params= delimited(LPAREN, separated_list(COMMA, separated_pair(SYM, COLON, core_base_type)), RPAREN)
  COLON bTy= core_base_type
  COLON_EQ fbody= pexpr
    { IFun_decl (fname, (bTy, params, fbody)) }
;

glob_ctype_attribute:
| LBRACKET AILCTYPE EQ ct = core_ctype RBRACKET
  { ct }

glob_declaration:
| GLOB gname= SYM COLON cTy= core_type ct = glob_ctype_attribute COLON_EQ e= expr
  { Glob_decl (gname, (cTy, ct), e) }
;

fun_declaration:
| FUN _sym= SYM params= delimited(LPAREN, separated_list(COMMA, separated_pair(SYM, COLON, core_base_type)), RPAREN)
  COLON bTy= core_base_type
  COLON_EQ fbody= pexpr
    { Fun_decl (_sym, (bTy, params, fbody)) }
;

proc_declaration:
| PROC attrs_opt= attribute? _sym= SYM params= delimited(LPAREN, separated_list(COMMA, separated_pair(SYM, COLON, core_base_type)), RPAREN)
  COLON EFF bTy= core_base_type
  COLON_EQ fbody= expr
    { let attrs = (function None -> [] | Some z -> z) attrs_opt in
      Proc_decl (_sym, attrs, (bTy, params, fbody)) }
;

builtin_declaration:
| BUILTIN _sym= SYM params= delimited(LPAREN, separated_list(COMMA, core_base_type), RPAREN) COLON EFF bTy= core_base_type
  { Builtin_decl (_sym, (bTy, params))  }
;

declaration:
| decl= def_declaration
| decl= ifun_declaration
| decl= glob_declaration
| decl= fun_declaration
| decl= proc_declaration
| decl= builtin_declaration
| decl= def_aggregate_declaration
    { decl }

%%
