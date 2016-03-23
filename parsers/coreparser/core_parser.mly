%{
open Lem_pervasives
open Either
open Global

open Core_parser_util

open Core

module Caux = Core_aux
module Cmm = Cmm_csem

let sym_compare =
  Symbol.instance_Basic_classes_Ord_Symbol_sym_dict.compare_method

let iCst_compare =
  compare

type parsed_pexpr = (unit, _sym) generic_pexpr
type parsed_expr  = (unit, unit, _sym) generic_expr

type declaration =
  | Def_decl  of Implementation_.implementation_constant * Core.core_base_type * parsed_pexpr
  | IFun_decl of Implementation_.implementation_constant * (Core.core_base_type * (_sym * Core.core_base_type) list * parsed_pexpr)
  | Glob_decl of _sym * Core.core_type * parsed_expr
  | Fun_decl  of _sym * (Core.core_base_type * (_sym * Core.core_base_type) list * parsed_pexpr)
  | Proc_decl of _sym * (Core.core_base_type * (_sym * Core.core_base_type) list * parsed_expr)



(* TODO: move to Caux *)
let rec mk_list_pe = function
  | [] ->
      Pexpr ((), PEctor (Cnil (), []))
  | _pe::_pes ->
      Pexpr ((), PEctor (Ccons, [_pe; mk_list_pe _pes]))



type symbolify_state = {
(*  expected_bTy: core_base_type; *)
  sym_scopes: ((Core_parser_util._sym, Symbol.sym * core_base_type option * Location_ocaml.t) Pmap.map) list
}

let initial_symbolify_state = {
(*  expected_bTy= bTy; *)
  sym_scopes= [Pmap.map (fun sym -> (sym, None, Location_ocaml.unknown)) M.std];
}

type parsing_error =
  | Unresolved_symbol of _sym
  | Multiple_declaration of Location_ocaml.t * _sym

let string_of_parsing_error = function
  | Unresolved_symbol _sym ->
      "Unresolved_symbol[" ^ fst _sym ^ "]"
  | Multiple_declaration (loc, _sym) ->
      "Multiple_declaration[" ^ fst _sym ^ "]"

module Eff : sig
  type 'a t
  val return: 'a -> 'a t
  val bind: 'a t -> ('a -> 'b t) -> 'b t
  val fmap: ('a -> 'b) -> 'a t -> 'b t
  val app: ('a -> 'b) t -> 'a t -> 'b t
  val mapM: ('a -> 'b t) -> 'a list -> ('b list) t
  val mapM_: ('a -> 'b t) -> 'a list -> unit t
  val foldrM: ('a -> 'b -> 'b t) -> 'b -> 'a list -> 'b t
  val fail: parsing_error -> 'a t
  val runM: 'a t -> symbolify_state -> (parsing_error, 'a * symbolify_state) either
  val get: symbolify_state t
  val put: symbolify_state -> unit t
(*  val with_expected_bTy: core_base_type -> 'a t -> 'a t *)
end = struct
  open Either
  type 'a t = symbolify_state -> (parsing_error, 'a * symbolify_state) either
  
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
  
  let fail err =
    fun _ -> Left err
  
  let runM m st =
    m st
  
  let get =
    fun st -> Right (st, st)
  
  let put st' =
    fun _ -> Right ((), st')
  
(*
  let with_expected_bTy bTy m =
    fun st ->
      match m {st with expected_bTy= bTy} with
        | Left err ->
            Left err
        | Right (z, st') ->
            Right (z, {st' with expected_bTy= st.expected_bTy})
*)
end

let (>>=)    = Eff.bind
let (>>) m f = Eff.bind m (fun _ -> f)
let (<$>)    = Eff.fmap
let (<*>)    = Eff.app



let open_scope : unit Eff.t =
  Eff.get >>= fun st ->
  Eff.put {st with sym_scopes= Pmap.empty Core_parser_util._sym_compare :: st.sym_scopes} >>
  Eff.return ()
  
let close_scope : ((Core_parser_util._sym, Symbol.sym * core_base_type option * Location_ocaml.t) Pmap.map) Eff.t =
  Eff.get >>= fun st ->
  match st.sym_scopes with
    | [] ->
        failwith "Core_parser.close_scope: found open scope"
    | scope :: scopes ->
        Eff.put {st with sym_scopes= scopes} >>
        Eff.return scope


let under_scope (m: 'a Eff.t) : 'a Eff.t =
  open_scope >>
  m >>= fun ret ->
  close_scope >>
  Eff.return ret



let register_sym ((_, (start_p, end_p)) as _sym) bTy : Symbol.sym Eff.t =
  Eff.get >>= fun st ->
  let sym = Symbol.Symbol (!M.sym_counter, Some (fst _sym)) in
  M.sym_counter := !M.sym_counter + 1;
  Eff.put {st with
    sym_scopes=
      match st.sym_scopes with
        | [] ->
            failwith "Core_parser.register_sym: found open scope"
        | scope::scopes ->
            Pmap.add _sym (sym, bTy, Location_ocaml.Loc_region (start_p, end_p, None)) scope :: scopes
  } >>
  Eff.return sym

let lookup_sym _sym : ((Symbol.sym * core_base_type option * Location_ocaml.t) option) Eff.t =
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



let symbolify_name = function
 | Sym _sym ->
     lookup_sym _sym >>= (function
       | Some (sym, None, _) ->
           Eff.return (Sym sym)
       | None ->
           Eff.fail (Unresolved_symbol _sym))
 | Impl iCst ->
     Eff.return (Impl iCst)

let rec symbolify_value _cval =
  match _cval with
(*
   | Vconstrained of list (list Mem.mem_constraint * (generic_value 'sym))
   | Vobject of (generic_object_value 'sym) (* C object value *)
   | Vspecified of (generic_object_value 'sym) (* non-unspecified loaded value *)
   | Vunspecified ty ->
      Eff.return (Vunspecified ty)
*)
   | Vunit ->
       Eff.return Vunit
   | Vtrue ->
       Eff.return Vtrue
   | Vfalse ->
       Eff.return Vfalse
   | Vctype ty ->
       Eff.return (Vctype ty)
(*
   | Vlist of core_base_type * list (generic_value 'sym) (* list *)
   | Vtuple _cvals ->
       Vtuple <$> Eff.mapM symbolify_value _cvals
*)

let convert_ctor : unit generic_ctor -> ctor = function
 | Cnil () ->
     failwith "Cnil"
 | Ccons ->
     Ccons
 | Ctuple ->
     Ctuple
 | Carray ->
     Carray
 | Civmax ->
     Civmax
 | Civmin ->
     Civmin
 | Civsizeof ->
     Civsizeof
 | Civalignof ->
     Civalignof
 | Cspecified ->
     Cspecified
 | Cunspecified ->
     Cunspecified

let rec symbolify_pattern _pat : pattern Eff.t =
  Eff.get >>= fun st ->
  match _pat with
    | CaseBase None ->
        Eff.return (CaseBase None)
    | CaseBase (Some (_sym, bTy)) ->
        register_sym _sym (Some bTy) >>= fun sym ->
        Eff.return (CaseBase (Some (sym, bTy)))

(*
    | CaseCtor (Cnil (), []) ->
        failwith "Eff.return (CaseCtor (Cnil bTy', []))"
    | CaseCtor (Ccons, [_pat1; _pat2]) ->
        symbolify_pattern _pat1 >>= fun pat1 ->
        symbolify_pattern _pat2 >>= fun pat2 ->
        Eff.return (CaseCtor (Ccons, [pat1; pat2]))
    | CaseCtor (Ctuple, _pats) ->
        failwith "WIP: CaseCtor Ctuple"
    | CaseCtor (Carray, _pats) ->
        failwith "WIP: CaseCtor Carray"
(*    | (CaseCtor ((Civmax|Civmin|Civsizeof|Civalignof) as _ctor, [_pat]), BTy_object OTy_integer) -> *)
    | CaseCtor ((Civmax|Civmin|Civsizeof|Civalignof) as _ctor, [_pat]) -> 
        let ctor = match _ctor with
          | Civmax     -> Civmax
          | Civmin     -> Civmin
          | Civsizeof  -> Civsizeof
          | Civalignof -> Civalignof
          | _          -> assert false in
        symbolify_pattern _pat >>= fun pat ->
        Eff.return (CaseCtor (ctor, [pat]))
    | CaseCtor (Cspecified, [_pat]) ->
        symbolify_pattern _pat >>= fun pat ->
        Eff.return (CaseCtor (Cspecified, [pat]))
    | CaseCtor (Cunspecified, [_pat]) ->
        symbolify_pattern _pat >>= fun pat ->
        Eff.return (CaseCtor (Cunspecified, [pat]))
*)
    | CaseCtor (_ctor, _pats) ->
        Eff.mapM symbolify_pattern _pats >>= fun pat ->
        Eff.return (CaseCtor (convert_ctor _ctor, pat))
    | _ ->
        failwith "WIP: symbolify_pattern"





(* WIP: TEMPORARY HACK *)
let mk_if_pe pe1 (Pexpr (bTy, _) as pe2) pe3 =
  Pexpr (bTy, PEif (pe1, pe2, pe3))

let mk_op_pe bop pe1 pe2 : pexpr =
  match bop with
    | OpAdd ->
        Pexpr( (BTy_object OTy_integer), (PEop( bop, pe1, pe2)))
    | OpSub ->
        Pexpr( (BTy_object OTy_integer), (PEop( bop, pe1, pe2)))
    | OpMul ->
        Pexpr( (BTy_object OTy_integer), (PEop( bop, pe1, pe2)))
    | OpDiv ->
        Pexpr( (BTy_object OTy_integer), (PEop( bop, pe1, pe2)))
    | OpRem_t ->
        Pexpr( (BTy_object OTy_integer), (PEop( bop, pe1, pe2)))
    | OpRem_f ->
        Pexpr( (BTy_object OTy_integer), (PEop( bop, pe1, pe2)))
    | OpExp ->
        Pexpr( (BTy_object OTy_integer), (PEop( bop, pe1, pe2)))
    | OpEq ->
        Pexpr( BTy_boolean, (PEop( bop, pe1, pe2)))
    | OpEq ->
        Pexpr( BTy_boolean, (PEop( bop, pe1, pe2)))
    | OpGt ->
        Pexpr( BTy_boolean, (PEop( bop, pe1, pe2)))
    | OpLt ->
        Pexpr( BTy_boolean, (PEop( bop, pe1, pe2)))
    | OpGe ->
        Pexpr( BTy_boolean, (PEop( bop, pe1, pe2)))
    | OpLe ->
        Pexpr( BTy_boolean, (PEop( bop, pe1, pe2)))
    | OpAnd ->
        Pexpr( BTy_boolean, (PEop( bop, pe1, pe2)))
    | OpOr ->
        Pexpr( BTy_boolean, (PEop( bop, pe1, pe2)))












let rec symbolify_pexpr expected_bTy (Pexpr ((), _pexpr): parsed_pexpr) : pexpr Eff.t =
  match _pexpr with
    | PEsym _sym ->
        Eff.get         >>= fun st ->
        lookup_sym _sym >>= (function
          | Some (sym, Some bTy, _) ->
              Eff.return (Caux.mk_sym_pe bTy sym)
          | None ->
              Eff.fail (Unresolved_symbol _sym)
        )
    | PEimpl iCst ->
        (* WIP: THIS TYPE IS WRONG *)
        Eff.return (Pexpr (BTy_unit, PEimpl iCst))
    | PEval (Vobject (OVinteger ival)) ->
        Eff.return (Pexpr (BTy_object OTy_integer, PEval (Vobject (OVinteger ival))))
    | PEval (Vobject (OVcfunction _nm)) ->
        symbolify_name _nm >>= fun nm ->
        Eff.return (Pexpr (BTy_object OTy_cfunction, PEval (Vobject (OVcfunction nm))))
    | PEval Vunit ->
        Eff.return (Pexpr (BTy_unit, PEval Vunit))
    | PEval Vtrue ->
        Eff.return (Pexpr (BTy_boolean, PEval Vtrue))
    | PEval Vfalse ->
        Eff.return (Pexpr (BTy_boolean, PEval Vfalse))
    | PEval (Vctype ty) ->
        Eff.return (Pexpr (BTy_ctype, PEval (Vctype ty)))
    | PEval _cval ->
        failwith "WIP: PEval"
(*  | PEconstrained of list (list Mem.mem_constraint * (generic_pexpr 'ty 'sym)) (* constrained value *) *)
    | PEundef ub ->
        (* WIP: THIS TYPE IS WRONG *)
        Eff.return (Pexpr (BTy_unit, PEundef ub))
    | PEerror (str, _pe) ->
        (* WIP: THE TYPES ARE WRONG *)
        symbolify_pexpr BTy_unit _pe >>= fun pe ->
        Eff.return (Pexpr (BTy_unit, PEerror (str, pe)))
    | PEctor (Cnil (), []) ->
        (match expected_bTy with
          | BTy_list bTy ->
              Eff.return (Pexpr (expected_bTy, PEctor (Cnil bTy, [])))
          | _ ->
              (* WIP THIS IS WRONG *)
              Eff.return (Pexpr (BTy_list BTy_unit, PEctor (Cnil BTy_unit, [])))
        )
    | PEctor (Ccons, [_pe1; _pe2]) ->
        (match expected_bTy with
          | BTy_list bTy ->
              symbolify_pexpr bTy _pe1          >>= fun pe1 ->
              symbolify_pexpr expected_bTy _pe2 >>= fun pe2 ->
              Eff.return (Pexpr (expected_bTy, PEctor (Ccons, [pe1; pe2])))
          | _ ->
              (* WIP THIS IS WRONG *)
              symbolify_pexpr BTy_unit _pe1            >>= fun pe1 ->
              symbolify_pexpr (BTy_list BTy_unit) _pe2 >>= fun pe2 ->
              Eff.return (Pexpr (BTy_list BTy_unit, PEctor (Ccons, [pe1; pe2])))
        )
    | PEctor (Ctuple, _pes) ->
        Eff.get >>= fun st ->
        Eff.mapM (symbolify_pexpr BTy_unit(*WIP*)) _pes >>= fun pes ->
        Eff.return (Pexpr (expected_bTy, PEctor (Ctuple, pes)))
    | PEctor (Carray, _pes) ->
        failwith "WIP: PEctor Carray"
    | PEctor (Civmax, [_pe]) ->
        symbolify_pexpr BTy_ctype _pe >>= fun pe ->
        Eff.return (Pexpr (BTy_object OTy_integer, PEctor (Civmax, [pe])))
    | PEctor (Civmin, [_pe]) ->
        symbolify_pexpr BTy_ctype _pe >>= fun pe ->
        Eff.return (Pexpr (BTy_object OTy_integer, PEctor (Civmin, [pe])))
    | PEctor (Civsizeof, [_pe]) ->
        symbolify_pexpr BTy_ctype _pe >>= fun pe ->
        Eff.return (Pexpr (BTy_object OTy_integer, PEctor (Civsizeof, [pe])))
    | PEctor (Civalignof, [_pe]) ->
        symbolify_pexpr BTy_ctype _pe >>= fun pe ->
        Eff.return (Pexpr (BTy_object OTy_integer, PEctor (Civalignof, [pe])))
    | PEctor (Cspecified, [_pe]) ->
        symbolify_pexpr BTy_unit(*WIP THIS IS WRONG*) _pe >>= fun pe ->
        Eff.return (Pexpr (expected_bTy, PEctor (Cspecified, [pe])))
    | PEctor (Cunspecified, [_pe]) ->
        symbolify_pexpr BTy_ctype _pe >>= fun pe ->
        Eff.return (Pexpr (expected_bTy, PEctor (Cunspecified, [pe])))
    | PEcase (_pe, _pat_pes) ->
        symbolify_pexpr BTy_unit(* WIP: TYPE IS WRONG*) _pe >>= fun pe ->
        Eff.mapM (fun (_pat, _pe) ->
          under_scope (
            symbolify_pattern _pat >>= fun pat ->
            symbolify_pexpr BTy_unit(* WIP: TYPE IS WRONG*) _pe >>= fun pe ->
            Eff.return (pat, pe)
          )
        ) _pat_pes >>= fun pat_pes ->
        Eff.return (Pexpr (expected_bTy, PEcase (pe, pat_pes)))
    | PEarray_shift (_pe1, ty, _pe2) ->
        symbolify_pexpr (BTy_object OTy_pointer) _pe1 >>= fun pe1 ->
        symbolify_pexpr (BTy_object OTy_integer) _pe2 >>= fun pe2 ->
        Eff.return (Pexpr (BTy_object OTy_pointer, PEarray_shift (pe1, ty, pe2)))
    | PEmember_shift (_pe, tag_sym, member_ident) ->
        failwith "WIP: PEmember_shift"
    | PEnot _pe ->
        Caux.mk_not_pe <$> symbolify_pexpr BTy_boolean _pe
    | PEop (bop, _pe1, _pe2) ->
        symbolify_pexpr ((*WIP*)BTy_object OTy_integer) _pe1 >>= fun pe1 ->
        symbolify_pexpr ((*WIP*)BTy_object OTy_integer) _pe2 >>= fun pe2 ->
        Eff.return (mk_op_pe bop pe1 pe2)
    | PEstruct (tag_sym, ident_pes) ->
        failwith "WIP: PEstruct"
    | PEunion (tag_sym, member_ident, _pe) ->
        failwith "WIP: PEunion"
    | PEcall (_nm, _pes) ->
        symbolify_name _nm >>= fun nm ->
        (* WIP: this is wrong *)
        Eff.mapM (symbolify_pexpr BTy_unit) _pes >>= fun pes ->
        Eff.return (Pexpr (BTy_unit, PEcall (nm, pes)))
    | PElet (_pat, _pe1, _pe2) ->
        symbolify_pexpr BTy_unit(*WIP*) _pe1   >>= fun pe1 ->
        open_scope             >>
        symbolify_pattern _pat >>= fun pat ->
        symbolify_pexpr BTy_unit(*WIP*) _pe2   >>= fun pe2  ->
        close_scope >>
        Eff.return (Caux.mk_let_pe pat pe1 pe2)
    | PEif (_pe1, _pe2, _pe3) ->
        mk_if_pe
          <$> symbolify_pexpr BTy_boolean _pe1
          <*> symbolify_pexpr BTy_unit(*WIP*) _pe2
          <*> symbolify_pexpr BTy_unit(*WIP*) _pe3
    | PEis_scalar _pe ->
        symbolify_pexpr BTy_ctype _pe >>= fun pe ->
        Eff.return (Pexpr (BTy_boolean, PEis_scalar pe))
    | PEis_integer _pe ->
        symbolify_pexpr BTy_ctype _pe >>= fun pe ->
        Eff.return (Pexpr (BTy_boolean, PEis_integer pe))
    | PEis_signed _pe ->
        symbolify_pexpr BTy_ctype _pe >>= fun pe ->
        Eff.return (Pexpr (BTy_boolean, PEis_signed pe))
    | PEis_unsigned _pe ->
        symbolify_pexpr BTy_ctype _pe >>= fun pe ->
        Eff.return (Pexpr (BTy_boolean, PEis_unsigned pe))


let rec symbolify_expr : parsed_expr -> (unit expr) Eff.t = function
 | Epure _pe ->
     (* WIP: THIS IS WRONG *)
     symbolify_pexpr BTy_unit _pe >>= fun pe ->
     Eff.return (Epure pe)
 | Ememop (memop, _pes) ->
     failwith "WIP: Ememop"
 | Eaction _pact ->
     symbolify_paction _pact >>= fun pact ->
     Eff.return (Eaction pact)
 | Ecase (_pe, _pat_es) ->
     failwith "WIP: Ecase"
 | Elet (_pat, _pe1, _e2) ->
     failwith "WIP: Elet"
  | Eif (_pe1, _e2, _e3) ->
      symbolify_pexpr BTy_boolean _pe1 >>= fun pe1 ->
      symbolify_expr _e2               >>= fun e2  ->
      symbolify_expr _e3               >>= fun e3  ->
      Eff.return (
        Eif (pe1, e2, e3)
      )
  | Eskip ->
      Eff.return Eskip
 | Eproc ((), _pe, _pes) ->
     symbolify_pexpr (BTy_object OTy_cfunction) _pe >>= fun pe ->
     Eff.mapM (symbolify_pexpr BTy_unit(*WIP THIS IS WRONG*)) _pes >>= fun pes ->
     Eff.return (Eproc ((), pe, pes))
 | Ereturn _pe ->
     symbolify_pexpr BTy_unit(*WIP THIS IS WRONG*) _pe >>= fun pe ->
     Eff.return (Ereturn pe)
 | Eunseq _es ->
     failwith "WIP: Eunseq"
 | Ewseq (_pat, _e1, _e2) ->
     failwith "WIP: Ewseq"
 | Esseq (_pat, _e1, _e2) ->
     symbolify_expr _e1 >>= fun e1 ->
     under_scope (
       symbolify_pattern _pat >>= fun pat ->
       symbolify_expr _e2     >>= fun e2  ->
       Eff.return (Esseq (pat, e1, e2))
     )
 | Easeq _ ->
     failwith "WIP: Easeq"
 | Eindet (n, _e) ->
     failwith "WIP: Eindet"
 | Ebound (n, _e) ->
     failwith "WIP: Ebound"
 | End _es ->
     failwith "WIP: End"
 | Esave _ ->
     failwith "WIP: Esave"
 | Erun _ ->
     failwith "WIP: Erun"
 | Epar _es ->
     Eff.mapM symbolify_expr _es >>= fun es ->
     Eff.return (Epar es)
 | Ewait tid ->
     failwith "WIP: Ewait"
 | Eloc (loc, _e) ->
     failwith "WIP: Eloc"

and symbolify_action_ = function
 | Create (_pe1, _pe2, pref) ->
     symbolify_pexpr BTy_ctype                _pe1 >>= fun pe1 ->
     symbolify_pexpr (BTy_object OTy_integer) _pe2 >>= fun pe2 ->
     Eff.return (Create (pe1, pe2, pref))
 | Alloc0 (_pe1, _pe2, pref) ->
     symbolify_pexpr (BTy_object OTy_integer) _pe1 >>= fun pe1 ->
     symbolify_pexpr (BTy_object OTy_integer) _pe2 >>= fun pe2 ->
     Eff.return (Alloc0 (pe1, pe2, pref))
 | Kill _pe -> 
     symbolify_pexpr (BTy_object OTy_pointer) _pe >>= fun pe ->
     Eff.return (Kill pe)
 | Store0 (_pe1, _pe2, _pe3, mo) ->
     symbolify_pexpr BTy_ctype _pe1 >>= fun pe1 ->
     symbolify_pexpr (BTy_object OTy_pointer) _pe2 >>= fun pe2 ->
     symbolify_pexpr (BTy_loaded OTy_integer (*WIP THIS IS WRONG*)) _pe3 >>= fun pe3 ->
     Eff.return (Store0 (pe1, pe2, pe3, mo))
 | Load0 (_pe1, _pe2, mo) ->
     symbolify_pexpr BTy_ctype _pe1 >>= fun pe1 ->
     symbolify_pexpr (BTy_object OTy_pointer) _pe2 >>= fun pe2 ->
     Eff.return (Load0 (pe1, pe2, mo))
 | RMW0 (_pe1, _pe2, _pe3, _pe4, mo1, mo2) ->
     failwith "WIP: RMW"
(*
     symbolify_pexpr BTy_ctype _pe1 >>= fun pe1 ->
     symbolify_pexpr _pe2 >>= fun pe2 ->
     symbolify_pexpr _pe3 >>= fun pe3 ->
     symbolify_pexpr _pe4 >>= fun pe4 ->
     Eff.return (RMW0 (pe1, pe2, pe3, pe4, mo1, mo2))
*)
 | Fence0 mo ->
     Eff.return (Fence0 mo)

and symbolify_paction = function
 | Paction (p, Action (loc, (), _act_)) ->
     symbolify_action_ _act_ >>= fun act_ ->
     Eff.return (Paction (p, Action (loc, (), act_)))



let symbolify_impl_or_file decls : ((Core.impl, Symbol.sym * (Symbol.sym * Core.core_type * unit Core.expr) list * unit Core.fun_map) either) Eff.t =
  (* Registering all the declaration symbol in first pass (and looking for the startup symbol) *)
  open_scope >>
  Eff.foldrM (fun decl acc ->
    match decl with
      | Glob_decl (_sym, _, _)
      | Fun_decl (_sym, _)
      | Proc_decl (_sym, _) ->
          lookup_sym _sym >>= (function
            | Some (_, _, loc) ->
                Eff.fail (Multiple_declaration (loc, _sym))
            | None ->
                register_sym _sym None >>= fun sym ->
                if fst _sym = "main" then
                  Eff.return (Some sym)
                else
                  Eff.return acc
          )
      | _ ->
          Eff.return acc
  ) None decls >>= fun startup_sym_opt ->
  Eff.foldrM (fun decl (impl_acc, globs_acc, fun_map_acc) ->
    match decl with
      | Def_decl (iCst, bTy, _pe) ->
          symbolify_pexpr bTy _pe >>= fun pe ->
          Eff.return (Pmap.add iCst (Def (bTy, pe)) impl_acc, globs_acc, fun_map_acc)
      | IFun_decl (iCst, (bTy, _sym_bTys, _pe)) ->
          under_scope (
            Eff.foldrM (fun (_sym, bTy) acc ->
              register_sym _sym (Some bTy) >>= fun sym ->
              Eff.return ((sym, bTy) :: acc)
            ) [] _sym_bTys      >>= fun sym_bTys ->
            symbolify_pexpr BTy_unit(*WIP: TYPE IS WRONG*) _pe >>= fun pe ->
            Eff.return (Pmap.add iCst (IFun (bTy, sym_bTys, pe)) impl_acc, globs_acc, fun_map_acc)
          )
      | Glob_decl (_sym, bTy, _e) ->
          lookup_sym _sym >>= (function
            | Some (decl_sym, None, _) ->
                symbolify_expr _e >>= fun e ->
                Eff.return (impl_acc, (decl_sym, bTy, e) :: globs_acc, fun_map_acc)
            | None ->
                assert false
          )
      | Fun_decl (_sym, (bTy, _sym_bTys, _pe)) ->
          lookup_sym _sym >>= (function
            | Some (decl_sym, None, _) ->
                open_scope >>
                Eff.foldrM (fun (_sym, bTy) acc ->
                  register_sym _sym (Some bTy) >>= fun sym ->
                  Eff.return ((sym, bTy) :: acc)
                ) [] _sym_bTys      >>= fun sym_bTys ->
                symbolify_pexpr BTy_unit(*WIP*) _pe >>= fun pe ->
                close_scope >>
                Eff.return (impl_acc, globs_acc, Pmap.add decl_sym (Fun (bTy, sym_bTys, pe)) fun_map_acc)
            | None ->
                assert false
          )
      | Proc_decl (_sym, (bTy, _sym_bTys, _e)) ->
          lookup_sym _sym >>= (function
            | Some (decl_sym, None, _) ->
                open_scope >>
                Eff.foldrM (fun (_sym, bTy) acc ->
                  register_sym _sym (Some bTy) >>= fun sym ->
                  Eff.return ((sym, bTy) :: acc)
                ) [] _sym_bTys    >>= fun sym_bTys ->
                symbolify_expr _e >>= fun e        ->
                close_scope >>
                Eff.return (impl_acc, globs_acc, Pmap.add decl_sym (Proc (bTy, sym_bTys, e)) fun_map_acc)
            | None ->
                assert false
          )
  ) (Pmap.empty iCst_compare, [], Pmap.empty sym_compare) decls >>= fun (impl, globs, fun_map) ->
  if not (Pmap.is_empty impl) &&  globs = [] && Pmap.is_empty fun_map then
    Eff.return (Left impl)
  else
    (* TODO: check the absence of impl stuff *)
    match startup_sym_opt with
      | Some sym ->
          Eff.return (Right (sym, globs, fun_map))
      | None ->
          failwith "TODO(msg) didn't find a main function/procedure"


let symbolify_std decls : (unit Core.fun_map) Eff.t =
  (* Registering all the declaration symbol in first pass (and looking for the startup symbol) *)
  open_scope >>
  Eff.mapM_ (fun decl ->
    match decl with
      | Glob_decl (_sym, _, _)
      | Fun_decl (_sym, _)
      | Proc_decl (_sym, _) ->
          lookup_sym _sym >>= (function
            | Some (_, None, loc) ->
                Eff.fail (Multiple_declaration (loc, _sym))
            | None ->
                register_sym _sym None >>= fun sym ->
                Eff.return ()
          )
      | _ ->
          Eff.return ()
  ) decls >>
  Eff.foldrM (fun decl fun_map_acc ->
    match decl with
      | Def_decl _ 
      | IFun_decl _
      | Glob_decl _ ->
         failwith "ERROR: TODO(msg) this is not a valid std file"
      | Fun_decl (_sym, (bTy, _sym_bTys, _pe)) ->
          lookup_sym _sym >>= (function
            | Some (decl_sym, None, _) ->
                open_scope >>
                Eff.foldrM (fun (_sym, bTy) acc ->
                  register_sym _sym (Some bTy) >>= fun sym ->
                  Eff.return ((sym, bTy) :: acc)
                ) [] _sym_bTys      >>= fun sym_bTys ->
                symbolify_pexpr BTy_unit(*WIP*) _pe >>= fun pe       ->
                close_scope >>
                Eff.return (Pmap.add decl_sym (Fun (bTy, sym_bTys, pe)) fun_map_acc)
            | None ->
                assert false
          )
      | Proc_decl (_sym, (bTy, _sym_bTys, _e)) ->
          lookup_sym _sym >>= (function
            | Some (decl_sym, None, _) ->
                open_scope >>
                Eff.foldrM (fun (_sym, bTy) acc ->
                  register_sym _sym (Some bTy) >>= fun sym ->
                  Eff.return ((sym, bTy) :: acc)
                ) [] _sym_bTys    >>= fun sym_bTys ->
                symbolify_expr _e >>= fun e        ->
                close_scope >>
                Eff.return (Pmap.add decl_sym (Proc (bTy, sym_bTys, e)) fun_map_acc)
            | None ->
                assert false
          )
  ) (Pmap.empty sym_compare) decls

let symbolify_impl decls : impl Eff.t =
  Eff.foldrM (fun decl impl_acc ->
    match decl with
      | Def_decl (iCst, bTy, _pe) ->
          symbolify_pexpr bTy _pe >>= fun pe ->
          Eff.return (Pmap.add iCst (Def (bTy, pe)) impl_acc)
      | IFun_decl (iCst, (bTy, _sym_bTys, _pe)) ->
          failwith "WIP"
      | _ ->
          failwith "ERROR: TODO(msg) this is not a valid impl file"
  ) (Pmap.empty iCst_compare) decls




(*
decls None >>= function
    | Some sym ->
        let file = {
          main=   sym;
          stdlib= Pmap.empty sym_compare; (* TODO hackish *)
          impl=   Pmap.empty iCst_compare;
          globs=  [];
          funs=   Pmap.empty sym_compare;
          

 


(* foldrM f xs a *)
  Eff.foldrM (fun

  ) decls 
{
   main   : Symbol.sym;
   stdlib : fun_map 'a;
   impl   : impl;
   globs  : list (Symbol.sym * core_type * expr 'a);
   funs   : fun_map 'a;
}



 function
  | Def_decl (iCst, bTy, _pe) ->
      St.with_expected_bTy bTy (symbolify_pexpr _pe) >>= fun pe ->
      St.return (Def_decl (iCst, bTy, pe))
(*
  | IFun_decl (iCst, (bTy, _sym_bTys, _pe)) ->
      
  | Glob_decl (_sym, coreTy, _e) ->
      
*)
  | Fun_decl (_sym, _sym_bTys, _pe) ->
      lookup_register _sym >>= fun sym ->
      KKK
(*
  | Proc_decl (_sym, _sym_bTys, _e) ->
      
*)

*)

(* TODO ... *)
let mk_file decls =
  match M.mode with
    | ImplORFileMode ->
        (match Eff.runM (symbolify_impl_or_file decls) initial_symbolify_state with
          | Left err ->
              failwith (string_of_parsing_error err)
          | Right (Left impl, _) ->
              Rimpl impl
          | Right (Right (main_sym, globs, fun_map), _) ->
              Rfile (main_sym, globs, fun_map))
    | StdMode ->
        (match Eff.runM (symbolify_std decls) initial_symbolify_state with
          | Left err ->
              failwith (string_of_parsing_error err)
          | Right (fun_map, _) ->
              Rstd fun_map)

(*
    | StdMode ->
        match Eff.runM (symbolify_std decls) (initial_symbolify_state BTy_unit(* TODO *)) with
          | Right (fun_map, _) ->
              Rstd fun_map
*)


(*
  if Pmap.is_empty M.std then
    Rstd begin
      Pmap.add (Symbol.Symbol (8, Some "catch_exceptional_condition")) (Fun (BTy_object OTy_integer, [], Pexpr (BTy_unit, PEval Vunit))) (
      Pmap.add (Symbol.Symbol (7, Some "is_representable")) (Fun (BTy_boolean, [], Pexpr (BTy_unit, PEval Vunit))) (
      Pmap.add (Symbol.Symbol (6, Some "ctype_width")) (Fun (BTy_object OTy_integer, [], Pexpr (BTy_unit, PEval Vunit))) (
      Pmap.add (Symbol.Symbol (5, Some "wrapI")) (Fun (BTy_object OTy_integer, [], Pexpr (BTy_unit, PEval Vunit))) (
      Pmap.add (Symbol.Symbol (4, Some "conv")) (Fun (BTy_object OTy_integer, [], Pexpr (BTy_unit, PEval Vunit))) (
      Pmap.add (Symbol.Symbol (3, Some "bitwise_OR")) (Fun (BTy_unit, [], Pexpr (BTy_unit, PEval Vunit))) (
      Pmap.add (Symbol.Symbol (2, Some "bitwise_XOR")) (Fun (BTy_unit, [], Pexpr (BTy_unit, PEval Vunit))) (
      Pmap.add (Symbol.Symbol (1, Some "bitwise_AND")) (Fun (BTy_unit, [], Pexpr (BTy_unit, PEval Vunit))) (
      Pmap.add (Symbol.Symbol (0, Some "conv_int")) (Fun (BTy_unit, [], Pexpr (BTy_unit, PEval Vunit))) (Pmap.empty compare)
     ))))))))
    end
  else
     Rimpl (Pmap.empty compare)
*)


%}

%token <Nat_big_num.num> INT_CONST
%token <Core_parser_util._sym> SYM
%token <Implementation_.implementation_constant> IMPL
%token <Undefined.undefined_behaviour> UB

(* ctype tokens *)
%token VOID ATOMIC (* SIZE_T INTPTR_T PTRDIFF_T WCHAR_T CHAR16_T CHAR32_T *) (* DOTS *)
%token ICHAR SHORT INT LONG LONG_LONG
%token CHAR BOOL SIGNED UNSIGNED
%token INT8_T INT16_T INT32_T INT64_T UINT8_T UINT16_T UINT32_T UINT64_T
%token STRUCT UNION

(* C11 memory orders *)
%token SEQ_CST RELAXED RELEASE ACQUIRE CONSUME ACQ_REL

(* definition keywords *)
%token DEF GLOB FUN PROC

(* Core types *)
%token INTEGER FLOATING BOOLEAN POINTER CTYPE CFUNCTION UNIT EFF LOADED

(* Core constant keywords *)
%token TRUE FALSE
%token ARRAY_SHIFT MEMBER_SHIFT
%token UNDEF ERROR
%token<string> STRING
%token SKIP IF THEN ELSE
%nonassoc ELSE


(* Core exception operators *)
%token RAISE REGISTER (* TRY WITH PIPE MINUS_GT *)

(* Core sequencing operators *)
%token LET WEAK STRONG ATOM UNSEQ IN END INDET RETURN PURE PCALL
%nonassoc IN DOT


%token DQUOTE LPAREN RPAREN LBRACKET RBRACKET COLON_EQ COLON (* SEMICOLON *) COMMA LBRACE RBRACE NEG

%token IS_INTEGER IS_SIGNED IS_UNSIGNED IS_SCALAR

(* unary operators *)
%token NOT

(* binary operators *)
%token STAR SLASH REM_T REM_F MINUS EQ PLUS CARET

(* boolean operators *)
%token GT LT GE LE

(* logical operators *)
%token SLASH_BACKSLASH BACKSLASH_SLASH

(* memory actions *)
%token CREATE ALLOC STORE LOAD KILL RMW FENCE

(* continuation operators *)
%token SAVE RUN DOT

(* binder patterns *)
%token UNDERSCORE

%token ND PAR 


(* integer values *)
%token IVMAX IVMIN IVSIZEOF IVALIGNOF CFUNCTION_VALUE
%token NIL CONS TUPLE ARRAY SPECIFIED UNSPECIFIED

%token CASE PIPE EQ_GT OF

(* TODO: not used yet, but the tracing mode of the parser crash othewise ..... *)
(*
%token FLOAT DOUBLE LONG_DOUBLE STRUCT UNION ENUM FUNCTION
RETURN   PROC CASE OF  TILDE PIPES PIPE MINUS_GT LBRACE RBRACE LBRACES RBRACES LANGLE RANGLE DOT SEMICOLON
 *)


%right BACKSLASH_SLASH
%right SLASH_BACKSLASH
%left EQ GT LT GE LE
%left PLUS MINUS
%left STAR SLASH REM_T REM_F
%nonassoc CARET

%token EOF

%type<Core_parser_util._sym Core.generic_value>
  value
%type<(unit, Core_parser_util._sym) Core.generic_pexpr>
  pexpr
%type<(unit, unit, Core_parser_util._sym) Core.generic_expr>
  expr


%start <Core_parser_util.result>start
%parameter <M : sig
                  val sym_counter: int ref
                  val mode: Core_parser_util.mode
                  val std: (Core_parser_util._sym, Symbol.sym) Pmap.map
                end>

%%

start:
| decls= nonempty_list(declaration) EOF
    { mk_file decls }
;


(* BEGIN Ail types *)
integer_base_type:
| ICHAR
    { AilTypes.Ichar }
| SHORT
    { AilTypes.Short }
| INT
    { AilTypes.Int_ }
| LONG
    { AilTypes.Long }
| LONG_LONG
    { AilTypes.LongLong }
;

integer_type:
| CHAR
    { AilTypes.Char }
| BOOL
    { AilTypes.Bool }
| INT8_T
    { AilTypes.Signed (AilTypes.IntN_t 8) }
| INT16_T
    { AilTypes.Signed (AilTypes.IntN_t 16) }
| INT32_T
    { AilTypes.Signed (AilTypes.IntN_t 32) }
| INT64_T
    { AilTypes.Signed (AilTypes.IntN_t 64) }
| UINT8_T
    { AilTypes.Unsigned (AilTypes.IntN_t 8) }
| UINT16_T
    { AilTypes.Unsigned (AilTypes.IntN_t 16) }
| UINT32_T
    { AilTypes.Unsigned (AilTypes.IntN_t 32) }
| UINT64_T
    { AilTypes.Unsigned (AilTypes.IntN_t 64) }
| SIGNED ibty= integer_base_type
    { AilTypes.Signed ibty }
| UNSIGNED ibty= integer_base_type
    { AilTypes.Unsigned ibty }
;

basic_type:
| ity= integer_type
    { AilTypes.Integer ity }
;

ctype:
| VOID
    { Core_ctype.Void0 }
| bty= basic_type
    { Core_ctype.Basic0 bty }
| ty= ctype LBRACKET n_opt= INT_CONST? RBRACKET
    { Core_ctype.Array0 (ty, n_opt) }
| ty= ctype tys= delimited(LPAREN, separated_list(COMMA, ctype), RPAREN)
    { Core_ctype.Function0 (ty, List.map (fun ty -> (AilTypes.no_qualifiers, ty)) tys, false) }
(* TODO *)
(* | ty= ctype LPAREN tys= separated_list(COMMA, ctype) COMMA DOTS RPAREN *)
(*     { Core_ctype.Function0 (ty, tys, true) } *)
| ty= ctype STAR
    { Core_ctype.Pointer0 (AilTypes.no_qualifiers, ty) }
| ATOMIC ty= delimited(LPAREN, ctype, RPAREN)
    { Core_ctype.Atomic0 ty }
| (* TODO: check the lexing *) str= SYM
    { match Builtins.translate_builtin_typenames ("__cerbty_" ^ fst str) with
        | Some ty ->
            Core_aux.proj_ctype ty
        | None ->
            $syntaxerror
    }
;
(* END Ail types *)


core_object_type:
| INTEGER
    { OTy_integer }
| FLOATING
    { OTy_floating }
| POINTER
    { OTy_pointer }
| CFUNCTION
    { OTy_cfunction }
| ARRAY oTy= delimited(LPAREN, core_object_type, RPAREN)
    { OTy_array oTy }
(*
| STRUCT tag= SYM
    { OTy_struct tag }
| UNION tag= SYM
    { OTy_union tag }
*)
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
;

core_type:
| baseTy = core_base_type
    { TyBase baseTy }
| EFF baseTy= core_base_type
    { TyEffect baseTy }
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






memory_order:
| SEQ_CST { Cmm.Seq_cst }
| RELAXED { Cmm.Relaxed }
| RELEASE { Cmm.Release }
| ACQUIRE { Cmm.Acquire }
| CONSUME { Cmm.Consume }
| ACQ_REL { Cmm.Acq_rel }
;



ctor:
| NIL
    { Cnil () }
| CONS
    { Ccons }
| TUPLE
    { Ctuple }
| ARRAY
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


pattern:
| _sym= SYM COLON bTy= core_base_type
    { CaseBase (Some (_sym, bTy)) }
| UNDERSCORE
    { CaseBase None }
| ctor=ctor _pats= delimited(LPAREN, separated_list(COMMA, pattern), RPAREN)
    { CaseCtor (ctor, _pats) }
(* Syntactic sugar for tuples and lists *)
| LPAREN _pat= pattern COMMA _pats= separated_nonempty_list(COMMA, pattern) RPAREN
    { CaseCtor (Ctuple, _pat :: _pats) }
;

pattern_pair(X):
| PIPE _pat= pattern EQ_GT _body= X
    { (_pat, _body) }

(*
typed_expr:
| _e= expr COLON bTy= core_base_type
  { (_e, bTy) }
*)


value:
(* TODO:
  | Vconstrained of list (list Mem.mem_constraint * generic_value 'sym)
  | Vobject of generic_object_value 'sym
  | Vloaded of generic_object_value 'sym
  | Vunspecified of ctype
*)
| n= INT_CONST
    { Vobject (OVinteger (Mem.integer_ival0 n)) }
| CFUNCTION_VALUE _nm= delimited(LPAREN, name, RPAREN)
  { Vobject (OVcfunction _nm) }
| UNIT
    { Vunit }
| TRUE
    { Vtrue }
| FALSE
    { Vfalse }
| ty= delimited(DQUOTE, ctype, DQUOTE)
    { Vctype ty }



pexpr:
| _pe= delimited(LPAREN, pexpr, RPAREN)
    { _pe }
| UNDEF LPAREN ub= UB RPAREN
    { Pexpr ((), PEundef ub) }
| ERROR LPAREN str= STRING COMMA _pe= pexpr RPAREN
    { Pexpr ((), PEerror (str, _pe))  }
| _cval= value
    { Pexpr ((), PEval _cval) }
(*
  | PEconstrained of list (list Mem.mem_constraint * generic_pexpr 'ty 'sym)
*)
| _sym= SYM
    { Pexpr ((), PEsym _sym) }
| iCst= IMPL
    { Pexpr ((), PEimpl iCst) }
(* Syntactic sugar for tuples and lists *)
| LPAREN _pe= pexpr COMMA _pes= separated_nonempty_list(COMMA, pexpr) RPAREN
    { Pexpr ((), PEctor (Ctuple, _pe :: _pes)) }
| _pes= delimited(LBRACKET, separated_list(COMMA, pexpr) , RBRACKET)
    { mk_list_pe _pes }
| ctor= ctor _pes= delimited(LPAREN, separated_list(COMMA, pexpr), RPAREN)
    { Pexpr ((), PEctor (ctor, _pes)) }
| CASE _pe= pexpr OF _pat_pes= list(pattern_pair(pexpr)) END
    { Pexpr ((), PEcase (_pe, _pat_pes)) }
| ARRAY_SHIFT LPAREN _pe1= pexpr COMMA ty= delimited(DQUOTE, ctype, DQUOTE) COMMA _pe2= pexpr RPAREN
    { Pexpr ((), PEarray_shift (_pe1, ty, _pe2)) }
(*
| MEMBER_SHIFT LPAREN _pe1= pexpr COMMA _sym= SYM COMMA RPAREN
*)
| NOT _pe= delimited(LPAREN, pexpr, RPAREN)
    { Pexpr ((), PEnot _pe) }
| MINUS _pe= pexpr
    { Pexpr ((), PEop (OpSub, Pexpr ((), PEval (Vobject (OVinteger (Mem.integer_ival0 (Nat_big_num.of_int 0))))), _pe)) }
| _pe1= pexpr bop= binary_operator _pe2= pexpr
    { Pexpr ((), PEop (bop, _pe1, _pe2)) }
(*
  | PEmemop of Mem.pure_memop * list (generic_pexpr 'ty 'sym)
  | PEstruct of Symbol.t * list (Cabs.cabs_identifier * generic_pexpr 'ty 'sym)
*)
| nm= name _pes= delimited(LPAREN, separated_list(COMMA, pexpr), RPAREN)
    { Pexpr ((), PEcall (nm, _pes)) }
| LET _pat= pattern EQ _pe1= pexpr IN _pe2= pexpr
    { Pexpr ((), PElet (_pat, _pe1, _pe2)) }
| IF _pe1= pexpr THEN _pe2= pexpr ELSE _pe3= pexpr
    { Pexpr ((), PEif (_pe1, _pe2, _pe3)) }
| IS_SCALAR _pe= delimited(LPAREN, pexpr, RPAREN)
    { Pexpr ((), PEis_scalar _pe) }
| IS_INTEGER _pe= delimited(LPAREN, pexpr, RPAREN)
    { Pexpr ((), PEis_integer _pe) }
| IS_SIGNED _pe= delimited(LPAREN, pexpr, RPAREN)
    { Pexpr ((), PEis_signed _pe) }
| IS_UNSIGNED _pe= delimited(LPAREN, pexpr, RPAREN)
    { Pexpr ((), PEis_unsigned _pe) }
;


expr:
| PURE pe_= delimited(LPAREN, pexpr, RPAREN)
    { Epure pe_ }
(*
  | Ememop of Mem.memop * list (generic_pexpr 'ty 'sym)
*)
| SKIP
    { Eskip }
| LET _pat= pattern EQ _pe1= pexpr IN _e2= expr
    { Elet (_pat, _pe1, _e2) }
| IF _pe1= pexpr THEN _e2= expr ELSE _e3= expr
    { Eif (_pe1, _e2, _e3) }
| CASE _pe= pexpr OF _pat_es= list(pattern_pair(expr)) END
    { Ecase (_pe, _pat_es) }
| PCALL LPAREN _pe= pexpr COMMA _pes= separated_list(COMMA, pexpr) RPAREN
    { Core.Eproc ((), _pe, _pes) }
| _pact= paction
    { Eaction _pact }
| UNSEQ _es= delimited(LPAREN, separated_list(COMMA, expr), RPAREN)
    { Eunseq _es }
| LET WEAK _pat= pattern EQ _e1= expr IN _e2= expr
    { Ewseq (_pat, _e1, _e2) }
| LET STRONG _pat= pattern EQ _e1= expr IN _e2= expr
    { Esseq (_pat, _e1, _e2) }
(*
  | Easeq of maybe (Symbol.t * core_base_type) * generic_action 'a 'ty 'sym * generic_paction 'a 'ty 'sym
| Eindet of generic_expr 'a 'ty 'sym
  | Ebound of nat * generic_expr 'a 'ty 'sym
  | Esave of ksym * list (Symbol.t * ctype) * generic_expr 'a 'ty 'sym
  | Erun of 'a * ksym * list (Symbol.t * generic_pexpr 'ty 'sym)
  *)
| RETURN _pe= delimited(LPAREN, pexpr, RPAREN)
    { Ereturn _pe }
| ND _es= delimited(LPAREN, separated_list(COMMA, expr), RPAREN)
    { End _es }
| PAR _es= delimited(LPAREN, separated_list(COMMA, expr), RPAREN)
    { Epar _es }
(*
  | Ewait of Thread.thread_id
*)
;

action:
| CREATE LPAREN _pe1= pexpr COMMA _pe2= pexpr RPAREN
    { Create (_pe1, _pe2, Symbol.PrefOther "Core") }
| ALLOC LPAREN _pe1= pexpr COMMA _pe2= pexpr RPAREN
    { Alloc0 (_pe1, _pe2, Symbol.PrefOther "Core") }
| KILL _pe= delimited(LPAREN, pexpr, RPAREN)
    { Kill _pe }
| STORE LPAREN _pe1= pexpr COMMA _pe2= pexpr COMMA _pe3= pexpr RPAREN
    { Store0 (_pe1, _pe2, _pe3, Cmm.NA) }
| LOAD LPAREN _pe1= pexpr COMMA _pe2= pexpr RPAREN
    { Load0 (_pe1, _pe2, Cmm.NA) }
| STORE LPAREN _pe1= pexpr COMMA _pe2= pexpr COMMA _pe3= pexpr COMMA mo= memory_order RPAREN
    { Store0 (_pe1, _pe2, _pe3, mo) }
| LOAD LPAREN _pe1= pexpr COMMA _pe2= pexpr COMMA mo= memory_order RPAREN
    { Load0 (_pe1, _pe2, mo) }
| RMW LPAREN _pe1= pexpr COMMA _pe2= pexpr COMMA _pe3= pexpr COMMA _pe4= pexpr COMMA mo1= memory_order COMMA mo2= memory_order RPAREN
    { RMW0 (_pe1, _pe2, _pe3, _pe4, mo1, mo2) }
| FENCE LPAREN mo= memory_order RPAREN
    { Fence0 mo }
;

paction:
| act= action
    { Paction (Pos, Action (Location_ocaml.unknown, (), act)) }
| NEG act= delimited(LPAREN, action, RPAREN)
    { Paction (Neg, Action (Location_ocaml.unknown, (), act)) }
;











def_declaration:
| DEF dname= IMPL COLON bTy= core_base_type COLON_EQ pe_= pexpr
    { Def_decl (dname, bTy, pe_) }
;

ifun_declaration:
| FUN fname= IMPL params= delimited(LPAREN, separated_list(COMMA, separated_pair(SYM, COLON, core_base_type)), RPAREN)
  COLON bTy= core_base_type
  COLON_EQ fbody= pexpr
    { IFun_decl (fname, (bTy, params, fbody)) }
;

glob_declaration:
| GLOB gname= SYM COLON cTy= core_type COLON_EQ e= expr
  { Glob_decl (gname, cTy, e) }
;

fun_declaration:
| FUN _sym= SYM params= delimited(LPAREN, separated_list(COMMA, separated_pair(SYM, COLON, core_base_type)), RPAREN)
  COLON bTy= core_base_type
  COLON_EQ fbody= pexpr
    { Fun_decl (_sym, (bTy, params, fbody)) }
;

proc_declaration:
| PROC _sym= SYM params= delimited(LPAREN, separated_list(COMMA, separated_pair(SYM, COLON, core_base_type)), RPAREN)
  COLON EFF bTy= core_base_type
  COLON_EQ fbody= expr
    { Proc_decl (_sym, (bTy, params, fbody)) }
;


declaration:
| decl= def_declaration
| decl= ifun_declaration
| decl= glob_declaration
| decl= fun_declaration
| decl= proc_declaration
    { decl }

%%
