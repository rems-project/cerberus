(************************************************************************************)
(*  BSD 2-Clause License                                                            *)
(*                                                                                  *)
(*  Cerberus                                                                        *)
(*                                                                                  *)
(*  Copyright (c) 2011-2020                                                         *)
(*    Kayvan Memarian                                                               *)
(*    Victor Gomes                                                                  *)
(*    Justus Matthiesen                                                             *)
(*    Peter Sewell                                                                  *)
(*    Kyndylan Nienhuis                                                             *)
(*    Stella Lau                                                                    *)
(*    Jean Pichon-Pharabod                                                          *)
(*    Christopher Pulte                                                             *)
(*    Rodolphe Lepigre                                                              *)
(*    James Lingard                                                                 *)
(*                                                                                  *)
(*  All rights reserved.                                                            *)
(*                                                                                  *)
(*  Redistribution and use in source and binary forms, with or without              *)
(*  modification, are permitted provided that the following conditions are met:     *)
(*                                                                                  *)
(*  1. Redistributions of source code must retain the above copyright notice, this  *)
(*     list of conditions and the following disclaimer.                             *)
(*                                                                                  *)
(*  2. Redistributions in binary form must reproduce the above copyright notice,    *)
(*     this list of conditions and the following disclaimer in the documentation    *)
(*     and/or other materials provided with the distribution.                       *)
(*                                                                                  *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"     *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE       *)
(*  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE  *)
(*  DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE    *)
(*  FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL      *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR      *)
(*  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER      *)
(*  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,   *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE   *)
(*  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.            *)
(************************************************************************************)

open Core_rewriter
open Core


module type S = sig 
  type t 
end

module STATE (S : S) = struct
  type s = S.t
  type 'a m = s -> ('a * s)
  type 'a t = 'a m
  let return a s = (a,s)
  let bind m f s = let (a,s) = m s in f a s
  let (>>=) = bind
  let (>>) m m' = bind m (fun _ -> m')
  let foldlM f xs init =
    List.fold_left (fun acc x ->
      acc >>= fun acc -> f x acc
    ) (return init) xs
  let mapM (type a) (type b)(f : a -> b t) (xs : a list) : (b list) t = 
    foldlM (fun (x : a) (acc : b list) -> 
        f x >>= fun (y : b) -> 
        return (y :: acc)
      ) xs [] >>= fun ys' ->
    return (List.rev ys')
  let get () s = (s,s)
  let put s' s = ((),s')
  let iterate (xs : 'a list) (f : 'a -> unit t): unit t =
    mapM f xs >>= fun _ -> return ()
  let pmap_foldM 
        (f : 'k -> 'x -> 'y -> 'y m)
        (map : ('k,'x) Pmap.map) (init: 'y) : 'y m =
    Pmap.fold (fun k v a -> a >>= f k v) map (return init)
  let pmap_iterM f m = 
    Pmap.fold (fun k v a -> a >> f k v) 
      m (return ())
end


module Sym = struct
  type t = Symbol.sym
  let compare = Symbol.symbol_compare
end


module Def = struct
  type t = 
    | Impl of Implementation.implementation_constant
    | Sym of Symbol.sym 
    | Id of string
  let rec compare a b = 
    match a, b with
    | Impl i1, Impl i2 -> Implementation.implementation_constant_compare i1 i2
    | Sym s1, Sym s2 -> Symbol.symbol_compare s1 s2
    | Id i1, Id i2 -> String.compare i1 i2
    | Impl _, Sym _ -> -1
    | Sym _, Id _ -> -1
    | Impl _, Id _ -> -1
    | Sym _, Impl _ -> 1
    | Id _, Sym _ -> 1
    | Id _, Impl _ -> 1
end

module DefPair = struct 
  type t = Def.t * Def.t
  let compare a b = Lem_basic_classes.pairCompare Def.compare Def.compare a b
end


module Symset = Set.Make(Sym)
module DefSet = Set.Make(Def)
module DefRel = Set.Make(DefPair)

(* module IdSet = Set.Make(String) *)

module State = struct 

  module S = struct 
    type t = { 
        deps: DefRel.t; 
        keep: DefSet.t;
        (* identifiers : IdSet.t *)
      }
    let empty = {
        deps = DefRel.empty;
        keep = DefSet.empty;
      }
  end

  open S
  include STATE(S)

  let record_dep a b : unit t = 
    get () >>= fun s ->
    put { s with deps = DefRel.add (a,b) s.deps }

  let record_keep sym : unit t = 
    get () >>= fun s ->
    put { s with keep = DefSet.add sym s.keep }

end

open State

module RW = Rewriter(State)




type ('a,'bty,'sym) name_collector =
  { names_in_pointer_value : Impl_mem.pointer_value -> unit t; 
    names_in_memory_value : Impl_mem.mem_value -> unit t; 
    names_in_object_value : 'sym generic_object_value -> unit t;
    names_in_loaded_value : 'sym generic_loaded_value -> unit t;
    names_in_ctype : Ctype.ctype -> unit t;
    names_in_core_object_type : core_object_type -> unit t;
    names_in_core_base_type : core_base_type -> unit t;
    names_in_value : 'sym generic_value -> unit t;
    names_in_pattern : 'sym generic_pattern -> unit t;
    names_in_name : 'sym generic_name -> unit t;
    names_in_pexpr : ('bty,'sym) generic_pexpr -> unit t;
    names_in_expr : ('a,'bty,'sym) generic_expr -> unit t}



(* Rewriter doing partial evaluation for Core (pure) expressions *)
(* this collects all the symbols mentioned *)
let deps_of fn_or_impl : ('a,'bty,'sym) name_collector = 

  let record_dep = record_dep fn_or_impl in

  let rec names_in_pointer_value pv : unit m = 
    Impl_mem.case_ptrval pv
      (fun ct -> names_in_ctype ct)
      (fun sym -> record_dep (Sym sym))
      (fun _ _ -> return ())
      (fun _ -> return ())

  and names_in_memory_value mv : unit m = 
    Impl_mem.case_mem_value mv 
      (fun ct -> names_in_ctype ct)
      (fun _ sym -> record_dep (Sym sym))
      (fun _ _ -> return ())
      (fun _ _ -> return ())
      (fun ct pv -> 
        names_in_ctype ct >>
        names_in_pointer_value pv)
      (fun mvs -> iterate mvs names_in_memory_value)
      (fun sym fields -> 
        names_in_struct sym fields)
      (fun sym id mv -> 
        names_in_union sym id mv)

  and names_in_struct (sym : Symbol.sym) fields : unit m =
    record_dep (Sym sym) >>
    iterate fields (fun (Identifier (_,id), ctype, mv) ->
        record_dep (Id id) >>
        names_in_ctype ctype >>
        names_in_memory_value mv
      )

  and names_in_union sym (Identifier (_,id)) mv : unit m = 
    record_dep (Sym sym) >>
    record_dep (Id id) >>
    names_in_memory_value mv

  and names_in_object_value ov : unit m =
    match ov with
    | OVinteger _ -> return ()
    | OVfloating _ -> return ()
    | OVpointer pv -> names_in_pointer_value pv
    | OVarray lvs -> iterate lvs names_in_loaded_value
    | OVstruct (sym,fields) -> names_in_struct sym fields
    | OVunion (sym,id,mv) -> names_in_union sym id mv

  and names_in_loaded_value lv : unit m =
    match lv with
    | LVspecified ov -> names_in_object_value ov
    | LVunspecified ctype -> names_in_ctype ctype

  and names_in_ctype (Ctype (_,ct_)) : unit m = 
    match ct_ with
    | Void -> return ()
    | Basic _ -> return ()
    | Array (ct,_) -> names_in_ctype ct
    | Function (_, (_,ct), args, _) ->
       names_in_ctype ct >>
       iterate args (fun (_,ct,_) -> names_in_ctype ct)
    | Pointer (_, ct) -> names_in_ctype ct
    | Atomic ct -> names_in_ctype ct
    | Struct sym -> record_dep (Sym sym)
    | Union sym -> record_dep (Sym sym)
  in

  let rec names_in_core_object_type = function
    | OTy_integer
    | OTy_floating
    | OTy_pointer -> return ()
    | OTy_array cot -> names_in_core_object_type cot
    | OTy_struct sym -> record_dep (Sym sym)
    | OTy_union sym -> record_dep (Sym sym)
  in

  let rec names_in_core_base_type = function
    | BTy_unit
    | BTy_boolean
    | BTy_ctype
    | BTy_storable -> return ()
    | BTy_list cbt -> names_in_core_base_type cbt
    | BTy_object cot -> names_in_core_object_type cot
    | BTy_loaded cot -> names_in_core_object_type cot
    | BTy_tuple cbts -> iterate cbts names_in_core_base_type
  in

  let rec names_in_value = function
    | Vobject ov -> names_in_object_value ov
    | Vloaded lv -> names_in_loaded_value lv
    | Vunit
    | Vtrue
    | Vfalse -> return ()
    | Vctype ct -> names_in_ctype ct
    | Vlist (cbt, vs) -> iterate vs names_in_value
    | Vtuple vs -> iterate vs names_in_value
  in

  let rec names_in_pattern (Pattern (_, pat_)) = 
    match pat_ with
    | CaseBase (None, cbt) -> 
       names_in_core_base_type cbt
    | CaseBase (Some sym, cbt) -> 
       record_dep (Sym sym) >>
       names_in_core_base_type cbt
    | CaseCtor (_, pats) ->
       iterate pats names_in_pattern
  in

  let names_in_name = function
    | Sym sym -> record_dep (Sym sym)
    | Impl impl -> record_dep (Impl impl)
  in

  let collect_names_rw = 
    let open RW in {
      rw_pexpr =
        RW.RW begin fun pexpr ->
          let (Pexpr (annots, bTy, pexpr_)) = pexpr in
          match pexpr_ with
          | PEsym sym -> 
             PostTraverseAction (fun () -> record_dep (Sym sym))
          | PEimpl impl -> 
             PostTraverseAction (fun () -> record_dep (Impl impl))
          | PEval v -> 
             let a () = names_in_value v in
             PostTraverseAction a
          | PEcase (_, patpes) ->
             let a () = iterate patpes (fun (pat,_) -> names_in_pattern pat) in
             PostTraverseAction a
          | PEarray_shift (_,ct,_) ->
             let a () = names_in_ctype ct in
             PostTraverseAction a
          | PEstruct (sym,fields) ->
             let a () = 
               record_dep (Sym sym) >>
               iterate fields (fun (Identifier (_,id),_) -> 
                   record_dep (Id id))
             in
             PostTraverseAction a
          | PEmember_shift (_,sym,Identifier (_,id))
          | PEunion (sym,Identifier (_,id),_)
          | PEmemberof (sym,Identifier (_,id),_) ->
             let a () = record_dep (Sym sym) >> record_dep (Id id) in
             PostTraverseAction a
          | PEcall (name,_) ->
             let a () = names_in_name name in
             PostTraverseAction a
          | PElet (pat,_,_) ->
             let a () = names_in_pattern pat in
             PostTraverseAction a
          | _ ->
             Traverse           
          end;

      rw_action =
        RW.RW begin fun act ->
          Traverse
          end;

      rw_expr=
        RW.RW begin fun (Expr (annots, expr_) (*as expr*)) ->
          match expr_ with
          | Eproc (_,name,_) ->
             let a () = names_in_name name in
             PostTraverseAction a
          | Ewseq (pat,_,_)
          | Esseq (pat,_,_) ->
             let a () = names_in_pattern pat in
             PostTraverseAction a
          | Easeq ((sym,cbt),_,_) ->
             let a () = record_dep (Sym sym) >> names_in_core_base_type cbt in
             PostTraverseAction a
          | Esave ((sym,cbt),ls,_) ->
             let a () = 
               record_dep (Sym sym) >> 
               names_in_core_base_type cbt >>
               iterate ls (fun (sym,_) -> record_dep (Sym sym))
             in
             PostTraverseAction a
          | Erun (_,sym,_) ->
             let a () = record_dep (Sym sym) in
             PostTraverseAction a
          | _ ->
                Traverse
        end
    }
  in

  (* These do one step of partial evaluation on an expression *)
  let names_in_expr expr =
    RW.(rewriteExpr collect_names_rw expr) >> return () in
  let names_in_pexpr expr =
    RW.(rewritePexpr collect_names_rw expr) >> return () in

  { names_in_pointer_value; 
    names_in_memory_value;
    names_in_object_value;
    names_in_loaded_value;
    names_in_ctype;
    names_in_core_object_type;
    names_in_core_base_type;
    names_in_value;
    names_in_pattern;
    names_in_name;
    names_in_pexpr;
    names_in_expr }



(* the above part is more general than we need for the part below: it
   collects all the symbols, whereas here, so far, we're only
   collecting some for discarding some unused functions *)

let do_impls is = 
  pmap_iterM (fun i decl ->
      (* record_keep (Impl i) >> *)
      let name_collector = deps_of (Impl i) in
      match decl with
      | Def (cbt, pe) -> 
         name_collector.names_in_core_base_type cbt >>
           name_collector.names_in_pexpr pe
      | IFun (cbt, args, pe) -> 
         name_collector.names_in_core_base_type cbt >>
           iterate args (fun (sym,cbt) ->
               record_dep (Impl i) (Sym sym) >>
                 name_collector.names_in_core_base_type cbt
             ) >>
           name_collector.names_in_pexpr pe) is >>
    return () 

let do_fun_map definitely_keep (fmap : ('bty,'a) generic_fun_map) =
  pmap_iterM (fun fn decl ->
    (if definitely_keep then record_keep (Sym fn) else return ()) >>
    let name_collector = deps_of (Sym fn) in
    begin match decl with
    | Fun (cbt, args, pe) -> 
       name_collector.names_in_core_base_type cbt >>
       iterate args (fun (sym,cbt) ->
           record_dep (Sym fn) (Sym sym) >>
           name_collector.names_in_core_base_type cbt
         ) >>
       name_collector.names_in_pexpr pe
    | Proc (_loc, cbt, args, e) -> 
       name_collector.names_in_core_base_type cbt >>
       iterate args (fun (sym,cbt) ->
           record_dep (Sym fn) (Sym sym) >>
           name_collector.names_in_core_base_type cbt
         ) >>
       name_collector.names_in_expr e
    | ProcDecl (_loc, cbt, bts)
    | BuiltinDecl (_loc, cbt, bts) -> 
       name_collector.names_in_core_base_type cbt >>
       iterate bts name_collector.names_in_core_base_type
    end) fmap >>
    return ()


let do_globs_list (gs : (Symbol.sym *  ('a, 'bty) generic_globs) list) =
  mapM (fun (glob, g) ->
      record_keep (Sym glob) >>
      let name_collector = deps_of (Sym glob) in
      match g with
      | GlobalDef (cbt, e) -> 
         name_collector.names_in_core_base_type cbt >>
           name_collector.names_in_expr e
      | GlobalDecl cbt -> 
         name_collector.names_in_core_base_type cbt
    ) gs


let do_tagDefs tagDefs =
  pmap_iterM (fun sym tagDef ->
    record_keep (Sym sym) >>
    let name_collector = deps_of (Sym sym) in
    match tagDef with
    | Ctype.StructDef (fields, flexible_opt) ->
       iterate fields (fun (Identifier (_,id), (_,_,ct)) -> 
           record_dep (Sym sym) (Id id) >>
           name_collector.names_in_ctype ct) >>
       begin match flexible_opt with
         | None ->
             return ()
         | Some (FlexibleArrayMember (_, _, _, elem_ty)) ->
             name_collector.names_in_ctype (Ctype ([], Array (elem_ty, None)))
       end
    | Ctype.UnionDef d ->
       iterate d (fun (Identifier (_,id), (_,_,ct)) -> 
           record_dep (Sym sym) (Id id) >>
           name_collector.names_in_ctype ct)
    ) tagDefs

let do_extern_map em = 
  pmap_iterM (fun (Symbol.Identifier (_,id)) (ls,_) ->
    record_keep (Id id) >>
      iterate ls (fun s -> record_dep (Id id) (Sym s))
    ) em >>
  return ()

let do_main = function
  | None -> return ()
  | Some main -> record_keep (Sym main)

let deps_file file = 
  do_main file.main >>
  do_tagDefs file.tagDefs >>
  do_fun_map false file.stdlib >>= fun stdlib_names ->
  do_impls file.impl >>
  do_globs_list file.globs >>
  do_fun_map true file.funs >>= fun fun_names ->
  do_extern_map file.extern >>
  return ()



(* the above part is more general than needed here *)


let remove_unused_functions file = 


  let ((),s) = deps_file file State.S.empty in

  (* transitively close deps first? *)

  let nothing_depends deps d = 
    not ((DefRel.exists (fun (a,b) -> b = d)) deps) in

  let can_remove deps d = not (DefSet.mem d s.keep) && nothing_depends deps d in

  let rec only_used maybe_remove deps = 
    match List.filter (can_remove deps) maybe_remove with
    | [] -> 
       (maybe_remove,deps)
    | x :: xs ->
       let deps' = DefRel.filter (fun (sym1,sym2) -> sym1 <> x) deps in
       let maybe_remove' = List.filter ((<>) x) maybe_remove in
       only_used maybe_remove' deps'
  in

  let used_stdlib : ('bty, 'a) generic_fun_map = 
    let stdlib_names = Pmap.fold (fun sym _ acc -> Def.Sym sym :: acc) file.stdlib [] in  
    let (used_stdlib,_) = only_used stdlib_names s.deps in
    Pmap.filter (fun name _ -> List.mem (Def.Sym name) used_stdlib) file.stdlib 
  in

  let used_impls = 
    let stdlib_names = Pmap.fold (fun sym _ acc -> Def.Impl sym :: acc) file.impl [] in  
    let (used_stdlib,_) = only_used stdlib_names s.deps in
    Pmap.filter (fun name _ -> List.mem (Def.Impl name) used_stdlib) file.impl
  in

  { file with stdlib = used_stdlib;
              impl = used_impls}


