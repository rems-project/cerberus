open Core_rewriter
open Core



let debug_print pp =
  Cerb_debug.print_debug 3
    [Cerb_debug.DB_core_rewriting] 
    pp



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

  let equal a b = 
    match a, b with
    | Impl i1, Impl i2 -> Implementation.implementation_constant_equal i1 i2
    | Sym s1, Sym s2 -> Symbol.symbolEquality s1 s2
    | Id i1, Id i2 -> String.equal i1 i2
    | Impl _, _
    | Sym _, _
    | Id _, _
      ->
       false

  let compare a b = 
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

  let pp = function
    | Impl i -> 
       "Impl " ^ Implementation.string_of_implementation_constant i
    | Sym s -> 
       "Sym " ^ Pp_symbol.to_string s
    | Id s -> 
       "S " ^ s

end

module DefPair = struct 
  type t = Def.t * Def.t
  let compare a b = Lem_basic_classes.pairCompare Def.compare Def.compare a b
end


module DefSet = struct
  include Pset
  type t = Def.t Pset.set
  let empty = Pset.empty Def.compare
end 

module DefRel = struct
  include Pset
  type t = DefPair.t Pset.set
  let empty = Pset.empty DefPair.compare
  let transitiveClosure = Pset.tc DefPair.compare
end 

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
    names_in_object_value : object_value -> unit t;
    names_in_loaded_value : loaded_value -> unit t;
    names_in_ctype : Ctype.ctype -> unit t;
    names_in_core_object_type : core_object_type -> unit t;
    names_in_core_base_type : core_base_type -> unit t;
    names_in_value : value -> unit t;
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
      (function Some sym -> record_dep (Sym sym) | None -> return ())
      (fun _ _ -> return ())

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
    | Function ((_,ct), args, _) ->
       names_in_ctype ct >>
       iterate args (fun (_,ct,_) -> names_in_ctype ct)
    | FunctionNoParams qs_ty ->
        failwith "TODO: names_in_ctype ==> FunctionNoParams"
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
    (* | Sym (Symbol.Symbol (_, _, Some name)) when
     *        List.mem name Not_unfold.not_unfold ->
     *    return () *)
    | Sym sym -> 
       record_dep (Sym sym)
    | Impl impl -> record_dep (Impl impl)
  in

  let collect_names_rw = 
    let open RW in {
      rw_pexpr =
        RW.RW begin fun _ pexpr ->
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
        RW.RW begin fun _ act ->
          Traverse
          end;

      rw_expr=
        RW.RW begin fun _ (Expr (annots, expr_) (*as expr*)) ->
          match expr_ with
          | Eproc (_,name,_) ->
             let a () = names_in_name name in
             PostTraverseAction a
          | Ewseq (pat,_,_)
          | Esseq (pat,_,_) ->
             let a () = names_in_pattern pat in
             PostTraverseAction a
          | Esave ((sym,cbt),ls,_) ->
             let a () = 
               record_dep (Sym sym) >> 
               names_in_core_base_type cbt >>
               iterate ls (fun (sym,((cbt,_),_)) -> 
                         names_in_core_base_type cbt >>
                         record_dep (Sym sym)
                       )
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
    (if definitely_keep 
     then record_keep (Sym fn) 
     else return ()) >>
    let name_collector = deps_of (Sym fn) in
    begin match decl with
    | Fun (cbt, args, pe) ->
       name_collector.names_in_core_base_type cbt >>
       iterate args (fun (sym,cbt) ->
           record_dep (Sym fn) (Sym sym) >>
           name_collector.names_in_core_base_type cbt
         ) >>
       name_collector.names_in_pexpr pe
    | Proc (_loc, _mrk, cbt, args, e) -> 
       name_collector.names_in_core_base_type cbt >>
       iterate args (fun (sym,cbt) ->
           record_dep (Sym fn) (Sym sym) >>
           name_collector.names_in_core_base_type cbt
         ) >>
       name_collector.names_in_expr e
    | ProcDecl (_loc, cbt, bts)
    | BuiltinDecl (_loc, cbt, bts) -> 
       (* record_keep (Sym fn) >>  *)
       name_collector.names_in_core_base_type cbt >>
       iterate bts name_collector.names_in_core_base_type
    end) fmap >>
    return ()


let do_globs_list (gs : (Symbol.sym *  ('a, 'bty) generic_globs) list) =
  mapM (fun (glob, g) ->
      record_keep (Sym glob) >>
      let name_collector = deps_of (Sym glob) in
      match g with
      | GlobalDef ((cbt,ct), e) -> 
         name_collector.names_in_core_base_type cbt >>
           name_collector.names_in_ctype ct >>
           name_collector.names_in_expr e
      | GlobalDecl (cbt, ct) -> 
         name_collector.names_in_core_base_type cbt >>
           name_collector.names_in_ctype ct
    ) gs


let do_tagDefs tagDefs =
  pmap_iterM (fun sym (loc, tagDef) ->
    record_keep (Sym sym) >>
    let name_collector = deps_of (Sym sym) in
    match tagDef with
    | Ctype.StructDef (fields, flexible_opt) ->
       iterate fields (fun (Identifier (_,id), (_,_,_,ct)) -> 
           record_dep (Sym sym) (Id id) >>
           name_collector.names_in_ctype ct) >>
       begin match flexible_opt with
         | None ->
             return ()
         | Some (FlexibleArrayMember (_, _, _, elem_ty)) ->
             name_collector.names_in_ctype (Ctype ([], Array (elem_ty, None)))
       end
    | Ctype.UnionDef d ->
       iterate d (fun (Identifier (_,id), (_,_,_,ct)) -> 
           record_dep (Sym sym) (Id id) >>
           name_collector.names_in_ctype ct)
    ) tagDefs

let do_extern_map em = 
  pmap_iterM (fun (Symbol.Identifier (_,id)) (ls,_) ->
      iterate ls (fun s -> record_dep (Id id) (Sym s))
    ) em >>
  return ()

let do_main = function
  | None -> return ()
  | Some main -> record_keep (Sym main)


let do_funinfo funinfo = 
  pmap_iterM (fun sym _ -> record_keep (Sym sym)) funinfo >>
  return ()

let deps_file file = 
  do_main file.main >>
  do_funinfo file.funinfo >>
  do_tagDefs file.tagDefs >>
  do_fun_map false file.stdlib >>
  do_impls file.impl >>
  do_globs_list file.globs >>
  do_fun_map false file.funs >>
  do_extern_map file.extern >>
  return ()



(* the above part is more general than needed here *)


let remove_unused_functions remove_funinfo_entries file = 


  let ((),s) = deps_file file State.S.empty in


  (* let _ = 
   *   debug_print (fun () ->
   *       "keep: " ^
   *       DefSet.fold (fun i pp ->
   *           pp ^ Def.pp i ^ ", "
   *         ) s.keep "" ^ "\n"
   *     )
   * in
   * 
   * let _ = 
   *   debug_print (fun () ->
   *       "deps: " ^
   *       DefRel.fold (fun (i1,i2) pp ->
   *           pp ^ Def.pp i1 ^ " -> " ^ Def.pp i2 ^ ", "
   *         ) s.deps "" ^ "\n"
   *     )
   * in *)

  let keep = 
    DefRel.fold (fun (l,r) keep ->
        if DefSet.mem l s.keep then DefSet.add r keep else keep
      ) (DefRel.transitiveClosure s.deps) s.keep
  in


  (* let _ = 
   *   debug_print (fun () ->
   *       "final keep: " ^
   *       DefSet.fold (fun i pp ->
   *           pp ^ Def.pp i ^ ", "
   *         ) keep "" ^ "\n"
   *     )
   * in *)


  let used_stdlib : ('bty, 'a) generic_fun_map = 
    Pmap.filter (fun name _ -> 
          Pset.mem (Def.Sym name) keep ||
            match Symbol.symbol_description name with
            | SD_Id sname ->
               Pset.mem (Def.Impl (BuiltinFunction sname)) keep
            | _ -> false
      ) file.stdlib 
  in

  let used_impls = 
    Pmap.filter (fun name _ -> 
        DefSet.mem (Def.Impl name) keep
      ) file.impl
  in

  let used_extern = 
    Pmap.filter (fun (Symbol.Identifier (_,name)) _ -> 
        DefSet.mem (Def.Id name) keep) file.extern
  in

  (* let used_funinfo = 
   *   if false then
   *     Pmap.filter (fun name _ -> 
   *         Pset.mem (Def.Sym name) keep ||
   *           match Symbol.symbol_name name with
   *           | Some sname ->
   *              Pset.mem (Def.Impl (BuiltinFunction sname)) keep
   *           | _ -> false
   *       ) file.funinfo
   *   else 
   *     file.funinfo 
   * in *)

  { file with 
    stdlib = used_stdlib;
    impl = used_impls;
    extern = used_extern;
  }


