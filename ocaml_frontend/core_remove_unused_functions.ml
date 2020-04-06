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

module SymPair = struct
  type t = Symbol.sym * Symbol.sym
  let compare (s1,s2) (s1',s2') = 
    match Symbol.symbol_compare s1 s1' with
    | 0 -> Symbol.symbol_compare s2 s2'
    | c -> c
end

module Symset = Set.Make(Sym)
module Symrel = Set.Make(SymPair)

(* module IdSet = Set.Make(String) *)

module State = struct 

  module S = struct 
    type t = { 
        deps: Symrel.t; 
        keep: Symset.t;
        (* identifiers : IdSet.t *)
      }
    let empty = {
        deps = Symrel.empty;
        keep = Symset.empty;
      }
  end

  open S
  include STATE(S)

  let record_dep sym sym' : unit t = 
    get () >>= fun s ->
    put { s with deps = Symrel.add (sym, sym') s.deps }

  let record_keep sym : unit t = 
    get () >>= fun s ->
    put { s with keep = Symset.add sym s.keep }

  let record_sym mfn sym = 
    match mfn with
    | Some fn -> record_dep fn sym 
    | None -> record_keep sym

  (* let record_id (Symbol.Identifier (_,id)) = 
   *   get () >>= fun s ->
   *   put {s with identifiers = IdSet.add id s.identifiers} *)
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
    names_in_pattern : ('bty,'sym) generic_pattern -> unit t;
    names_in_name : 'sym generic_name -> unit t;
    names_in_pexpr : ('bty,'sym) generic_pexpr -> unit t;
    names_in_expr : ('a,'bty,'sym) generic_expr -> unit t}



(* Rewriter doing partial evaluation for Core (pure) expressions *)
(* this collects all the symbols mentioned *)
let name_collector mfn : ('a,'bty,'sym) name_collector = 

  let record_sym = record_sym mfn in

  (* let record_id id = record_sym (fn,id) *)


  let rec names_in_pointer_value pv : unit m = 
    Impl_mem.case_ptrval pv
      (fun ct -> names_in_ctype ct)
      (fun sym -> record_sym sym)
      (fun _ _ -> return ())
      (fun _ -> return ())

  and names_in_memory_value mv : unit m = 
    Impl_mem.case_mem_value mv 
      (fun ct -> names_in_ctype ct)
      (fun _ sym -> record_sym sym)
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
    record_sym sym >>
    iterate fields (fun (id, ctype, mv) ->
        (* record_id id >> *)
        names_in_ctype ctype >>
        names_in_memory_value mv
      )

  and names_in_union sym id mv : unit m = 
    record_sym sym >>
    (* record_id id >> *)
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
    | Struct sym -> record_sym sym
    | Union sym -> record_sym sym
  in

  let rec names_in_core_object_type = function
    | OTy_integer
    | OTy_floating
    | OTy_pointer -> return ()
    | OTy_array cot -> names_in_core_object_type cot
    | OTy_struct sym -> record_sym sym
    | OTy_union sym -> record_sym sym
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
       record_sym sym >>
       names_in_core_base_type cbt
    | CaseCtor (_, pats) ->
       iterate pats names_in_pattern
  in

  let names_in_name = function
    | Sym sym -> record_sym sym
    | Impl _impl -> return ()
  in

  let collect_names_rw = 
    let open RW in {
      rw_pexpr =
        RW.RW begin fun pexpr ->
          let (Pexpr (annots, bTy, pexpr_)) = pexpr in
          match pexpr_ with
          | PEsym sym -> PostTraverseAction (fun () -> record_sym sym)
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
               record_sym sym(*  >>
                * iterate fields (fun (id,_) -> record_id id) *)
             in
             PostTraverseAction a
          |  PEmember_shift (_,sym,id)
          | PEunion (sym,id,_)
          | PEmemberof (sym,id,_) ->
             let a () = 
               record_sym sym (* >> 
                * record_id id  *)
             in
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
             let a () = record_sym sym >> names_in_core_base_type cbt in
             PostTraverseAction a
          | Esave ((sym,cbt),ls,_) ->
             let a () = 
               record_sym sym >> 
               names_in_core_base_type cbt >>
               iterate ls (fun (sym,_) -> record_sym sym)
             in
             PostTraverseAction a
          | Erun (_,sym,_) ->
             let a () = record_sym sym in
             PostTraverseAction a
          | _ ->
                Traverse
        end
    }
  in

  (* This does one step of partial evaluation on an expression *)
  let names_in_expr expr =
    RW.(rewriteExpr collect_names_rw expr) >>
    return ()
  in
  (* This does one step of partial evaluation on an expression *)
  let names_in_pexpr expr =
    RW.(rewritePexpr collect_names_rw expr) >>
    return ()
  in

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

let called_names_file file = 

  let called_names_impl (is : 'bty generic_impl) = 
    let called_names_impl_decl decl = 
      let name_collector = name_collector None in
      match decl with
      | Def (cbt, pe) -> 
         name_collector.names_in_core_base_type cbt >>
         name_collector.names_in_pexpr pe
      | IFun (cbt, args, pe) -> 
         name_collector.names_in_core_base_type cbt >>
         iterate args (fun (sym,cbt) ->
             record_sym None sym >>
             name_collector.names_in_core_base_type cbt
           ) >>
         name_collector.names_in_pexpr pe
    in
    pmap_iterM (fun _ v -> called_names_impl_decl v) is >>
    return ()
  in


  let called_names_fun_map (fmap : ('bty,'a) generic_fun_map) =
    let called_names_fun_map_decl fn decl acc =
      let name_collector = name_collector (Some fn) in
      begin match decl with
      | Fun (cbt, args, pe) -> 
         name_collector.names_in_core_base_type cbt >>
         iterate args (fun (sym,cbt) ->
             record_sym None sym >>
             name_collector.names_in_core_base_type cbt
           ) >>
         name_collector.names_in_pexpr pe
      | Proc (_loc, cbt, args, e) -> 
         name_collector.names_in_core_base_type cbt >>
         iterate args (fun (sym,cbt) ->
             record_sym None sym >>
             name_collector.names_in_core_base_type cbt
           ) >>
         name_collector.names_in_expr e
      | ProcDecl (_loc, cbt, bts)
      | BuiltinDecl (_loc, cbt, bts) -> 
         name_collector.names_in_core_base_type cbt >>
         iterate bts name_collector.names_in_core_base_type
      end >>
      return (fn :: acc)
    in
    pmap_foldM called_names_fun_map_decl fmap []
  in


  let called_names_globs_list (gs : (Symbol.sym *  ('a, 'bty) generic_globs) list ) =
    let called_names_globs glob (g : ('a, 'bty) generic_globs) = 
      let name_collector = name_collector (Some glob) in
      match g with
      | GlobalDef (cbt, e) -> 
         name_collector.names_in_core_base_type cbt >>
         name_collector.names_in_expr e
      | GlobalDecl cbt -> 
         name_collector.names_in_core_base_type cbt
    in
    mapM (fun (sym,g) -> (called_names_globs sym g)) gs >>
    return ()
  in

  let called_names_tagDefs tagDefs =
    let called_names_tagDef sym tagDef = 
      let name_collector = name_collector (Some sym) in
      match tagDef with
      | Ctype.StructDef fields ->
         iterate fields (fun (_id, (_,_,ct)) -> 
             name_collector.names_in_ctype ct)
      | Ctype.UnionDef d ->
         iterate d (fun (_id, (_,_,ct)) -> 
             name_collector.names_in_ctype ct)
    in
    pmap_iterM called_names_tagDef tagDefs >>
    return ()
  in

  let called_names_extern_map em = 
    let called_names_extern _extern (ls,_) = 
      iterate ls (record_sym None)
    in
    pmap_iterM called_names_extern em
  in
  (* let called_names_extern_map  *)

  begin match file.main with
  | None -> return ()
  | Some sym -> record_sym None sym
  end >>

  called_names_tagDefs file.tagDefs >>
  called_names_fun_map file.stdlib >>= fun stdlib_names ->
  called_names_impl file.impl >>
  called_names_globs_list file.globs >>
  called_names_fun_map file.funs >>= fun fun_names ->
  called_names_extern_map file.extern >>

  return (fun_names,stdlib_names)



(* the above part is more general than needed here *)


let remove_unused_functions file = 

  let ((fun_names,stdlib_names),s) = called_names_file file State.S.empty in

  (* transitively close deps first? *)

  let nothing_depends (sym : Symbol.sym) (deps : Symrel.t) = 
    not ((Symrel.exists (fun (sym1,sym2) -> sym2 = sym)) deps) in

  let rec only_used maybe_remove deps = 
    match List.filter (fun sym -> nothing_depends sym deps) maybe_remove with
    | [] -> 
       (maybe_remove,deps)
    | x :: xs ->
       let deps' = Symrel.filter (fun (sym1,sym2) -> sym1 <> x) deps in
       let maybe_remove' = List.filter ((<>) x) maybe_remove in
       only_used maybe_remove' deps'
  in

  let (used_stdlib,_) = 
    only_used 
      (List.filter (fun sym -> Symset.mem sym s.keep) stdlib_names)
      s.deps 
  in

  let remove_unused stdlib 
      : ('bty, 'a) generic_fun_map = 
    Pmap.filter (fun name _ -> List.mem name used_stdlib) stdlib
  in

  { file with stdlib = remove_unused file.stdlib }


