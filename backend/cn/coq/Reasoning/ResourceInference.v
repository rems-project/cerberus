Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.FSets.FSetInterface.

From Cn Require Import Prooflog Request Resource Context Sym.

Import ListNotations.

(* Helper functoin to get set of resources from contex *)

Definition ctx_resources_set (l:((list (Resource.t * Z)) * Z)) : ResSet.t
  :=
  Resource.set_from_list (List.map fst (fst l)).

(* Helper function to convert struct piece to resource *)
Definition struct_piece_to_resource (piece:Memory.struct_piece) (iinit:init) (ipointer:IndexTerms.t) (iargs:list IndexTerms.t) (iout:output) : option Resource.t :=
  match Memory.piece_member_or_padding piece with
  | Some (pid,pty) => Some (Request.P {| Predicate.name := Request.Owned pty iinit; 
                                        Predicate.pointer := ipointer; 
                                        Predicate.iargs := iargs |}, iout)
  | None => None
  end.

(* resource = (P {name,pointer,iargs}) * output *)  
Inductive resource_unfold (globals:Global.t): Resource.t -> ResSet.t -> Prop :=
(* non-struct resources unfold to themselves *)
| resource_unfold_nonstruct:
    forall ipointer iargs iout iinit ity,
    not (SCtypes.is_struct ity) ->

    resource_unfold globals
      (Request.P 
        {| 
          Predicate.name := Request.Owned ity iinit; 
          Predicate.pointer := ipointer; 
          Predicate.iargs := iargs 
        |}, 
        iout) 
      (* TODO: maybe need recursive unfolding *)
      (ResSet.singleton 
        (Request.P 
        {| 
          Predicate.name := Request.Owned ity iinit; 
          Predicate.pointer := ipointer; 
          Predicate.iargs := iargs 
        |}, 
        iout)         
      ) 

| resource_unfold_struct:
  forall out_res ipointer iargs iout iinit isym sdecl,

  (* lookup struct declaration in global environment *)
  SymMap.MapsTo isym sdecl globals.(Global.struct_decls) ->

  (* convert struct list members to set resources *)
  let member_resources := 
    List.fold_right (fun piece acc =>
      match struct_piece_to_resource piece iinit ipointer iargs iout with
      | Some r => ResSet.add r acc
      | None => acc
      end) ResSet.empty sdecl 
  in
  
  (* bijection between struct members and out_res: *)

  ResSet.Equal member_resources out_res /\
  (forall r, ResSet.In r out_res ->
    exists piece, List.In piece sdecl /\
      match struct_piece_to_resource piece iinit ipointer iargs iout with
      | Some r' => r = r'
      | None => False
      end) ->
  
  resource_unfold globals
    (Request.P 
      {| 
        Predicate.name := Request.Owned (SCtypes.Struct isym) iinit; 
        Predicate.pointer := ipointer; 
        Predicate.iargs := iargs 
      |}, 
      iout) 
    out_res.
  
(** Inductive predicate which defines correctness of resource unfolding step *)
Inductive unfold_step : Context.t -> Context.t -> Prop :=
| simple_unfold_step:
    forall 
    icomputational ilogical iresources iconstraints iglobal
    ocomputational ological oresources oconstraints oglobal,
    
  (* The following parts of context are not changed *)
    icomputational = ocomputational ->
    iglobal = oglobal ->
    ilogical = ological ->
    iconstraints = oconstraints ->

    let in_res := ctx_resources_set iresources in
    let out_res := ctx_resources_set oresources in

    (* The `out_res` is union of `resource_unfold` of all resources in `in_res` *)
    (forall r', ResSet.In r' out_res <-> 
      exists r, ResSet.In r in_res /\ exists s, 
      resource_unfold iglobal r s /\ ResSet.In r' s
    ) 
    
    ->

    unfold_step
    (* input context *)
    {|
      Context.computational := icomputational;
      Context.logical := ilogical;
      Context.resources := iresources;
      Context.constraints := iconstraints;
      Context.global := iglobal
    |}

    (* output context *)
    {|
      Context.computational := ocomputational;
      Context.logical := ological;
      Context.resources := oresources;
      Context.constraints := oconstraints;
      Context.global := oglobal
    |}.
  

(** Inductive predicate which defines correctess of log inference step *)
Inductive log_entry_valid : log_entry -> Prop :=
| unfold_resources_step:
    forall loc c c',
    unfold_step c c' ->
    log_entry_valid (ResourceInferenceStep c (UnfoldResources loc) c')

(* simple case: non-recursive request, no packing *)
| simple_resource_inference_step:
  forall iname  ipointer  iargs
    oname  opointer  oargs
    err out lines oloc
    icomputational ilogical iresources iconstraints iglobal
    ocomputational ological oresources oconstraints oglobal,

  (* The following parts of context are not changed *)
  icomputational = ocomputational ->
  iglobal = oglobal ->
  ilogical = ological ->
  iconstraints = oconstraints ->

  let in_res := ctx_resources_set iresources in
  let out_res := ctx_resources_set oresources in

  (* alt. definition sketch:
  let res_diff := Resource.ResSet.diff in_res out_res in
  Resource.ResSet.cardinal res_diff = 1 /\
  ...
   *)

  (* [out_res] is a subset of [in_res] with exactly one element [used] removed. *)
  (exists (upred: Request.Predicate.t),
      ResSet.Equal (Resource.ResSet.add (P upred, out) out_res) in_res /\
      Request.subsumed iname upred.(Request.Predicate.name)
  )
  ->

    log_entry_valid
      (ResourceInferenceStep
         (* input context *)
         {|
           Context.computational := icomputational;
           Context.logical := ilogical;
           Context.resources := iresources;
           Context.constraints := iconstraints;
           Context.global := iglobal
         |}

         (* request type *)
         (PredicateRequest
            err (* unused *)
            (* input predicate *)
            {| Predicate.name:=iname; Predicate.pointer:=ipointer; Predicate.iargs:=iargs |}
            oloc (* unused *)
            ((
                (* output predicate *)
                {| Predicate.name:=oname; Predicate.pointer:=opointer; Predicate.iargs:=oargs |},
                  out
              ), lines (* unused *)
         ))

         (* output context *)
         {|
           Context.computational := ocomputational;
           Context.logical := ological;
           Context.resources := oresources;
           Context.constraints := oconstraints;
           Context.global := oglobal
         |}
      ).

(** Proof log is valid if all entries are valid *)
Definition prooflog_valid (l:Prooflog.log) := List.Forall log_entry_valid l.


