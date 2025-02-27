Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.FSets.FSetInterface.

From Cn Require Import Prooflog Request Resource Context.


(* Helper functoin to get set of resources from contex *)

Definition ctx_resources_set (l:((list (Resource.t * Z)) * Z)) : Resource.ResSet.t
  :=
  Resource.set_from_list (List.map fst (fst l)).

(** Inductive predicate which defines correctess of log inference step *)
Inductive log_entry_valid : log_entry -> Prop :=

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
      ResSet.eq (Resource.ResSet.remove (P upred, out) in_res) out_res /\
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


