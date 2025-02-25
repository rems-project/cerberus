Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.MSets.MSetInterface.

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
      Resource.ResSet.remove (P upred, out) in_res = out_res /\
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

(* Automation to prove single entry *)
Ltac prove_log_entry_valid :=
  match goal with
  | [ |- log_entry_valid (ResourceInferenceStep _ _ _) ] =>
      (* TODO: define automation to prove validity *)
      constructor; try auto
  end.

Ltac prove_log_entry_list_valid :=
  match goal with
  | [ |- List.Forall log_entry_valid ?l ] =>
      let rec aux l :=
        match l with
        | nil => constructor
        | ?hd :: ?tl =>
            constructor; [ prove_log_entry_valid | aux tl ]
        end
      in aux l
  end.

(* Sample usage for the proof log extracted from CN:
Theorem resource_inference_steps_valid: prooflog_valid _cn_ResourceInferenceSteps.
Proof.
  unfold prooflog_valid.
  unfold _cn_ResourceInferenceSteps.
  prove_log_entry_list_valid.
Qed.
 *)

 (* Experimental Ltac2 automation below *)
From Ltac2 Require Import Ltac2 Notations Std Constr.

Ltac2 rec list_subtract
  (eq : 'a -> 'a -> bool)
  (l1 : 'a list)
  (l2 : 'a list) : 'a list :=
  match l1 with
  | [] => []
  | h :: t =>
      if Ltac2.List.exist (fun x => eq h x) l2 then
        list_subtract eq t l2
      else
        h :: list_subtract eq t l2
  end.

(* Specialisation of [list_subtract] for [constr] that uses strict
       syntactic equality: only up to α-conversion and evar
       expansion *)
Ltac2 const_list_subtract (l1 : constr list) (l2 : constr list) : constr list :=
  list_subtract (fun t1 t2 => Constr.equal t1 t2) l1 l2.

  Import Unsafe.

  (*
    get_constructor_name : constr -> constr
  
    Given a term c, if c is an application then this function returns its head,
    which is usually the actual constructor name; otherwise it returns c itself.
  *)
  Ltac2 get_constructor_name (c : constr) : constr :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f _ => f
    | _ => c
    end.
  
  (** [destruct_list a l] deconstructs the Coq list [l] (of type [list A], where [a] represents the element type) into an Ltac2 list of [constr] elements. It raises a tactic failure if [l] is not a well‐formed list.
  
  @param a A Coq term representing the element type [A].
  @param l A Coq term of type [list A].
  @return An Ltac2 list of [constr] containing the elements of [l].
  
  @example If [l] is equivalent to [e1 :: e2 :: ... :: en :: nil], then [destruct_list a l] returns [e1; e2; ...; en].
  *)
  Ltac2 rec destruct_list (a : constr) (l : constr) : constr list :=
    let nil_constr  := constr:(@nil $a) in
    let cons_constr := constr:(@cons $a) in
    match Constr.Unsafe.kind l with
    | Constr.Unsafe.App f args =>
        let f_name     := get_constructor_name f in
        let nil_name   := get_constructor_name nil_constr in
        let cons_name  := get_constructor_name cons_constr in
        if Constr.equal f_name nil_name then
          []
        else if Constr.equal f_name cons_name then
               let head := Array.get args 1 in
               let tail := Array.get args 2 in
               head :: destruct_list a tail
             else
               Control.throw (Tactic_failure (Some (Message.of_string "Not a list 1")))
    | _ =>
        Control.throw (Tactic_failure (Some (Message.of_string "Not a list 2")))
    end.
  
  (*
    recons_list : constr list -> constr -> constr
  
    Description:
      Given an Ltac2 list of Coq terms (i.e. a value of type 'constr list')
      and a Coq term 'A' representing the element type,
      this Ltac2 function reconstructs a Coq list (of type 'list A').
      Internally, it constructs the nil and cons constructors for type 'A' and then
      recursively rebuilds the Coq list.
  
    Parameters:
      - l : An Ltac2 list of 'constr' representing the elements of the list.
      - A : A Coq term representing the element type.
  
    Returns:
      - A Coq term (of type 'constr') representing the list of type 'list A'
        that contains exactly the elements in 'l'.
  
    Behavior:
      - If 'l' is empty, it returns 'constr:(@nil A)'.
      - Otherwise, it takes the head 'h' and recursively builds the tail,
        then returns 'constr:(@cons A h tail)'.
  *)
  
  Ltac2 rec recons_list (a : constr) (l : constr list) : constr :=
    match l with
    | [] => constr:(@nil $a)
    | h :: t =>
        let tail_constr := recons_list a t in
        constr:(@cons $a $h $tail_constr)
    end.
  
  
Ltac2 res_set_remove_step () :=
  match! goal with
  | [ |- exists upred,
      ResSet.remove (P upred, ?out) (set_from_list ?in_res) = set_from_list ?out_res /\ subsumed _ (Predicate.name upred) ] =>
      (* break down goal into components *)
      let outname   := Fresh.in_goal @out in
      let inresname := Fresh.in_goal @in_res in
      let outresname:= Fresh.in_goal @out_res in
      let clause := { on_hyps := None; on_concl := AllOccurrences } in
      Std.remember false (Some inresname) (fun _ => in_res) None clause;
      Std.remember false (Some outresname) (fun _ => out_res) None clause;
      Std.remember false (Some outname) (fun _ => out) None clause;
      (* now try to compare lists *)
      let list_of_constr l := destruct_list (constr:(Resource.t)) l in
      let in_res_list  := list_of_constr  in_res in
      let out_res_list := list_of_constr out_res in     
      let diff := const_list_subtract in_res_list out_res_list in
      (* debug *)
      let diff_constr := recons_list (constr:(Resource.t)) diff in
      Message.print (Message.of_constr diff_constr) 
end.
    