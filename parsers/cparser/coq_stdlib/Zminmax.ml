open BinInt
open Datatypes
open ZOrderedType

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val coq_Zmax : coq_Z -> coq_Z -> coq_Z **)

let coq_Zmax n m =
  match coq_Zcompare n m with
  | Lt -> m
  | _ -> n

(** val coq_Zmin : coq_Z -> coq_Z -> coq_Z **)

let coq_Zmin n m =
  match coq_Zcompare n m with
  | Gt -> m
  | _ -> n

module ZHasMinMax = 
 struct 
  (** val max : coq_Z -> coq_Z -> coq_Z **)
  
  let max =
    coq_Zmax
  
  (** val min : coq_Z -> coq_Z -> coq_Z **)
  
  let min =
    coq_Zmin
 end

module Z = 
 struct 
  module OT = 
   struct 
    type t = coq_Z
    
    (** val compare : coq_Z -> coq_Z -> comparison **)
    
    let compare =
      coq_Zcompare
    
    (** val eq_dec : coq_Z -> coq_Z -> bool **)
    
    let eq_dec =
      Z_as_OT.eq_dec
   end
  
  module T = 
   struct 
    
   end
  
  module ORev = 
   struct 
    type t = coq_Z
   end
  
  module MRev = 
   struct 
    (** val max : coq_Z -> coq_Z -> coq_Z **)
    
    let max x y =
      coq_Zmin y x
   end
  
  module MPRev = GenericMinMax.MaxLogicalProperties(ORev)(MRev)
  
  module P = 
   struct 
    (** val max_case_strong :
        coq_Z -> coq_Z -> (coq_Z -> coq_Z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1)
        -> (__ -> 'a1) -> 'a1 **)
    
    let max_case_strong n m compat hl hr =
      let c = coq_CompSpec2Type n m (coq_Zcompare n m) in
      (match c with
       | CompGtT -> compat n (coq_Zmax n m) __ (hl __)
       | _ -> compat m (coq_Zmax n m) __ (hr __))
    
    (** val max_case :
        coq_Z -> coq_Z -> (coq_Z -> coq_Z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1
        -> 'a1 **)
    
    let max_case n m x x0 x1 =
      max_case_strong n m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : coq_Z -> coq_Z -> bool **)
    
    let max_dec n m =
      max_case n m (fun x y _ h0 -> h0) true false
    
    (** val min_case_strong :
        coq_Z -> coq_Z -> (coq_Z -> coq_Z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1)
        -> (__ -> 'a1) -> 'a1 **)
    
    let min_case_strong n m compat hl hr =
      let c = coq_CompSpec2Type n m (coq_Zcompare n m) in
      (match c with
       | CompGtT -> compat m (coq_Zmin n m) __ (hr __)
       | _ -> compat n (coq_Zmin n m) __ (hl __))
    
    (** val min_case :
        coq_Z -> coq_Z -> (coq_Z -> coq_Z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1
        -> 'a1 **)
    
    let min_case n m x x0 x1 =
      min_case_strong n m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : coq_Z -> coq_Z -> bool **)
    
    let min_dec n m =
      min_case n m (fun x y _ h0 -> h0) true false
   end
  
  (** val max_case_strong :
      coq_Z -> coq_Z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n m x x0 =
    P.max_case_strong n m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : coq_Z -> coq_Z -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n m x x0 =
    max_case_strong n m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : coq_Z -> coq_Z -> bool **)
  
  let max_dec =
    P.max_dec
  
  (** val min_case_strong :
      coq_Z -> coq_Z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n m x x0 =
    P.min_case_strong n m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : coq_Z -> coq_Z -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n m x x0 =
    min_case_strong n m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : coq_Z -> coq_Z -> bool **)
  
  let min_dec =
    P.min_dec
 end

