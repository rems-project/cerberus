open BinInt
open Datatypes
open Equalities
open OrdersTac
open Zbool

module Z_as_UBE = 
 struct 
  type t = coq_Z
  
  (** val eqb : coq_Z -> coq_Z -> bool **)
  
  let eqb =
    coq_Zeq_bool
 end

module Z_as_DT = Make_UDTF(Z_as_UBE)

module Z_as_OT = 
 struct 
  type t = coq_Z
  
  (** val eqb : coq_Z -> coq_Z -> bool **)
  
  let eqb =
    coq_Zeq_bool
  
  (** val eq_dec : coq_Z -> coq_Z -> bool **)
  
  let eq_dec x y =
    let b = coq_Zeq_bool x y in if b then true else false
  
  (** val compare : coq_Z -> coq_Z -> comparison **)
  
  let compare =
    coq_Zcompare
 end

module ZOrder = OTF_to_OrderTac(Z_as_OT)

