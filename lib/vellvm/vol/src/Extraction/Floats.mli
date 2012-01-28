open BinInt
open BinPos
open Datatypes
open Integers

module Float : 
 sig 
  val zero : float
  
  val eq_dec : float -> float -> bool
  
  val neg : float -> float
  
  val abs : float -> float
  
  val singleoffloat : float -> float
  
  val intoffloat : float -> Int.int
  
  val intuoffloat : float -> Int.int
  
  val floatofint : Int.int -> float
  
  val floatofintu : Int.int -> float
  
  val add : float -> float -> float
  
  val sub : float -> float -> float
  
  val mul : float -> float -> float
  
  val div : float -> float -> float
  
  val rem : float -> float -> float
  
  val cmp : comparison -> float -> float -> bool
  
  val bits_of_double : float -> Int.int
  
  val double_of_bits : Int.int -> float
  
  val bits_of_single : float -> Int.int
  
  val single_of_bits : Int.int -> float
  
  val from_words : Int.int -> Int.int -> float
  
  val ox8000_0000 : Int.int
  
  val ox4330_0000 : Int.int
 end

