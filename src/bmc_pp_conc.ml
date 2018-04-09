open Bmc_conc_types
open Printf
open Z3

let pp_memory_order = function
  | NA -> "na"
  | Seq_cst -> "sc"
  | Relaxed -> "rlx"
  | Release -> "rel"
  | Acquire -> "acq"
  | Consume -> "con"
  | Acq_rel -> "a/r"

let pp_tid = string_of_int
let pp_aid = string_of_int
let pp_loc = string_of_int

let pp_value = function
  | Rigid _
  | Flexible _ ->
      assert false
  | Z3Expr expr -> Expr.to_string expr

let pp_action = function
  | Load (aid, tid, memord, loc, cval) ->
    sprintf "%s:Load %s @%s %s %s" (pp_aid aid) (pp_tid tid) (pp_loc loc) 
                                  (pp_memory_order memord) (pp_value cval)
  | Store (aid, tid, memord, loc, cval) ->
    sprintf "%s:Store %s @%s %s %s" (pp_aid aid) (pp_tid tid) (pp_loc loc) 
                                   (pp_memory_order memord) (pp_value cval)
  | _ -> assert false

let pp_location_kind = function
  | Non_Atomic -> "na"
  | Atomic     -> "atomic"
  | Mutex      -> "mutex"


let pp_preexecution (preexec: pre_execution) =
  print_endline "===ACTIONS";
  List.iter (fun action ->
    print_endline (pp_action action)) preexec.actions;
  print_endline "===Threads";
  List.iter (fun tid ->
    Printf.printf "%d " tid) preexec.threads;
  print_endline "===SB";
  List.iter (fun (a1, a2) ->
    Printf.printf "(%s,%s)\n" (pp_action a1) (pp_action a2);
  ) preexec.sb;
  print_endline "===ASW";
  List.iter (fun (a1, a2) ->
    Printf.printf "(%s,%s)\n" (pp_action a1) (pp_action a2);
  ) preexec.asw;
  print_endline "===LK";
  Pmap.iter (fun loc kind ->
    Printf.printf "@%d -> %s\n" loc (pp_location_kind kind)
  ) preexec.lk


let pp_witness (witness: execution_witness) =
  print_endline "===RF";
  List.iter (fun (a1, a2) ->
    Printf.printf "(%s,%s)\n" (pp_action a1) (pp_action a2);
  ) witness.rf;
  print_endline "===MO";
  List.iter (fun (a1, a2) ->
    Printf.printf "(%s,%s)\n" (pp_action a1) (pp_action a2);
  ) witness.mo;
  print_endline "===SW";
  List.iter (fun (a1, a2) ->
    Printf.printf "(%s,%s)\n" (pp_action a1) (pp_action a2);
  ) witness.sw;



(*
let pp_cst () = function
  | Cmm.Concrete n -> Printf.sprintf "%i" n
  | Cmm.Symbolic x -> x

(* TODO: parametrise this on an lval/rval argument, and include & in rval Const_id*)
let pp_value () = function
  | Cmm.Rigid r -> pp_cst () r
  | Cmm.Flexible x -> x

let subst_val s = function
  | Cmm.Rigid r -> Cmm.Rigid r
  | Cmm.Flexible x ->
    (try List.assoc x s
     with Not_found -> Cmm.Flexible x)
*)

(*
type aid = int
type tid = int

type memory_order =
  | NA
  | Seq_cst
  | Relaxed
  | Release
  | Acquire
  | Consume
  | Acq_rel

type flexsym = string

type cst =
  | Concrete of int  
  | Symbolic of string

type cvalue =
  | Rigid of cst
  | Flexible of flexsym

type location = int

type lock_outcome =
    Locked
  | Blocked

type action = 
  | Lock of aid * tid * location * lock_outcome
  | Unlock of aid * tid * location
  | Load of aid * tid * memory_order * location * cvalue
  | Store of aid * tid * memory_order * location * cvalue
  | RMW of aid * tid * memory_order * location * cvalue * cvalue
  | Fence of aid * tid * memory_order
  | Blocked_rmw of aid * tid * location

type location_kind =
  | Non_Atomic
  | Atomic
  | Mutex

type 'a set = 'a list

type pre_execution =
  {  actions : action set;
      threads : tid set;
      lk      : location -> location_kind;
      sb      : (action * action) set ;
      asw     : (action * action) set ;
(*      dd      : (action * action) set ; *)
  }

type execution_witness =
  {  rf      : (action * action) set;
     mo      : (action * action) set;
     sc      : (action * action) set;
     (*
     lo      : (action * action) set;
     ao      : (action * action) set;
     tot     : (action * action) set;
     *)
 }

type observable_execution = (pre_execution * execution_witness)

(*************************************************** *)
(*    Projection functions *)
(*************************************************** *)
let aid_of a =    
((match a with
    | Lock( aid, _, _, _)            -> aid
    | Unlock( aid, _, _)            -> aid
    | Load( aid, _, _, _, _)          -> aid
    | Store( aid, _, _, _, _)         -> aid
    | RMW( aid, _, _, _, _, _)         -> aid
    | Fence( aid, _, _)             -> aid
    | Blocked_rmw( aid, _, _)       -> aid
    ))

let tid_of a =    
((match a with
      Lock( _, tid, _, _)           -> tid
    | Unlock( _, tid, _)           -> tid
    | Load( _, tid, _, _, _)         -> tid
    | Store( _, tid, _, _, _)        -> tid
    | RMW( _, tid, _, _, _, _)        -> tid
    | Fence( _, tid, _)            -> tid
    | Blocked_rmw( _, tid, _)      -> tid
    ))

let loc_of a =    
((match a with
      Lock( _, _, l, _)           -> Some( l)
    | Unlock( _, _, l)           -> Some( l)
    | Load( _, _, _, l, _)         -> Some( l)
    | Store( _, _, _, l, _)        -> Some( l)
    | RMW( _, _, _, l, _, _)        -> Some( l)
    | Fence( _, _, _)            -> None
    | Blocked_rmw( _, _, l)      -> Some( l)
    ))

let value_read_by a =    
((match a with
      Load( _, _, _, _, v)         -> Some( v)
    | RMW( _, _, _, _, v, _)        -> Some( v)
    | _                      -> None
    ))

let value_written_by a =    
((match a with
      Store( _, _, _, _, v)        -> Some( v)
    | RMW( _, _, _, _, _, v)        -> Some( v)
    | _                      -> None
    ))

let is_atomic_load a =    
((match a with
      Load( _, _, mo, _, _) -> mo <> NA
    | _               -> false
    ))

let is_atomic_store a =    
((match a with
      Store( _, _, mo, _, _) -> mo <> NA
    | _                -> false
    ))

let is_NA_load a =    
((match a with
      Load( _, _, mo, _, _) -> mo = NA
    | _               -> false
    ))

let is_NA_store a =    
((match a with
      Store( _, _, mo, _, _) -> mo = NA
    | _                -> false
    ))

let is_load a =    
((match a with
      Load( _, _, _, _, _) -> true
    | _              -> false
    ))

let is_store a =    
((match a with
      Store( _, _, _, _, _) -> true
    | _               -> false
    ))

let is_atomic_action a =    
((match a with
      Load( _, _, mo, _, _)  -> mo <> NA
    | Store( _, _, mo, _, _) -> mo <> NA
    | RMW( _, _, _, _, _, _)  -> true
    | _                -> false
    ))

let is_read a =    
((match a with
      Load( _, _, _, _, _)  -> true
    | RMW( _, _, _, _, _, _) -> true
    | _               -> false
    ))

let is_write a =    
((match a with
      Store( _, _, _, _, _) -> true
    | RMW( _, _, _, _, _, _) -> true
    | _               -> false
    ))

let is_acquire a =    
 ((match a with
      Load( _, _, mo, _, _)  -> Pset.mem  mo 
  (Pset.from_list Pervasives.compare [Acquire;Seq_cst])
    | RMW( _, _, mo, _, _, _) -> Pset.mem  mo 
  (Pset.from_list Pervasives.compare [Acquire;Acq_rel;Seq_cst])
    | Fence( _, _, mo)     -> Pset.mem  mo 
  (Pset.from_list Pervasives.compare [Acquire;Consume;Acq_rel;Seq_cst])
    | _                -> false
    ))

let is_release a =    
 ((match a with
      Store( _, _, mo, _, _)  -> Pset.mem  mo 
  (Pset.from_list Pervasives.compare [Release;Seq_cst])
    | RMW( _, _, mo, _, _, _)  -> Pset.mem  mo 
  (Pset.from_list Pervasives.compare [Release;Acq_rel;Seq_cst])
    | Fence( _, _, mo)      -> Pset.mem  mo 
  (Pset.from_list Pervasives.compare [Release;Acq_rel;Seq_cst])
    | _                 -> false
    ))
*)
