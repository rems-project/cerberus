(* Adapted from cppmem model exploration tool *)
(*========================================================================*)
(*                                                                        *)
(*             cppmem model exploration tool                              *)
(*                                                                        *)
(*                    Mark Batty                                          *)
(*                    Scott Owens                                         *)
(*                    Jean Pichon                                         *)
(*                    Susmit Sarkar                                       *)
(*                    Peter Sewell                                        *)
(*                                                                        *)
(*  This file is copyright 2011, 2012 by the above authors.               *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*  notice, this list of conditions and the following disclaimer.         *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*  notice, this list of conditions and the following disclaimer in the   *)
(*  documentation and/or other materials provided with the distribution.  *)
(*  3. The names of the authors may not be used to endorse or promote     *)
(*  products derived from this software without specific prior written    *)
(*  permission.                                                           *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    *)
(*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    *)
(*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       *)
(*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     *)
(*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         *)
(*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHE   *)
(*  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       *)
(*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   *)
(*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         *)
(*========================================================================*)

open Auxl
open Bmc_sorts
open Core
open Printf
open Z3

(* ======== Concurrency ========= *)
type aid = int
type tid = int

type z3_location = Expr.expr
(*
  | LocZ3Expr of Expr.expr
  | LocStr of string 
*)

type z3_value    = Expr.expr
type guard       = Expr.expr

type memory_order =
  | C_mem_order of Cmm_csem.memory_order
  | Linux_mem_order of Linux.memory_order0

type action =
  | Load  of aid * tid * memory_order * z3_location * z3_value
  | Store of aid * tid * memory_order * z3_location * z3_value
  | RMW   of aid * tid * memory_order * z3_location * z3_value * z3_value
  | Fence of aid * tid * memory_order

type location_kind =
  | Non_Atomic
  | Atomic
  | Mutex

type action_rel = (action * action) list

type preexec2 =
  { actions : action list
  ; threads : tid list
  ; sb      : action_rel
  ; asw     : action_rel
  }

type witness =
  { rf : action_rel
  ; mo : action_rel
  ; sc : action_rel
  }

type fault =
    One of action list
  | Two of action_rel

type execution_derived_data = {
  derived_relations : (string * action_rel) list;
  undefined_behaviour : (string * fault) list;
}



(* ===== ACCESSORS ===== *)
let aid_of_action (a: action) = match a with
  | Load  (aid, _, _, _, _)
  | Store (aid, _, _, _, _)
  | RMW   (aid, _, _, _, _, _)
  | Fence (aid, _, _) ->
      aid

let tid_of_action (a: action) = match a with
  | Load  (_, tid, _, _, _)
  | Store (_, tid, _, _, _)
  | RMW   (_, tid, _, _, _, _)
  | Fence (_, tid, _) ->
      tid

let memorder_of_action (a: action) = match a with
  | Load  (_,_,m,_,_)
  | Store (_,_,m,_,_)
  | RMW   (_,_,m,_,_,_)
  | Fence (_,_,m) ->
      m

let addr_of_action (a: action) = match a with
  | Load  (_, _, _, l, _)
  | Store (_, _, _, l, _)
  | RMW   (_, _, _, l, _, _) -> l
  | Fence (_, _, _) -> assert false

let rval_of_action (a: action) = match a with
  | Load (_, _, _, _, v)
  | RMW (_, _, _, _, v, _) -> v
  | _ -> assert false

let wval_of_action (a: action) = match a with
  | Store (_, _, _, _, v)
  | RMW   (_, _, _, _, _, v) -> v
  | _ -> assert false

let is_write (a: action) = match a with
  | Store _ | RMW _ -> true
  | _ -> false

let is_read (a: action) = match a with
  | Load _ | RMW _ -> true
  | _ -> false

let is_atomic (a: action) = match memorder_of_action a with
  | C_mem_order NA -> false
  | _  -> true

let is_fence (a: action) = match a with
  | Fence _ -> true
  | _       -> false

(* ======== PPRINTERS. TODO: MOVE THIS ========= *)
let pp_memory_order = function
  | C_mem_order mo ->
      Cmm_csem.(function
      | NA -> "na"
      | Seq_cst -> "sc"
      | Relaxed -> "rlx"
      | Release -> "rel"
      | Acquire -> "acq"
      | Consume -> "con"
      | Acq_rel -> "a/r") mo
  | Linux_mem_order mo ->
      Linux.(function
      | Once      -> "once"
      | Acquire0  -> "acq"
      | Release0  -> "rel"
      | Rmb       -> "rmb"
      | Wmb       -> "wmb"
      | Mb        -> "mb"
      | RbDep     -> "rbdep"
      | RcuLock   -> "rculock"
      | RcuUnlock -> "rcuunlock"
      | SyncRcu -> assert false) mo


let pp_memory_order_enum2 = fun () -> pp_memory_order

let pp_memory_order_enum3 m () =
  function mo ->
    sprintf "%a" pp_memory_order_enum2 mo

let pp_tid = string_of_int
let pp_aid = string_of_int
let pp_loc () loc =
  begin match Expr.get_args loc with
  | [a1;a2] -> sprintf "(%s.%s)" (Expr.to_string a1) (Expr.to_string a2)
  | _ -> Expr.to_string loc 
  end

  (*match loc with
  | LocZ3Expr expr ->
      begin match Expr.get_args expr with
      | [a1;a2] -> sprintf "(%s.%s)" (Expr.to_string a1) (Expr.to_string a2)
      | _ -> Expr.to_string expr
      end
  | LocStr str ->
      str*)
    
let pp_thread_id () tid =
  pp_tid tid

let pp_value () expr =
  assert (Expr.get_num_args expr = 1);
  let arg = List.hd (Expr.get_args expr) in
  if (Sort.equal (Expr.get_sort arg) (LoadedInteger.mk_sort)) then
    begin
      if (Boolean.is_true
        (Expr.simplify (LoadedInteger.is_unspecified arg) None)) then
        "?"
      else
      Expr.to_string (List.hd (Expr.get_args arg))
    end
  else if (Sort.equal (Expr.get_sort arg) (LoadedPointer.mk_sort)) then
    begin
      if (Boolean.is_true
        (Expr.simplify (LoadedPointer.is_unspecified arg) None)) then
        "?"
      else
      Expr.to_string (List.hd (Expr.get_args arg))
    end
  else
    Expr.to_string arg

let pp_action_long = function
  | Load (aid, tid, memord, loc, cval) ->
    sprintf "%s:Load %s @%s %s %s" (pp_aid aid) (pp_tid tid) (pp_loc () loc)
                                  (pp_memory_order memord) (pp_value () cval)
  | Store (aid, tid, memord, loc, cval) ->
    sprintf "%s:Store %s @%s %s %s" (pp_aid aid) (pp_tid tid) (pp_loc () loc)
                                   (pp_memory_order memord) (pp_value () cval)
  | _ -> assert false

let pp_location_kind = function
  | Non_Atomic -> "na"
  | Atomic     -> "atomic"
  | Mutex      -> "mutex"

type column_head =
  | CH_tid of tid
  | CH_loc of z3_location

type layoutmode =
  | LO_dot
  | LO_neato_par
  | LO_neato_par_init
  | LO_neato_downwards

type ppmode = {
    fontsize    : int;
    fontname    : string;
    node_height : float;
    node_width  : float;
    filled      : bool;
    xscale      : float;
    yscale      : float;
    ranksep     : float;
    nodesep     : float;
    penwidth    : float;
    legend      : string option;
    layout      : layoutmode;
    texmode     : bool;
    thread_ids  : bool;
}

let ppmode_default_web = {
  fontsize    = 8;
  fontname    = "Helvetica";
  node_height = 0.2;
  node_width  = 1.3;
  filled      = false;
  xscale      = 1.5;
  yscale      = 0.7;
  ranksep     = 0.2;
  nodesep     = 0.75;   (* for dot and for self-loops in neato *)
  penwidth    = 1.0;
  legend      = None; (*Some "filename";*)
  layout      = LO_neato_par;
  texmode     = false;
  thread_ids  = false
}

type layout = {
    columns : ((column_head*(int*int)) * (action * (int*int)) list) list;
    column_of : action -> int;
    size_x : int;
    size_y : int;
    relabelling : (aid*string) list * (tid*string) list
  }

let layout_by_thread (do_relabel: bool) (preexec: preexec2) : layout =
  let sb a1 a2 =
    if List.mem (a1,a2) preexec.sb then -1
    else if List.mem (a2,a1) preexec.sb then 1
    else 0 in
  let sorted_threads = List.sort
      (fun tid1 tid2 -> compare tid1 tid2)
      preexec.threads in
  let actions_of_thread tid = List.filter
      (fun a -> tid = tid_of_action a)
      preexec.actions in
  let actions_by_column =
    List.map (function tid ->
        (CH_tid tid, List.stable_sort sb (actions_of_thread tid)))
      sorted_threads in
  let size_x = List.length actions_by_column in
  let size_y = List.fold_left max 0
        (List.map (function (ch,actions) -> 1+List.length actions)
                  actions_by_column) in

  let rec add_coords_col actions x y =
    match actions with
    | [] -> []
    | a::actions' -> (a,(x,y)):: add_coords_col actions' x (y+1) in
  let rec add_coords x abc =
    let x_offset,y_offset = 0,0 in
    match abc with
    | [] -> []
    | (ch,actions)::abc' ->
        ((ch,(x+x_offset,0+y_offset)),
         add_coords_col actions (x+x_offset) (1+y_offset))
         :: add_coords (x+1) abc' in
  let actions_by_column_with_coords = add_coords 0 actions_by_column in

  let rec action_relabelling_column actions n acc =
    match actions with
    | [] -> (acc,n)
    | (a,(x,y))::actions' ->
        let new_label =
          if n < 25 then String.make 1 (Char.chr (n+Char.code 'a'))
          else sprintf "z%i" n in
        action_relabelling_column actions' (n+1)
                                  ((aid_of_action a,new_label)::acc) in
  let rec action_relabelling_columns abc n acc =
    match abc with
    | [] -> acc
    | (ch,actions)::abc' ->
        let (acc',n') = action_relabelling_column actions n acc in
        action_relabelling_columns abc' n' acc' in

  let rec thread_relabelling ts n acc =
    match ts with
    | [] -> acc
    | tid::ts' ->
        let new_label = (sprintf "%i" n) in
        thread_relabelling ts' (n+1) ((tid,new_label)::acc) in
  let action_relabelling : (aid * string) list =
    action_relabelling_columns actions_by_column_with_coords 0 [] in

  let thread_relabelling : (tid * string) list =
    thread_relabelling sorted_threads 0 [] in
  { columns = actions_by_column_with_coords;
    column_of = (function a -> let rec f ts n =
        match ts with tid::ts' -> if tid_of_action a = tid then n
                                  else f ts' (n+1)
                    | [] -> raise (Failure "thread id not found") in
        f sorted_threads 0);
    size_x = size_x;
    size_y = 1*size_y+2 ;
    relabelling = if do_relabel then (action_relabelling,thread_relabelling)
                                else ([],[])
  }

let rec pp_action rl () a = match a with
  (*| Lock (aid,tid,l,oc) ->
      assert false
  | Unlock (aid,tid,l) ->
      assert false*)
  | Load (aid,tid,mo,l,v) ->
     sprintf "%a,%a:Load %a %a %a"
             (pp_action_id' rl) aid  (pp_thread_id' rl) tid
             pp_memory_order_enum2 mo  pp_loc l  pp_value v
  | Store (aid,tid,mo,l,v) ->
     sprintf "%a,%a:Store %a %a %a" (pp_action_id' rl) aid  (pp_thread_id' rl)
             tid  pp_memory_order_enum2 mo  pp_loc l  pp_value v
  | RMW (aid,tid,mo,l,v1,v2) ->
     sprintf "%a,%a:RMW %a %a %a %a" (pp_action_id' rl) aid  (pp_thread_id' rl)
             tid  pp_memory_order_enum2 mo  pp_loc l  pp_value v1  pp_value v2
  (*| Blocked_rmw (aid,tid,l) ->
      assert false*)
  | Fence (aid,tid,mo) ->
      assert false

and pp_action_id () aid = string_of_int aid

and pp_action_id' rl () aid =
  let (action_relabelling,thread_relabelling) = rl in
  try List.assoc aid action_relabelling with Not_found -> pp_action_id () aid

and pp_thread_id' rl () tid =
  let (action_relabelling,thread_relabelling) = rl in
  try List.assoc tid thread_relabelling with Not_found -> pp_thread_id () tid

and pp_action_thread_id' m rl () (aid,tid) =
  if m.thread_ids then
    sprintf "%a,%a" (pp_action_id' rl) aid (pp_thread_id' rl) tid
  else
    sprintf "%a" (pp_action_id' rl) aid

and pp_action' m rl () = function a -> match a with
  (*| Lock (aid,tid,l,oc) ->
      assert false
  | Unlock(aid,tid,l) ->
      assert false*)
  | Load (aid,tid,mo,l,v) ->
      let fmt =
        if m.texmode then format_of_string "\\\\RA{%a}{%a}{%a}{%a}" else format_of_string "%a:R%a %a=%a" in
      sprintf fmt (pp_action_thread_id' m rl) (aid,tid)  (pp_memory_order_enum3 m) mo  pp_loc l  pp_value v
  | Store (aid,tid,mo,l,v) ->
      let fmt =
        if m.texmode then format_of_string "\\\\WA{%a}{%a}{%a}{%a}" else format_of_string "%a:W%a %a=%a" in
     sprintf fmt (pp_action_thread_id' m rl) (aid,tid)  (pp_memory_order_enum3 m) mo  pp_loc l  pp_value v
  | RMW (aid,tid,mo,l,v1,v2) ->
      let fmt =
        if m.texmode then format_of_string "\\\\RMWA{%a}{%a}{%a}{%a}{%a}" else
          format_of_string "%a:RMW%a %a=%a/%a" in
     sprintf fmt (pp_action_thread_id' m rl) (aid,tid)  (pp_memory_order_enum3
     m) mo  pp_loc l  pp_value v1 pp_value v2
  (*| Blocked_rmw (aid,tid,l) ->
      assert false *)
  | Fence (aid,tid,mo) ->
      let fmt =
        if m.texmode then format_of_string "\\\\FA{%a}{%a}" else format_of_string "%a:F%a" in
     sprintf fmt (pp_action_thread_id' m rl) (aid,tid)  (pp_memory_order_enum3 m) mo

and pp_column_head rl () = function
  | CH_tid tid -> sprintf "%a" (pp_thread_id' rl) tid
  | CH_loc loc -> sprintf "%a" pp_loc loc

exception NonLinearSB

let partition_faults faults =
  let (unary,binary) =
    List.fold_left
      (fun (un,bin) (nm,fault) -> match fault with
        | One acts -> ((nm,acts) :: un,bin)
        | Two rel -> (un,(nm,rel) :: bin))
      ([],[]) faults in
  (List.rev unary, List.rev binary)

let pp_dot () (m, (preexec, exedo, exddo)) =
  let lo = layout_by_thread false preexec in
  let fontsize_node   = m.fontsize in
  let fontsize_edge   = m.fontsize in
  let fontsize_legend = m.fontsize in

  let fontname_node   = m.fontname in
  let fontname_edge   = m.fontname in
  let fontname_legend = m.fontname in

  let pp_attr () (attr,v) = match v with
  | "" -> ""
  | _  -> sprintf ", %s=\"%s\"" attr v in

  let pp_intattr () (attr,v) =
    sprintf ", %s=%i" attr v in

  let pp_floatattr () (attr,v) =
    sprintf ", %s=%s" attr (string_of_float v) in

  let pp_fontsize () f = pp_intattr () ("fontsize",f) in

  let pp_fontcolor () color = pp_attr () ("fontcolor",color) in

  let pp_fontname () fontname = pp_attr () ("fontname",fontname) in

  let pp_extra () attr_value = match attr_value  with
  | "" -> ""
  | _  -> sprintf "%s" attr_value in

  let pl () = sprintf  "%s\n" in
  let pf () fmt = sprintf fmt in

  let pp_edge_label () (m, lbl) =
    (* escape_label lbl in *)
    if m.texmode then
      "\"" ^ String.concat "," (List.map (fun (l,c) -> "\\\\color{" ^ c ^ "}{" ^ l ^ "}") lbl) ^ "\""
    else "<" ^ String.concat "," (List.map (fun (l,c) -> "<font color=\"" ^ c ^ "\">" ^ l ^ "</font>") lbl) ^ ">" in

  let pp_node_name () a = sprintf "node%s" (pp_aid (aid_of_action a)) in

  let is_ur_or_dr lbls =
    match lbls with
        (* TODO: jp: the information of which relations are faults should be piped to here *)
      | [(lbl, _)] -> List.mem lbl ["ur";"dr"]
      | _ -> false in

  let pp_edge () m a1 a2 lbl colours style arrowsize extra_attr =
    let colour = String.concat ":" colours in
    sprintf "%a -> %a [label=%a%s%a%a%a%a%a%s%a]%a;\n"
      pp_node_name a1
      pp_node_name a2
      pp_edge_label (m, lbl)
      "" (* (if filled then ",style=\"filled\",labelfloat=\"true\"" else "") *)
      pp_attr ("color",colour)
      pp_fontname fontname_edge
      pp_fontsize fontsize_edge
      pp_attr ("style",style)
      pp_floatattr ("penwidth",m.penwidth)
      (if is_ur_or_dr lbl then ",constraint=false,arrowhead=\"none\"" else "")
      pp_attr ("arrowsize",arrowsize)
      pp_extra extra_attr  in

  let max_y = lo.size_y -1 in

  let xorigin=1.0 in
  let yorigin=1.0 in

  let action_position (x,y) =
    (m.xscale *. float_of_int x +. xorigin),
    (m.yscale *. (float_of_int max_y -. (float_of_int y )) +. yorigin) in

  let pp_action_position () (x,y) =
    let (x',y') = action_position (x,y) in
    sprintf "pos=\"%f,%f!\"" x' y' in

  let (unary_faults,binary_faults) =
    match exddo with
      | None -> ([],[])
      | Some exdd -> partition_faults exdd.undefined_behaviour in

  let axygeometry = sprintf "[margin=\"0.0,0.0\"][fixedsize=\"true\"][height=\"%f\"][width=\"%f\"]" m.node_height m.node_width in
  let pp_axy () color rank (a,(x,y)) =
    sprintf
      "%a [shape=plaintext%a%a%s%a] %s [label=\"%s\", %a] %s;\n"
      pp_node_name a
      pp_fontname fontname_node
      pp_fontsize fontsize_node
      (if m.filled then ", style=\"filled\"" else "")
      pp_fontcolor color
      rank
      (((pp_action' m lo.relabelling) () a))
      pp_action_position (x,y)
      axygeometry
  in

  (* TODO *)
  let faulty_action_ids = [] in
  let rec pp_axys () axys =
    match axys with
    | [] -> ""
    | (a,(x,y))::axys' ->
      let color = if List.mem (aid_of_action a) faulty_action_ids
                  then "darkorange" else "" in
      pp_axy () color "" (a,(x,y)) ^  pp_axys () axys' in

  let rec pp_columns () columns =
    match columns with
    | [] -> ""
    | ((ch,(x,y)),axys)::columns' ->
        pl () "/* column */\n"
        ^ sprintf "%s%a%a"
          "" (* (if m.neato then pp_column_head_node () ("","",(ch,(x,y))) else "")*)
          pp_axys axys
          pp_columns columns' in

  let relations =
    [ ("sb","black", transitive_reduction preexec.sb);
      (*("dd","magenta", transitive_reduction exod.dd);
      ("cd","magenta", transitive_reduction exod.cd); *)
      (* ("asw","deeppink4",preexec.asw) ]  *)
    ]
    @
      (match exedo with None -> [] | Some exed ->
        [ ("rf",  "red",   exed.rf);
          ("sc",  "orange", transitive_reduction exed.sc);
          ("mo",  "blue",  transitive_reduction exed.mo);
          (* ("lo",  "gray54", transitive_reduction exed.lo);
          ("ao",  "black", exed.ao);
          ("tot", "blue", transitive_reduction exed.tot) *)
        ])
    @
      (match exddo with None -> [] | Some exdd ->
        (* TODO: jp: make this generic *)
        let colour_scheme = [
          ("sw", "deeppink4");
          ("rs", "black");
          ("hrs", "black");
          ("cad", "deeppink4");
          ("dob", "deeppink4");
          ("ithb", "forestgreen");
          ("hb", "forestgreen");
          ("vse", "brown");
          ("vsses", "brown4");
          ("dummy", "white")
        ] in
        let try_to_transitive_reduce rel = if is_transitive rel then try transitive_reduction rel with Transitive -> rel else rel in
        (* Note: doing the reduction on each relation is expensive *)
        let colour_and_prepare (nm, rel) =
          (nm,
           (try List.assoc nm colour_scheme with Not_found -> "black"),
           try_to_transitive_reduce rel) in
        List.map colour_and_prepare exdd.derived_relations
        @
        let relation_faults =
          List.map
            (fun (nm, rel) -> (nm, rel))
              (* ((try List.assoc nm Atomic.short_names with Not_found -> nm), rel)) *)
            binary_faults in
        List.map (fun (nm, rel) -> (nm, "darkorange", symmetric_reduction rel)) relation_faults
        ) in
  let debug s = () (* print_string s;flush stdout *) in
  let relayout_downwards columns =
    try
      let relayout_downwards_reln =
        transitive_reduction
          (transitive_closure
             (reflexive_reduction
                (List.flatten
                   (option_map
                      (function (e,c,r) ->
                        if List.mem e ["dr";"ur"] then None
                        else Some r)
                      relations)))) in
      let r = ref relayout_downwards_reln in
      let print_r () = debug "r = \n"; List.iter (function (a',b') -> debug (sprintf "   <%a, %a>\n" (pp_action lo.relabelling) a' (pp_action lo.relabelling)  b')) !r; debug "" in
      let () = print_r() in
      let n = List.length columns in
      let a_todo = Array.of_list (List.map (function (_,axys) ->axys) columns) in
      let chs = Array.of_list (List.map (function (ch,_) ->ch) columns) in
      let a_done = Array.make n [] in
      let y_next = Array.make n 0 in
      let y_next' = Array.make n 0 in
      let newly_done = ref [] in
      let print_axy (a,(x,y)) = debug (sprintf "(%a,(%n,%n))[%n] " (pp_action lo.relabelling) a x y (lo.column_of a)) in
      let print_axys axys = List.iter print_axy axys; debug "\n" in
      let () =
        debug "a_todo: ";
        for i = 0 to n-1 do
          debug (Printf.sprintf "@%i = " i); print_axys (a_todo.(i))
        done;
        debug "\n"
      in
      let print_r () = debug "r = \n"; List.iter (function (a',b') -> debug (sprintf "   <%a, %a>\n" (pp_action lo.relabelling) a' (pp_action lo.relabelling)  b')) !r; debug "" in
      while Array.fold_right (function a_s -> function b -> (a_s <> [] || b)) a_todo false do
        let _ = read_line () in
        debug "\nnew round:\n";
        print_r ();
        debug "a_todo: ";
        for i = 0 to n-1 do
          debug (Printf.sprintf "@%i = " i); print_axys (a_todo.(i))
        done;
        debug "\n" ;
        debug "y_next:  ";for i = 0 to n-1 do debug (sprintf "%n  " y_next.(i)) done; debug "\n";
        newly_done := [];
        for i = 0 to n-1 do
          match a_todo.(i) with
          | [] -> ()
          | (a,(x,y))::axys' ->
              if List.exists (function (a',b') -> b'=a) (!r) then ()
              else (
                a_todo.(i)<- axys' ;
                let axy' = (a,(x,y_next.(i))) in
                print_axy axy';
                a_done.(i)<- a_done.(i) @ [axy'];
                newly_done := a :: (!newly_done);
               )
        done;
        debug "newly done: ";
        List.iter (function a -> debug (pp_action lo.relabelling () a)) (!newly_done); debug "\n";
        for i= 0 to n-1 do
          y_next'.(i) <-
            List.fold_left max
              (y_next.(i) + (if List.exists (function a -> lo.column_of a = i) !newly_done then 1 else 0) )
              ( option_map
                  (function (a',b') ->
                    if List.mem a' (!newly_done) && lo.column_of b' = i
                    then Some (1 + y_next.(lo.column_of a'))
                    else None)
                  !r )
        done;
        for i = 0 to n-1 do
          y_next.(i) <- y_next'.(i)
        done;
        r := List.filter (function (a',b') -> not (List.mem a' (!newly_done))) (!r)
      done;
      Array.to_list (Array.mapi (fun i axys' -> ( chs.(i), a_done.(i))) a_done )
    with
      Transitive ->
        debug "relayout_downwards invoked on a transitive set of relations\n";
        columns
    |  NonLinearSB ->
        debug "relayout_downwards invoked on structure with non-linear sequenced-before relations\n";
        columns  in

  let relayout_par_init columns =
    let (column0, columns') = (List.hd columns, List.tl columns) in
    let y_start = match column0 with (_,axys) -> List.length axys in
    column0 :: List.map (function (ch,axys) ->
      (ch, List.map (function (a,(x,y))->(a,(x,y+y_start))) axys)) columns' in

  let lo =
    let columns' = match m.layout with
    | LO_neato_downwards -> relayout_downwards lo.columns
    | LO_neato_par_init -> relayout_par_init lo.columns
    | LO_dot | LO_neato_par -> lo.columns
    in
    { lo
    with
      columns = columns';
      size_y = List.fold_left max 0
        (List.map
           (function (ch,axys) ->
             1+
               List.fold_right
               (function (a,(x,y)) -> function y' -> max y y')
               axys
               0
           )
           columns')
    } in

  let flattened = List.flatten (List.map (function (e,c,r) -> (List.map (function (a1,a2) -> (e,c,a1,a2)) r)) relations) in

  let source_target_pairs = remove_duplicates (List.map (function (e,c,a1,a2)->(a1,a2)) flattened) in

  let glommed_edges =
    List.map
      (function (a1',a2') ->
        let parallel_edges = List.filter (function (e,c,a1,a2)->a1=a1'&&a2=a2') flattened in
        let (_,_,a1,a2) = List.hd parallel_edges in
(* the following would make multiple labels appear vertically, but the overall layout produced by graphviz is often much worse *)
(*        let labels = "\\\\ml{"^String.concat "\\\\\\\\" (List.map (function (e,_,_,_)-> "\\\\"^e) parallel_edges)^"}" in *)
        let labels = List.map (function (e,c,_,_) -> (e,c)) parallel_edges in
(*         let non_hb_colours = remove_duplicates (option_map (function (e,c,_,_) -> match e with "hb"->None |_->Some c) parallel_edges) in *)
(*         let colour = match non_hb_colours with [c]->c | _ -> "black" in *)
        let colours = remove_duplicates (option_map (function (_,c,_,_) -> Some c) parallel_edges) in
        let arrowsize = match List.length colours with
        | 1 -> "0.8"
        | 2 -> "1.0"
        | _ -> "1.2" in
        (labels,colours,arrowsize,a1,a2))
      source_target_pairs in

  let pp_graph () legend =
    "digraph G {\n"
(* this gives *different* results to invoking dot/neato on the command-line *)
(*     ^ " layout = "^(match m.layout with Dot -> "dot" | _ -> "neato") ^"\n"  *)
    ^ " splines=true;\n"
    ^ " overlap=false;\n"
    ^ " ranksep = "^string_of_float m.ranksep ^";\n"
    ^ " nodesep = "^string_of_float m.nodesep ^";\n"
(*    ^ " fontname = \""^fontname_graph^"\";\n"*)
    ^ "/* legend */\n"
    ^ pf () "fontsize=%i fontname=\"%s\" label=\"%s\"; \n\n" fontsize_legend fontname_legend legend
    ^ "/* columns */\n"
    ^ pf () "%a" pp_columns lo.columns
    (* ^ pf () "%a" pp_constraint exod.vconstraint *)
    ^ String.concat "" (List.map (function (labels,c,arrowsize,a1,a2) -> pp_edge () m a1 a2 labels c "" arrowsize "") glommed_edges)
    ^ "}" in

   let legend = match m.legend with
   | None -> ""
   (*
   | Some "filename" -> (match testname with None -> "" | Some testname -> escape_label testname)
*)
   | Some s -> s in

   pp_graph () legend
