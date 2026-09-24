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

type ('a,'b) either = Left of 'a | Right of 'b

let rec option_map f xs = 
  match xs with 
  | [] -> [] 
  | x::xs -> 
      ( match f x with 
      | None -> option_map f xs 
      | Some x -> x :: (option_map f xs) ) 

let rec remove_duplicates l =
  match l with
  | x::xs -> 
      if (List.mem x xs) then remove_duplicates xs else x::(remove_duplicates xs)
  | [] -> []

let rec remove_duplicates3 f acc l =
  match l with
  | x::xs -> 
      let y = f x in 
      if (List.mem y acc) then remove_duplicates3 f acc xs else remove_duplicates3 f (y::acc) xs
  | [] -> acc

let pad n s = 
   let m = n - String.length s in 
   if m>=1 then s ^ String.make m ' ' else s

let rec split3 xyzs = 
  match xyzs with
  | [] -> [],[],[]
  | (x,y,z) :: l -> 
      let (rx,ry,rz) = split3 l in (x :: rx, y :: ry, z :: rz)

let list_subset l1 l2 =
  List.for_all
    (fun x -> List.mem x l2)
    l1

exception Exc_lex_error of char * int * int

exception My_parse_error of string

let error s = print_string s; print_string "\n"; flush stdout; exit 2

exception Transitive

let transitive_reduction r = 
  let transitive_pairs = 
    List.flatten 
      (List.map 
         (fun (a1,a2) -> 
           option_map (fun (a1',a2') -> if a2=a1' then Some (a1,a2') else None) r)
         r) in
    (* a partial check for cycles *)
  if List.exists (fun (a1,a2)->a1=a2) (r @ transitive_pairs) then 
    raise Transitive;
  List.filter (fun (a1,a2) -> not (List.mem (a1,a2) transitive_pairs)) r 


let transitive_closure r = 
  let rec f r = 
    let two_step_edges =
      List.flatten 
        (List.map (fun (n,n') -> 
          option_map (fun (n'',n''') -> 
            if n'=n'' then Some (n,n''') else None) r) r) in
    let new_two_step_edges = remove_duplicates (List.filter (function e -> not (List.mem e r)) two_step_edges) in
    match new_two_step_edges with
    | [] -> r
    | _  -> f (r @ new_two_step_edges) in
  let r' = f r in
  if List.exists (fun (n1,n2)->n1=n2) r' then 
    raise Transitive (*(Failure "internal error: transitive_closure invoked on a cyclic relation")*);
  r'


let is_transitive r = 
  let two_step_edges =
    List.flatten 
      (List.map (fun (n,n') -> 
        option_map (fun (n'',n''') -> 
          if n'=n'' then Some (n,n''') else None) r) r) in
  List.for_all (function (n,n''') -> List.mem (n,n''') r) two_step_edges



let rec symmetric_reduction xs = 
  match xs with
  | (a,b)::xs -> 
      if (List.mem (a,b) xs) || (List.mem (b,a) xs) then remove_duplicates xs else (a,b)::(symmetric_reduction xs)
  | [] -> []

let rec reflexive_reduction xs = 
  match xs with
  | (a,b)::xs -> if a=b then reflexive_reduction xs else (a,b)::reflexive_reduction xs
  | [] -> []


let non_empty_intersect xs1 xs2 = List.exists (function x1 -> List.mem x1 xs2) xs1

let rec equiv_closure xss = 
  match xss with
  | [] -> []
  | xs::xss' -> 
      let xss'' = equiv_closure xss' in 
      let intersects,nonintersects = List.partition (non_empty_intersect xs) xss'' in
      remove_duplicates (xs @ List.flatten intersects) :: nonintersects

let char_list_of_string s = 
  let n = String.length s in
  let rec f i = if i=n then [] else String.get s i :: f (i+1) in
  f 0

let string_of_char_list ts =
  String.concat "" (List.map (String.make 1) ts)

let fold_right_string f s x =
  let n = String.length s in
  let rec g i x =
    if i = -1 then x
    else g (i - 1) (f (String.get s i) x) in
  g (n - 1) x

let fold_left_string f x s =
  let n = String.length s in
  let rec g i x =
    if i = n then x
    else g (i + 1) (f x (String.get s i)) in
  g 0 x

(* insert x at all positions into ys and return the list of results *)
let rec inserts x ys = match ys with
| [] -> [[x]]
| y::ys' -> (x::ys) :: (List.map (fun zs -> y::zs) (inserts x ys')) 
                        
(* list of all permutations of xs *)
let rec perms xs = match xs with
| x::xs' -> List.flatten (List.map (inserts x) (perms xs'))
| [] -> [[]] 

(* turn a list into a strict linear order as a list of pairs *)
let rec adjacent_pairs xs = match xs with
| [] -> []
| [x] -> []
| x1::x2::xs' -> (x1,x2)::adjacent_pairs (x2::xs')

let rec fact n =
  if n <= 1 then 1 else n * fact (n-1)

let assoc_opt x l =
  try
    Some (List.assoc x l)
  with
    | Not_found -> None


let find_minimals lst order eqf =
  List.filter
    (fun a1 ->
      not (List.exists
	     (fun a2 ->
	       List.mem (a2,a1) order && not (eqf a1 a2))
	     lst))
    lst

let concat2 l = List.fold_left (fun (l1, l2) (l3, l4) -> (l1 @ l3, l2 @ l4)) ([], []) l

let maximal a step =
  List.for_all (fun (x, _) -> x <> a) step

