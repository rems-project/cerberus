module RE = Resources
module LS = LogicalSorts
module IT = IndexTerms
module BT = BaseTypes

module SymSet = Set.Make(Sym)

open Pp

module StringMap = Map.Make(String)




(* more to be added *)
type memory_state = 
  | Nothing
  | Block of RE.block_type * IT.t
  | Integer of string * RE.size
  | Location of string * RE.size
  | Within of {base_location : string; resource : Sym.t}
  | Predicate of {name : RE.predicate_name; args : string list}

type location_state = { location : string; state : memory_state; }
type variable_location = { name : string; location : string}

type t = 
  { memory_state : location_state list;
    variable_locations : variable_location list;
  }



module Make (G : sig val global : Global.t end) = struct

module L = Local.Make(G)
module Solver = Solver.Make(G)

let evaluate model expr = 
  match Z3.Model.evaluate model expr true with
  | None -> Debug_ocaml.error "failure constructing counter model"
  | Some evaluated_expr -> evaluated_expr

let all_it_names_good it = 
  SymSet.for_all (fun s -> Sym.named s) (IT.vars_in it)



let model local solver : t option =
  match Z3.Solver.get_model solver with
  | None -> None
  | Some model ->
     let all_locations = 
       let from_context = 
         List.filter_map (fun (s, ls) -> 
             if LS.equal ls (LS.Base Loc) 
             then Some (IT.S (BT.Loc, s)) else None
           ) (L.all_logical local)
       in
       let from_resources = 
         List.filter_map RE.pointer (L.all_resources local)
       in
       List.fold_right (fun location_it acc ->
           let expr = SolverConstraints.of_index_term G.global location_it in
           let expr_val = evaluate model expr in
           let expr_val = Z3.Expr.to_string expr_val in
           (StringMap.add expr_val location_it acc)
         ) (from_context @ from_resources) StringMap.empty
     in
     let memory_state = 
       List.map (fun (location_s, location_it) ->
           let o_resource = 
             Solver.resource_for local location_it in
           let state = match o_resource with
             | None -> Nothing
             | Some (_, RE.Block b) -> (Block (b.block_type, b.size))
             | Some (_, RE.Points p) -> 
                let (Base bt) = L.get_l p.pointee local in
                let expr = SolverConstraints.of_index_term G.global 
                             (IT.S (bt, p.pointee)) in
                let expr_val = evaluate model expr in
                begin match bt with
                | Integer -> 
                   Integer (Z3.Expr.to_string expr_val, p.size)
                | Loc -> 
                   Location (Z3.Expr.to_string expr_val, p.size)
                | Struct _ ->
                   Debug_ocaml.error "todo: value of struct in counter model"
                | Array ->
                   Debug_ocaml.error "todo: value of array in counter model"
                | _ -> 
                   Debug_ocaml.error "non-object stored in memory"
                end
             | Some (_, RE.Predicate p) -> 
                let oargs_it = 
                  List.map (fun arg ->
                      let (Base bt) = L.get_l arg local in
                      (IT.S (bt, arg))
                    ) p.oargs
                in
                let args = 
                  List.map (fun it ->
                      let expr = 
                        SolverConstraints.of_index_term G.global it in
                      let expr_val = evaluate model expr in
                      Z3.Expr.to_string expr_val
                    ) (p.key_arg :: p.iargs @ oargs_it)
                in
                Predicate {name = p.name; args}
           in
           { location = location_s; state }
         ) (StringMap.bindings all_locations)
     in
     let variable_locations =
       List.filter_map (fun (c, (l, bt)) ->
           let expr = SolverConstraints.of_index_term G.global (S (bt, l)) in
           let expr_val = evaluate model expr in
           let expr_val = Z3.Expr.to_string expr_val in
           let entry = match Sym.name c, bt with
             | Some name, BT.Loc -> Some { name; location = expr_val }
             | _, _ -> None
           in
           entry
         ) (L.all_computational local)
     in
     Some { memory_state; variable_locations }




let is_reachable_and_model local =
  let (unreachable, solver) = 
    Solver.constraint_holds local (LC (Bool false)) 
  in
  let model = 
    Solver.handle_z3_problems (fun () -> model local solver) 
  in
  (not unreachable, model)






end




let pp_variable_and_location_state ( ovar, { location; state } ) =
  let var = match ovar with
    | None -> Pp.empty
    | Some v -> !^v
  in
  let value, size = match state with
    | Nothing -> Pp.empty, Pp.empty
    | Block (block_type,size) -> 
       begin match block_type with
       | Nothing -> !^"block", IT.pp size
       | Uninit -> !^"uninitialised", IT.pp size
       | Padding -> !^"padding", IT.pp size
       end
    | Integer (value, size) -> typ !^value !^"integer", Z.pp size
    | Location (value, size) -> typ !^value !^"pointer", Z.pp size
    | Within {base_location; _} -> 
       parens (!^"within owned region at" ^^^ !^base_location), Pp.empty
    | Predicate {name; args} ->
       begin match name with
       | Id id ->
          Id.pp id ^^ parens (separate_map (space ^^ comma) string args), Pp.empty
       | Tag tag ->
          Sym.pp tag ^^ parens (separate_map (space ^^ comma) string args), Pp.empty
       end
  in
  ( (R, var), (R, !^location), (R, size), (L, value) )



let pp model = 
  let variable_and_location_state : (string option * location_state) list = 
    List.concat_map (fun (ls : location_state) ->
        let vars = 
          List.filter (fun vl -> String.equal ls.location vl.location
            ) model.variable_locations
        in
        match vars with
        | [] -> [(None, ls)]
        | _ -> List.map (fun v -> (Some v.name, ls)) vars
      ) model.memory_state
  in
  Pp.table4 
    (("var"), ("location"), ("size") , ("value"))
    (List.map pp_variable_and_location_state variable_and_location_state)


