open Nondeterminism
open Memory_model

let runND (type cs) cs_module (m: ('a, 'err, cs, 'st) ndM) (st0: 'st) =
  Debug_ocaml.print_debug 0 [] (fun () ->
    match Global_ocaml.current_execution_mode () with
      | Some mode ->
          "HELLO from Smt2.runND, exec mode= " ^ Global_ocaml.string_of_execution_mode mode
      | None ->
          "HELLO from Smt2.runND, found NO exec mode!"
  );
  
  
  let module CS = (val cs_module : Constraints with type t = cs) in
  let (>>=) = CS.bind in
  let open CS in
  
  let rec with_backtracking m xs =
    let i = (Random.int (List.length xs)) in
    let x = List.nth xs in
    let xs' = List.init (List.length xs - 1) (fun z ->
      List.nth xs (if z < i then z else z+1)
    ) in
    m x >>= function
      | [] ->
          with_backtracking m xs'
      | ys ->
          return ys in
  
  let rec aux (ND m_act) st =
(*
    let aux m st =
      match Global_ocaml.current_execution_mode () with
        | None ->
            failwith "Smt2.runND, found NO exec mode!"
        | Some Exhaustive ->
            aux m st
        | Some Random ->
            aux m st >>= fun xs ->
            return [List.nth xs (Random.int (List.length xs))]
        | Some Interactive ->
            failwith "Smt2.runND: todo interactive mode"
    in
*)
    (* TODO: graph export *)
    match m_act st with
      | (NDactive a, st') ->
          check_sat >>= begin function
            | `UNSAT ->
                failwith "NDactive found to be UNSATISFIABLE"
            | `SAT ->
                CS.string_of_solver >>= fun str ->
                return [(Active a, str, st')]
          end

      | (NDkilled r, st') ->
          CS.string_of_solver >>= fun str ->
          return [(Killed r, str, st')]

      | (NDnd (debug_str, str_ms), st') ->
          begin match Global_ocaml.current_execution_mode () with
            | Some Random ->
                let (str, m_act) = List.nth str_ms (Random.int (List.length str_ms)) in
                aux m_act st'
            | Some Exhaustive ->
                foldlM (fun acc (_, m_act) ->
                  (* with_constraints debug_str  *)
                  aux m_act st'
                ) [] str_ms
            | Some Interactive ->
                failwith "Smt2.runND: TODO interactive mode"
            | None ->
                failwith "Smt2.runND, found NO exec mode!"
          end
      | (NDguard (debug_str, cs, m_act), st') ->
          with_constraints debug_str cs begin
            check_sat >>= function
              | `UNSAT ->
                  return [] (* backtrack *)
              | `SAT ->
                  aux m_act st'
          end
      | (NDbranch (debug_str, cs, m_act1, m_act2), st') ->
          with_constraints debug_str cs begin
            check_sat >>= function
              | `UNSAT ->
                  return []
              | `SAT ->
                  aux m_act1 st'
          end >>= fun xs1 ->
          with_constraints debug_str (negate cs) begin
            check_sat >>= function
              | `UNSAT ->
                  return []
              | `SAT ->
                  aux m_act2 st'
          end >>= fun xs2 ->
          return (xs1 @ xs2)
  in runEff (aux m st0)

