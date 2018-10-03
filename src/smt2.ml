open Nondeterminism
open Memory_model

(* TODO: we would be using poly variants if it weren't for Lem... *)
type execution_mode =
  | Exhaustive
  | Random

let runND exec_mode (type cs) cs_module (m: ('a, 'info, 'err, cs, 'st) ndM) (st0: 'st) =
  Debug_ocaml.print_debug 1 [] (fun () ->
    "HELLO from Smt2.runND, exec mode= " ^ match exec_mode with
      | Exhaustive ->
          "exhaustive"
      | Random ->
          "random"
  );
  let module CS = (val cs_module : Constraints with type t = cs) in
  let (>>=) = CS.bind in
  let open CS in
  let rec with_backtracking m xs =
    let i = (Random.int (List.length xs)) in
    let x = List.nth xs i in
    let xs' = List.init (List.length xs - 1) (fun z ->
      List.nth xs (if z < i then z else z+1)
    ) in
    m x >>= function
      | [] ->
          with_backtracking m xs'
      | ys ->
          return ys in
  let rec aux (ND m_act) st =
    (* TODO: graph export *)
    match m_act st with
      | (NDactive a, st') ->
(*
          prerr_endline "NDactive";
          flush_all ();
*)
          check_sat >>= begin function
            | `UNSAT ->
                failwith "NDactive found to be UNSATISFIABLE"
            | `SAT ->
                CS.string_of_solver >>= fun str ->
                return [(Active a, str, st')]
          end

      | (NDkilled r, st') ->
(*
          prerr_endline "NDkilled";
          flush_all ();
*)
          CS.string_of_solver >>= fun str ->
          return [(Killed r, str, st')]

      | (NDnd (debug_str, str_ms), st') ->
(*
          Printf.printf "NDnd[%s]\n" debug_str;
          flush_all ();
*)
          begin match exec_mode with
            | Random ->
                with_backtracking (fun (_, z) -> aux z st') str_ms
            | Exhaustive ->
                foldlM (fun acc (_, m_act) ->
                  (* with_constraints debug_str  *)
                  aux m_act st' >>= fun z ->
                  return (z @ acc)
                ) [] str_ms
(*
            | Interactive ->
                failwith "Smt2.runND: TODO interactive mode"
*)
          end
      | (NDguard (debug_str, cs, m_act), st') ->
(*
          Printf.printf "NDguard[%s]\n" debug_str;
          flush_all ();
*)
          with_constraints debug_str cs begin
            check_sat >>= function
              | `UNSAT ->
                  return [] (* backtrack *)
              | `SAT ->
                  aux m_act st'
          end
      | (NDbranch (debug_str, cs, m_act1, m_act2), st') ->
(*
          Printf.printf "NDbranch[%s]\n" debug_str;
          flush_all ();
*)
          begin match exec_mode with
(*
            | Some Interactive ->
                failwith "Smt2.runND: TODO interactive mode"
*)
            | Random ->
                with_backtracking (fun (cs, m_act) ->
                  with_constraints debug_str cs begin
                    check_sat >>= function
                      | `UNSAT ->
                           return []
                      | `SAT ->
                          aux m_act st'
                end) [(cs, m_act1); (negate cs, m_act2)]
            | Exhaustive ->
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
                end
      | (NDstep str_ms, st') -> aux (ND (fun st -> NDnd ("step", str_ms), st)) st'

  in runEff (aux m st0)

