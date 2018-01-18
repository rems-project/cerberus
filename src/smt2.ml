open Nondeterminism
open Memory_model

let runND (type cs) cs_module (m: ('a, 'err, cs, 'st) ndM) (st0: 'st) =
  let module CS = (val cs_module : Constraints with type t = cs) in
  let (>>=) = CS.bind in
  let open CS in
  
  let rec aux (ND m_act) st =
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
          foldlM (fun acc (_, m_act) ->
            (* with_constraints debug_str  *)
            aux m_act st'
          ) [] str_ms

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

