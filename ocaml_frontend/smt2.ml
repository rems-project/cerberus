open Nondeterminism
open Memory_model
open Global_ocaml

let pad = ref 0

let prerr str = () (* prerr_endline (String.make !pad ' ' ^ str) *)

let do_red str= "\x1b[31m" ^ str ^ "\x1b[0m"

let runND exec_mode (type cs) cs_module (m: ('a, Driver.step_kind, 'err, cs, 'st) ndM) (st0: 'st) =
  prerr "ENTERING runND";
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
  let (*rec*) with_backtracking m xs =
    let i = (Random.int (List.length xs)) in
    let x = List.nth xs i in
    (*
    let xs' = List.init (List.length xs - 1) (fun z ->
      List.nth xs (if z < i then z else z+1)
    ) in
    *)
    m x in (*>>= function
      | [] ->
          with_backtracking m xs'
      | ys ->
          return ys in *)
  let rec aux (ND m_act) st =
    (* TODO: graph export *)
    match m_act st with
      | (NDactive a, st') ->
          prerr "NDactive";
          flush_all ();
          check_sat >>= begin function
            | `UNSAT ->
                failwith "NDactive found to be UNSATISFIABLE"
            | `SAT ->
                CS.string_of_solver >>= fun str ->
                return [(Active a, str, st')]
          end

      | (NDkilled r, st') ->
          prerr "NDkilled";
          flush_all ();
          CS.string_of_solver >>= fun str ->
          return [(Killed r, str, st')]

      | (NDnd (info, str_ms), st') ->
          (* let xx = Random.int 10000 in *)
          incr pad;
          (* let str = Printf.sprintf "%sNDnd[%s] <%d> <size: %d>\n" (String.make !pad ' ')
            (Driver.instance_Show_Show_Driver_step_kind_dict.show_method info)
            xx
            (List.length str_ms) in
          let str = if List.length str_ms > 1 then do_red str else str in
          prerr_string str;
          flush_all (); *)
          let ret = begin match exec_mode with
            | Random ->
                with_backtracking (fun (_, z) -> aux z st') str_ms
            | Exhaustive ->
                foldlM (fun acc (idx, (info, m_act)) ->
                  (* Printf.fprintf stderr "%s<%d>[%d] ==> %s\n" (String.make !pad ' ') xx idx
                    (Driver.instance_Show_Show_Driver_step_kind_dict.show_method info);
                  flush_all (); *)
                  (* with_constraints debug_str  *)
                  aux m_act st' >>= fun z ->
                  return (z @ acc)
                ) [] (List.mapi (fun n z -> (n, z)) str_ms)
(*
            | Interactive ->
                failwith "Smt2.runND: TODO interactive mode"
*)
          end in decr pad; ret
      | (NDguard (info, cs, m_act), st') ->
          (* Printf.fprintf stderr "%sNDguard[%s]\n" (String.make !pad ' ')
          (Driver.instance_Show_Show_Driver_step_kind_dict.show_method info);
          flush_all (); *)
          with_constraints info cs begin
            check_sat >>= function
              | `UNSAT ->
                  return [] (* backtrack *)
              | `SAT ->
                  aux m_act st'
          end
      | (NDbranch (info, cs, m_act1, m_act2), st') ->
          (* Printf.fprintf stderr "%sNDbranch[%s]\n"  (String.make !pad ' ')
          (Driver.instance_Show_Show_Driver_step_kind_dict.show_method info);
          flush_all (); *)
          begin match exec_mode with
(*
            | Some Interactive ->
                failwith "Smt2.runND: TODO interactive mode"
*)
            | Random ->
                with_backtracking (fun (cs, m_act) ->
                  with_constraints info cs begin
                    check_sat >>= function
                      | `UNSAT ->
                           return []
                      | `SAT ->
                          aux m_act st'
                end) [(cs, m_act1); (negate cs, m_act2)]
            | Exhaustive ->
                with_constraints info cs begin
                  check_sat >>= function
                    | `UNSAT ->
                         return []
                    | `SAT ->
                        aux m_act1 st'
                end >>= fun xs1 ->
                with_constraints info (negate cs) begin
                  check_sat >>= function
                    | `UNSAT ->
                        return []
                    | `SAT ->
                        aux m_act2 st'
                end >>= fun xs2 ->
                return (xs1 @ xs2)
                end
      | (NDstep (info, str_ms), st') ->
          (* Printf.fprintf stderr "%sNDstep[%s]\n" (String.make !pad ' ')
            (Driver.instance_Show_Show_Driver_step_kind_dict.show_method info);
          flush_all (); *)
          aux (ND (fun st -> NDnd (info, str_ms), st)) st'

  in let ret = runEff (aux m st0) in
  (* prerr "EXITING"; *)
  ret

