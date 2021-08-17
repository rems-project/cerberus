module Make (L : Local.S) = struct

  module State_and_exception =
    State_and_exception.Make(struct type e = TypeErrors.type_error type s = L.t end)

  include State_and_exception

  include Effectful.Make(State_and_exception)



  let pure (m : 'a t) : 'a t =
    let c s = 
      Z3.Solver.push (L.solver s);
      let outcome = match m.c s with
        | Ok (a, _) -> Ok (a, s)
        | Error e -> Error e
      in
      Z3.Solver.pop (L.solver s) 1;
      outcome
    in
    { c }




  let all_computational () = 
    let@ l = get () in
    return (L.all_computational l)

  let all_logical () = 
    let@ l = get () in
    return (L.all_logical l)

  let all_constraints () = 
    let@ l = get () in
    return (L.all_constraints l)

  let solver () =
    let@ l = get () in
    return (L.solver l)

  let all_resources () = 
    let@ l = get () in
    return (L.all_resources l)

  let descriptions () = 
    let@ l = get () in
    return (L.descriptions l)

  let bound s kind = 
    let@ l = get () in
    return (L.bound s kind l)

  let get_a s = 
    let@ l = get () in
    return (L.get_a s l)

  let get_l s = 
    let@ l = get () in
    return (L.get_l s l)

  let add_a s (bt, s') = 
    let@ l = get () in
    set (L.add_a s (bt, s') l)

  let add_l s ls =
    let@ l = get () in
    set (L.add_l s ls l)

  let add_c lc = 
    let@ l = get () in
    set (L.add_c lc l)

  let add_cs lcs = 
    let@ l = get () in
    set (L.add_cs lcs l)

  let add_r r = 
    let@ l = get () in
    set (L.add_r r l)

  let remove_resource re = 
    let@ l = get () in
    set (L.remove_resource re l)

  let map_and_fold_resources f acc =
    let@ l = get () in
    let (l', acc) = L.map_and_fold_resources f l acc in
    let@ () = set l' in
    return acc

  let add_description descr = 
    let@ l = get () in
    set (L.add_description descr l)

  let add_descriptions descrs = 
    let@ l = get () in
    set (L.add_descriptions descrs l)


  let all_vars () = 
    let@ l = get () in
    return (L.all_vars l)

  let bind s rt = 
    let@ l = get () in
    set (L.bind l s rt)

  let bind_logical rt = 
    let@ l = get () in
    set (L.bind_logical l rt)

  let bind_logically rt = 
    let@ l = get () in
    let ((bt, s), l') = L.bind_logically l rt in
    let@ () = set l' in
    return (bt, s)
    

end
