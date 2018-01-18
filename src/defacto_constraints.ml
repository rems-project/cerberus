module Make(CS: sig type t end) : Memory_model.Constraints = struct
  type t = CS.t

  let negate cs = assert false

  type 'a eff = 'a (*TODO*)
  let return _ = assert false
  let bind _ _ = assert false
  let foldlM _ _ _ = assert false
  
  let runEff _ = assert false
  
  let string_of_solver = assert false
  let check_sat = assert false
  
  let with_constraints _ _ _ = assert false
end
