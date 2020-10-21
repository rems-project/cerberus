open Pp
module L = Local
module VB = VariableBinding
module SymSet = Set.Make(Sym)

type t = {
    local : Local.t;
    global : Global.t;
    consts : (Sym.t * string) list;
  }


let pp {local; global; consts} = 
  
  (* let a = 
   *   Local.filter (fun s b ->
   *       match Sym.named s, b with
   *       | true, Computational (ls, bt) -> Some (s, ls, bt)
   *       | _, _ -> None
   *     ) local
   * in
   * 
   * let ar =
   *   List.fold_left (fun acc (s, ls, bt) ->
   *       
   *     ) [] a
   * in *)


  Pp.flow_map (comma ^^ break 1) (fun (sym,s) -> 
      item (Sym.pp_string sym) !^s
    ) consts



           


