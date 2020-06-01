open VarTypes

module RT = ReturnTypes
module FT = FunctionTypes

module NReturnTypes = struct

  type t = 
    { computational : (Sym.t * BaseTypes.t) list
    ; logical : (Sym.t * LogicalSorts.t) list
    ; resources : Resources.t list
    ; constraints : LogicalConstraints.t list
    }


  let i = 
    { computational = []
    ; logical = []
    ; resources = []
    ; constraints = [] 
    }


  let from_returntype rt = 
    let rec aux acc = function
      | RT.I -> acc
      | RT.Computational (name,bt,t) -> 
         aux {acc with computational = acc.computational@[(name,bt)]} t
      | RT.Logical (name,ls,t) -> 
         aux {acc with logical = acc.logical@[(name,ls)]} t
      | RT.Resource (re,t) -> 
         aux {acc with resources = acc.resources@[re]} t
      | RT.Constraint (lc,t) -> 
         aux {acc with constraints = acc.constraints@[lc]} t
    in
    aux i rt


  let to_returntype t = 
    let rec computational bs t = match bs with
      | [] -> t
      | (name,bt)::bs -> RT.Computational (name,bt,computational bs t) in
    let rec logical bs t = match bs with
      | [] -> t
      | (name,ls)::bs -> RT.Logical (name,ls,logical bs t) in
    let rec resources bs t = match bs with
      | [] -> t
      | re::bs -> RT.Resource (re,resources bs t) in
    let rec constraints bs t = match bs with
      | [] -> t
      | lc::bs -> RT.Constraint (lc,constraints bs t) in
    computational t.computational 
      (logical t.logical (resources t.resources (constraints t.constraints I)))


  let pp t = ReturnTypes.pp (to_returntype t)

  let subst_var s t = 
    { computational = 
        List.map (fun (n,bt) -> (Sym.subst s n, BT.subst_var s bt)) t.computational
    ; logical = 
        List.map (fun (n,ls) -> (Sym.subst s n, LS.subst_var s ls)) t.logical
    ; resources = 
        List.map (fun re -> RE.subst_var s re) t.resources
    ; constraints = 
        List.map (fun lc -> (LC.subst_var s lc)) t.constraints
    }

  let subst_vars = Subst.make_substs subst_var

end


module NFunctionTypes = struct

  type arguments = 
    { computational : (Sym.t * BaseTypes.t) list
    ; logical : (Sym.t * LogicalSorts.t) list
    ; resources : Resources.t list
    ; constraints : LogicalConstraints.t list
    }

  type t = {n_arguments : arguments; n_return : RT.t}


  let from_functiontype t = 
    let rec aux acc = function
      | FT.Return rt -> {n_arguments = acc; n_return = rt}
      | FT.Computational (name,bt,t) -> 
         aux {acc with computational = acc.computational@[(name,bt)]} t
      | FT.Logical (name,ls,t) -> 
         aux {acc with logical = acc.logical@[(name,ls)]} t
      | FT.Resource (re,t) -> 
         aux {acc with resources = acc.resources@[re]} t
      | FT.Constraint (lc,t) -> 
         aux {acc with constraints = acc.constraints@[lc]} t
    in
    aux { computational = []
        ; logical = []
        ; resources = []
        ; constraints = [] 
        } t


  let to_functiontype (ft : t)  = 
    List.fold_right (fun (name,t) ft -> FT.Computational (name,t,ft)) 
      ft.n_arguments.computational
      (List.fold_right (fun (name,t) ft -> FT.Logical (name,t,ft)) 
         ft.n_arguments.logical
         (List.fold_right (fun t ft -> FT.Resource (t,ft)) 
            ft.n_arguments.resources
            (List.fold_right (fun t ft -> FT.Constraint (t,ft)) 
               ft.n_arguments.constraints
               (FT.Return ft.n_return))))



  let pp t = FunctionTypes.pp (to_functiontype t)

  let subst_var s t = 
    { n_arguments = 
        { computational = 
            List.map (fun (n,bt) -> (Sym.subst s n, BT.subst_var s bt)) 
              t.n_arguments.computational
        ; logical = 
            List.map (fun (n,ls) -> (Sym.subst s n, LS.subst_var s ls)) 
              t.n_arguments.logical
        ; resources = 
            List.map (fun re -> RE.subst_var s re) 
              t.n_arguments.resources
        ; constraints = 
            List.map (fun lc -> (LC.subst_var s lc)) 
              t.n_arguments.constraints
        }
    ; n_return = ReturnTypes.subst_var s t.n_return
    }
      
  let subst_vars = Subst.make_substs subst_var

  let updateAargs ft t = 
    { ft with n_arguments = { ft.n_arguments with computational = t }}

  let updateLargs ft t = 
    { ft with n_arguments = { ft.n_arguments with logical = t }}

  let updateRargs ft t = 
    { ft with n_arguments = { ft.n_arguments with resources = t }}

  let updateCargs ft t = 
    { ft with n_arguments = { ft.n_arguments with constraints = t }}


end
