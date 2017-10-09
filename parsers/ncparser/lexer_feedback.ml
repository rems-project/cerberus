(* Created by Victor Gomes 2017-10-04 *)

(* Based on Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
   "A simple, possibly correct LR parser for C11" *)

module IdSet = Set.Make(String)

type context = IdSet.t

let current = ref IdSet.empty

let declare_typedefname id =
  current := IdSet.add id !current

let declare_varname id =
  current := IdSet.remove id !current

let is_typedefname id =
  IdSet.mem id !current

let save_context () = !current

let restore_context ctxt =
  current := ctxt

type decl_sort =
  | DeclId
  | DeclFun of context
  | DeclOther

type declarator =
  { id:      string;
    sort:    decl_sort;
    pointer: Cabs.pointer_declarator option;
    direct:  Cabs.direct_declarator;
  }

let identifier decl = decl.id

let cabs_of_declarator d = Cabs.Declarator (d.pointer, d.direct)

let cabs_of_declarator_option = function
  | Some d -> Some (cabs_of_declarator d)
  | None -> None

let pointer_decl pdecl d =
  { d with pointer= Some pdecl;
           sort=    DeclOther;
  }

let identifier_decl loc str =
  { id=      str;
    sort=    DeclId;
    pointer= None;
    direct=  Cabs.DDecl_identifier (Cabs.CabsIdentifier (loc, str));
  }

let declarator_decl d =
  { d with direct= Cabs.DDecl_declarator (cabs_of_declarator d);
           sort=   DeclOther;
  }

let array_decl arrdecl d =
  { d with direct= Cabs.DDecl_array (d.direct, arrdecl);
           sort=   DeclOther;
  }

let fun_decl ptys ctxt d =
  { d with direct= Cabs.DDecl_function (d.direct, ptys);
           sort=   DeclFun ctxt;
  }

let reinstall_function_context d =
  match d.sort with
  | DeclFun ctxt ->
    restore_context ctxt;
    declare_varname d.id
  | _ -> failwith "error lex_feedback"
