open Except
open Location
open PPrint
open Pp_tools


module StringMap = Map.Make(String)
module SymMap = Map.Make(Sym)

type t = 
  { sym_of_name : Sym.t StringMap.t;
    name_of_sym : string SymMap.t; 
    loc_of_sym : Location.t SymMap.t;
  }

let sym_of call_loc (string : string) (namemap : t) : (Sym.symbol,'e) m  = 
  match StringMap.find_opt string namemap.sym_of_name with
  | Some sym -> return sym
  | None -> 
     let err = withloc call_loc ((!^ "Unbound name") ^^^ (squotes (!^ string))) in
     Except.fail err

let name_of call_loc (sym : Sym.t) (namemap : t) : (string,'e) m  = 
  match SymMap.find_opt sym namemap.name_of_sym with
  | Some name -> return name
  | None -> 
     let err = withloc call_loc ((!^ "Unbound name") ^^^ (squotes (Sym.pp sym))) in
     Except.fail err

let loc_of call_loc (sym : Sym.t) (namemap : t) : (Location.t,'e) m  = 
  match SymMap.find_opt sym namemap.loc_of_sym with
  | Some loc -> return loc
  | None -> 
     let err = withloc call_loc ((!^ "Unbound name") ^^^ (squotes (Sym.pp sym))) in
     Except.fail err


let all_names m = StringMap.bindings m.sym_of_name

let empty = 
  { sym_of_name = StringMap.empty;
    name_of_sym = SymMap.empty; 
    loc_of_sym = SymMap.empty;
  }

let record (string : string) (sym : Sym.t) (loc : Location.t) namemap = 
  { sym_of_name = StringMap.add string sym namemap.sym_of_name;
    name_of_sym = SymMap.add sym string namemap.name_of_sym;
    loc_of_sym  = SymMap.add sym loc namemap.loc_of_sym }


