open List
open Utils
open Cerb_frontend
open Core 
open Mucore
open Except
open Nat_big_num
open Sexplib
open Printf
open Sym
open Uni
open Pp_tools
module Loc = Location
open LogicalConstraints
open Resources
open IndexTerms
open BaseTypes


module SymSet = Set.Make(Sym)



module VarTypes = struct

  type t = 
    | A of BaseTypes.t
    | L of LogicalSorts.t
    | R of Resources.t
    | C of LogicalConstraints.t

  let subst sym with_it t = 
    match t with
    | A t -> A (BaseTypes.subst sym with_it t)
    | L t -> L (LogicalSorts.subst sym with_it t)
    | R t -> R (Resources.subst sym with_it t)
    | C t -> C (LogicalConstraints.subst sym with_it t)

   type kind = 
     | Argument
     | Logical
     | Resource
     | Constraint
 
   let kind_of_t = function
     | A _  -> Argument
     | L _  -> Logical
     | R _  -> Resource
     | C _  -> Constraint
 
   let pp_kind = function
     | Argument  -> "computational"
     | Logical  -> "logical"
     | Resource  -> "resource"
     | Constraint  -> "constraint"
 
end


module Binders = struct

  type t = {name: Sym.t; bound: VarTypes.t}


  let pp {name;bound} = 
    match bound with
    | A t -> 
       sprintf "(A %s : %s)" (Sym.pp name) (BaseTypes.pp t)
    | L t  -> 
       sprintf "(L %s : %s)" (Sym.pp name) (LogicalSorts.pp t)
    | R t -> 
       sprintf "(R %s : %s)" (Sym.pp name) (Resources.pp t)
    | C t -> 
       sprintf "(C %s : %s)" (Sym.pp name) (LogicalConstraints.pp t)


  let parse_sexp loc (names : namemap) s = 
    match s with
    | Sexp.List [Sexp.Atom id; Sexp.Atom ":"; t] ->
       let name = Sym.fresh_pretty id in
       let names = StringMap.add id (name,loc) names in
       BaseTypes.parse_sexp loc names t >>= fun t ->
       return ({name; bound = A t}, names)
    | Sexp.List [Sexp.Atom "Logical"; Sexp.Atom id; Sexp.Atom ":"; ls] ->
       let name = Sym.fresh_pretty id in
       let names = StringMap.add id (name,loc) names in
       LogicalSorts.parse_sexp loc names ls >>= fun t ->
       return ({name; bound = L t}, names)
    | Sexp.List [Sexp.Atom "Resource"; Sexp.Atom id; Sexp.Atom ":"; re] ->
       let name = Sym.fresh_pretty id in
       let names = StringMap.add id (name,loc) names in
       Resources.parse_sexp loc names re >>= fun t ->
       return ({name; bound = R t}, names)
    | Sexp.List [Sexp.Atom "Constraint"; Sexp.Atom id; Sexp.Atom ":"; lc] ->
       let name = Sym.fresh_pretty id in
       let names = StringMap.add id (name,loc) names in
       LogicalConstraints.parse_sexp loc names lc >>= fun t ->
       return ({name; bound = C t}, names)
    | t -> 
       parse_error "binders" t loc

      let subst sym with_it b = 
        { name = sym_subst sym with_it b.name;
          bound = VarTypes.subst sym with_it b.bound }
        

end


module Types = struct

  type t = Binders.t list

  let pp ts = 
    String.concat " , " (map Binders.pp ts)

  let parse_sexp loc (names : namemap) s = 
    let rec aux (names : namemap) acc ts = 
      match ts with
      | [] -> return (rev acc, names)
      | b :: bs ->
         Binders.parse_sexp loc names b >>= fun (b, names) ->
         aux names (b :: acc) bs
    in
    match s with
    | Sexp.List ts -> aux names [] ts
    | t -> parse_error "binders" t loc

  let subst sym with_sym bs = 
    map (Binders.subst sym with_sym) bs

  let names t = List.map (fun {Binders.name; _} -> name) t

  let rename newname t = 
    match t with
    | [] -> print_endline "\n\nempty return type\n\n"; []
    | {Binders.name; _} :: _ ->
       subst name newname t

end


module FunctionTypes = struct

  type t = F of {arguments: Types.t;return: Types.t}

  let subst sym sym' (F t) = 
    F { arguments = Types.subst sym sym' t.arguments;
        return = Types.subst sym sym' t.return }

  let pp (F t) = 
    sprintf "%s -> %s" (Types.pp t.arguments) (Types.pp t.return)
end

open FunctionTypes
open VarTypes
open Binders
open Types
      

module UU = struct

  type u = 
    | Undefined of Loc.t * Undefined.undefined_behaviour
    | Unspecified of Loc.t (* * Ctype.ctype *)

  type 'a or_u = 
    | Normal of 'a
    | Bad of u

  type ut = Types.t or_u

  let rec all_normal : ('a or_u) list -> ('a list) or_u = function
    | [] -> Normal []
    | Bad u :: _ -> Bad u
    | Normal a :: rest -> 
       match all_normal rest with
       | Normal rest -> Normal (a :: rest)
       | Bad b -> Bad b

end

open UU



module Err = struct

  type call_return_switch_error = 
    | Surplus_A of Sym.t * BaseTypes.t
    | Surplus_L of Sym.t * LogicalSorts.t
    | Surplus_R of Sym.t * Resources.t
    | Missing_A of Sym.t * BaseTypes.t
    | Missing_L of Sym.t * LogicalSorts.t
    | Missing_R of Sym.t * Resources.t
    | Mismatch of { mname: Sym.t option; has: VarTypes.t; expected: VarTypes.t; }
    | Unsat_constraint of Sym.t * LogicalConstraints.t
    | Unconstrained_l of Sym.t * LogicalSorts.t

  type type_error = 
    | Var_kind_error of {
        loc : Loc.t;
        sym: Sym.t;
        expected : VarTypes.kind;
        has : VarTypes.kind;
      }
    | Name_bound_twice of {
        loc : Loc.t;
        name: Sym.t
      }
    | Unreachable of {
        loc: Loc.t;
        unreachable : string;
      }
    | Illtyped_it of {
        loc: Loc.t;
        it: IndexTerms.t;
      }
    | Unsupported of { 
        loc: Loc.t;
        unsupported: string; 
      }
    | Unbound_name of {
        loc: Loc.t; 
        is_function: bool;
        unbound: Sym.t;
      }
    | Inconsistent_fundef of {
        loc: Loc.t;
        decl: FunctionTypes.t;
        defn: FunctionTypes.t;
      }
    | Variadic_function of {
        loc: Loc.t;
        fn: Sym.t;
      }
    | Return_error of 
        Loc.t * call_return_switch_error
    | Call_error of 
        Loc.t * call_return_switch_error
    | Switch_error of 
        Loc.t * call_return_switch_error
    | Integer_value_error of 
        Loc.t
    | Undefined_behaviour of
        Loc.t * Undefined.undefined_behaviour
    | Unspecified_value of
        Loc.t
    | Generic_error of Loc.t * string

  let pp_return_error loc = function
    | Surplus_A (_name,t) ->
       sprintf "Line %s. Returning unexpected value of type %s" 
         (Loc.pp loc) (BaseTypes.pp t)
    | Surplus_L (_name,t) ->
       sprintf "%s. Returning unexpected logical value of type %s" 
         (Loc.pp loc) (LogicalSorts.pp t)
    | Surplus_R (_name,t) ->
       sprintf "%s. Returning unexpected resource of type %s" 
         (Loc.pp loc) (Resources.pp t)
    | Missing_A (_name,t) ->
       sprintf "%s. Missing return value of type %s" 
         (Loc.pp loc) (BaseTypes.pp t)
    | Missing_L (_name,t) ->
       sprintf "%s. MIssing logical return value of type %s" 
         (Loc.pp loc) (LogicalSorts.pp t)
    | Missing_R (_name,t) ->
       sprintf "%s. Missing return resource of type %s" 
         (Loc.pp loc) (Resources.pp t)
    | Mismatch {mname; has; expected} ->
       let has_pp = match has with
         | A t -> sprintf "return value of type %s" (BaseTypes.pp t)
         | L t -> sprintf "logical return value of type %s" (LogicalSorts.pp t)
         | R t -> sprintf "return resource of type %s" (Resources.pp t)
         | C t -> sprintf "return constraint %s" (LogicalConstraints.pp t)
       in
       begin match expected with
       | A t ->
          sprintf "%s. Expected return value of type %s but found %s" 
            (Loc.pp loc) (BaseTypes.pp t) has_pp
       | L t ->
          sprintf "%s. Expected logical return value of type %s but found %s" 
            (Loc.pp loc) (LogicalSorts.pp t) has_pp
       | R t ->
          sprintf "%s. Expected return resource of type %s but found %s" 
            (Loc.pp loc) (Resources.pp t) has_pp
       | C t ->
          (* dead, I think *)
          sprintf "%s. Expected return constraint %s but found %s" 
            (Loc.pp loc) (LogicalConstraints.pp t) has_pp
       end
    | Unsat_constraint (name,c) ->
       sprintf "%s. Unsatisfied return constraint %s: %s" 
         (Loc.pp loc) (Sym.pp name) (LogicalConstraints.pp c)
    | Unconstrained_l (name, ls) ->
       sprintf "%s. Unconstrained logical variable %s: %s" 
         (Loc.pp loc) (Sym.pp name) (LogicalSorts.pp ls)
    

  let pp_call_error loc = function
    | Surplus_A (_name,t) ->
       sprintf "Line %s. Supplying unexpected argument of type %s" 
         (Loc.pp loc) (BaseTypes.pp t)
    | Surplus_L (_name,t) ->
       sprintf "%s. Supplying unexpected logical argument of type %s" 
         (Loc.pp loc) (LogicalSorts.pp t)
    | Surplus_R (_name,t) ->
       sprintf "%s. Supplying unexpected resource of type %s" 
         (Loc.pp loc) (Resources.pp t)
    | Missing_A (_name,t) ->
       sprintf "%s. Missing argument of type %s" 
         (Loc.pp loc) (BaseTypes.pp t)
    | Missing_L (_name,t) ->
       sprintf "%s. Missing logical argument of type %s" 
         (Loc.pp loc) (LogicalSorts.pp t)
    | Missing_R (_name,t) ->
       sprintf "%s. Missing resource argument of type %s" 
         (Loc.pp loc) (Resources.pp t)
    | Mismatch {mname; has; expected} ->
       let has_pp = match has with
         | A t -> sprintf "argument of type %s" (BaseTypes.pp t)
         | L t -> sprintf "logical argument of type %s" (LogicalSorts.pp t)
         | R t -> sprintf "resource argument of type %s" (Resources.pp t)
         | C t -> sprintf "constraint argument %s" (LogicalConstraints.pp t)
       in
       begin match expected with
       | A t ->
          sprintf "%s. Expected argument of type %s but found %s" 
            (Loc.pp loc) (BaseTypes.pp t) has_pp
       | L t ->
          sprintf "%s. Expected logical argument of type %s but found %s" 
            (Loc.pp loc) (LogicalSorts.pp t) has_pp
       | R t ->
          sprintf "%s. Expected resource argument of type %s but found %s" 
            (Loc.pp loc) (Resources.pp t) has_pp
       | C t ->
          (* dead, I think *)
          sprintf "%s. Expected constraint argument %s but found %s" 
            (Loc.pp loc) (LogicalConstraints.pp t) has_pp
       end
    | Unsat_constraint (name,lc) ->
       sprintf "%s. Unsatisfied return constraint %s: %s" 
         (Loc.pp loc) (Sym.pp name) (LogicalConstraints.pp lc)
    | Unconstrained_l (name,ls) ->
       sprintf "%s. Unconstrained logical variable %s: %s" 
         (Loc.pp loc) (Sym.pp name) (LogicalSorts.pp ls)

  let pp = function 
    | Var_kind_error err ->
       sprintf "%s. Expected kind %s but found kind %s"
         (Loc.pp err.loc) (VarTypes.pp_kind err.expected) (VarTypes.pp_kind err.has)
    | Name_bound_twice err ->
       sprintf "%s. Name bound twice: %s" 
         (Loc.pp err.loc) (Sym.pp err.name)
    | Generic_error (loc, err) ->
       sprintf "%s. %s" 
         (Loc.pp loc) err
    | Unreachable {loc; unreachable} ->
       sprintf "%s. Should be unreachable: %s" 
         (Loc.pp loc) unreachable
    | Illtyped_it {loc; it} ->
       sprintf "%s. Illtyped index term: %s" 
         (Loc.pp loc) (IndexTerms.pp it)
    | Unsupported {loc; unsupported} ->
       sprintf "%s. Unsupported feature: %s" 
         (Loc.pp loc) unsupported
    | Unbound_name {loc; is_function; unbound} ->
       sprintf "%s. Unbound %s %s"
         (Loc.pp loc) (if is_function then "function" else "symbol") (Sym.pp unbound)
    | Inconsistent_fundef {loc; decl; defn} ->
       sprintf "%s. Function definition inconsistent. Should be %s, is %s"
         (Loc.pp loc) (FunctionTypes.pp decl) (FunctionTypes.pp defn)
    | Variadic_function {loc; fn } ->
       sprintf "Line %s. Variadic functions unsupported (%s)" 
         (Loc.pp loc) (Sym.pp fn)
    | Return_error (loc, err) -> 
       pp_return_error loc err
    | Call_error (loc, err) -> 
       pp_call_error loc err
    | Switch_error (loc, err) -> 
       pp_call_error loc err
    | Integer_value_error loc ->
       sprintf "%s. integer_value_to_num return None"
         (Loc.pp loc)
    | Undefined_behaviour (loc, undef) ->
       sprintf "%s. Undefined behaviour: %s"
         (Loc.pp loc)
         (Undefined.pretty_string_of_undefined_behaviour undef)
    | Unspecified_value loc ->
       sprintf "%s. Unspecified value"
         (Loc.pp loc)




end

open Err



module GEnv = struct 

  type t = 
    { struct_decls : Types.t SymMap.t ; 
      fun_decls : (Loc.t * FunctionTypes.t * Sym.t) SymMap.t; (* third item is return name *)
      names : namemap
    } 
  type genv = t


  let empty = 
    { struct_decls = SymMap.empty; 
      fun_decls = SymMap.empty;
      names = StringMap.empty }

  let pp_struct_decls decls = 
    let pp_entry (sym, bs) = sprintf "%s: %s" (Sym.pp sym) (Types.pp bs) in
    pp_list pp_entry "\n" (SymMap.bindings decls)

  let pp_fun_decls decls = 
    let pp_entry (sym, (_, t, _ret)) = sprintf "%s: %s" (Sym.pp sym) (FunctionTypes.pp t) in
    pp_list pp_entry "\n" (SymMap.bindings decls)

  let pp_name_map m = 
    let pp_entry (name,(sym,_)) = sprintf "%s: %s" name (Sym.pp sym) in
    pp_list pp_entry "\n" (StringMap.bindings m)

  let pp genv = 
    lines 
      [ h2 "Structs"
      ; pp_struct_decls genv.struct_decls
      ; ""
      ; h2 "Functions"
      ; pp_fun_decls genv.fun_decls
      ; ""
      ; h2 "Names"
      ; pp_name_map genv.names
      ; ""
      ]

end

module LEnv = struct
  type t = { vars : VarTypes.t SymMap.t }
  type lenv = t
  let empty = { vars = SymMap.empty }

  let pp_vars decls = 
    let pp_entry (sym, t) = Binders.pp {name = sym; bound = t} in
    pp_list pp_entry ", " (SymMap.bindings decls)

  let pp_rmap decls = 
    let pp_entry (sym, sym2) = sprintf "(%s,%s)" (Sym.pp sym) (Sym.pp sym2) in
    pp_list pp_entry ", " (SymMap.bindings decls)

  let pp lenv = 
    sprintf "%s" (pp_vars lenv.vars)

end

module Env = struct


  type t = 
    { local : LEnv.t ; 
      global : GEnv.t }

  type env = t

  let empty = 
    { local = LEnv.empty; 
      global = GEnv.empty }

  let with_fresh_local genv = 
    { global = genv; 
      local = LEnv.empty }

  let add_var (env : t) (sym, t) = 
    { env with local = { vars = SymMap.add sym t env.local.vars } }

  let add_vars env bindings = 
    fold_left add_var env bindings

  let remove_var env sym = 
    let vars = SymMap.remove sym env.local.vars in
    { env with local = {vars} }

  let remove_vars env bindings = 
    fold_left remove_var env bindings

  let add_rt env rt = 
    fold_left (fun env b -> add_var env (b.name, b.bound)) env rt

  let add_Avar env (sym, t) = add_var env (sym, VarTypes.A t)
  let add_Lvar env (sym, t) = add_var env (sym, VarTypes.L t)
  let add_Rvar env (sym, t) = add_var env (sym, VarTypes.R t)
  let add_Cvar env (sym, t) = add_var env (sym, VarTypes.C t)

  let add_Avars env vars = List.fold_left add_Avar env vars

  let lookup ?is_function:(is_function=false) (loc : Loc.t) (env: 'v SymMap.t) (name: Sym.t) =
    match SymMap.find_opt name env with
    | None -> fail (Unbound_name {loc; is_function; unbound = name})
    | Some v -> return v

  let get_var (loc : Loc.t) (env: t) (name: Sym.t) =
    lookup loc env.local.vars name >>= function
    | VarTypes.A t -> return (`A t)
    | VarTypes.L t -> return (`L t)
    | VarTypes.R t -> return (`R (t, remove_var env name))
    | VarTypes.C t -> return (`C t)


  let kind = function
    | `A _ -> VarTypes.Argument
    | `L _ -> VarTypes.Logical
    | `R _ -> VarTypes.Resource
    | `C _ -> VarTypes.Constraint

  let get_Avar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | `A t -> return t
    | t -> fail (Var_kind_error {loc; sym; expected = VarTypes.Argument; has = kind t})

  let get_Lvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | `L t -> return t
    | t -> fail (Var_kind_error {loc; sym; expected = VarTypes.Logical; has = kind t})

  let get_Rvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | `R (t, env) -> return (t, env)
    | t -> fail (Var_kind_error {loc; sym; expected = VarTypes.Resource; has = kind t})

  let get_Cvar (loc : Loc.t) (env: env) (sym: Sym.t) = 
    get_var loc env sym >>= function
    | `C t -> return t
    | t -> fail (Var_kind_error {loc; sym; expected = VarTypes.Constraint; has = kind t})

  let get_owned_resource loc env owner_sym = 
    let relevant = 
      SymMap.fold (fun name b acc ->
          match b with
          | (R t) -> if Resources.owner t = owner_sym then (name,t) :: acc else acc
          | _ -> acc
        ) env.local.vars []
    in
    match relevant with
    | [] -> return None
    | [owned] -> return (Some owned)
    | _ -> fail (Unreachable {loc; unreachable = "multiple owners of resource"})

end

open Env



let rec recursively_owned_resources loc env owner_sym = 
  get_owned_resource loc env owner_sym >>= function
  | Some (res,t) -> 
     let owned = Resources.owned t in
     mapM (recursively_owned_resources loc env) owned >>= fun owneds ->
     return (res :: concat owneds)
  | None -> 
     return []




let rec infer_it loc env it = 
  match it with
  | Num _ -> return BaseTypes.Int
  | Bool _ -> return BaseTypes.Bool

  | Add (it,it')
  | Sub (it,it')
  | Mul (it,it')
  | Div (it,it')
  | Exp (it,it')
  | App (it,it')
  | Rem_t (it,it')
  | Rem_f (it,it') ->
     check_it loc env it BaseTypes.Int >>
     check_it loc env it' BaseTypes.Int >>
     return BaseTypes.Int

  | EQ (it,it')
  | NE (it,it')
  | LT (it,it')
  | GT (it,it')
  | LE (it,it')
  | GE (it,it') ->
     check_it loc env it BaseTypes.Int >>
     check_it loc env it' BaseTypes.Int >>
     return BaseTypes.Bool

  | Null it ->
     check_it loc env it BaseTypes.Loc >>
     return BaseTypes.Bool

  | And (it,it')
  | Or (it,it') ->
     check_it loc env it BaseTypes.Int >>
     check_it loc env it' BaseTypes.Int >>
     return BaseTypes.Bool

  | Not it ->
     check_it loc env it BaseTypes.Bool >>
     return BaseTypes.Bool

  | List (it, its) ->
     infer_it loc env it >>= fun bt ->
     check_it loc env it bt >>
     return (List bt)

  | S sym ->
     get_var loc env sym >>= function
     | `A t -> return t
     | `L (LogicalSorts.Base t) -> return t
     | `R _ -> fail (Illtyped_it {loc; it})
     | `C _ -> fail (Illtyped_it {loc; it})


and check_it loc env it bt =
  infer_it loc env it >>= fun bt' ->
  if bt = bt' then return ()
  else fail (Illtyped_it {loc; it})

and check_its loc env its bt = 
  match its with
  | [] -> return ()
  | it :: its -> 
     check_it loc env it bt >>
     check_its loc env its bt




let constraint_holds env loc (LC c) = 
  true                          (* todo: call z3 *)

let is_unreachable env loc =
  constraint_holds env loc (LC (Bool false))


let rec constraints_hold loc env = function
  | [] -> return ()
  | (n, t) :: constrs ->
     if constraint_holds loc env t 
     then constraints_hold loc env constrs
     else fail (Call_error (loc, (Unsat_constraint (n, t))))




let subtype loc env rt1 rt2 = 

  let open Binders in

  let rec check env rt1 rt2 =
    match rt1, rt2 with
    | [], [] -> 
       return env
    | {name; bound = A r1} :: _, [] -> 
       fail (Return_error (loc, Surplus_A (name, r1)))
    | {name; bound = L r1} :: _, [] -> 
       fail (Return_error (loc, Surplus_L (name, r1)))
    | {name; bound = R r1} :: _, [] -> 
       fail (Return_error (loc, Surplus_R (name, r1)))

    | [], {name; bound = A r2} :: _ -> 
       fail (Return_error (loc, Missing_A (name, r2)))
    | [], {name; bound = L r2} :: _ -> 
       fail (Return_error (loc, Missing_L (name, r2)))
    | [], {name; bound = R r2} :: _ -> 
       fail (Return_error (loc, Missing_R (name, r2)))
    | {name; bound = C c1} :: rt1', _ ->
       check (add_var env (name,C c1)) rt1' rt2
    | _, {name = n2; bound = C c2} :: rt2' ->
       if constraint_holds loc env c2 
       then check env rt1 rt2'
       else fail (Return_error (loc, Unsat_constraint (n2, c2)))
    | (r1 :: rt1), (r2 :: rt2) ->
       match r1, r2 with
       | {name = n1; bound = A t1}, {name = n2; bound = VarTypes.A t2} 
            when BaseTypes.type_equal t1 t2 ->
          check (add_var env (n1, A t1)) rt1 (Types.subst n2 n1 rt2)
       | {name = n1; bound = L t1}, {name = n2; bound = L t2} 
            when LogicalSorts.type_equal t1 t2 ->
          check (add_var env (n1, L t1)) rt1 (Types.subst n2 n1 rt2)
       | {name = n1; bound = R t1}, {name = n2; bound = R t2} 
            when Resources.type_equal env t1 t2 ->
          check env rt1 rt2
       | _, _ ->
          let msm = Mismatch {mname = Some r1.name; 
                              has = r1.bound; 
                              expected = r2.bound} in
          fail (Return_error (loc, msm))
  in

  check env rt1 rt2






let rec bt_of_core_base_type loc cbt : (BaseTypes.t, type_error) m = 

  let bt_of_core_object_type loc = function
    | OTy_integer -> 
       return BaseTypes.Int
    | OTy_pointer -> 
       return BaseTypes.Loc
    | OTy_array cbt -> 
       return BaseTypes.Array
    | OTy_struct sym -> 
       return (Struct sym)
    | OTy_union _sym -> 
       failwith "todo: union types"

    | OTy_floating -> 
       fail (Unsupported {loc; unsupported = "float"})
  in

  match cbt with
  | Core.BTy_unit -> 
     return BaseTypes.Unit
  | Core.BTy_boolean -> 
     return BaseTypes.Bool
  | Core.BTy_list bt -> 
     bt_of_core_base_type loc bt >>= fun bt ->
     return (BaseTypes.List bt)
  | Core.BTy_tuple bts -> 
     mapM (bt_of_core_base_type loc) bts >>= fun bts ->
     return (BaseTypes.Tuple bts)
  | Core.BTy_object ot -> 
     bt_of_core_object_type loc ot
  | Core.BTy_loaded ot -> 
     bt_of_core_object_type loc ot

  | Core.BTy_storable -> 
     fail (Unsupported {loc; unsupported = "BTy_storable"})
  | Core.BTy_ctype -> 
     fail (Unsupported {loc; unsupported = "ctype"})




(* according to https://en.wikipedia.org/wiki/C_data_types *)
(* and *)
(* https://en.wikibooks.org/wiki/C_Programming/stdint.h#Exact-width_integer_types *)
let integerBaseType name signed ibt =

  let make f t = 
    let ft = Num (of_string f) in
    let tt = Num (of_string t) in
    let constr = LC ((S name %>= ft) %& (S name %<= tt)) in
    let l = [] in
    let r = [] in
    let c = [{name = fresh (); bound = C constr}] in
    ((name,Int), l, r, c)
  in

  match signed, ibt with
  | true,  Ctype.Ichar     -> make "-127" "127"
  | true,  Ctype.IntN_t 8  -> make "-127" "127"
  | true,  Ctype.Short     -> make "-32767" "32767"
  | true,  Ctype.Int_      -> make "-32767" "32767"
  | true,  Ctype.IntN_t 16 -> make "-32768" "32767"
  | true,  Ctype.Long      -> make "-2147483647" "2147483647"
  | true,  Ctype.LongLong  -> make "-9223372036854775807" "9223372036854775807"
  | true,  Ctype.IntN_t 32 -> make "-2147483648" "2147483647"
  | true,  Ctype.IntN_t 64 -> make "-9223372036854775808" "9223372036854775807"
  | false, Ctype.Ichar     -> make "0" "255"
  | false, Ctype.Short     -> make "0" "65535"
  | false, Ctype.Int_      -> make "0" "65535"
  | false, Ctype.Long      -> make "0" "4294967295"
  | false, Ctype.LongLong  -> make "0" "18446744073709551615"
  | false, Ctype.IntN_t 8  -> make "0" "255"
  | false, Ctype.IntN_t 16 -> make "0" "65535"
  | false, Ctype.IntN_t 32 -> make "0" "4294967295"
  | false, Ctype.IntN_t 64 -> make "0" "18446744073709551615"

  | _, Ctype.IntN_t n       -> failwith (sprintf "UIntN_t %d" n)
  | _, Ctype.Int_leastN_t n -> failwith "todo standard library types"
  | _, Ctype.Int_fastN_t n  -> failwith "todo standard library types"
  | _, Ctype.Intmax_t       -> failwith "todo standard library types"
  | _, Ctype.Intptr_t       -> failwith "todo standard library types"


let integerType name it =
  match it with
  | Ctype.Bool -> ((name, Bool), [], [], [])
  | Ctype.Signed ibt -> integerBaseType name true ibt
  | Ctype.Unsigned ibt -> integerBaseType name false ibt
  | Ctype.Char -> failwith "todo char"
  | Ctype.Enum _sym -> failwith "todo enum"
  | Ctype.Wchar_t -> failwith "todo wchar_t"
  | Ctype.Wint_t ->failwith "todo wint_t"
  | Ctype.Size_t -> failwith "todo size_t"
  | Ctype.Ptrdiff_t -> failwith "todo standard library types"


let rec ctype_aux name (Ctype.Ctype (annots, ct)) =
  match ct with
  | Ctype.Void -> (* check *)
     return ((name,Unit), [], [], [])
  | Ctype.Basic (Integer it) -> 
     return (integerType name it)
  | Ctype.Array (ct, _maybe_integer) -> 
     return ((name,Array),[],[],[])
  | Ctype.Pointer (_qualifiers, ct) ->
     ctype_aux (fresh ()) ct >>= fun ((pointee_name,bt),l,r,c) ->
     let res = R (Points (S name, S pointee_name)) in
     let r = {name = fresh (); bound = res} :: r in
     let l = {name = pointee_name; bound = L (Base bt)} :: l in
     return ((name,Loc),l,r,c)
  | Ctype.Atomic ct ->              (* check *)
     ctype_aux name ct
  | Ctype.Struct sym -> 
     return ((name, Struct sym),[],[],[])
  | Ctype.Union sym ->
     failwith "todo: union types"
  | Ctype.Basic (Floating _) -> 
     fail (Unsupported {loc = Annot.get_loc_ annots; unsupported = "floats"} )
  | Ctype.Function _ -> 
     fail (Unsupported {loc = Annot.get_loc_ annots; unsupported = "function pointers"}) 


let ctype (name : Sym.t) (ct : Ctype.ctype) =
  ctype_aux name ct >>= fun ((name,bt), l,r,c) ->
  return ({name;bound = A bt} :: l @ r @ c)

let make_pointer_ctype ct = 
  (* fix *)
  let q = {Ctype.const = false; Ctype.restrict = false; Ctype.volatile = false} in
  Ctype.Ctype ([], Ctype.Pointer (q, ct))




let remove_logical t = 
  List.filter_map (function {name; bound = L _} -> None | b -> Some b) t
let only_resources t = 
  List.filter_map (function ({name; bound = R _} as b) -> Some b | _ -> None) t



let make_create_type ct : (FunctionTypes.t,'e) m = 
  let arguments = [{name = fresh (); bound = A Int}] in
  ctype (fresh ()) (make_pointer_ctype ct) >>= fun rt ->
  let ftyp = FunctionTypes.F {arguments; return = rt} in
  return ftyp


let make_load_type ct : (FunctionTypes.t,'e) m = 
  let pointer_name = fresh () in
  ctype_aux (fresh ()) ct >>= fun ((pointee_name,bt),l,r,c) ->
  let addr_argument = 
    let a = {name = pointer_name; bound = A Loc} in
    let l = {name = pointee_name; bound = L (Base bt)} :: l in
    let r = {name = fresh (); bound = R (Points (S pointer_name, S pointee_name))} :: r in
    a :: l @ r @ c
  in
  let ret = {name = pointee_name; bound = A bt} :: r in
  let ftyp = FunctionTypes.F {arguments = addr_argument; return = ret} in
  return ftyp

let make_store_type ct : (FunctionTypes.t,'e) m = 
  let pointer_name = fresh () in
  ctype pointer_name (make_pointer_ctype ct) >>= fun address ->
  begin 
    ctype_aux (fresh ()) ct >>= fun ((value_name,bt),l,r,c) ->
    let value = {name = value_name; bound = A bt} :: l @ r @ c in
    let ret = 
      {name = fresh (); bound = A Unit} ::
      {name = fresh (); bound = R (Points (S pointer_name, S value_name))} :: r
    in
    return (value,ret)
  end >>= fun (value,ret) ->
  let ftyp = FunctionTypes.F {arguments = address @ value; return = ret} in
  return ftyp


let sym_or_fresh (msym : Sym.t option) : Sym.t = 
  match msym with
  | Some sym -> sym
  | None -> Sym.fresh ()



let ensure_type loc mname has expected : (unit, type_error) m = 
  if BaseTypes.type_equal has expected 
  then return ()
  else fail (Call_error (loc, Mismatch {mname; has; expected}))


let args_same_typ (mtyp : BaseTypes.t option) (args_bts : (BaseTypes.t * Loc.t) list) =
  fold_leftM (fun mt (bt,loc) ->
      match mt with
      | None -> return (Some bt)
      | Some t -> 
         ensure_type loc None (A bt) (A t) >>
         return (Some t)
    ) mtyp args_bts


let make_Aargs_bts env tsyms = 
  mapM (fun tsym ->
      let (sym, loc) = lof_a tsym in
      get_Avar loc env sym >>= fun t ->
      return (t, loc)) tsyms



let infer_object_value (env : env) loc ov = 

  let integer_value_to_num loc iv = 
    of_maybe (Integer_value_error loc) 
      (Impl_mem.eval_integer_value iv)
  in

  let name = fresh () in

  match ov with
  | M_OVinteger iv ->
     integer_value_to_num loc iv >>= fun i ->
     let t = {name; bound = A Int} in
     let constr = {name = fresh (); bound = C (LC (S name %= Num i))} in
     return (Normal [t; constr])
  | M_OVpointer p ->
     Impl_mem.case_ptrval p
       ( fun _cbt -> 
         let t = {name; bound = A Loc} in
         let constr = {name = fresh (); bound = C (LC (Null (S name)))} in
         return (Normal [t; constr]) )
       ( fun sym -> 
         fail (Unsupported {loc; unsupported = "function pointers"}) )
       ( fun _prov loc ->
         let t = {name; bound = A Loc} in
         let constr = {name = fresh (); bound = C (LC (S name %= Num loc))} in
         return (Normal [t; constr]) )
       ( fun () -> return (Bad (Unspecified loc)) )
  | M_OVarray items ->
     make_Aargs_bts env items >>= fun args_bts ->
     args_same_typ None args_bts >>
     return (Normal [{name; bound = A Array}])
  | M_OVstruct (sym, fields) ->
     failwith "todo: struct"
  | M_OVunion _ -> 
     failwith "todo: union types"

  | M_OVfloating iv ->
     fail (Unsupported {loc; unsupported = "floats"})

let infer_loaded_value env loc lv = 
  match lv with
 | M_LVspecified ov -> infer_object_value env loc ov
 | M_LVunspecified _ct -> return (Bad (Unspecified loc))


let infer_value loc env v : (UU.ut,'e) m = 
  match v with
  | M_Vobject ov ->
     infer_object_value env loc ov
  | M_Vloaded lv ->
     infer_loaded_value env loc lv
  | M_Vunit ->
     let rt = [{name = fresh (); bound = A Unit}] in
     return (Normal rt)
  | M_Vtrue ->
     let name = fresh () in
     let t = {name; bound = A Bool} in
     let constr = {name = fresh (); bound = C (LC (S name))} in
     let rt = [t; constr] in
     return (Normal rt)
  | M_Vfalse -> 
     let name = fresh () in
     let t = {name; bound = A Bool} in
     let constr = {name = fresh (); bound = C (LC (Not (S name)))} in
     let rt = [t; constr] in
     return (Normal rt)
  | M_Vlist (cbt, asyms) ->
     bt_of_core_base_type loc cbt >>= fun bt ->
     begin match bt with
     | List i_t ->
        make_Aargs_bts env asyms >>= fun args_bts ->
        args_same_typ (Some i_t) args_bts >>
        (* maybe record list length? *)
        let rt = [{name = fresh (); bound = A (List i_t)}] in
        return (Normal rt)
     | bt ->
        fail (Generic_error (loc, "Cnil without list type"))
     end 
  | M_Vtuple args ->
     make_Aargs_bts env args >>= fun args_bts ->
     let rt = [{name = fresh (); bound = A (Tuple (List.map fst args_bts))}] in
     return (Normal rt)




let pp_unis unis = 
  let pp_entry (sym, {spec_name; spec; resolved}) =
    match resolved with
    | Some res -> 
       sprintf "%s : %s resolved as %s" 
         (Sym.pp sym) (LogicalSorts.pp spec) (Sym.pp res)
    | None -> sprintf "%s : %s unresolved"
         (Sym.pp sym) (LogicalSorts.pp spec) 
  in
  pp_list pp_entry ", " (SymMap.bindings unis)



let call_typ loc_call env decl_typ args =

  let find_resolved env unis = 
    SymMap.foldM
      (fun usym ({spec_name : Sym.t; spec; resolved} as uni) (unresolved,substs) ->
        match resolved with
        | None ->
           return (SymMap.add usym uni unresolved, substs)
        | Some sym -> 
           let (LogicalSorts.Base bt) = spec in
           check_it loc_call env (S sym) bt >>
           return (unresolved, (usym, sym) :: substs)
      ) unis (SymMap.empty, [])
  in

  let rec check_and_refine env args (F ftyp) unis constrs = 
    
    debug_print 2 
      [ h2 "check_and_refine"
      ; item "lenv" (LEnv.pp env.local)
      ; item "ftyp" (FunctionTypes.pp (F ftyp))
      ; item "args" (pp_list (fun (a,_) -> Sym.pp a) ", " args)
      ; item "unis" (pp_unis unis)
      ];


    match ftyp.arguments with
    | [] -> 
       begin match args with
       | [] -> 
          find_resolved env unis >>= fun (unresolved,substs) ->
          if not (SymMap.is_empty unresolved) then
            let (usym, {spec_name : Sym.t; spec; resolved}) =
              SymMap.find_first (fun _ -> true) unresolved in
            fail (Call_error (loc_call, Unconstrained_l (spec_name,spec)))
          else
            let ret = 
              fold_left (fun ret (s, subst) -> Types.subst s subst ret)
                ftyp.return substs 
            in
            let constrs = 
              fold_left (fun constrs (s, subst) -> 
                  map (fun (n,lc) -> (n, LogicalConstraints.subst s subst lc)) constrs)
                 constrs substs
            in
            constraints_hold loc_call env constrs >>
              return (ret,env)
          
       | (sym,loc) :: args -> 
          get_Avar loc env sym >>= fun bt ->
          fail (Call_error (loc, Surplus_A (sym, bt)))
       end

    | {name = n; bound =  A t} :: decl_args ->
       begin match args with
       | (sym,loc) :: args ->
          get_Avar loc env sym >>= fun t' ->
          if BaseTypes.type_equal t' t then 
            let ftyp = FunctionTypes.subst n sym (F {ftyp with arguments = decl_args}) in
            check_and_refine env args ftyp unis constrs
          else 
            let msm = Mismatch {mname = Some sym; has = A t'; expected = A t} in
            fail (Call_error (loc, msm))
       | [] ->
          fail (Call_error (loc_call, Missing_A (n, t)))
       end

    | {name = n; bound = R t} :: decl_args -> 
       let owner = Resources.owner t in
       get_owned_resource loc_call env owner >>= begin function
       | None -> fail (Call_error (loc_call, (Missing_R (n, t))))
       | Some (sym, _) -> 
          get_Rvar loc_call env sym >>= fun (t',env) ->
          tryM (Resources.unify t t' unis)
            (let err = Mismatch {mname = Some sym; has = R t'; expected = R t} in
             fail (Call_error (loc_call, err))) >>= fun unis ->
          let ftyp = FunctionTypes.subst n sym (F {ftyp with arguments = decl_args}) in
          find_resolved env unis >>= fun (_,substs) ->
          let ftyp = fold_left (fun f (s, s') -> FunctionTypes.subst s s' f) ftyp substs in
          check_and_refine env args ftyp unis constrs
       end

    | {name = n; bound = L t} :: decl_args -> 
       let sym = Sym.fresh () in
       let uni = { spec_name = n; spec = t; resolved = None } in
       let unis' = SymMap.add sym uni unis in
       let ftyp' = FunctionTypes.subst n sym (F {ftyp with arguments = decl_args}) in
       check_and_refine env args ftyp' unis' constrs

    | {name = n; bound = C t} :: decl_args ->        
       let constrs' = (constrs @ [(n, t)]) in
       check_and_refine env args (F {ftyp with arguments = decl_args}) unis constrs'

  in

  check_and_refine env args decl_typ SymMap.empty []


let call_typ_fn loc_call fname env args =
  match fname with
  | Core.Impl _ -> 
     failwith "todo implementation-defined constrant"
  | Core.Sym sym ->
     lookup ~is_function:true loc_call env.global.fun_decls sym >>= fun decl ->
     let (_loc,decl_typ,_ret_name) = decl in 
     call_typ loc_call env decl_typ args


let good_ctor loc = function
  | Cnil cbt -> Normal (`Cnil cbt)
  | Ccons -> Normal (`Ccons)
  | Ctuple -> Normal (`Ctuple)
  | Carray -> Normal (`Carray)
  | Civmax -> Normal (`Civmax)
  | Civmin -> Normal (`Civmin)
  | Civsizeof -> Normal (`Civsizeof)
  | Civalignof -> Normal (`Civalignof)
  | CivCOMPL -> Normal (`CivCOMPL)
  | CivAND -> Normal (`CivAND)
  | CivOR -> Normal (`CivOR)
  | CivXOR -> Normal (`CivXOR)
  | Cspecified -> Normal (`Cspecified)
  | Cfvfromint -> Normal (`Cfvfromint)
  | Civfromfloat -> Normal (`Civfromfloat)
  | Cunspecified -> Bad (Unspecified loc)



let ctor_typ loc ctor (args_bts : ((BaseTypes.t * Loc.t) list)) = 
  match ctor with
  | `Cnil cbt ->
     bt_of_core_base_type loc cbt >>= fun bt ->
     begin match bt, args_bts with
     | List _, [] ->
        return bt
     | _, [] ->
        fail (Generic_error (loc, "Cnil without list type"))
     | _, args -> 
        let err = sprintf "Cons applied to %d argument(s)" (List.length args) in
        fail (Generic_error (loc, err))
     end
  | `Ccons ->
     begin match args_bts with
     | [(hd_bt,hd_loc); (tl_bt,tl_loc)] ->
        ensure_type tl_loc None (A tl_bt) (A (List hd_bt)) >>
        let t = List tl_bt in
        return t
     | args ->
        let err = sprintf "Cons applied to %d argument(s)" 
                    (List.length args) in
        fail (Generic_error (loc, err))
     end
  | `Ctuple ->
     let t = BaseTypes.Tuple (List.map fst args_bts) in
     return t
  | `Carray -> 
     args_same_typ None args_bts >>
     return BaseTypes.Array
  | `Civmax
  | `Civmin
  | `Civsizeof
  | `Civalignof
  | `CivCOMPL
  | `CivAND
  | `CivOR
  | `CivXOR -> failwith "todo"
  | `Cspecified ->
    begin match args_bts with
    | [(bt,_)] ->
       return bt
    | args ->
       let err = sprintf "Cspecified applied to %d argument(s)" 
                   (List.length args) in
       fail (Generic_error (loc, err))
    end

  | `Cfvfromint -> 
     fail (Unsupported {loc; unsupported = "floats"})
  | `Civfromfloat -> 
     fail (Unsupported {loc; unsupported = "floats"})




let check_name_disjointness names_and_locations = 
  fold_leftM (fun names_so_far (name,loc) ->
      if not (SymSet.mem name names_so_far )
      then return (SymSet.add name names_so_far)
      else fail (Name_bound_twice {name; loc})
    ) SymSet.empty names_and_locations


let rec collect_pattern_names (Pattern (annots, pat)) = 
  match pat with
  | CaseBase (None, _) -> []
  | CaseBase (Some sym, _) -> [(sym,Annot.get_loc_ annots)]
  | CaseCtor (_, pats) -> concat_map collect_pattern_names pats


let infer_pat pat = 

  let rec aux pat = 
    let (Core.Pattern (annots, pat_)) = pat in
    let loc = Annot.get_loc_ annots in
    match pat_ with
    | CaseBase (None, cbt) ->
       bt_of_core_base_type loc cbt >>= fun bt ->
       return (Normal ([((Sym.fresh (), bt), loc)], (bt, loc)))
    | CaseBase (Some sym, cbt) ->
       bt_of_core_base_type loc cbt >>= fun bt ->
       return (Normal ([((sym, bt), loc)], (bt, loc)))
    | CaseCtor (ctor, args) ->
       match good_ctor loc ctor with
       | Bad bad -> return (Bad bad)
       | Normal ctor ->
          mapM aux args >>= fun bindingses_args_bts ->
          match all_normal bindingses_args_bts with
          | Bad b -> return (Bad b)
          | Normal bindingses_args_bts ->
             let bindingses, args_bts = List.split bindingses_args_bts in
             let bindings = List.concat bindingses in
             ctor_typ loc ctor args_bts >>= fun bt ->
             return (Normal (bindings, (bt, loc)))
  in

  check_name_disjointness (collect_pattern_names pat) >>
  aux pat >>= function 
  | Normal (bindings, (bt, loc)) ->
     let (bindings,_) = List.split bindings in
     return (Normal (bindings, bt, loc))
  | Bad bad -> 
     return (Bad bad)

     

let infer_binop env loc op sym1 sym2 = 

  let make_binop_constr (v1 : IndexTerms.t) (v2 : IndexTerms.t) =
    match op with
    | OpAdd -> Add (v1, v2)
    | OpSub -> Sub (v1, v2)
    | OpMul -> Mul (v1, v2)
    | OpDiv -> Div (v1, v2) 
    | OpRem_t -> Rem_t (v1, v2)
    | OpRem_f -> Rem_f (v1, v2)
    | OpExp -> Exp (v1, v2)
    | OpEq -> EQ (v1, v2)
    | OpGt -> GT (v1, v2)
    | OpLt -> LT (v1, v2)
    | OpGe -> GE (v1, v2)
    | OpLe -> LE (v1, v2)
    | OpAnd -> And (v1, v2)
    | OpOr -> Or (v1, v2)
  in

  let bt_of_binop : ((BaseTypes.t * BaseTypes.t) * BaseTypes.t) = 
    match op with
    | OpAdd -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Int)
    | OpSub -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Int)
    | OpMul -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Int)
    | OpDiv -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Int)
    | OpRem_t -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Int)
    | OpRem_f -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Int)
    | OpExp -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Int)
    | OpEq -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Bool)
    | OpGt -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Bool)
    | OpLt -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Bool)
    | OpGe -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Bool)
    | OpLe -> ((BaseTypes.Int, BaseTypes.Int), BaseTypes.Bool)
    | OpAnd -> ((BaseTypes.Bool, BaseTypes.Bool), BaseTypes.Bool)
    | OpOr -> ((BaseTypes.Bool, BaseTypes.Bool), BaseTypes.Bool)
  in

  let (sym1, loc1) = lof_a sym1 in
  let (sym2, loc2) = lof_a sym2 in
  get_Avar loc env sym1 >>= fun t1 ->
  get_Avar loc env sym2 >>= fun t2 ->
  let ((st1,st2),rt) = bt_of_binop in
  ensure_type loc1 (Some sym1) (A t1) (A st1) >>
  ensure_type loc2 (Some sym2) (A t2) (A st2) >>
  let name = fresh () in
  let constr = LC (S name %= (make_binop_constr (S sym1) (S sym2))) in
  let t = [{name; bound = A rt}; {name = fresh (); bound = C constr}] in
  return t
  



let ensure_bad_unreachable loc env bad = 
  if is_unreachable env loc then return env else 
    begin match bad with
    | Undefined (loc,undef) -> fail (Undefined_behaviour (loc, undef))
    | Unspecified loc -> fail (Unspecified_value loc)
    end


let infer_pexpr env (pe : 'bty mu_pexpr) = 

  debug_print 1
    [ h2 "infer_pexpr"
    ; item "env" (LEnv.pp env.local)
    ; item "e" ""
    ; pp_pexpr pe
    ];

  let (M_Pexpr (annots, _bty, pe_)) = pe in
  let loc = Annot.get_loc_ annots in
  match pe_ with
  | M_PEsym sym ->
     get_Avar loc env sym >>= fun b ->
     let rt = [{name = sym; bound = A b}] in
     return (Normal rt, env)
  | M_PEimpl _ ->
     failwith "todo PEimpl"
  | M_PEval v ->
     infer_value loc env v >>= fun t ->
     return (t, env)
  | M_PEconstrained _ ->
     failwith "todo PEconstrained"
  | M_PEundef (loc,undef) ->
     return (Bad (Undefined (loc, undef)), env)
  | M_PEerror _ ->
     failwith "todo PEerror"
  | M_PEctor (ctor, args) ->
     make_Aargs_bts env args >>= fun args_bts ->
     begin match good_ctor loc ctor with
     | Normal ctor ->
        ctor_typ loc ctor args_bts >>= fun t ->
        let rt = [{name = fresh (); bound = A t}] in
        return (Normal rt, env)
     | Bad bad -> return (Bad bad, env)
     end
  | M_PEcase (asym, pats_es) ->
     failwith "PEcase in inferring position"
  | M_PEarray_shift _ ->
     failwith "todo PEarray_shift"
  | M_PEmember_shift _ ->
     failwith "todo PEmember_shift"
  | M_PEnot sym ->
     let (sym,a_loc) = lof_a sym in
     get_Avar loc env sym >>= fun t ->
     ensure_type a_loc (Some sym) (A t) (A BaseTypes.Bool) >>
     let name = fresh () in
     let constr = LC ((S name) %= Not (S sym)) in
     let env = add_Cvar env (name, constr) in
     let rt = [{name; bound = A t}] in
     return (Normal rt, env)
  | M_PEop (op,sym1,sym2) ->
     infer_binop env loc op sym1 sym2 >>= fun rt ->
     return (Normal rt, env)
  | M_PEstruct _ ->
     failwith "todo PEstruct"
  | M_PEunion _ ->
     failwith "todo PEunion"
  | M_PEmemberof _ ->
     failwith "todo M_PEmemberof"
  | M_PEcall (fname, asyms) ->
     (* include the resource arguments into asyms *)
     (* let env = call_resources annots env in *)
     call_typ_fn loc fname env (List.map lof_a asyms) >>= fun (rt, env) ->
     return (Normal rt, env)
  | M_PElet (p, e1, e2) ->
     failwith "PElet in inferring position"
  | M_PEif _ ->
     failwith "PEif in inferring position"


let rec check_pexpr env (e : 'bty mu_pexpr) ret = 

  debug_print 1
    [ h2 "check_pexpr"
    ; item "env" (LEnv.pp env.local)
    ; item "ret" (Types.pp ret)
    ; item "e" ""
    ; pp_pexpr e
    ];

  let (M_Pexpr (annots, _, e_)) = e in
  let loc = Annot.get_loc_ annots in
  match e_ with
  | M_PEif (asym1, e2, e3) ->
     let sym1, loc1 = lof_a asym1 in
     get_Avar loc env sym1 >>= fun t1 -> 
     ensure_type loc1 (Some sym1) (A t1) (A Bool) >>
     let then_constr = (Sym.fresh (), LC (S sym1 %= Bool true)) in
     let else_constr = (Sym.fresh (), LC (S sym1 %= Bool true)) in
     check_pexpr (add_Cvar env then_constr) e2 ret >>
     check_pexpr (add_Cvar env else_constr) e3 ret
  | M_PEcase (asym, pats_es) ->
     let (esym,eloc) = lof_a asym in
     get_Avar eloc env esym >>= fun bt ->
     mapM (fun (pat,pe) ->
         (* check pattern type against bt *)
         infer_pat pat >>= fun pinfo ->
         match pinfo with 
         | Bad bad -> 
            ensure_bad_unreachable loc env bad
         | Normal (bindings, bt', ploc) ->
            ensure_type ploc None (A bt') (A bt) >>
            (* check body type against spec *)
            let env' = add_Avars env bindings in
            check_pexpr env' pe ret
       ) pats_es >>
     return env
  | M_PElet (p, e1, e2) ->
     begin match p with 
     | M_symbol (Annotated (_annots, _, newname)) ->
        infer_pexpr env e1 >>= fun (rt, env) ->
        begin match rt with
        | Normal rt -> check_pexpr (add_rt env (rename newname rt)) e2 ret
        | Bad bad -> ensure_bad_unreachable loc env bad
        end
     | M_normal_pattern (Pattern (_annot, CaseBase (mnewname,_cbt))) ->
        let newname = sym_or_fresh mnewname in
        infer_pexpr env e1 >>= fun (rt, env) ->
        begin match rt with
        | Normal rt -> check_pexpr (add_rt env (rename newname rt)) e2 ret
        | Bad bad -> ensure_bad_unreachable loc env bad
        end        
     | M_normal_pattern (Pattern (_annot, CaseCtor _)) ->
        failwith "todo ctor pattern"
     end
  | _ ->
     infer_pexpr env e >>= fun (rt, env) ->
     begin match rt with
     | Normal rt -> subtype loc env rt ret
     | Bad bad -> ensure_bad_unreachable loc env bad
     end        



let rec infer_expr env (e : ('a,'bty) mu_expr) = 

  debug_print 1
    [ h2 "infer_expr"
    ; item "env" (LEnv.pp env.local)
    ; item "e" ""
    ; pp_expr e
    ];

  let (M_Expr (annots, e_)) = e in
  let loc = Annot.get_loc_ annots in
  match e_ with
  | M_Epure pe -> 
     infer_pexpr env pe
  | M_Ememop _ ->
     failwith "todo ememop"
  | M_Eaction (M_Paction (_pol, M_Action (aloc,_,action_))) ->
     begin match action_ with
     | M_Create (asym,a_ct,_prefix) -> 
        let (ct, _ct_loc) = lof_a a_ct in
        make_create_type ct >>= fun decl_typ ->
        call_typ loc env decl_typ [lof_a asym] >>= fun (rt, env) ->
        return (Normal rt, env)
     | M_CreateReadOnly (sym1, ct, sym2, _prefix) -> 
        failwith "CreateReadOnly"
     | M_Alloc (ct, sym, _prefix) -> 
        failwith "Alloc"
     | M_Kill (_is_dynamic, asym) -> 
        let (sym,loc) = lof_a asym in
        recursively_owned_resources loc env sym >>= fun resources ->
        let env = remove_vars env resources in
        let rt = [{name = fresh (); bound = A Unit}] in
        return (Normal rt, env)
     | M_Store (_is_locking, a_ct, asym1, asym2, mo) -> 
        let (ct, _ct_loc) = lof_a a_ct in
        make_store_type ct >>= fun decl_typ ->
        call_typ loc env decl_typ [lof_a asym1; lof_a asym2] >>= fun (rt, env) ->
        return (Normal rt, env)
     | M_Load (a_ct, asym, _mo) -> 
        let (ct, _ct_loc) = lof_a a_ct in
        make_load_type ct >>= fun decl_typ ->
        call_typ loc env decl_typ [lof_a asym] >>= fun (rt, env) ->
        return (Normal rt, env)
     | M_RMW (ct, sym1, sym2, sym3, mo1, mo2) -> 
        failwith "RMW"
     | M_Fence mo -> 
        failwith "Fence"
     | M_CompareExchangeStrong (ct, sym1, sym2, sym3, mo1, mo2) -> 
        failwith "CompareExchangeStrong"
     | M_CompareExchangeWeak (ct, sym1, sym2, sym3, mo1, mo2) -> 
        failwith "CompareExchangeWeak"
     | M_LinuxFence mo -> 
        failwith "LinuxFemce"
     | M_LinuxLoad (ct, sym1, mo) -> 
        failwith "LinuxLoad"
     | M_LinuxStore (ct, sym1, sym2, mo) -> 
        failwith "LinuxStore"
     | M_LinuxRMW (ct, sym1, sym2, mo) -> 
failwith "LinuxRMW"
     end
  | M_Ecase _ ->
     failwith "todo ecase"
  | M_Elet (p, e1, e2) ->
     failwith "Elet in inferring position"
| M_Eif _ ->
     failwith "todo eif"
  | M_Eskip -> 
     let rt = [{name = fresh (); bound = A Unit}] in
     return (Normal rt, env)
  | M_Eccall (_a, asym, asd, asyms) ->
     failwith "todo eccall"
  | M_Eproc _ ->
     failwith "todo eproc"
  | M_Ewseq (p, e1, e2) ->      (* for now, the same as Esseq *)
     failwith "Ewseq in inferring position"
  | M_Esseq (p, e1, e2) ->
     failwith "Esseq in inferring position"
  | M_Ebound (n, e) ->
     infer_expr env e
  | M_End _ ->
     failwith "todo end"
  | M_Esave _ ->
     failwith "todo esave"
  | M_Erun _ ->
     failwith "todo erun"


let rec check_expr env (e : ('a,'bty) mu_expr) ret = 

  debug_print 1
    [ h2 "check_expr"
    ; item "env" (LEnv.pp env.local)
    ; item "ret" (Types.pp ret)
    ; item "e" ""
    ; pp_expr e
    ];

  let (M_Expr (annots, e_)) = e in
  let loc = Annot.get_loc_ annots in
  match e_ with
  | M_Eif (asym1, e2, e3) ->
     let sym1, loc1 = lof_a asym1 in
     get_Avar loc env sym1 >>= fun t1 -> 
     ensure_type loc1 (Some sym1) (A t1) (A Bool) >>
     let then_constr = (Sym.fresh (), LC (S sym1 %= Bool true)) in
     let else_constr = (Sym.fresh (), LC (S sym1 %= Bool true)) in
     check_expr (add_Cvar env then_constr) e2 ret >>
     check_expr (add_Cvar env else_constr) e3 ret
  | M_Ecase (asym, pats_es) ->
     let (esym,eloc) = lof_a asym in
     get_Avar eloc env esym >>= fun bt ->
     mapM (fun (pat,pe) ->
         (* check pattern type against bt *)
         infer_pat pat >>= fun pinfo ->
         match pinfo with 
         | Bad bad -> 
            ensure_bad_unreachable loc env bad
         | Normal (bindings, bt', ploc) ->
            ensure_type ploc None (A bt') (A bt) >>
            (* check body type against spec *)
            let env' = add_Avars env bindings in
            check_expr env' pe ret
       ) pats_es >>
     return env     
  | M_Epure pe -> 
     check_pexpr env pe ret
  | M_Elet (p, e1, e2) ->
     begin match p with 
     | M_symbol (Annotated (_annots, _, newname)) ->
        infer_pexpr env e1 >>= fun (rt, env) ->
        begin match rt with
        | Normal rt -> check_expr (add_rt env (rename newname rt)) e2 ret
        | Bad bad -> ensure_bad_unreachable loc env bad
        end
     | M_normal_pattern (Pattern (_annot, CaseBase (mnewname,_cbt))) ->
        let newname = sym_or_fresh mnewname in
        infer_pexpr env e1 >>= fun (rt, env) ->
        begin match rt with
        | Normal rt -> check_expr (add_rt env (rename newname rt)) e2 ret
        | Bad bad -> ensure_bad_unreachable loc env bad
        end        
     | M_normal_pattern (Pattern (_annot, CaseCtor _)) ->
        failwith "todo ctor pattern"
     end
  | M_Ewseq (p, e1, e2)      (* for now, the same as Esseq *)
  | M_Esseq (p, e1, e2) ->
     begin match p with 
     | Pattern (_annot, CaseBase (mnewname,_cbt)) ->
        let newname = sym_or_fresh mnewname in
        infer_expr env e1 >>= fun (rt, env) ->
        begin match rt with
        | Normal rt -> check_expr (add_rt env (rename newname rt)) e2 ret
        | Bad bad -> ensure_bad_unreachable loc env bad
        end        
     | Pattern (_annot, CaseCtor _) ->
        failwith "todo ctor pattern"
     end
  | M_Esave (_ret, args, body) ->
     fold_leftM (fun env (sym, (_, asym)) ->
         let (vsym,loc) = lof_a asym in
         get_Avar loc env vsym >>= fun bt ->
         return (add_Avar env (sym,bt))
       ) env args >>= fun env ->
     check_expr env body ret
  | _ ->
     infer_expr env e >>= fun (rt, env) ->
     begin match rt with
     | Normal rt -> subtype loc env rt ret
     | Bad bad -> ensure_bad_unreachable loc env bad
     end        
     





let check_function_body (type a bty) genv name (body : (a,bty) mu_expr) (F decl_typ) = 
  let env = with_fresh_local genv in
  let env = add_rt env decl_typ.arguments in
  check_expr (* name *) env body decl_typ.return >>= fun _env ->
  return ()



let embed_fun_proc body = 
  let (M_Pexpr (annots, _, _)) = body in
  M_Expr (annots, M_Epure (body))



let check_function (type bty a) genv fsym (fn : (bty,a) mu_fun_map_decl) = 

  let forget = 
    filter_map (function {name; bound = A t} -> Some (name,t) | _ -> None) in


  let binding_of_core_base_type loc (sym,cbt) = 
    bt_of_core_base_type loc cbt >>= fun bt ->
    return {name = sym; bound = A bt}
  in

  let check_consistent loc decl args ret = 
    mapM (binding_of_core_base_type loc) args >>= fun args ->
    binding_of_core_base_type loc ret >>= fun ret ->
    let (F decl_typ) = decl in
    let _ = forget args in
    return ()
    (* if BaseTypes.types_equal (forget decl_typ.arguments) (forget args) &&
     *      BaseTypes.types_equal (forget decl_typ.return) (forget [ret])
     * then return ()
     * else 
     *   let defn = F {arguments = args; return = [ret]} in
     *   fail (Inconsistent_fundef {loc; decl; defn = defn}) *)
  in

  match fn with
  | M_Fun (ret, args, body) ->
     let loc = Loc.unknown in
     lookup ~is_function:true loc genv.GEnv.fun_decls fsym >>= fun decl ->
     let (loc,decl_typ,ret_name) = decl in
     check_consistent loc decl_typ args (ret_name,ret) >>
     check_function_body genv fsym (embed_fun_proc body) decl_typ
  | M_Proc (loc, ret, args, body) ->
     lookup ~is_function:true loc genv.fun_decls fsym >>= fun decl ->
     let (loc,decl_typ,ret_name) = decl in
     check_consistent loc decl_typ args (ret_name,ret) >>
     check_function_body genv fsym body decl_typ
  | M_ProcDecl _
  | M_BuiltinDecl _ -> 
     return ()


let check_functions (type a bty) env (fns : (bty,a) mu_fun_map) =
  pmap_iterM (check_function env) fns

                             






let record_fun sym (loc,_attrs,ret_ctype,args,is_variadic,_has_proto) fun_decls =

  let make_arg_t (msym,ct) = 
    let name = sym_or_fresh msym in
    ctype name (make_pointer_ctype ct)
  in

  if is_variadic 
  then fail (Variadic_function {loc; fn = sym})
  else 
    let ret_name = Sym.fresh () in
    mapM make_arg_t args >>= fun args_types ->
    let arguments = concat args_types in
    ctype ret_name ret_ctype >>= fun ret ->
    let ft = F {arguments; return = ret} in
    let fun_decls = SymMap.add sym (loc, ft, ret_name) fun_decls in
    return fun_decls

let record_funinfo genv funinfo = 
  pmap_foldM record_fun funinfo genv.GEnv.fun_decls >>= fun fun_decls ->
  return { genv with GEnv.fun_decls = fun_decls }



let record_tagDef sym def genv =

  match def with
  | Ctype.UnionDef _ -> 
     failwith "todo: union types"
  | Ctype.StructDef (fields, _) ->

     fold_leftM (fun (names,fields) (id, (_attributes, _qualifier, ct)) ->
       let id = Id.s id in
       let name = Sym.fresh_pretty id in
       let names = (id, (name, Loc.unknown)) :: names in
       ctype name ct >>= fun newfields ->
       return (names, fields @ newfields)
       (* fun bt_constr ->
        * let fields = match bt_constr with
        *   | (bt, Some c) -> 
        *      fields @ [{name = sym; bound = A bt}; 
        *                {name = fresh (); bound = C (LC (c (S sym)))}]
        *   | (bt, None) -> 
        *      fields @ [{name = sym; bound = A bt}]
        * in
        * return (names, fields) *)
     ) ([],[]) fields >>= fun (names,fields) ->

     let struct_decls = SymMap.add sym fields genv.GEnv.struct_decls in
     let names = fold_left (fun m (k,v) -> StringMap.add k v m) genv.names names in
     return { genv with names = names; struct_decls = struct_decls }

let record_tagDefs genv tagDefs = 
  pmap_foldM record_tagDef tagDefs genv







let pp_fun_map_decl funinfo = 
  let pp = Pp_core.All.pp_funinfo_with_attributes funinfo in
  print_string (Pp_utils.to_plain_string pp)




let check mu_file =
  let env = GEnv.empty in
  record_tagDefs env mu_file.mu_tagDefs >>= fun env ->
  record_funinfo env mu_file.mu_funinfo >>= fun env ->
  let () = print_endline (GEnv.pp env) in
  check_functions env mu_file.mu_funs

let check_and_report core_file = 
  match check core_file with
  | Result () -> ()
  | Exception err -> 
     print_endline ("\n" ^ underline '=' "Error!" ^ "\n" ^ pp err)
