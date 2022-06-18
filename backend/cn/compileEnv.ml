module CF = Cerb_frontend
module IT = IndexTerms


(* moving Kayvan's originally compilePredicates.ml environment definitions over here *)


module X = Map.Make(Sym)
module Y = Map.Make(String)

type function_sig = {
    args: (Sym.t * BaseTypes.t) list;
    return_bty: BaseTypes.t;
  }

type predicate_sig = {
  pred_iargs: (Sym.t * BaseTypes.t) list;
  pred_oargs: (Sym.t * BaseTypes.t) list;
}

type resource_def =
  | RPred_owned of Sctypes.t
  | RPred_block of Sctypes.t
  | RPred_named of Sym.t
  | RPred_I_owned of Sctypes.t
  | RPred_I_block of Sctypes.t
  | RPred_I_named of Sym.t

type t = {
  logicals: BaseTypes.t X.t;
  pred_names: Sym.t Y.t;
  functions: function_sig X.t;
  predicates: predicate_sig X.t;
  resources: resource_def X.t;
  tagDefs: CF.Core_to_mucore.Mu.mu_tag_definitions;
}

let empty tagDefs =
  { logicals= X.empty; pred_names= Y.empty; functions = X.empty; predicates= X.empty; resources= X.empty; tagDefs }

let add_logical sym bTy env =
  {env with logicals= X.add sym bTy env.logicals }

let add_pred_name str sym env =
  {env with pred_names= Y.add str sym env.pred_names }

let add_function sym func_sig env =
  {env with functions= X.add sym func_sig env.functions }

let add_predicate sym pred_sig env =
  {env with predicates= X.add sym pred_sig env.predicates }

let add_resource sym res_def env =
  { env with resources= X.add sym res_def env.resources }

let lookup_logical sym env =
  X.find_opt sym env.logicals

let lookup_pred_name str env =
  Y.find_opt str env.pred_names

let lookup_predicate sym env =
  X.find_opt sym env.predicates

let lookup_resource sym env =
  X.find_opt sym env.resources

let lookup_struct sym env =
  match Pmap.lookup sym env.tagDefs with
    | Some (M_StructDef xs) ->
        Some xs
    | Some (M_UnionDef _)| None ->
        None








