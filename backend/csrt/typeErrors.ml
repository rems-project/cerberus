open Pp
module Loc=Locations
module BT=BaseTypes
module IT=IndexTerms
module LS=LogicalSorts
module CF=Cerb_frontend
module RE=Resources


type label_kind = 
  | Return
  | Loop
  | Other


type access =
  | Load 
  | Store
  | Kill
  | Free

type situation = 
  | Access of access
  | FunctionCall
  | LabelCall of label_kind
  | Subtyping
  | Unpacking


type sym_or_string = 
  | Sym of Sym.t
  | String of string


type type_error = 
  | Unbound_name of sym_or_string
  | Name_bound_twice of sym_or_string
  | Missing_function of Sym.t
  | Missing_struct of BT.tag
  | Missing_predicate of String.t
  | Missing_member of BT.tag * BT.member

  | Missing_ownership of BT.member option * (Loc.t list) option * situation
  | Resource_mismatch of { has: RE.t; expect: RE.t; situation : situation}
  | Cannot_unpack of Resources.predicate * situation
  | Cannot_pack of Resources.t * situation

  | Uninitialised of BT.member option
  | Unused_resource of { resource: Resources.t }
  | Misaligned of access

  | Number_members of {has: int; expect: int}
  | Number_arguments of {has: int; expect: int}
  | Mismatch of { has: LS.t; expect: LS.t; }
  | Illtyped_it : 'bt IndexTerms.term -> type_error
  | Polymorphic_it : 'bt IndexTerms.term -> type_error
  | Unsat_constraint of LogicalConstraints.t * Pp.document
  | Unconstrained_logical_variable of Sym.t

  | Kind_mismatch of {has: Kind.t; expect: Kind.t}

  | Undefined_behaviour of CF.Undefined.undefined_behaviour * Model.t option
  | Unspecified of CF.Ctype.ctype
  | StaticError of string

  | Unsupported of Pp.document
  | Generic of Pp.document













let pp_type_error = function
  | Unbound_name unbound ->
     let name_pp = match unbound with
       | Sym s -> Sym.pp s
       | String str -> !^str
     in
     (!^"Unbound name" ^^ colon ^^^ name_pp, [])
  | Name_bound_twice name ->
     let name_pp = match name with
       | Sym s -> Sym.pp s
       | String str -> !^str
     in
     (!^"Name bound twice" ^^ colon ^^^ squotes name_pp, [])
  | Missing_function sym ->
     (!^"function" ^^^ Sym.pp sym ^^^ !^"not defined", [])
  | Missing_struct tag ->
     (!^"struct" ^^^ Sym.pp tag ^^^ !^"not defined", [])
  | Missing_predicate id ->
     (!^"predicate" ^^^ !^id ^^^ !^"not defined", [])
  | Missing_member (tag, member) ->
     (!^"struct" ^^^ Sym.pp tag ^^^ !^"does not have member" ^^^ 
        Id.pp member, [])

    | Missing_ownership (omember, owhere, situation) ->
     let msg = match situation, omember with
     | Access Kill, None ->  
        !^"Missing ownership for de-allocating"
     | Access Kill, Some m ->  
        !^"Missing ownership for de-allocating struct member" ^^^ Id.pp m
     | Access Load, None   ->  
        !^"Missing ownership for reading"
     | Access Load, Some m -> 
        !^"Missing ownership for reading struct member" ^^^ Id.pp m
     | Access Store, None   -> 
        !^"Missing ownership for writing"
     | Access Store, Some m -> 
        !^"Missing ownership for writing struct member" ^^^ Id.pp m
     | Access Free, _ -> 
        !^"Missing ownership for free-ing"
     | FunctionCall, _ -> 
        !^"Missing ownership for calling function"
     | LabelCall Return, _ -> 
        !^"Missing ownership for returning"
     | LabelCall Loop, _ -> 
        !^"Missing ownership for loop"
     | LabelCall Other, _ -> 
        !^"Missing ownership for calling label"
     | Subtyping, _ -> 
        !^"Missing ownership for subtyping"
     | Unpacking, _ -> 
        !^"Missing ownership for unpacking"
     in
     let extra = match owhere with
       | None -> []
       | Some locs -> 
          [!^"Maybe last used in the following places:" ^^^
             Pp.list Loc.pp locs]
     in
     (msg, extra)
  | Resource_mismatch {has; expect; situation} ->
     (!^"Need a resource" ^^^ RE.pp expect ^^^
        !^"but have resource" ^^^ RE.pp has, [])
  | Cannot_unpack (predicate, situation) ->
     let re = RE.Predicate predicate in
     let msg = match situation with
     | Access Kill ->
        !^"Cannot unpack resource needed for de-allocating"
     | Access Load ->
        !^"Cannot unpack resource needed for reading"
     | Access Store ->
        !^"Cannot unpack resource needed for writing"
     | Access Free ->
        !^"Cannot unpack resource needed for free-ing"
     | FunctionCall ->
        !^"Cannot unpack resource needed for calling function"
     | LabelCall Return ->
        !^"Cannot unpack resource needed for returning"
     | LabelCall Loop ->
        !^"Cannot unpack resource needed for loop"
     | LabelCall Other ->
        !^"Cannot unpack resource needed for jumping to label"
     | Subtyping ->
        !^"Cannot unpack resource needed for subtyping"
     | Unpacking ->
        !^"Cannot unpack resource needed for unpacking"
     in
     (msg ^^^ parens (RE.pp re), [])
  | Cannot_pack (re, situation) ->
     let msg = match situation with
     | Access Kill ->
        !^"Cannot pack resource needed for de-allocating"
     | Access Load ->
        !^"Cannot pack resource needed for reading"
     | Access Store ->
        !^"Cannot pack resource needed for writing"
     | Access Free ->
        !^"Cannot pack resource needed for free-ing"
     | FunctionCall ->
        !^"Cannot pack resource needed for calling function"
     | LabelCall Return ->
        !^"Cannot pack resource needed for returning"
     | LabelCall Loop ->
        !^"Cannot pack resource needed for loop"
     | LabelCall Other ->
        !^"Cannot pack resource needed for jumping to label"
     | Subtyping ->
        !^"Cannot pack resource needed for subtyping"
     | Unpacking ->
        !^"Cannot pack resource needed for unpacking"
     in
     (msg ^^^ parens (RE.pp re), [])

  | Uninitialised omember ->
     begin match omember with
     | None -> 
        (!^"Trying to read uninitialised data", [])
     | Some m -> 
        (!^"Trying to read uninitialised struct member" ^^^ Id.pp m, [])
     end
  | Unused_resource {resource;_} ->
     (!^"Left-over unused resource" ^^^ Resources.pp resource, [])
  | Misaligned access ->
     let msg = match access with
     | Kill -> !^"Misaligned de-allocation operation"
     | Load -> !^"Misaligned read"
     | Store ->  !^"Misaligned write"
     | Free ->  !^"Misaligned free"
     in
     (msg, [])

  | Number_members {has;expect} ->
     (!^"Wrong number of struct members:" ^^^
        !^"expected" ^^^ !^(string_of_int expect) ^^^ comma ^^^
          !^"has" ^^^ !^(string_of_int has), [])
  | Number_arguments {has;expect} ->
     (!^"Wrong number of arguments:" ^^^
        !^"expected" ^^^ !^(string_of_int expect) ^^^ comma ^^^
          !^"has" ^^^ !^(string_of_int has), [])
  | Mismatch {has; expect} ->
     (!^"Expected value of type" ^^^ LS.pp false expect ^^^
        !^"but found value of type" ^^^ LS.pp false has, [])
  | Illtyped_it it ->
     (!^"Illtyped index term" ^^ colon ^^^ (IndexTerms.pp it), [])
  | Polymorphic_it it ->
     (!^"Polymorphic index term" ^^ colon ^^^ (IndexTerms.pp it), [])
  | Unsat_constraint (c,extra) ->
     (!^"Unsatisfied constraint" ^^^ LogicalConstraints.pp c, [extra])
  | Unconstrained_logical_variable name ->
     (!^"Unconstrained logical variable" ^^^ Sym.pp name, [])
  | Kind_mismatch {has; expect} ->
     (!^"Expected" ^^^ Kind.pp expect ^^^ 
        !^"but found" ^^^ Kind.pp has, [])

  | Undefined_behaviour (undef, omodel) -> 
     let ub = CF.Undefined.pretty_string_of_undefined_behaviour undef in
     let extras = match omodel with 
       | Some model -> [!^ub; !^"Consider the case:" ^/^ Model.pp model] 
       | None -> [!^ub] 
     in
     (!^"Undefined behaviour", extras)
  | Unspecified _ctype ->
     (!^"Unspecified value", [])
  | StaticError err ->
     (!^("Static error: " ^ err), [])

  | Unsupported unsupported ->
     (!^"Unsupported feature" ^^ colon ^^^ unsupported, [])
  | Generic err ->
     (err, [])


(* stealing some logic from pp_errors *)
let report (loc : Loc.t) (ostacktrace : string option) (err : type_error) = 
  let (msg, extras) = pp_type_error err in
  let extras = match ostacktrace with
    | Some stacktrace -> extras @ [item "stacktrace" !^stacktrace]
    | None -> extras
  in
  Pp.error loc msg extras
