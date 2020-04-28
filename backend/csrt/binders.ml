open Utils
open Except
open List
open Sym
open Pp_tools


module Loc = Location
module LC = LogicalConstraints
module RE = Resources
module IT = IndexTerms
module BT = BaseTypes
module LS = LogicalSorts

module SymSet = Set.Make(Sym)

type t = {name: Sym.t; bound: VarTypes.t}

let pp {name;bound} = 
 match bound with
 | A t -> alrctyp 'A' (Sym.pp name) (BT.pp t)
 | L t -> alrctyp 'L' (Sym.pp name) (LS.pp t)
 | R t -> alrctyp 'R' (Sym.pp name) (RE.pp t)
 | C t -> alrctyp 'C' (Sym.pp name) (LC.pp t)


let parse_sexp loc (names : NameMap.t) s = 
 let open Sexplib in
 let open Sexp in
 match s with
 | List [Atom id; Atom ":"; t] ->
    let name = Sym.fresh_pretty id in
    let names = NameMap.record loc id name names in
    BT.parse_sexp loc names t >>= fun t ->
    return ({name; bound = A t}, names)
 | List [Atom "Logical"; Atom id; Atom ":"; ls] ->
    let name = Sym.fresh_pretty id in
    let names = NameMap.record loc id name names in
    LS.parse_sexp loc names ls >>= fun t ->
    return ({name; bound = L t}, names)
 | List [Atom "Resource"; Atom id; Atom ":"; re] ->
    let name = Sym.fresh_pretty id in
    let names = NameMap.record loc id name names in
    RE.parse_sexp loc names re >>= fun t ->
    return ({name; bound = R t}, names)
 | List [Atom "Constraint"; Atom id; Atom ":"; lc] ->
    let name = Sym.fresh_pretty id in
    let names = NameMap.record loc id name names in
    LC.parse_sexp loc names lc >>= fun t ->
    return ({name; bound = C t}, names)
 | t -> 
    parse_error loc "binders" t



let subst sym with_it b = 
  { name = sym_subst sym with_it b.name;
    bound = VarTypes.subst sym with_it b.bound }

let makeA name bt = {name; bound = A bt}
let makeL name bt = {name; bound = L (Base bt)}
let makeR name re = {name; bound = R re}
let makeC name it = {name; bound = C (LC it)}

let makeUA bt = makeA (fresh ()) bt
let makeUL bt = makeL (fresh ()) bt
let makeUR bt = makeR (fresh ()) bt
let makeUC bt = makeC (fresh ()) bt

