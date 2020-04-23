open Except

type t = LC of IndexTerms.t

let pp (LC c) = IndexTerms.pp c

let parse_sexp loc env s = 
  IndexTerms.parse_sexp loc env s >>= fun it ->
  return (LC it)

let subst sym with_it (LC c) = 
  LC (IndexTerms.subst sym with_it c)

