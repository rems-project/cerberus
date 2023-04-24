module CF=Cerb_frontend
module A=CF.AilSyntax
module C=CF.Ctype

let rm_expr (A.AnnotatedExpression (_, _, _, expr_)) = expr_

let mk_expr expr_ = 
  A.AnnotatedExpression ((), [], Cerb_location.unknown, expr_)

let empty_qualifiers : C.qualifiers = {const = false; restrict = false; volatile = false}