module CF=Cerb_frontend
module A=CF.AilSyntax
module C=CF.Ctype


let mk_expr expr_ = 
  A.AnnotatedExpression ((), [], Location_ocaml.unknown, expr_)

let rm_expr (A.AnnotatedExpression (_, _, _, expr_)) = expr_

let mk_stmt stmt_ = 
  A.AnnotatedStatement(Location_ocaml.unknown, CF.Annot.Attrs [], stmt_)

let empty_qualifiers : C.qualifiers = {const = false; restrict = false; volatile = false}