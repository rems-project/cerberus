val rename_nested_module : Name.t list -> Typed_ast.env -> Typed_ast.def list -> Typed_ast.def list 
val flatten_modules : Name.t -> Typed_ast.env -> Typed_ast.def list -> Typed_ast.def list
val rename_ocaml : Name.t list -> Typed_ast.env -> Typed_ast.def list -> Typed_ast.def list
