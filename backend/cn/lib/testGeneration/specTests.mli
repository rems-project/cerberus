module CF = Cerb_frontend
module A = CF.AilSyntax

val generate
  :  output_dir:string ->
  filename:string ->
  without_ownership_checking:bool ->
  CF.GenTypes.genTypeCategory A.sigma ->
  unit Mucore.file ->
  unit
