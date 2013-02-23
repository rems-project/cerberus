exception Error = C_parser.Error
type token  = Pre_parser.token
type result = Cabs_parser.definition list

let start = Pre_parser.translation_unit_file
