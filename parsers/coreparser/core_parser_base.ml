exception Error = Core_parser.Error
type token  = Core_parser.token
type result = (Global.zero Core.file, Global.zero Core.fun_map) Global.either

let start = Core_parser.start
