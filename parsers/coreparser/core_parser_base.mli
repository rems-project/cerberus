include (Parser_util.BASE with type token  = Core_parser.token
                          and  type result = (Global.zero Core.file, Global.zero Core.fun_map) Global.either)
