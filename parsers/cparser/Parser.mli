exception Error


val translation_unit_file: (Lexing.lexbuf -> Tokens.token) -> Lexing.lexbuf -> (Cabs.translation_unit)