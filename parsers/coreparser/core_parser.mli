module Make
           (M : sig
                  val sym_counter: int ref
                  val std: (Core_parser_util._sym, Core.sym) Pmap.map
                end)
: sig

  exception Error
  
  
  val start: (Lexing.lexbuf -> Core_parser_util.token) -> Lexing.lexbuf -> (Core_parser_util.result)

end
