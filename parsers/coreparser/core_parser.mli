module Make
           (M : sig
                  val sym_counter: int ref
                  val std: (Core_parser_util._sym, Core.sym) Pmap.map
                end)
: sig

  (* This exception is raised by the monolithic API functions. *)
  exception Error
  
  (* The monolithic API. *)
  val start: (Lexing.lexbuf -> Core_parser_util.token) -> Lexing.lexbuf -> (Core_parser_util.result)
  
  

end
