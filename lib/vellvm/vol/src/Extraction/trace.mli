type coq_Event =
  | Coq_mkEvent

val coq_Event_rect : 'a1 -> coq_Event -> 'a1

val coq_Event_rec : 'a1 -> coq_Event -> 'a1

type trace =
  | Coq_trace_nil
  | Coq_trace_cons of coq_Event * trace

val trace_rect : 'a1 -> (coq_Event -> trace -> 'a1 -> 'a1) -> trace -> 'a1

val trace_rec : 'a1 -> (coq_Event -> trace -> 'a1 -> 'a1) -> trace -> 'a1

type coq_Trace = __coq_Trace Lazy.t
and __coq_Trace =
  | Trace_cons of coq_Event * coq_Trace

val trace_app : trace -> trace -> trace

val coq_Trace_app : trace -> coq_Trace -> coq_Trace

