type coq_Event =
  | Coq_mkEvent

(** val coq_Event_rect : 'a1 -> coq_Event -> 'a1 **)

let coq_Event_rect f e =
  f

(** val coq_Event_rec : 'a1 -> coq_Event -> 'a1 **)

let coq_Event_rec f e =
  f

type trace =
  | Coq_trace_nil
  | Coq_trace_cons of coq_Event * trace

(** val trace_rect :
    'a1 -> (coq_Event -> trace -> 'a1 -> 'a1) -> trace -> 'a1 **)

let rec trace_rect f f0 = function
  | Coq_trace_nil -> f
  | Coq_trace_cons (e, t0) -> f0 e t0 (trace_rect f f0 t0)

(** val trace_rec :
    'a1 -> (coq_Event -> trace -> 'a1 -> 'a1) -> trace -> 'a1 **)

let rec trace_rec f f0 = function
  | Coq_trace_nil -> f
  | Coq_trace_cons (e, t0) -> f0 e t0 (trace_rec f f0 t0)

type coq_Trace = __coq_Trace Lazy.t
and __coq_Trace =
  | Trace_cons of coq_Event * coq_Trace

(** val trace_app : trace -> trace -> trace **)

let rec trace_app tr1 tr2 =
  match tr1 with
    | Coq_trace_nil -> tr2
    | Coq_trace_cons (e, tr1') -> Coq_trace_cons (e, (trace_app tr1' tr2))

(** val coq_Trace_app : trace -> coq_Trace -> coq_Trace **)

let rec coq_Trace_app tr1 tr2 =
  match tr1 with
    | Coq_trace_nil -> tr2
    | Coq_trace_cons (e, tr1') -> lazy (Trace_cons (e,
        (coq_Trace_app tr1' tr2)))

