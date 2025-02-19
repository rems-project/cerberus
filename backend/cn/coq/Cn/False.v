(* Define the False type *)

(* TODO not sure if this is the good name. Maybe retname to TFalse later *)
Inductive False_t : Type :=
  | False. 

Definition t := False_t.