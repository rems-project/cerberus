open bossLib Theory Parse stringTheory
open HolDoc

val _ = new_theory "Machine-extract"

val _ = Define `
let write_reaching_coherence_point_action s w = 
   (*: add [[w]] :*)
   let writes_past_coherence_point' =
      s.writes_past_coherence_point union {w} in
   (*: make [[w]] before all other writes to this address not past coherence :*)
   let coherence' = s.coherence union
      { (w,wother) | forall (wother IN (writes_not_past_coherence s)) 
                   | (not (wother = w)) && (wother.w_addr = w.w_addr) } in
   <| s with coherence := coherence';
             writes_past_coherence_point := writes_past_coherence_point'|> 
let sem_of_instruction i ist =
   match i with
   | Padd  set rD rA rB -> op3regs Add set rD rA rB ist
   | Pandi rD rA simm   -> op2regi And SetCR0 rD rA (intToV simm) ist`;

val _ = export_theory()
