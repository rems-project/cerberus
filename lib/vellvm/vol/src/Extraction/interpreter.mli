open Alist
open Dopsem
open Genericvalues
open Infrastructure
open Monad
open Syntax
open Targetdata
open Trace

val interInsn :
  Opsem.OpsemAux.coq_Config -> Opsem.Opsem.coq_State ->
  (Opsem.Opsem.coq_State*trace) option

