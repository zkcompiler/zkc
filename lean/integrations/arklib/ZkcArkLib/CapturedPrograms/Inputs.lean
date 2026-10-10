import ZkcArkLib.CapturedPrograms.Selection
import ZkcArkLib.LocalProver.Inputs

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.CapturedPrograms
open Zkc.Protocols.CapturedPrograms Zkc.Protocols.Sumcheck.LocalProver ZkcArkLib.LocalProver OracleComp Zkc.Source.Availability

variable {F A : Type} [CommRing F] [DecidableEq F]

theorem issued_no_default (scope : List Nat) (s : Env F) (p : Tree) (x : Issued F)
    (h : issue scope s p = some x) (fallback : Nat → F) (k : Cut F → ProbComp A) :
    execFallback fallback k x.code.causal (initial x.inputs) =
      exec k x.code.causal (initial x.inputs) :=
  exec_no_default fallback k x.code.causal (initial x.inputs) (issued_ok scope s p x h).2.2


end ZkcArkLib.CapturedPrograms
