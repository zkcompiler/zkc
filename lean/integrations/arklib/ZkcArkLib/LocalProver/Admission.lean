import Zkc.Protocols.Sumcheck.LocalProver.Admission
import ZkcArkLib.LocalProver.Source
import ZkcArkLib.LocalProver.Inputs

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.LocalProver.Source
open PIR Zkc.Protocols.Sumcheck.LocalProver Zkc.Protocols.Sumcheck.LocalProver.Source

/-- Admission also rules out every missing-input fallback in the actual
    probabilistic source execution, not merely in a dependency inventory. -/
theorem checked_no_default {F : Type} [CommRing F] [DecidableEq F]
    (p : Code) (inputs : List F) (checked : inputCheck p inputs = true)
    (fallback : Nat → F) :
    (source p (initial inputs)).runM handler () =
      retain <$> ZkcArkLib.LocalProver.execFallback fallback pure p (initial inputs) := by
  rw [ZkcArkLib.LocalProver.exec_no_default fallback pure p (initial inputs)
    ((inputCheck_iff p inputs).mp checked)]
  exact execution_exact p (initial inputs)


end ZkcArkLib.LocalProver.Source
