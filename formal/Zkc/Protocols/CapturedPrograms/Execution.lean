import Zkc.Protocols.CorrelatedSetup.Execution
import Zkc.Protocols.CapturedPrograms.Inputs

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Zkc.Protocols.CorrelatedSetup.Execution
open PIR Zkc.Probability.AdaptiveTape Zkc.Protocols.CorrelatedSetup.Service

variable {F : Type} [CommRing F]

variable [DecidableEq F]

/-- The actual issued service program now feeds the common source interpreter.
    The old compiler's source computation is retained through its exact theorem. -/
theorem issued_source_exact (x : Zkc.Protocols.CapturedPrograms.Issued F) (w : Witness F)
    (n : Nat) (tape : Triple F × Tape F n) :
    let p := publicationsOf w tape.1
    ((source (Zkc.Protocols.CapturedPrograms.controller x w) p n empty).run
      (handler (Zkc.Protocols.CapturedPrograms.setup x) w p) (empty,tapeList n tape.2)).outcome =
      .returned (Zkc.Protocols.CorrelatedSetup.Source.sourceCompiled x.code.service (Zkc.Protocols.CapturedPrograms.setup x) w n tape).2 := by
  dsimp only
  rw [history_exact,Zkc.Protocols.CorrelatedSetup.Source.source_compiled_correct,Zkc.Protocols.CorrelatedSetup.Service.compiled_correct]
  rfl


end Zkc.Protocols.CorrelatedSetup.Execution
