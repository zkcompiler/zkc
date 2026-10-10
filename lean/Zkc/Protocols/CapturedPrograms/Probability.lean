import Zkc.Protocols.CapturedPrograms.Execution

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Zkc.Protocols.CapturedPrograms.Probability
open PIR Zkc.Protocols.CorrelatedSetup Zkc.Probability.AdaptiveTape Zkc.Protocols.CorrelatedSetup.Service

variable {F : Type} [CommRing F] [DecidableEq F]

/-- The existing publication/history observer on the ACTUAL common execution.
    Hidden setup, witness and residual tape are not added to this observer. -/
def view (x : Zkc.Protocols.CapturedPrograms.Issued F) (w : Witness F) (n : Nat)
    (tape : Triple F × Tape F n) : Triple F × Outcome (History F) :=
  let p := publicationsOf w tape.1
  (p,((Zkc.Protocols.CorrelatedSetup.Execution.source (Zkc.Protocols.CapturedPrograms.controller x w) p n empty).run
    (Zkc.Protocols.CorrelatedSetup.Execution.handler (Zkc.Protocols.CapturedPrograms.setup x) w p)
      (empty,Zkc.Protocols.CorrelatedSetup.Execution.tapeList n tape.2)).outcome)

theorem view_exact (x : Zkc.Protocols.CapturedPrograms.Issued F) (w : Witness F) (n : Nat)
    (tape : Triple F × Tape F n) :
    view x w n tape =
      let old := Zkc.Protocols.CorrelatedSetup.Source.sourceCompiled x.code.service (Zkc.Protocols.CapturedPrograms.setup x) w n tape
      (old.1,.returned old.2) := by
  unfold view
  dsimp only
  rw [Zkc.Protocols.CorrelatedSetup.Execution.issued_source_exact]
  rfl

theorem view_fiber (x : Zkc.Protocols.CapturedPrograms.Issued F) (w : Witness F) (n : Nat)
    (out : Triple F × History F) (tape : Triple F × Tape F n) :
    view x w n tape = (out.1,.returned out.2) ↔
      Zkc.Protocols.CorrelatedSetup.Source.sourceCompiled x.code.service (Zkc.Protocols.CapturedPrograms.setup x) w n tape = out := by
  rw [view_exact]
  simp [Prod.ext_iff]

/-- Reuse the proved adaptive setup/session coupling through the exact common
    source observer. Uniform full tapes have enough cells for the public bound. -/
theorem witness_mass [Fintype F] (x : Zkc.Protocols.CapturedPrograms.Issued F)
    (good : x.code.service.Good) (w v : Witness F) (n : Nat)
    (out : Triple F × History F) :
    (Fintype.card {r : Triple F × Tape F n // view x w n r = (out.1,.returned out.2)} : ℚ) /
      Fintype.card (Triple F × Tape F n) =
    (Fintype.card {r : Triple F × Tape F n // view x v n r = (out.1,.returned out.2)} : ℚ) /
      Fintype.card (Triple F × Tape F n) := by
  simp_rw [view_fiber]
  exact Zkc.Protocols.CorrelatedSetup.Source.source_compiled_witness_mass _ good _ w v n out


end Zkc.Protocols.CapturedPrograms.Probability
