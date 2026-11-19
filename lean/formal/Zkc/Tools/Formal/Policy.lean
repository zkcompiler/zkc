import Zkc.Tools.Audit

namespace Zkc.Tools.Formal

/-- Pinned upstream proofs participate in transitive axiom checking. Project modules
and their logical declarations are replayed locally. -/
def policy : Audit.Policy where
  axioms := Audit.allowedAxioms.push ``Classical.choice
  packages := #[`Mathlib, `VCVio]

end Zkc.Tools.Formal
