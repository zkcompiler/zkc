import Zkc.Tools.Audit

namespace Zkc.Tools.Formal

/-- Pinned upstream proofs participate in transitive axiom checking. Project modules
and their logical declarations are replayed locally. -/
def policy : Audit.Policy where
  axioms := Audit.allowedAxioms.push ``Classical.choice
  packages := #[`Mathlib, `VCVio]

/-- Source-facing clients recheck admission and refer to elaboration. Each client is
a separate replay root outside the formal semantics library. -/
def publicIssuers (directory : System.FilePath) : Array Audit.Library :=
  #[`Zkc.Tools.Formal.DrawCharge].map fun root =>
    { name := toString root, root, kind := .tests, directory }

end Zkc.Tools.Formal
