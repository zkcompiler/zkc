import Zkc.Tools.Audit

namespace Zkc.Tools.Formal

/-- Pinned upstream proofs participate in transitive axiom checking. Project modules
and their logical declarations are replayed locally. -/
def policy : Audit.Policy where
  axioms := Audit.allowedAxioms.push ``Classical.choice
  packages := #[`Mathlib, `VCVio]

/-- An executable proof client imports other tools. Load its source file explicitly and
audit its declarations with the same replay and axiom policy as the formal library. -/
def chargeIssuer (directory : System.FilePath) : Audit.Library :=
  { name := "written charge issuer", root := `Zkc.Tools.Formal.DrawCharge, kind := .tests, directory }

end Zkc.Tools.Formal
