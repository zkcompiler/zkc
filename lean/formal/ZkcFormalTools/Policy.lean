import Zkc.Tools.Audit

namespace ZkcFormalTools

/-- Pinned upstream proofs participate in transitive axiom checking. Project modules
and their logical declarations are replayed locally. -/
def policy : Zkc.Tools.Audit.Policy where
  axioms := Zkc.Tools.Audit.allowedAxioms.push ``Classical.choice
  packages := #[`Mathlib, `VCVio]
  parts := Zkc.Tools.Audit.compilerParts ++
    #[(`ZkcFormal, .library), (`ZkcFormalTests, .tests), (`ZkcFormalTools, .tools)]

/-- Source-facing clients recheck admission and refer to elaboration. Each client is
a separate replay root outside the formal semantics library. -/
def publicIssuers (directory : System.FilePath) : Array Zkc.Tools.Audit.Library :=
  #[`ZkcFormalTools.DrawCharge].map fun root =>
    { name := toString root, root, kind := .tests, directory }

end ZkcFormalTools
