module

import ProtocolProof
import ProtocolProofExamples
import Lean.Util.CollectAxioms

/-!
Audit every declaration owned by this package, including generated and private declarations.
Dependencies are traversed by Lean's axiom collector; only the standard logical axioms are
allowed. The package's ordinary build separately kernel-checks each theorem.
-/

open Lean Elab Command

run_cmd do
  let environment ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    let some index := environment.getModuleIdxFor? name | continue
    let owner := environment.header.moduleNames[index.toNat]!
    unless (`ProtocolProof).isPrefixOf owner || (`ProtocolProofExamples).isPrefixOf owner do
      continue
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Nonstandard axiom {axiomName} in {name} (module {owner})"
    checked := checked + 1
  if checked == 0 then
    throwError "No framework declarations were audited"
  logInfo m!"Axiom audit passed: {checked} package declarations; only propext, Classical.choice, Quot.sound."
