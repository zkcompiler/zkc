import Zkc.Construction.ArtifactBindingTactic

/-! Generic proof-search controls: branching, all replies, checkpoints and
refusal of unequal stops and returns. No protocol-specific rule is used. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace Tests.ArtifactBindingControls
open Zkc Zkc.Source Zkc.Construction
variable (carriers : Structured.Carriers)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
example (condition : Prop) [Decidable condition] :
    Original.Simulation (carriers := carriers) Eq (fun _ _ => True)
      (if condition then .done (1 : Nat) else .halt .reject)
      (if condition then .done (1 : Nat) else .halt .reject) := by
  derive_artifact_binding normalizing (try simp only [ite_true, ite_false]) solving (first | rfl | trivial)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
example (operation : Domain.Effect carriers) :
    Original.Simulation (carriers := carriers) Eq (fun _ _ => True)
      (.call operation fun _ => .done (1 : Nat))
      (.call (.checkpoint []) fun _ => .call operation fun _ => .done (1 : Nat)) := by
  derive_artifact_binding normalizing (skip) solving (first | rfl | trivial)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
example : True := by
  fail_if_success
    have invalid : Original.Simulation (carriers := carriers) Eq (fun _ _ => True)
        (.halt .reject : PIR.Process (Domain.effects carriers) Nat) (.halt .refused) := by
      derive_artifact_binding normalizing (skip) solving (first | rfl | trivial)
  trivial

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
example : True := by
  fail_if_success
    have invalid : Original.Simulation (carriers := carriers) Eq (fun _ _ => True)
        (.done (1 : Nat)) (.done (2 : Nat)) := by
      derive_artifact_binding normalizing (skip) solving (first | rfl | trivial)
  trivial

private def observed (n : Nat) : PIR.Process (Domain.effects carriers) Nat :=
  .call (.observe (.challenge ⟨"entry", [], none⟩)) fun _ => .done n

private def inferredWitness (n witness : Nat) (_fixed : witness = n) :
    Original.Simulation (carriers := carriers) Eq (fun _ _ => True)
      (observed carriers n)
      (.call (.observe (.challenge ⟨"entry", [], none⟩)) fun _ => .done n) :=
  .call _ fun _ => .done rfl

attribute [local irreducible] observed

-- The equation must infer the data witness before any witness side tactic.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
example (n : Nat) :
    Original.Simulation (carriers := carriers) Eq (fun _ _ => True)
      (observed carriers n)
      (.call (.observe (.challenge ⟨"entry", [], none⟩)) fun _ => .done n) := by
  derive_artifact_binding [inferredWitness carriers n]
    normalizing (skip) solving (first | rfl | exact True.intro)

end Tests.ArtifactBindingControls
