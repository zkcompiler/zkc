import ZkcExamples.Structured.SchnorrBinding
import ZkcExamples.Structured.SchnorrContract
import ZkcExamples.Structured.SchnorrSharedWitness

set_option smartUnfolding false

namespace Tests.StructuredSchnorrBinding
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured.SchnorrBinding

example : owner.contract.clauses = [clause] := all_clauses
example : clause.kind = .target ∧ clause.name = "knowledge" ∧
    clause.residual = none ∧ clause.decision = some decisionSelector.erase := exact_clause

/-- A prover output cannot masquerade as the selected verifier decision. -/
example : ({ decisionSelector.erase with role := "role00000000" }).resolve
    owner.protocol.signature = .error "structured-contract-role" := by decide +kernel

/-- Formula absence is rejected rather than assigned a fresh mathematical meaning. -/
example : checkFormulaLinks { ZkcExamples.Structured.SchnorrInteractiveData.snapshot with
    relations := [{ application.relation.declaration with formula := none }] } =
      .error "structured-relation-formula" := by decide +kernel

/-- Equal types do not make the two role-local public-key copies equal. The
target reads the verifier's key and the explicitly assigned extracted witness. -/
example : (target (F := ZMod 3) (G := ZMod 3)).Holds {}
    (boundary 2 0 1 1 0 4 5 (some true)) (assignments 1 1) := by
  rw [target_holds_iff, relation_iff]
  simp

example : ¬ (target (F := ZMod 3) (G := ZMod 3)).Holds {}
    (boundary 2 0 1 1 0 4 5 (some true)) (assignments 1 0) := by
  rw [target_holds_iff, relation_iff]
  simp

/-- Extraction's new witness is not claimed to agree with the honest input port. -/
example : ¬ application.Agrees {}
    (boundary (F := ZMod 3) (G := ZMod 3) 2 0 1 1 0 4 5 (some true))
    (assignments 1 1) := by
  intro same
  have witness := congrArg (fun values => values.get (.there (.there .here))) same
  change some (1 : ZMod 3) = some 0 at witness
  exact one_ne_zero (Option.some.inj witness)

example : ((∃ first : ZMod 3, (0 : ZMod 3) = first • (1 : ZMod 3)) ∧
    (∃ second : ZMod 3, (1 : ZMod 3) = second • (1 : ZMod 3))) ∧
    ¬ ∃ witness : ZMod 3,
      ZkcExamples.Structured.SchnorrSharedWitness.Relation (1 : ZMod 3) 1 0 1 witness :=
  ZkcExamples.Structured.SchnorrSharedWitness.independent_not_shared

/-- An actual selected acceptance is required; an unrelated role's true return
and a stopped verifier cannot supply it. -/
example (reason : PIR.Stop) :
    decisionSelector.read {} (BoundaryValuation.ofOutcome 1
      (ZkcExamples.Structured.SchnorrInteractive.verifierInputs (F := ZMod 3) (1 : ZMod 3) 1 0)
      (.stopped reason)) = none :=
  decisionSelector.read_stopped_output {} 1 _ reason .here rfl

example : decisionSelector.read {} (BoundaryValuation.ofReturned 0
    (ZkcExamples.Structured.SchnorrInteractive.verifierInputs (F := ZMod 3) (1 : ZMod 3) 1 0)
    (.cons (some true) .nil)) = none := rfl

example : decisionSelector.read {} (BoundaryValuation.ofReturned 1
    (ZkcExamples.Structured.SchnorrInteractive.verifierInputs (F := ZMod 3) (1 : ZMod 3) 1 0)
    (.cons (some false) .nil)) ≠ some true := by
  change some false ≠ some true
  decide

example : decisionSelector.read {}
    (ZkcExamples.Structured.SchnorrContract.observedBoundary (F := ZMod 3) (1 : ZMod 3) 0 0
      ⟨1, fun _ => 0⟩ 0) ≠ some true := by
  intro accepted
  have returned := (ZkcExamples.Structured.SchnorrContract.observed_accepts_iff
    (1 : ZMod 3) 0 0 ⟨1, fun (_ : ZMod 3) => 0⟩ 0).mp accepted
  have equation := (ZkcExamples.Structured.SchnorrInteractive.accepted_iff
    (1 : ZMod 3) 0 0 ⟨1, fun (_ : ZMod 3) => 0⟩ 0).mp returned
  simp at equation

/-- Two concrete source executions, with the common commitment fixed before
the challenges, produce the retained formula's extracted witness. -/
example : (target (F := ZMod 3) (G := ZMod 3)).Holds {}
    (ZkcExamples.Structured.SchnorrContract.observedBoundary 1 1 0
      ⟨1, fun c => 1 + c⟩ 0)
    (assignments 1 (((1 : ZMod 3) - (1 + 1)) / (0 - 1))) := by
  apply ZkcExamples.Structured.SchnorrContract.extracted_target
    (1 : ZMod 3) 1 0 ⟨1, fun c => 1 + c⟩ 0 1
  · exact zero_ne_one
  · rw [ZkcExamples.Structured.SchnorrContract.observed_accepts_iff,
      ZkcExamples.Structured.SchnorrInteractive.accepted_iff]
    simp
  · rw [ZkcExamples.Structured.SchnorrContract.observed_accepts_iff,
      ZkcExamples.Structured.SchnorrInteractive.accepted_iff]
    simp

end Tests.StructuredSchnorrBinding
