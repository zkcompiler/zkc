import Zkc.Construction.OriginalCorrespondence
import Zkc.Construction.ArtifactBindingTactic
import Zkc.Source.KernelRfl
import Mathlib.Data.ZMod.Basic

/-! A nonlinear original/constructed certificate independent of Sumcheck.
This is a symbolic all-input interpretation test, not a security endpoint or a
claim that an arbitrary ring realizes the source catalogue's concrete field. -/
set_option autoImplicit false
set_option smartUnfolding false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
namespace Tests.OriginalPolynomial
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Construction.Original

private def source : Snapshot where
  source := "sha256:0000000000000000000000000000000000000000000000000000000000000000"
  entry := "Square"
  domains := []
  relations := []
  bindings := []
  definitions := [.function ⟨"Square", .protocol, .publicDef,
    [.field "bls12-381.fr", .field "bls12-381.fr"], [.boolean],
    some ⟨["P", "V"], [["P", "V"], ["P", "V"]], [["V"]]⟩, [], none,
    .block [
      .instruction (.fieldMultiply "bls12-381.fr") [0, 0] [.field "bls12-381.fr"] [] "",
      .instruction (.fieldEqual "bls12-381.fr") [0, 2] [.boolean] [] ""] (.ret [0])⟩]
  contracts := [⟨"Square", []⟩]
  catalogue := admittedCatalogue

private def program : Program := (check source).toOption.get (by decide +kernel)
private def context : Context :=
  ⟨"Square", ["P", "V"], 0, 1, 0, "random.bls12-381.fr/0", none, "suite", []⟩
private def routing : Routing := ⟨source, context, .validator, 73, [], [], [], []⟩
private def artifact : Participant where
  source := "fixture"
  candidate := "fixture"
  policy := ⟨"Square", "P", "V", 0, "suite", [], [], [], "fixture", "fixture"⟩
  symbol := "validator"
  inputs := [.data (.field "bls12-381.fr"), .data (.field "bls12-381.fr"), .transcript "suite"]
  outputs := [.data .boolean, .transcript "suite"]
  instructions := [
    ⟨.calculate (.fieldMultiply "bls12-381.fr"), [0, 0], [.data (.field "bls12-381.fr")], []⟩,
    ⟨.calculate (.fieldEqual "bls12-381.fr"), [3, 1], [.data .boolean], []⟩]
  returned := [4, 2]

variable {F : Type} [CommRing F] [DecidableEq F]
private abbrev model : DomainModel := ringModel F F
private abbrev SourceResult := Values (Component (model (F := F)).Value) [.boolean] × State (model (F := F)).toCarriers
private def inputs (value claim : F) (history : Domain.History (model (F := F)).toCarriers) : Domain.Environment (model (F := F)).toCarriers :=
  [.data (.field "bls12-381.fr" value), .data (.field "bls12-381.fr" claim), .transcript "suite" history]
private def original (value claim : F) (history : Domain.History (model (F := F)).toCarriers) :=
  Original.participant model program routing 1
    (.cons (some value) (.cons (some claim) .nil)) ⟨[], history⟩
private def originalNormal (value claim : F) (history : Domain.History (model (F := F)).toCarriers) :
    PIR.Process (Domain.effects (model (F := F)).toCarriers) (SourceResult (F := F)) :=
  .done (.cons (some (decide (value * value = claim))) .nil, ⟨[], history⟩)

private theorem original_equation (value claim : F) (history : Domain.History (model (F := F)).toCarriers) :
    original value claim history = originalNormal value claim history := by kernel_rfl

private def returns (value claim : F) (history : Domain.History (model (F := F)).toCarriers)
    (source : SourceResult (F := F)) (actual : Domain.Result (model (F := F)).toCarriers) : Prop :=
  source = (.cons (some (decide (value * value = claim))) .nil, ⟨[], history⟩) ∧
  actual.values = [.data (.boolean (decide (value * value = claim))), .transcript "suite" history] ∧
  actual.environment[4]? = some (.data (.boolean (decide (value * value = claim)))) ∧
  actual.environment[2]? = some (.transcript "suite" history)

-- The artifact remains the actual interpreter input. Structural proof search
-- discharges every checkpoint; no callback-size or family recognizer is used.
private def certificate (value claim : F) (history : Domain.History (model (F := F)).toCarriers) :
    Simulation (returns value claim history)
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures (inputs value claim history) frame)
      (original value claim history)
      (Domain.participant model program context artifact (inputs value claim history)) := by
  rw [original_equation]
  unfold originalNormal
  unfold Domain.participant
  dsimp only [artifact]
  derive_artifact_binding
    normalizing (try simp [artifact, inputs, Domain.evaluate, Domain.step, Domain.read,
      Domain.sortsMatch, Domain.Value.sort, Domain.Payload.ty, PIR.Process.bind,
      Domain.Calculations.fieldMultiply, Domain.Calculations.fieldEqual])
    solving (simp [returns, Zkc.Construction.ArtifactBinding.Captures, inputs])

#print axioms certificate
end Tests.OriginalPolynomial
