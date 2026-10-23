module

public import ZkcSecurity.Examples.Components.TwoSumsReadback
public import ZkcSecurity.Examples.Components.TwoSumsOrigins
public import ZkcSecurity.Examples.Components.TwoSumsFormula
public import ZkcSecurity.FiatShamir.HonestReadbackCompleteness

@[expose] public section

/-! Compiled honest completeness of the fixed generated TwoSums Subject. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace ZkcSecurity.Examples.Components.TwoSums
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair ZkcSecurity.Domains.PrimeField
open ZkcSecurity.FiatShamir

open ZkcSecurity.Examples.Generated.TwoSums (subject)
local notation "Scalar" => TwoSums.Formula.Scalar
local instance : ∀ event : Domain.Event blsScalarModel.toCarriers,
    SampleableType (Domain.Raw event) := rawSampleable blsModulus

open ZkcSecurity.Examples.Generated.Components.TwoSumsABI

/-- Mathematical input law for the shared read-back assembler. Runtime input
elimination and environment transport are handled by the checked ABI. -/
theorem mathematical_readback (values : Data) (related : subject.Relation (abi.pack values))
    (honest : subject.HonestInput (abi.pack values)) :
    Readback
      (fun _ result => HonestCompiled.acceptanceAt subject.selection.position result.values = some true)
      (Domain.participant blsScalarModel ZkcSecurity.Examples.Generated.TwoSums.imported.program
        subject.selection.context ZkcSecurity.Examples.Generated.TwoSums.selected.artifacts.producer (abi.producer values))
      (Domain.participant blsScalarModel ZkcSecurity.Examples.Generated.TwoSums.imported.program
        subject.selection.context ZkcSecurity.Examples.Generated.TwoSums.selected.artifacts.validator (abi.validator values)) := by
  obtain ⟨left, right, leftClaim, rightClaim, count, service, rfl⟩ := data_surjective values
  obtain ⟨_, _, _, leftBound, leftShape, _, _, _, rightBound, rightShape, allowed, _⟩ :=
    (honestInput_iff left right leftClaim rightClaim count service).mp honest
  obtain ⟨leftCorrect, rightCorrect⟩ :=
    (Formula.relation_iff left right leftClaim rightClaim count service leftBound rightBound).mp related
  subst leftClaim
  subst rightClaim
  exact root_readback (G := Scalar) actualContext (by rfl)
    actualOrigins left right count allowed
    (by simpa only [Nat.one_mul] using leftShape) (by simpa only [Nat.one_mul] using rightShape)
    leftBound rightBound (initialHistory left right left.sum right.sum count)

/-- Zero ENNReal failure mass for the actual exported pair, from the empty
shared ROM cache, on every source-related honest input. -/
theorem compiled_ideal_complete : CanonicalCompleteness subject 0 :=
  Readback.perfect_abi subject abi Formula.nonvacuous mathematical_readback

end ZkcSecurity.Examples.Components.TwoSums
