module

public import ZkcSecurity.Examples.Components.SmallSumcheckReadback
public import ZkcSecurity.Examples.Components.SmallSumcheckOrigins
public import ZkcSecurity.Examples.Components.SmallSumcheckFormula
public import ZkcSecurity.FiatShamir.HonestReadbackCompleteness

@[expose] public section

/-! Compiled honest completeness of the fixed generated SmallSumcheck Subject. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace ZkcSecurity.Examples.Components.SmallSumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair ZkcSecurity.Domains.PrimeField
open ZkcSecurity.FiatShamir

open ZkcSecurity.Examples.Generated.SmallSumcheck (subject)
local notation "Scalar" => SmallSumcheck.Formula.Scalar
local instance : ∀ event : Domain.Event blsScalarModel.toCarriers,
    SampleableType (Domain.Raw event) := rawSampleable blsModulus

open ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI

/-- Mathematical input law for the shared read-back assembler. Runtime input
elimination and environment transport are handled by the checked ABI. -/
theorem mathematical_readback (values : Data) (related : subject.Relation (abi.pack values))
    (honest : subject.HonestInput (abi.pack values)) :
    Readback
      (fun _ result => HonestCompiled.acceptanceAt subject.selection.position result.values = some true)
      (Domain.participant blsScalarModel ZkcSecurity.Examples.Generated.SmallSumcheck.imported.program
        subject.selection.context ZkcSecurity.Examples.Generated.SmallSumcheck.selected.artifacts.producer (abi.producer values))
      (Domain.participant blsScalarModel ZkcSecurity.Examples.Generated.SmallSumcheck.imported.program
        subject.selection.context ZkcSecurity.Examples.Generated.SmallSumcheck.selected.artifacts.validator (abi.validator values)) := by
  obtain ⟨raw, claim, count, service, rfl⟩ := data_surjective values
  obtain ⟨_, _, _, bounded, shape, allowed, _⟩ := (honestInput_iff raw claim count service).mp honest
  have correct := (Formula.relation_iff raw claim count service bounded).mp related
  subst claim
  exact root_readback (G := Scalar) actualContext (by rfl)
    actualOrigins raw count allowed (by simpa only [Nat.one_mul] using shape) bounded
    (initialHistory raw raw.sum count)

/-- Zero ENNReal failure mass for the actual exported pair, from the empty
shared ROM cache, on every source-related honest input. -/
theorem compiled_ideal_complete : CanonicalCompleteness subject 0 :=
  Readback.perfect_abi subject abi Formula.nonvacuous mathematical_readback

end ZkcSecurity.Examples.Components.SmallSumcheck
