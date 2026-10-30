module

public import ZkcSecurity.Bindings.Sumcheck.DomainHelpers
public import Zkc.Protocols.Sumcheck.Source.DomainHelpers

@[expose] public section

/-! Total raw-table terminal law at the bounded challenge-prefix lengths used
by compiled validators. Oversized vectors exhaust in the actual helper before
acceptance; their absence from honest input policies is irrelevant here. -/
set_option autoImplicit false
namespace ZkcSecurity.Realizations.Sumcheck.ValidatorHelpers
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured PrimitiveLibrary SumcheckHelperBodies SumcheckHelperLaws
open ZkcExamples.Structured.SumcheckArtifacts

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Exhaustion in a typed invocation forces the actual lookup and signature;
a missing helper or mismatched signature would refuse instead. -/
theorem call_exhausted (program : Structured.Program) (helper : Helper)
    (arguments : Values (assignment F G) helper.inputs)
    (encoded : Domain.Environment (ringModel F G).toCarriers)
    (encoding : Domain.encodeValues arguments = some encoded)
    (law : invoke (closedMeanings program.payload.definitions) helper arguments = .halt .exhausted) :
    Domain.callHelper (ringModel F G) program helper.name (helper.outputs.map ValueSort.data) encoded =
      .stopped .exhausted := by
  unfold closedMeanings at law
  rw [← Domain.Binding.helperTable_ringModel] at law
  cases found : (Domain.helperTable (ringModel F G) program).find? (fun entry => entry.helper.name == helper.name) with
  | none => simp [invoke, found] at law
  | some entry =>
    by_cases signature : entry.helper = helper
    · subst helper
      simp only [invoke, found, ↓reduceDIte] at law
      rw [Domain.Binding.callHelper_of_lookup (ringModel F G) program entry found arguments encoded encoding, law]
      rfl
    · simp [invoke, found, signature] at law

/-- Every raw length is included. The sole prefix bound is supplied by the
actual Max guard plus successful loop output, never by a receipt premise. -/
theorem terminal_all (program : Structured.Program) (bodies : ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers.Bodies program)
    (raw point : List F) (claim : F) (pointSmall : point.length < 64) :
    Domain.callHelper (ringModel F G) program checkHelper.name [.data .boolean]
      [.data (.vector "bls12-381.fr" raw), .data (.vector "bls12-381.fr" point),
        .data (.field "bls12-381.fr" claim)] =
      if raw.length < indexLimit then
        .returned [.data (.boolean (decide (HasShape raw point.length 1 ∧
          (Zkc.Polynomial.Multilinear.restrictPrefixValues raw point).sum = claim)))]
      else .stopped .exhausted := by
  by_cases bounded : raw.length < indexLimit
  · rw [ite_eq_left bounded]
    exact ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers.check program bodies.terminal
      raw point claim bounded (pointSmall.trans (by decide +kernel))
  · rw [ite_eq_right bounded]
    apply call_exhausted program checkHelper (checkInputs raw point claim) _ rfl
    rw [bodies.check.invoke program.payload.linked]
    exact check_vector_exhausted_generic_body _
      (lessAll_bounded _ (SumcheckUnitContracts.first_laws program.payload.linked bodies.sumcheck).less)
      (SumcheckUnitContracts.shape_body program.payload.linked bodies.sumcheck) raw point claim pointSmall bounded

/-- A false table residual makes this implementation's actual terminal check
reject. The source-specific shape predicate belongs at the helper-realization
boundary, while the family reduction remains independent of that predicate. -/
theorem terminal_rejects (raw point : List F) (scalar : F)
    (wrong : raw.length ≠ 2 ^ point.length ∨
      scalar ≠ (Zkc.Polynomial.Multilinear.restrictPrefixValues raw point).sum) :
    decide (PrimitiveLibrary.HasShape raw point.length 1 ∧
      (Zkc.Polynomial.Multilinear.restrictPrefixValues raw point).sum = scalar) = false := by
  apply decide_eq_false_iff_not.mpr
  rintro ⟨shape, same⟩
  rcases wrong with bad | bad
  · exact bad (by simpa only [Nat.mul_one] using shape.length)
  · exact bad same.symm

/-- Source normalization may use the proved iteration count in the terminal
shape test. Retain the loop length fact when transporting its rejection law. -/
theorem terminal_rejects_at (raw point : List F) (scalar : F) (count : Nat)
    (wrong : (raw.length ≠ 2 ^ point.length ∨
      scalar ≠ (Zkc.Polynomial.Multilinear.restrictPrefixValues raw point).sum) ∧ point.length = count) :
    decide (PrimitiveLibrary.HasShape raw count 1 ∧
      (Zkc.Polynomial.Multilinear.restrictPrefixValues raw point).sum = scalar) = false := by
  rw [← wrong.2]
  exact terminal_rejects raw point scalar wrong.1

end ZkcSecurity.Realizations.Sumcheck.ValidatorHelpers
