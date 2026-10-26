module

public import ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers
public import ZkcSecurity.Families.Sumcheck.TableComponentReadbackRound
public import ZkcSecurity.Families.Sumcheck.TableComponentPrefix

@[expose] public section
set_option autoImplicit false
namespace ZkcSecurity.Realizations.Sumcheck.DomainHelpers
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured PrimitiveLibrary SumcheckHelperBodies SumcheckHelperLaws
open ZkcExamples.Structured.SumcheckArtifacts.DomainHelpers
variable (program : Structured.Program)
  (bodies : SumcheckUnitContracts.Bodies program.payload.definitions)
include bodies
omit bodies in
/-- Only the example layer connects complete admitted bodies to the generic
family's semantic law record. All names and the nominal domain are checked. -/
theorem round_helpers {K H : Type} [Field K] [AddCommGroup H] [Module K H]
    [DecidableEq K] [DecidableEq H] (program : Structured.Program) (bodies : Bodies program)
    (plan : ZkcSecurity.Families.Sumcheck.TableComponent.ReadbackRound.Plan)
    (fieldName : plan.field = "bls12-381.fr")
    (sumsName : plan.sumsHelper = sumsHelper.name)
    (firstName : plan.firstHelper = MapFirstBodies.firstHelper.name)
    (appendName : plan.appendHelper = appendHelper.name) :
    ZkcSecurity.Families.Sumcheck.TableComponent.ReadbackRound.HelperLaws
      (F := K) (G := H) program plan := by
  constructor
  · intro raw dimension length bounded small positive
    rw [fieldName, sumsName]
    have shape : HasShape raw dimension 1 :=
      hasShape_of_length _ _ _ (by decide) small (by simpa using length)
    exact sums program bodies.sumcheck raw dimension 1
      (lt_trans small (by decide +kernel)) positive (shape.split_valid positive)
  · intro raw dimension challenge length bounded small positive
    rw [fieldName, firstName]
    exact first program bodies.sumcheck raw dimension 1 challenge
      (hasShape_of_length _ _ _ (by decide) small (by simpa using length)) bounded positive
  · intro point challenge
    rw [fieldName, appendName]
    exact append program bodies.sumcheck point challenge

omit bodies in
/-- The same terminal source condition follows from every completed honest
prefix invariant, independently of the caller's retained frame. -/
theorem terminal_condition {K Frame : Type} [Field K]
    (raw : List K) (state : ZkcSecurity.Families.Sumcheck.TableComponent.PrefixState K Frame 0)
    (original : state.original = raw) (bounded : raw.length < indexLimit)
    (honest : state.scalar = state.entries.sum) :
    HasShape raw state.point.length 1 ∧
      (Zkc.Polynomial.Multilinear.restrictPrefixValues raw state.point).sum = state.scalar := by
  have length : raw.length = 2 ^ state.point.length := by
    simpa only [original, List.length_nil, Nat.zero_add] using state.shape
  have shape : HasShape raw state.point.length 1 := by
    apply hasShape_of_length _ _ _ (by decide)
    · apply (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : Nat))).mp
      simpa only [length, indexLimit] using bounded
    · simpa only [Nat.mul_one] using length
  refine ⟨shape, ?_⟩
  simpa only [ZkcSecurity.Families.Sumcheck.TableComponent.PrefixState.entries, original]
    using honest.symm

end ZkcSecurity.Realizations.Sumcheck.DomainHelpers
