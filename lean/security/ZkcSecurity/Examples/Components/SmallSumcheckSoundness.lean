module

public import ZkcSecurity.Examples.Components.SmallSumcheckValidator
public meta import ZkcSecurity.Tools.ComponentCost
public import ZkcSecurity.Families.Sumcheck.CompiledValidatorSoundness

@[expose] public section
noncomputable section

/-! All-reply soundness for the actual full SmallSumcheck validator. Shape and
round bounds are internal execution cases. They are not false-statement or
soundness-policy premises. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ZkcSecurity.Examples.Components.SmallSumcheck.Soundness
open ZkcExamples.Structured
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript Zkc.Obligations
open ZkcSecurity.Obligations ZkcSecurity.FiatShamir
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Families.Sumcheck.TableComponent

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev field := Validator.field
abbrev compiled := ZkcSecurity.Examples.Generated.SmallSumcheck.validatorCompiled

def Rejected (result : Domain.Result (uniformCarriers F G)) : Prop :=
  compiled.acceptance result ≠ some true

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
 theorem terminal_false (raw : List F) (state : CompiledValidator.State F G)
    (wrong : raw.length ≠ 2 ^ state.point.length ∨
      state.scalar ≠ (Zkc.Polynomial.Multilinear.restrictPrefixValues raw state.point).sum) :
    decide (PrimitiveLibrary.HasShape raw state.point.length 1 ∧
      (Zkc.Polynomial.Multilinear.restrictPrefixValues raw state.point).sum = state.scalar) = false := by
  apply decide_eq_false_iff_not.mpr
  rintro ⟨shape, same⟩
  rcases wrong with bad | bad
  · exact bad (by simpa only [Nat.mul_one] using shape.length)
  · exact bad same.symm

noncomputable def derivation
    [∀ event : Domain.Event (uniformCarriers F G), SampleableType (Domain.Raw event)]
    (charge : Domain.History (uniformCarriers F G) → Domain.Event (uniformCarriers F G) → ENNReal)
    (sampling : (Nominal.queriesWithFrame (G := G) field (CompiledValidator.frameUpdate (F := F) (G := G) field)).ConditionalBound
      (Nominal.layoutWithFrame field (CompiledValidator.frameUpdate (F := F) (G := G) field)).representation 1 1 charge)
    (raw : List F) (claim : F) (count : Nat) (initial : Domain.History (uniformCarriers F G))
    (wrong : raw.length = 2 ^ count → claim ≠ raw.sum) :
    Derivation (Nominal.interface (G := G) field) (boundedEscape charge)
      (fun _ result => Rejected result) initial (Validator.presented raw claim count initial) := by
  unfold Validator.presented
  split
  · rw [PIR.Process.bind_assoc]
    apply (CompiledValidator.run_rejecting field ValidatorRound.sites charge sampling raw claim count initial initial wrong).bind
    intro reached state post
    simp only [PIR.Process.bind, Validator.finish, CompiledValidator.decode, CompiledValidator.carried]
    split
    · apply Derivation.done
      have decision := terminal_false raw state post
      rw [decision]
      change some false ≠ some true
      decide
    · exact .halt .exhausted
  · exact .halt .refused

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
 theorem cost
    (charge : Domain.History (uniformCarriers F G) → Domain.Event (uniformCarriers F G) → ENNReal)
    (price : ENNReal) (priced : ∀ history origin, charge history (.challenge origin) ≤ price)
    (raw : List F) (claim : F) (count : Nat) (initial : Domain.History (uniformCarriers F G)) :
    Typed.ChargedCostBound (Nominal.interface (G := G) field) charge
      (Validator.presented raw claim count initial) initial (2 • price) := by
  derive_component_cost [CompiledValidator.run_cost _ _ charge price priced] unfolding
    [Validator.presented, Validator.finish, CompiledValidator.carried, CompiledValidator.decode]

#print axioms derivation
#print axioms cost
end ZkcSecurity.Examples.Components.SmallSumcheck.Soundness
