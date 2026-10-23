module

public import ZkcSecurity.Examples.Components.TwoSumsValidator
public meta import ZkcSecurity.Tools.ComponentCost
public import ZkcSecurity.Examples.Components.SmallSumcheckSoundness

@[expose] public section
noncomputable section

/-! Sequential adversarial composition at the actual reached history. A false
child forces the final conjunction to be false outside the already installed
conditional escape events. No independence premise is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ZkcSecurity.Examples.Components.TwoSums.Soundness
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript Zkc.Obligations
open ZkcSecurity.Obligations ZkcSecurity.FiatShamir
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Families.Sumcheck.TableComponent

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]
abbrev field := Validator.field
abbrev compiled := ZkcSecurity.Examples.Generated.TwoSums.validatorCompiled

def Rejected (result : Domain.Result (uniformCarriers F G)) : Prop :=
  compiled.acceptance result ≠ some true

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
 theorem decision_false (raw : List F) (state : CompiledValidator.State F G)
    (wrong : raw.length ≠ 2 ^ state.point.length ∨
      state.scalar ≠ (Zkc.Polynomial.Multilinear.restrictPrefixValues raw state.point).sum) :
    Validator.decision raw state = false :=
  SmallSumcheck.Soundness.terminal_false raw state wrong

noncomputable def finish_reject
    [∀ event : Domain.Event (uniformCarriers F G), SampleableType (Domain.Raw event)]
    (charge : Domain.History (uniformCarriers F G) → Domain.Event (uniformCarriers F G) → ENNReal)
    (right : List F) (capture : Domain.Environment (uniformCarriers F G))
    (leftAccepted : Bool) (state : CompiledValidator.State F G) (history : Domain.History (uniformCarriers F G))
    (bad : leftAccepted = false ∨ Validator.decision right state = false) :
    Derivation (Nominal.interface (G := G) field) (boundedEscape charge)
      (fun _ result => Rejected result) history
      (Validator.finish right capture leftAccepted (CompiledValidator.carried field Validator.suite state)) := by
  simp only [Validator.finish, CompiledValidator.carried, CompiledValidator.decode]
  split
  · apply Derivation.done
    have decision : (leftAccepted && Validator.decision right state) = false := by
      rcases bad with bad | bad <;> simp only [bad, Bool.false_and, Bool.and_false]
    rw [decision]
    change some false ≠ some true
    decide
  · exact .halt .exhausted

noncomputable def afterLeft_reject
    [∀ event : Domain.Event (uniformCarriers F G), SampleableType (Domain.Raw event)]
    (charge : Domain.History (uniformCarriers F G) → Domain.Event (uniformCarriers F G) → ENNReal)
    (sampling : (Nominal.queriesWithFrame (G := G) field (CompiledValidator.frameUpdate (F := F) (G := G) field)).ConditionalBound
      (Nominal.layoutWithFrame field (CompiledValidator.frameUpdate (F := F) (G := G) field)).representation 1 1 charge)
    (left right : List F) (rightClaim : F) (count : Nat)
    (capture : Domain.Environment (uniformCarriers F G)) (state : CompiledValidator.State F G)
    (history : Domain.History (uniformCarriers F G))
    (bad : Validator.decision left state = false ∨ (right.length = 2 ^ count → rightClaim ≠ right.sum)) :
    Derivation (Nominal.interface (G := G) field) (boundedEscape charge)
      (fun _ result => Rejected result) history
      (Validator.afterLeft left right rightClaim count capture (CompiledValidator.carried field Validator.suite state)) := by
  simp only [Validator.afterLeft, CompiledValidator.carried, CompiledValidator.decode]
  split
  · rw [PIR.Process.bind_assoc]
    by_cases leftBad : Validator.decision left state = false
    · apply (ZkcSecurity.Obligations.unrestricted (absorb := Nominal.interface (G := G) field)
        (charge := charge) (CompiledValidator.run field ValidatorRightRound.sites (List.range count)
          ⟨[], rightClaim, state.history⟩) history).bind
      intro reached final _
      simp only [PIR.Process.bind]
      exact finish_reject charge right _ _ final reached (Or.inl leftBad)
    · have rightBad := bad.resolve_left leftBad
      apply (CompiledValidator.run_rejecting field ValidatorRightRound.sites charge sampling right rightClaim count state.history history rightBad).bind
      intro reached final post
      simp only [PIR.Process.bind]
      exact finish_reject charge right _ _ final reached (Or.inr (decision_false right final post))
  · exact .halt .exhausted

noncomputable def derivation
    [∀ event : Domain.Event (uniformCarriers F G), SampleableType (Domain.Raw event)]
    (charge : Domain.History (uniformCarriers F G) → Domain.Event (uniformCarriers F G) → ENNReal)
    (sampling : (Nominal.queriesWithFrame (G := G) field (CompiledValidator.frameUpdate (F := F) (G := G) field)).ConditionalBound
      (Nominal.layoutWithFrame field (CompiledValidator.frameUpdate (F := F) (G := G) field)).representation 1 1 charge)
    (left right : List F) (leftClaim rightClaim : F) (count : Nat) (initial : Domain.History (uniformCarriers F G))
    (wrong : left.length = 2 ^ count → right.length = 2 ^ count →
      leftClaim ≠ left.sum ∨ rightClaim ≠ right.sum) :
    Derivation (Nominal.interface (G := G) field) (boundedEscape charge)
      (fun _ result => Rejected result) initial (Validator.presented left right leftClaim rightClaim count initial) := by
  have side : (left.length = 2 ^ count → leftClaim ≠ left.sum) ∨
      (right.length = 2 ^ count → rightClaim ≠ right.sum) := by
    by_cases leftShape : left.length = 2 ^ count
    · by_cases rightShape : right.length = 2 ^ count
      · rcases wrong leftShape rightShape with bad | bad
        · exact Or.inl (fun _ => bad)
        · exact Or.inr (fun _ => bad)
      · exact Or.inr (fun shape => (rightShape shape).elim)
    · exact Or.inl (fun shape => (leftShape shape).elim)
  unfold Validator.presented
  split
  · rw [PIR.Process.bind_assoc]
    by_cases leftBad : left.length = 2 ^ count → leftClaim ≠ left.sum
    · apply (CompiledValidator.run_rejecting field ValidatorLeftRound.sites charge sampling left leftClaim count initial initial leftBad).bind
      intro reached final post
      simp only [PIR.Process.bind]
      exact afterLeft_reject charge sampling left right rightClaim count _ final reached
        (Or.inl (decision_false left final post))
    · have rightBad := side.resolve_left leftBad
      apply (ZkcSecurity.Obligations.unrestricted (absorb := Nominal.interface (G := G) field)
        (charge := charge) (CompiledValidator.run field ValidatorLeftRound.sites (List.range count)
          ⟨[], leftClaim, initial⟩) initial).bind
      intro reached final _
      simp only [PIR.Process.bind]
      exact afterLeft_reject charge sampling left right rightClaim count _ final reached (Or.inr rightBad)
  · exact .halt .refused

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
 theorem cost
    (charge : Domain.History (uniformCarriers F G) → Domain.Event (uniformCarriers F G) → ENNReal)
    (price : ENNReal) (priced : ∀ history origin, charge history (.challenge origin) ≤ price)
    (left right : List F) (leftClaim rightClaim : F) (count : Nat) (initial : Domain.History (uniformCarriers F G)) :
    Typed.ChargedCostBound (Nominal.interface (G := G) field) charge
      (Validator.presented left right leftClaim rightClaim count initial) initial (8 • price) := by
  derive_component_cost [CompiledValidator.run_cost _ _ charge price priced] unfolding
    [Validator.presented, Validator.afterLeft, Validator.finish, CompiledValidator.carried, CompiledValidator.decode]

#print axioms derivation
#print axioms cost
end ZkcSecurity.Examples.Components.TwoSums.Soundness
