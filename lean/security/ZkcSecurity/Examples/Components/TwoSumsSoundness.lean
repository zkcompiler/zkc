module

public import ZkcSecurity.Examples.Components.TwoSumsValidator
public meta import ZkcSecurity.Tools.ComponentCost
public meta import ZkcSecurity.Tools.ComponentDerivation
public import ZkcSecurity.Families.Sumcheck.CompiledValidatorSoundness

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
  derive_component_rejection
    [CompiledValidator.run_rejecting field ValidatorLeftRound.sites charge sampling left,
      CompiledValidator.run_rejecting field ValidatorRightRound.sites charge sampling right]
    unfolding [Validator.presented, Validator.afterLeft, Validator.finish, Validator.decision,
      CompiledValidator.carried, CompiledValidator.decode]
    finishing (change some _ ≠ some true; simp (disch := assumption) only [SumcheckValidatorHelpers.terminal_rejects, Bool.false_and, Bool.and_false]; decide)

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
