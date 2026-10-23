module

public import ZkcSecurity.Examples.Components.SmallSumcheckValidator
public meta import ZkcSecurity.Tools.ComponentCost
public meta import ZkcSecurity.Tools.ComponentDerivation
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


noncomputable def derivation
    [∀ event : Domain.Event (uniformCarriers F G), SampleableType (Domain.Raw event)]
    (charge : Domain.History (uniformCarriers F G) → Domain.Event (uniformCarriers F G) → ENNReal)
    (sampling : (Nominal.queriesWithFrame (G := G) field (CompiledValidator.frameUpdate (F := F) (G := G) field)).ConditionalBound
      (Nominal.layoutWithFrame field (CompiledValidator.frameUpdate (F := F) (G := G) field)).representation 1 1 charge)
    (raw : List F) (claim : F) (count : Nat) (initial : Domain.History (uniformCarriers F G))
    (wrong : raw.length = 2 ^ count → claim ≠ raw.sum) :
    Derivation (Nominal.interface (G := G) field) (boundedEscape charge)
      (fun _ result => Rejected result) initial (Validator.presented raw claim count initial) := by
  derive_component_rejection [CompiledValidator.run_rejecting field ValidatorRound.sites charge sampling raw]
    unfolding [Validator.presented, Validator.finish, CompiledValidator.carried, CompiledValidator.decode]
    finishing (change some _ ≠ some true; simp (disch := assumption) only [SumcheckValidatorHelpers.terminal_rejects, Bool.false_and, Bool.and_false]; decide)

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
