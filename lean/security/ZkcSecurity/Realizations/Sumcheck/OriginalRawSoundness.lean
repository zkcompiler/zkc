module

public import ZkcSecurity.Realizations.Sumcheck.OriginalRawPresentation

@[expose] public section

/-! All-input rejection and pathwise cost through the existing table reference.
Raw shape is a case in the residual proof, never an input-policy premise. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript Zkc.Obligations
open ZkcSecurity.FiatShamir ZkcSecurity.Obligations
open ZkcSecurity.Families.Sumcheck TableComponent

variable {F G : Type} [Field F] [DecidableEq F]
variable {charge : Domain.History (uniformCarriers F G) → Domain.Event (uniformCarriers F G) → ENNReal}
variable [∀ event, SampleableType (@Domain.Raw (uniformCarriers F G) event)]

def terminal_rejected (raw point : List F) (scalar : F)
    (construction : ConstructionState (F := F) (G := G)) (history : Domain.History (uniformCarriers F G))
    (wrong : raw.length < indexLimit → raw.length ≠ 2 ^ point.length ∨
      scalar ≠ (Zkc.Polynomial.Multilinear.restrictPrefixValues raw point).sum) :
    Derivation (Nominal.interface (G := G) "bls12-381.fr") (boundedEscape charge)
      (fun _ result => acceptance result ≠ some true) history
      ((terminal raw point scalar).bind fun result => .done (result, construction)) := by
  unfold terminal
  split
  · split
    · split
      · rename_i rawBound
        rw [ValidatorHelpers.terminal_rejects raw point scalar (wrong rawBound)]
        exact .done (by change some false ≠ some true; decide)
      · exact .halt .exhausted
    · exact .done (by change some false ≠ some true; decide)
  · exact .halt .exhausted

/-- False target scalars reject for every raw shape and count. The weaker
conditional premise also covers target index exhaustion and malformed tables.
Every successful prior callback remains in the derivation, including its query. -/
noncomputable def root_rejected
    (sampling : (Nominal.queriesWithFrame (G := G) "bls12-381.fr"
      (TableComponent.Execution.frameUpdate (F := F) (G := G) "bls12-381.fr")).ConditionalBound
      (Nominal.layoutWithFrame "bls12-381.fr"
        (TableComponent.Execution.frameUpdate (F := F) (G := G) "bls12-381.fr")).representation 1 1 charge)
    (maximum : Nat) (schedule : Nominal.Schedule "bls12-381.fr")
    (raw : List F) (scalar : F) (count : Nat)
    (construction : ConstructionState (F := F) (G := G)) (history : Domain.History (uniformCarriers F G))
    (wrong : raw.length < indexLimit → raw.length = 2 ^ count → scalar ≠ raw.sum) :
    Derivation (Nominal.interface (G := G) "bls12-381.fr") (boundedEscape charge)
      (fun _ result => acceptance result ≠ some true) history
      (root maximum schedule raw scalar count construction) := by
  unfold root
  by_cases bound : count ≤ maximum
  · rw [ite_eq_left bound]
    by_cases rawBound : raw.length < indexLimit
    · apply (TableComponent.Execution.run_rejecting "bls12-381.fr" schedule charge sampling
        raw scalar count construction.history history (wrong rawBound)).bind
      intro reached final residual
      exact terminal_rejected raw final.point final.scalar _ reached (fun _ => residual.1)
    · apply (unrestricted
        (TableComponent.Execution.run "bls12-381.fr" schedule (List.range count) ⟨[], scalar, construction.history⟩)
        history).bind
      intro reached final _
      exact terminal_rejected raw final.point final.scalar _ reached (fun bounded => (rawBound bounded).elim)
  · rw [ite_eq_right bound]
    exact .halt .refused

omit [∀ event, SampleableType (@Domain.Raw (uniformCarriers F G) event)] in
/-- A terminal helper never asks the random oracle, including exhaustion. -/
theorem terminal_cost (raw point : List F) (scalar : F)
    (construction : ConstructionState (F := F) (G := G)) (history : Domain.History (uniformCarriers F G)) :
    Typed.ChargedCostBound (Nominal.interface (G := G) "bls12-381.fr") charge
      ((terminal (G := G) raw point scalar).bind fun result => .done (result, construction)) history 0 := by
  unfold terminal
  split
  · split
    · split <;> trivial
    · trivial
  · trivial

omit [∀ event, SampleableType (@Domain.Raw (uniformCarriers F G) event)] in
/-- All counts have the same maximum budget: excessive counts refuse before
any interaction; admitted counts pay for every reached source callback. -/
theorem root_cost (price : ENNReal)
    (priced : ∀ history origin, charge history (.challenge origin) ≤ price)
    (maximum : Nat) (schedule : Nominal.Schedule "bls12-381.fr")
    (raw : List F) (scalar : F) (count : Nat)
    (construction : ConstructionState (F := F) (G := G)) (history : Domain.History (uniformCarriers F G)) :
    Typed.ChargedCostBound (Nominal.interface (G := G) "bls12-381.fr") charge
      (root maximum schedule raw scalar count construction) history (maximum • price) := by
  unfold root
  by_cases bound : count ≤ maximum
  · rw [ite_eq_left bound]
    have rounds := TableComponent.Execution.run_cost "bls12-381.fr" schedule charge price priced
      (List.range count) (⟨[], scalar, construction.history⟩ : TableComponent.Execution.State F G) history
    have full := CostComposition.bind
      (TableComponent.Execution.run "bls12-381.fr" schedule (List.range count)
        (⟨[], scalar, construction.history⟩ : TableComponent.Execution.State F G))
      (fun final => (terminal (G := G) raw final.point final.scalar).bind
        fun result => .done (result, { construction with history := final.history })) (count • price) 0
      (by simpa only [List.length_range] using rounds)
      (fun final reached => terminal_cost raw final.point final.scalar _ reached)
    apply CostComposition.mono (by simpa only [add_zero] using full)
    exact nsmul_le_nsmul_left (bot_le : (0 : ENNReal) ≤ price) bound
  · rw [ite_eq_right bound]
    trivial

end ZkcSecurity.Realizations.Sumcheck.OriginalRaw
