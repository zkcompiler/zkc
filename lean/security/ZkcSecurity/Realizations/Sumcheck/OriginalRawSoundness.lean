module

public import ZkcSecurity.Realizations.Sumcheck.OriginalRawPresentation
public import ZkcSecurity.Obligations.WeakestPrecondition

@[expose] public section

/-! All-input rejection and pathwise cost through the existing table reference.
Raw shape is a case in the residual proof, never an input-policy premise. -/
set_option autoImplicit false
namespace ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript Zkc.Obligations
open ZkcSecurity.FiatShamir ZkcSecurity.Obligations
open ZkcSecurity.Families.Sumcheck TableComponent
open Std.WP ZkcSecurity.Obligations.WeakestPrecondition

variable {F G : Type} [Field F] [DecidableEq F]
variable {charge : Domain.History (uniformCarriers F G) → Domain.Event (uniformCarriers F G) → ENNReal}
variable [∀ event, SampleableType (@Domain.Raw (uniformCarriers F G) event)]

def terminal_rejected (raw point : List F) (scalar : F)
    (construction : ConstructionState (F := F) (G := G)) (history : Domain.History (uniformCarriers F G))
    (wrong : raw.length < indexLimit → raw.length ≠ 2 ^ point.length ∨
      scalar ≠ (Zkc.Polynomial.Multilinear.restrictPrefixValues raw point).sum) :
    Derivation (NominalField.interface (G := G) "bls12-381.fr") (boundedEscape charge)
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

theorem terminal_spec (raw point : List F) (scalar : F)
    (construction : ConstructionState (F := F) (G := G)) :
    ChargedTriple (NominalField.interface (G := G) "bls12-381.fr") (boundedEscape charge)
      (boundedEscape_antitone charge) (terminal raw point scalar)
      (fun _ => raw.length < indexLimit → raw.length ≠ 2 ^ point.length ∨
        scalar ≠ (Zkc.Polynomial.Multilinear.restrictPrefixValues raw point).sum)
      (fun result _ => acceptance (result, construction) ≠ some true) estack⟨fun _ _ => True⟩ := by
  let := chargedMonad (NominalField.interface (F := F) (G := G) "bls12-381.fr")
    (boundedEscape charge) (boundedEscape_antitone charge)
  constructor
  intro history wrong
  change (NominalField.interface (G := G) "bls12-381.fr").Charged (boundedEscape charge)
    (fun _ result => acceptance (result, construction) ≠ some true) (terminal raw point scalar) history
  have rejected := (terminal_rejected raw point scalar construction history wrong).charged
    (boundedEscape_antitone charge)
  simpa only [Interface.charged_bind, Interface.charged_done] using rejected

set_option experimental.vcgen true in
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
    Derivation (NominalField.interface (G := G) "bls12-381.fr") (boundedEscape charge)
      (fun _ result => acceptance result ≠ some true) history
      (root maximum schedule raw scalar count construction) := by
  let absorb := NominalField.interface (F := F) (G := G) "bls12-381.fr"
  let := chargedMonad absorb (boundedEscape charge) (boundedEscape_antitone charge)
  apply ofTriple absorb (boundedEscape charge) (boundedEscape_antitone charge)
    (pre := fun _ => True) ?_ history trivial
  unfold root
  by_cases rawBound : raw.length < indexLimit
  · have rounds := derivation_spec absorb (boundedEscape charge) (boundedEscape_antitone charge)
      (TableComponent.Execution.run "bls12-381.fr" schedule (List.range count) ⟨[], scalar, construction.history⟩)
      (fun _ => True) _ (fun reached _ => TableComponent.Execution.run_rejecting "bls12-381.fr"
        schedule charge sampling raw scalar count construction.history reached (wrong rawBound))
    vcgen [rounds, terminal_spec (charge := charge) (construction := construction),
      halt_spec absorb (boundedEscape charge) (boundedEscape_antitone charge)]
    all_goals grind [OriginalSecurity.acceptance]
  · have rounds := derivation_spec absorb (boundedEscape charge) (boundedEscape_antitone charge)
      (TableComponent.Execution.run "bls12-381.fr" schedule (List.range count) ⟨[], scalar, construction.history⟩)
      (fun _ => True) _ (fun reached _ => unrestricted _ reached)
    vcgen [rounds, terminal_spec (charge := charge) (construction := construction),
      halt_spec absorb (boundedEscape charge) (boundedEscape_antitone charge)]
    all_goals simp_all [OriginalSecurity.acceptance]

omit [∀ event, SampleableType (@Domain.Raw (uniformCarriers F G) event)] in
/-- A terminal helper never asks the random oracle, including exhaustion. -/
theorem terminal_cost (raw point : List F) (scalar : F)
    (construction : ConstructionState (F := F) (G := G)) (history : Domain.History (uniformCarriers F G)) :
    Typed.ChargedCostBound (NominalField.interface (G := G) "bls12-381.fr") charge
      ((terminal (G := G) raw point scalar).bind fun result => .done (result, construction)) history 0 := by
  unfold terminal
  split
  · split
    · split <;> trivial
    · trivial
  · trivial

omit [∀ event, SampleableType (@Domain.Raw (uniformCarriers F G) event)] in
set_option experimental.vcgen true in
/-- All counts have the same maximum budget: excessive counts refuse before
any interaction; admitted counts pay for every reached source callback. -/
theorem root_cost (price : ENNReal)
    (priced : ∀ history origin, charge history (.challenge origin) ≤ price)
    (maximum : Nat) (schedule : Nominal.Schedule "bls12-381.fr")
    (raw : List F) (scalar : F) (count : Nat)
    (construction : ConstructionState (F := F) (G := G)) (history : Domain.History (uniformCarriers F G)) :
    Typed.ChargedCostBound (NominalField.interface (G := G) "bls12-381.fr") charge
      (root maximum schedule raw scalar count construction) history (maximum • price) := by
  let absorb := NominalField.interface (F := F) (G := G) "bls12-381.fr"
  let := costMonad absorb charge
  apply cost_of_triple absorb charge (pre := fun _ cost => maximum • price ≤ cost) ?_ history _ le_rfl
  have bounded (reached) := TableComponent.Execution.run_cost "bls12-381.fr" schedule charge price priced
    (List.range count) (⟨[], scalar, construction.history⟩ : TableComponent.Execution.State F G) reached
  have spec := bound_spec absorb charge
    (TableComponent.Execution.run "bls12-381.fr" schedule (List.range count) ⟨[], scalar, construction.history⟩)
    (count • price) 0 (fun reached => by simpa only [List.length_range] using bounded reached)
  unfold root
  vcgen [spec, ZkcSecurity.Realizations.Sumcheck.OriginalRaw.terminal, halt_cost absorb charge]
  simpa only [add_zero] using
    (nsmul_le_nsmul_left (bot_le : (0 : ENNReal) ≤ price) ‹count ≤ maximum›).trans
      ‹maximum • price ≤ _›

end ZkcSecurity.Realizations.Sumcheck.OriginalRaw
