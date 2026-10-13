module

public import ZkcSecurity.ArkLib.FiatShamir.Prefix.Experiment

@[expose] public section

/-! The pinned ArkLib restoration theorem applied to the proved two-round
full-prefix simulation. All-prefix knowledge premises remain protocol-specific;
the oracle correspondence and extra salt-selection query are proved here. -/

namespace ZkcSecurity.ArkLib.FiatShamir.Prefix
open OracleComp OracleSpec Interaction.Oracle Interaction.Oracle.Security

universe w

variable {Input W : Type} {round : StateRestoration.Round}
variable [DecidableEq Input] [DecidableEq round.Challenge]

/-- Full-prefix classical-RO extraction with adaptive input and terminal witness.
The extra first-round access selects a consistent second salt. The conservative
charge includes that access and both ArkLib completion accesses, including hits. -/
theorem extraction_bound
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) →
      RoundExtractor (StateRestoration.protocol [round, round]).tree (state z))
    (Z : Set Input) (error : ENNReal)
    (preserving : ∀ z ∈ Z, (extractor z).IsProverPreserving
      (StateRestoration.protocol [round, round]).roles)
    (bounded : ∀ z ∈ Z, RoundExtractor.IsLocallyBounded (extractor z)
      (StateRestoration.protocol [round, round]).roles
      (StateRestoration.uniformSchedule error [round, round]))
    (terminalWitness : (z : Input) → (path : Path round) →
      W → ((extractor z).terminalState path).Witness)
    (adversary : OracleComp (Spec Input round) (Output Input W round))
    (Q : Nat) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ (Spec Input round).randomOracle (execution adversary)).run' ∅}[
      result.1 ∈ Z ∧
      ((extractor result.1).terminalState result.2.1).holds
        (terminalWitness result.1 result.2.1 result.2.2) ∧
      ¬ (state result.1).holds ((extractor result.1).extractWitness result.2.1
        (terminalWitness result.1 result.2.1 result.2.2))] ≤
      ((Q + 3 : Nat) : ENNReal) * error := by
  have bound := StateRestoration.restored_extraction_bound state extractor Z error
    preserving bounded terminalWitness (adversaryMap adversary) (Q + 1)
    (adversaryMap_queryBound adversary Q queryBound)
  rw [experiment_eq, view_empty] at bound
  simpa only [List.length_cons, List.length_nil, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat, add_assoc, Nat.reduceAdd, show (1 + 2 : ENNReal) = 3 by norm_num] using bound

end ZkcSecurity.ArkLib.FiatShamir.Prefix
