module

public import ZkcSecurity.ArkLib.Sumcheck.FiatShamir.Observation
public import ZkcSecurity.ArkLib.FiatShamir.Prefix.Security

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Sumcheck consumes the separately proved full-prefix/restoration simulation.
The second full-prefix key retains the first challenge. The reduction selects
that challenge as its second restoration salt and charges the extra access.
-/

namespace ZkcSecurity.ArkLib.Sumcheck.FiatShamir

open Interaction.Oracle Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration
open OracleComp OracleSpec
open Zkc.Protocols.Sumcheck.Common

namespace FullPrefix

open ZkcSecurity.ArkLib.FiatShamir

variable {F Input : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
variable [DecidableEq Input]

abbrev Oracle (Input F : Type) [Field F] [DecidableEq F] [Fintype F] [SampleableType F] :=
  Prefix.Spec Input (round (F := F))

abbrev Adversary (Input F : Type) [Field F] [DecidableEq F] [Fintype F] [SampleableType F] :=
  OracleComp (Oracle Input F) (Prefix.Output Input Unit (round (F := F)))

/-- The full public binding can also carry source, schedule and application
context. This projection fixes its Sumcheck statement before any experiment. -/
def pathAccepted (statement : Input → Statement F) (z : Input)
    (p : (tree (F := F)).ExecutionPath) : Prop :=
  accepted (statement z) p.1 p.2.1 p.2.2.1 p.2.2.2.1

/-- Every local Sumcheck premise is discharged; the simulation is applied to
arbitrary adaptive full-prefix queries, including inconsistent prefixes. -/
theorem soundness (statement : Input → Statement F) (adversary : Adversary Input F)
    (Q : Nat) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (Prefix.execution adversary)).run' ∅}[
      pathAccepted statement result.1 result.2.1 ∧
        (statement result.1).claim ≠ (polynomial (statement result.1).coefficients).booleanSum] ≤
          (Q + 3 : ENNReal) * (2 / (Fintype.card F : ENNReal)) := by
  have bound := Prefix.extraction_bound (round := round (F := F))
    (fun z => inputState (statement z)) (fun z => statementExtractor (statement z)) Set.univ
    (2 / (Fintype.card F : ENNReal))
    (fun z _ => prover_preserving 2 True (polynomial (statement z).coefficients) (statement z).claim)
    (fun z _ => locally_bounded 2 True (polynomial (statement z).coefficients) (statement z).claim)
    (fun z p w => terminalWitness (statement z) p w)
    adversary Q queryBound
  simp only [Nat.cast_add, Nat.cast_ofNat] at bound
  simp only [Set.mem_univ, true_and, inputState, residualState, true_and] at bound
  apply le_trans (le_of_eq ?_) bound
  apply prEvent_congr
  rintro ⟨z, p, witness⟩
  rcases p with ⟨m, first, n, second, finish⟩
  cases finish
  exact and_congr (terminal_iff (statement z) m first n second witness).symm Iff.rfl

/-- Acceptance of the existing actual common-source verifier after full-prefix
completion; its own early-stop state and event record are retained. -/
def programGame (statement : Input → Statement F) (program : Verifier F) (service : Nat)
    (adversary : Adversary Input F) :=
  (fun result => (result.1, replayProgram program service (statement result.1) result.2.1)) <$>
    Prefix.execution adversary

theorem program_soundness {wiring : Wiring} {program : Verifier F}
    (certificate : VerifierContract wiring program) (statement : Input → Statement F)
    (service : Nat) (adversary : Adversary Input F) (Q : Nat)
    (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle
      (programGame statement program service adversary)).run' ∅}[
      result.2.outcome = PIR.Outcome.returned (some true) ∧
        (statement result.1).claim ≠ (polynomial (statement result.1).coefficients).booleanSum] ≤
          (Q + 3 : ENNReal) * (2 / (Fintype.card F : ENNReal)) := by
  rw [programGame, simulateQ_map]
  simp only [StateT.run'_map', prEvent_map]
  apply le_trans (le_of_eq ?_) (soundness statement adversary Q queryBound)
  apply prEvent_congr
  rintro ⟨z, p, witness⟩
  rcases p with ⟨m, first, n, second, finish⟩
  cases finish
  exact and_congr ((actualVerifier_accepts_iff certificate (statement z) service
    m first n second).trans
    (by change decide (accepted (statement z) m first n second) = true ↔ _
        exact ⟨of_decide_eq_true, fun h => decide_eq_true h⟩)) Iff.rfl

end FullPrefix
end ZkcSecurity.ArkLib.Sumcheck.FiatShamir
