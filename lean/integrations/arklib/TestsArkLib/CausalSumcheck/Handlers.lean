module

public import TestsArkLib.CausalSumcheck.Phases
public import Mathlib.Algebra.Field.ZMod
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

@[expose] public section


namespace TestsSecurity.CausalSumcheck.Handlers

open ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal ZkcSecurity.VCVio.Execution
open OracleComp OracleSpec Zkc.Source Zkc.Source.Structured
open Zkc.Protocols.Sumcheck.Multilinear Zkc.Polynomial.Multilinear ZkcSecurity.Examples.CausalSumcheck
open scoped ENNReal

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

noncomputable local instance : SampleableType (ZMod 2) := SampleableType.ofFintype _

abbrev F := ZMod 2
abbrev Actual := participantInterface F F

def names : Sites := {}
def tables : Evaluation.ComponentTables F F Actual := ⟨[], []⟩
def tail : Message F → F → PIR.Proc Actual Unit := fun _ _ => .done ()
def zeroTable : Table F 1 := fun _ => 0

def participant (claim : F) : PIR.Proc Actual (List F × F) :=
  scalarRound (.silent Actual) (participantActions F F) tables names 7 claim tail tail

/-- Samples before the first committed scalar, then reuses that sample at query.
    This is a real well-typed structured handler, but it violates freshQuery. -/
noncomputable def earlyHandler : PIR.MonadHandler ProbComp Actual F String
  | .receive (.field _) site _, s =>
      if site = names.low then do
        let r ← ($ᵗ F)
        pure ⟨.returned r, r, ["sample-at-low", "low-ack"]⟩
      else pure ⟨.returned (1-s), s, ["high"]⟩
  | .receive _ _ _, s => pure ⟨.stopped .refused, s, ["unexpected"]⟩
  | .query _ _ _, s => pure ⟨.returned s, s, ["reused-query"]⟩
  | .send .., s => pure ⟨.returned (), s, ["delivered"]⟩

/-- Constant-challenge provider: seed-seed is zero. The HIGH-time uniform
    seed is discarded; timing does not cause this failure. -/
noncomputable def constantChallengeHandler : PIR.MonadHandler ProbComp Actual F String
  | .receive (.field _) site _, s =>
      if site = names.low then pure ⟨.returned 0, s, ["low-ack"]⟩
      else do
        let seed ← ($ᵗ F)
        pure ⟨.returned 1, seed-seed, ["sample-at-high", "constant-challenge"]⟩
  | .receive _ _ _, s => pure ⟨.stopped .refused, s, ["unexpected"]⟩
  | .query _ _ _, s => pure ⟨.returned s, s, ["reused-query"]⟩
  | .send .., s => pure ⟨.returned (), s, ["delivered"]⟩

/-- The literal high-only fresh uniform control: LOW is already zero; HIGH
    samples a uniform challenge without bias and query reuses it. -/
noncomputable def uniformHighHandler : PIR.MonadHandler ProbComp Actual F String
  | .receive (.field _) site _, s =>
      if site = names.low then pure ⟨.returned 0, s, ["low-ack"]⟩
      else do
        let r ← ($ᵗ F)
        pure ⟨.returned 1, r, ["sample-at-high"]⟩
  | .receive _ _ _, s => pure ⟨.stopped .refused, s, ["unexpected"]⟩
  | .query _ _ _, s => pure ⟨.returned s, s, ["reused-query"]⟩
  | .send .., s => pure ⟨.returned (), s, ["delivered"]⟩

set_option backward.isDefEq.respectTransparency false in
/-- A uniform sample first taken during HIGH, after LOW is committed,
    accepts this false ZMod 2 claim exactly when it equals LOW. -/
theorem accepting_challenge_is_low (lo hi r : F)
    (guard : boundary (lo, hi) = 1) (accepted : evaluate (lo, hi) r = 0) : r = lo := by
  fin_cases lo <;> fin_cases hi <;> fin_cases r <;> revert guard accepted <;> decide

theorem tableTerminal_zero (r c : F) : tableTerminal zeroTable [r] c ↔ c = 0 := by
  constructor
  · rintro ⟨coordinates, _, checked⟩
    simpa [zeroTable, extension] using checked.symm
  · intro hc
    subst c
    refine ⟨fun _ => r, ?_, ?_⟩
    · simp
    · simp [zeroTable, extension]

set_option backward.isDefEq.respectTransparency false in
theorem early_execution : (participant 1).runM earlyHandler 0 = (do
    let r ← ($ᵗ F)
    pure ⟨.returned ([r], 0), r, ["sample-at-low", "low-ack", "high", "reused-query", "delivered"]⟩) := by
  simp only [participant, scalarRound_eq]
  simp [SiteObservations.silent, participantActions, PIR.Proc.runM, PIR.Proc.bind, PIR.Execution.followM,
    earlyHandler, names, tail, lowAction, queryAction, sendAction, boundary]
  congr 1
  funext r
  fin_cases r <;> simp [evaluate]

set_option backward.isDefEq.respectTransparency false in
theorem constant_challenge_execution : (participant 1).runM constantChallengeHandler 0 = (do
    let _ ← ($ᵗ F)
    pure ⟨.returned ([0], 0), 0,
      ["low-ack", "sample-at-high", "constant-challenge", "reused-query", "delivered"]⟩) := by
  simp [participant, scalarRound_eq, SiteObservations.silent, participantActions,
    PIR.Proc.runM, PIR.Proc.bind, PIR.Execution.followM, constantChallengeHandler, names, tail,
    lowAction, queryAction, sendAction, boundary, evaluate]

set_option backward.isDefEq.respectTransparency false in
theorem uniform_high_execution : (participant 1).runM uniformHighHandler 0 = (do
    let r ← ($ᵗ F)
    pure ⟨.returned ([r], r), r,
      ["low-ack", "sample-at-high", "reused-query", "delivered"]⟩) := by
  simp [participant, scalarRound_eq, SiteObservations.silent, participantActions,
    PIR.Proc.runM, PIR.Proc.bind, PIR.Execution.followM, uniformHighHandler, names, tail,
    lowAction, queryAction, sendAction, boundary, evaluate]


def acceptedGame (h : PIR.MonadHandler ProbComp Actual F String) : ProbComp Prop := do
  let e ← (participant 1).runM h 0
  pure (accepts (tableTerminal zeroTable) e)

theorem early_handler_mass : mass (acceptedGame earlyHandler) = 1 := by
  simp [acceptedGame, early_execution, accepts, tableTerminal_zero, mass]

theorem constant_challenge_handler_mass : mass (acceptedGame constantChallengeHandler) = 1 := by
  simp [acceptedGame, constant_challenge_execution, accepts, tableTerminal_zero, mass]

theorem typed_handler_exceeds_bound :
    ¬ mass (acceptedGame earlyHandler) ≤ (1 : ENNReal) / Fintype.card F := by
  rw [early_handler_mass]
  norm_num [F]

theorem constant_challenge_exceeds_bound :
    ¬ mass (acceptedGame constantChallengeHandler) ≤ (1 : ENNReal) / Fintype.card F := by
  rw [constant_challenge_handler_mass]
  norm_num [F]

theorem uniform_high_handler_mass : mass (acceptedGame uniformHighHandler) = (1 : ENNReal)/2 := by
  simp only [acceptedGame, uniform_high_execution, bind_assoc, pure_bind, accepts]
  simp_rw [propext (tableTerminal_zero _ _)]
  change Pr{let r ← ($ᵗ F)}[r = 0] = _
  rw [SampleableType.prEvent_uniformSample_eq_singleton]
  norm_num [F]

theorem early_handler_not_factorizable :
    ¬ ∃ (before : Phase F String Unit) (after : F → Phase F String Unit),
      ∀ s, (participantActions F F (queryAction names.query 7)).runM earlyHandler s =
        freshQuery before after s := by
  rintro ⟨before, after, law⟩
  have bound := one_round_soundness (.silent Actual) (participantActions F F)
    earlyHandler names before after tail tail tables 7 1 0 law zeroTable
    (by simp [zeroTable, booleanSum, half])
  apply typed_handler_exceeds_bound
  simpa only [acceptedGame, participant, acceptanceOf] using bound

noncomputable def honestHandler : PIR.MonadHandler ProbComp Actual F String
  | .receive (.field _) _ _, s => pure ⟨.returned 0, s, ["endpoint"]⟩
  | .receive _ _ _, s => pure ⟨.stopped .refused, s, ["unexpected"]⟩
  | .query _ _ _, _ => do
      let r ← ($ᵗ F)
      pure ⟨.returned r, r, ["fresh-query"]⟩
  | .send .., s => pure ⟨.returned (), s, ["delivered"]⟩

set_option backward.isDefEq.respectTransparency false in
theorem honest_query_law (s : F) :
    (participantActions F F (queryAction names.query 7)).runM honestHandler s =
      freshQuery noOp (fun r _ => pure ⟨.returned (), r, ["fresh-query"]⟩) s := by
  simp [participantActions, queryAction, PIR.Proc.runM, honestHandler, freshQuery,
    noOp, result, PIR.Execution.followM]

theorem honest_participant_mass :
    mass (acceptanceOf honestHandler (participant 0) 0 (tableTerminal zeroTable)) = 1 := by
  simp [acceptanceOf, participant, scalarRound_eq, SiteObservations.silent, participantActions,
    PIR.Proc.runM, PIR.Proc.bind, PIR.Execution.followM, honestHandler, names, tail,
    lowAction, queryAction, sendAction, boundary, evaluate, accepts,
    mass]
  change ∀ r : F, tableTerminal zeroTable [r] 0
  intro r
  exact (tableTerminal_zero r 0).mpr rfl


end TestsSecurity.CausalSumcheck.Handlers
