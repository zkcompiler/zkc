module

public import ZkcArkLib.Sumcheck.Multilinear.Causal
public import ZkcArkLibExamples.CausalSumcheck.ExactRound

@[expose] public section


namespace TestsSecurity.CausalSumcheck.Phases

open ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal ZkcSecurity.VCVio.Execution
open OracleComp OracleSpec Zkc.Protocols.Sumcheck.Multilinear
open scoped ENNReal

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]

def stopLow (n : Nat) : Strategy F Nat String (n+1) := fun s =>
  pure ⟨.stopped .abort, s+1, ["low-stop"]⟩

theorem all_stop_before_pair (n : Nat) (claim : F) (point : List F) (s : Nat) :
    run (n+1) claim point (stopLow n) s =
      pure ⟨.stopped .abort, s+1, ["low-stop"]⟩ := by
  simp [run, prepare, stopLow, PIR.Execution.followM]

theorem all_stop_before_pair_mass (n : Nat) (claim : F) (s : Nat)
    (terminal : List F → F → Prop) :
    mass (phaseGame (n+1) claim [] (stopLow n) s terminal) = 0 := by
  simp [phaseGame, all_stop_before_pair, accepts, mass_false]

def stopHigh (n : Nat) (lo : F) : Strategy F Nat String (n+1) := fun s =>
  pure ⟨.returned (lo, fun t => pure ⟨.stopped .abort, t+1, ["high-stop"]⟩),
    s+1, ["low-ack"]⟩

theorem second_receive_stop (n : Nat) (claim lo : F) (s : Nat) :
    run (n+1) claim [] (stopHigh n lo) s =
      pure ⟨.stopped .abort, s+2, ["low-ack", "high-stop"]⟩ := by
  simp [run, prepare, stopHigh, PIR.Execution.followM, Nat.add_assoc]

def goodTail : AfterPair F Nat String (Strategy F Nat String 0) where
  beforeDraw := fun s => pure ⟨.returned (), s, ["guard-pass"]⟩
  publicAbort := fun s => do
    let coin ← ($ᵗ Bool)
    pure ⟨.returned (), s+1, [if coin then "abort-true" else "abort-false"]⟩
  afterDraw := fun _ s => pure ⟨.returned (), s, ["queried"]⟩
  deliver := fun _ s => pure ⟨.returned (fun t => pure (result () t)), s, ["delivered"]⟩

def fixedPair (lo hi : F) (tail : AfterPair F Nat String (Strategy F Nat String 0)) : Strategy F Nat String 1 :=
  fun s => pure ⟨.returned (lo, fun t => pure ⟨.returned (hi, tail), t, ["high"]⟩), s, ["low"]⟩

/-- The high computation is chosen by the low computation and consumes the
    acknowledgment state. This is deliberately not an atomic pair input. -/
def adaptiveHigh (lo : F) : Strategy F Nat String 1 := fun s =>
  pure ⟨.returned (lo, fun t => pure ⟨.returned ((t : F), goodTail), t, ["high"]⟩),
    s+1, ["low-ack"]⟩

omit [SampleableType F] in
theorem high_depends_on_first_ack (lo : F) (s : Nat) :
    prepare (lo + (s+1 : Nat)) (adaptiveHigh lo) s =
      pure ⟨.returned ((lo, (s+1 : Nat)), goodTail), s+1,
        ["low-ack", "high", "guard-pass"]⟩ := by
  simp [prepare, adaptiveHigh, goodTail, boundary, PIR.Execution.followM, result]

def stopBeforeDraw : AfterPair F Nat String (Strategy F Nat String 0) :=
  { goodTail with beforeDraw := fun s => pure ⟨.stopped .abort, s, ["guard-pass", "service-stop"]⟩ }

theorem stop_after_guard (lo hi : F) (s : Nat) :
    run 1 (lo+hi) [] (fixedPair lo hi stopBeforeDraw) s =
      pure ⟨.stopped .abort, s, ["low", "high", "guard-pass", "service-stop"]⟩ := by
  simp [run, prepare, fixedPair, stopBeforeDraw, boundary, PIR.Execution.followM, result]

def stopAfterDraw : AfterPair F Nat String (Strategy F Nat String 0) :=
  { goodTail with afterDraw := fun _ s => pure ⟨.stopped .abort, s, ["queried", "service-stop"]⟩ }

theorem stop_after_challenge (lo hi : F) (s : Nat) :
    run 1 (lo+hi) [] (fixedPair lo hi stopAfterDraw) s = (do
      let _ ← ($ᵗ F)
      pure ⟨.stopped .abort, s, ["low", "high", "guard-pass", "queried", "service-stop"]⟩) := by
  simp [run, prepare, fixedPair, stopAfterDraw, goodTail, boundary,
    PIR.Execution.followM, result]

def stopDelivery : AfterPair F Nat String (Strategy F Nat String 0) :=
  { goodTail with deliver := fun _ s => pure ⟨.stopped .abort, s, ["delivery-stop"]⟩ }

theorem final_delivery_stops (lo hi : F) (s : Nat) :
    run 1 (lo+hi) [] (fixedPair lo hi stopDelivery) s = (do
      let _ ← ($ᵗ F)
      pure ⟨.stopped .abort, s, ["low", "high", "guard-pass", "queried", "delivery-stop"]⟩) := by
  simp [run, prepare, fixedPair, stopDelivery, goodTail, boundary,
    PIR.Execution.followM, result]

theorem final_delivery_source_mass (lo hi : F) :
    mass (phaseGame 1 (lo+hi) [] (fixedPair lo hi stopDelivery) 0 (fun _ _ => True)) = 0 := by
  simp [phaseGame, final_delivery_stops, accepts, mass]

theorem final_delivery_completed_mass (lo hi : F) :
    mass (endpointGame 1 (lo+hi) []
      (complete 1 (lo+hi) (fixedPair lo hi stopDelivery) 0) (fun _ _ => True)) = 1 := by
  simp [endpointGame, complete, prepare, fixedPair, stopDelivery, goodTail, boundary,
    PIR.Execution.followM, result, mass]

theorem public_abort_effect (lo hi claim : F) (failed : lo+hi ≠ claim) (s : Nat) :
    run 1 claim [] (fixedPair lo hi goodTail) s = (do
      let coin ← ($ᵗ Bool)
      pure ⟨.stopped .reject, s+1, ["low", "high",
        if coin then "abort-true" else "abort-false"]⟩) := by
  simp [run, prepare, fixedPair, goodTail, boundary, failed,
    PIR.Execution.followM, result, stopped]

/-- Equality of open computations: the Bool query on public abort really runs
    in the ordinary endpoint strategy, even though its result is irrelevant to
    the rejected accepted-event observation. -/
theorem completed_public_abort_effect (lo hi claim : F) (failed : lo+hi ≠ claim)
    (terminal : List F → F → Prop) :
    endpointGame 1 claim [] (complete 1 claim (fixedPair lo hi goodTail) 0) terminal =
      (do let _ ← ($ᵗ Bool); pure False) := by
  simp [endpointGame, complete, prepare, fixedPair, goodTail, boundary, failed,
    PIR.Execution.followM, result]

def stopAfterDelivery : AfterPair F Nat String (Strategy F Nat String 0) :=
  { goodTail with advance := fun _ s => pure ⟨.stopped .exhausted, s, ["trusted-append-stop"]⟩ }

theorem stop_after_delivery (lo hi : F) (s : Nat) :
    run 1 (lo+hi) [] (fixedPair lo hi stopAfterDelivery) s = (do
      let _ ← ($ᵗ F)
      pure ⟨.stopped .exhausted, s,
        ["low", "high", "guard-pass", "queried", "delivered", "trusted-append-stop"]⟩) := by
  simp [run, prepare, fixedPair, stopAfterDelivery, goodTail, boundary,
    PIR.Execution.followM, result]

theorem zero_rounds (claim : F) (s : Nat) :
    run 0 claim [] (S := Nat) (E := String) (fun t => pure (result () t)) s =
      pure (result ([], claim) s) := by simp [run, result, PIR.Execution.followM]

theorem zero_terminal_stops (claim : F) (s : Nat) :
    run 0 claim [] (S := Nat) (E := String)
      (fun t => pure ⟨.stopped .exhausted, t+1, ["terminal-length-stop"]⟩) s =
      pure ⟨.stopped .exhausted, s+1, ["terminal-length-stop"]⟩ := by
  simp [run, PIR.Execution.followM]

theorem zero_terminal_stop_mass (claim : F) (s : Nat) (terminal : List F → F → Prop) :
    mass (phaseGame 0 claim [] (S := Nat) (E := String)
      (fun t => pure ⟨.stopped .exhausted, t+1, ["terminal-length-stop"]⟩) s terminal) = 0 := by
  simp [phaseGame, zero_terminal_stops, accepts]

open Zkc.Polynomial.Multilinear in
theorem honest_one_round_mass :
    mass (phaseGame 1 (0 : F) [] (fixedPair 0 0 goodTail) 0
      (tableTerminal (fun _ : Fin 1 → Bool => (0 : F)))) = 1 := by
  have truth (r : F) : tableTerminal (fun _ : Fin 1 → Bool => (0 : F)) [r] 0 := by
    refine ⟨fun _ => r, ?_, ?_⟩
    · simp
    · simp [extension]
  have observation : phaseGame 1 (0 : F) [] (fixedPair 0 0 goodTail) 0
      (tableTerminal (fun _ : Fin 1 → Bool => (0 : F))) = (do let _ ← ($ᵗ F); pure True) := by
    simp [phaseGame, run, prepare, fixedPair, goodTail, boundary, evaluate,
      PIR.Execution.followM, result, accepts, truth]
  rw [observation]
  simp [mass]


/-- Outer history retains its own actual acknowledgment state and stop prefix.
No future challenge or input-independence premise is inferred from it. -/
theorem random_history_stop (histories : ProbComp Nat) (claim lo : F) :
    (do let s ← histories; run 1 claim [] (stopHigh 0 lo) s) =
      (do let s ← histories
          pure ⟨.stopped .abort, s + 2, ["low-ack", "high-stop"]⟩) := by
  simp only [second_receive_stop]

/-- A caller with no observation capacity excludes acceptance without resampling. -/
theorem no_observer_capacity (n : Nat) (claim : F) (strategy : Strategy F Nat String n)
    (terminal : List F → F → Prop) :
    mass (do let e ← run n claim [] strategy 0; pure (False ∧ accepts terminal e)) = 0 := by
  simp [mass]

omit [SampleableType F] in
/-- A singleton raw table is malformed for one round, even if the run returns. -/
theorem malformed_singleton (executions : ProbComp (PIR.Execution Nat String (List F × F))) :
    mass (do let e ← executions; pure (accepts (rawTerminal 1 [0]) e)) = 0 :=
  malformed_raw_zero 1 [0] (by simp) executions

omit [SampleableType F] [DecidableEq F] in
/-- A one-coordinate residual is a Boolean sum of the original remaining
coordinates, rather than a complete two-coordinate table evaluation. -/
theorem residual_observation (table : Zkc.Polynomial.Multilinear.Table F 2) (r claim : F) :
    residualTerminal 1 1 table [r] claim ↔
      Zkc.Protocols.Sumcheck.Multilinear.ResidualClaim 1 table (fun _ => r) claim := by
  rw [residualTerminal_eq_marginal]
  have point : ([r] : List F) = List.ofFn (fun _ : Fin 1 => r) := by simp
  rw [point, tableTerminal_ofFn, Zkc.Polynomial.Multilinear.extension_sumRemaining]
  rfl

end TestsSecurity.CausalSumcheck.Phases
