import ZkcSecurity.ProgramLogic.HonestComposition
import Zkc.Semantics.MonadExecution
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.EvalDist.Sum
import TestsSecurity.PrivateProducerWP

/-! Controls over actual PIR executions and the existing `OptionT ProbComp`
semantics. These are composition laws, not protocol or native receipts. -/

set_option autoImplicit false

namespace TestsSecurity.HonestComposition

open OracleComp OracleSpec PIR.WeakestPrecondition
open ZkcSecurity.Obligations.HonestComposition

inductive Operation where
  | write (value : Nat)
  | read

abbrev effects : PIR.Signature where
  Op := Operation
  Reply
    | .write _ => Unit
    | .read => Nat

/-- Shared state is changed by the prefix and read by the suffix. -/
def handler : PIR.Handler effects Nat Nat
  | .write value, _ => ⟨.returned (), value, [value]⟩
  | .read, state => ⟨.returned state, state, [state]⟩

def first : PIR.Process effects Nat :=
  .call (.write 1) fun _ => .done 4

def suffix (expected value : Nat) : PIR.Process effects Bool :=
  .call .read fun (state : Nat) =>
    if state = expected ∧ value = 4 then .done true else .halt .reject

def intermediate (value state : Nat) (history : List Nat) : Prop :=
  value = 4 ∧ state = 1 ∧ history = [8, 1]

def accepted (value : Bool) (state : Nat) (history : List Nat) : Prop :=
  value = true ∧ state = 1 ∧ history = [8, 1, 1]

theorem first_returns : satisfies (first.run handler 0) intermediate
    (fun _ _ _ => False) [8] := by
  simp [first, handler, PIR.Process.run, PIR.Execution.follow, satisfies, intermediate]

theorem suffix_at_return : ∀ value reached events,
    first.run handler 0 = ⟨.returned value, reached, events⟩ →
    intermediate value reached ([8] ++ events) →
    satisfies ((suffix 1 value).run handler reached) accepted
      (fun _ _ _ => False) ([8] ++ events) := by
  intro value reached events observed inside
  rcases inside with ⟨rfl, rfl, history⟩
  simp only [first, PIR.Process.run, handler, PIR.Execution.follow] at observed
  cases observed
  simp [suffix, handler, PIR.Process.run, PIR.Execution.follow, satisfies, accepted]

theorem reached_state_composes :
    satisfies ((first.bind (suffix 1)).run handler 0) accepted
      (fun _ _ _ => False) [8] :=
  deterministic_bind handler first (suffix 1) 0 [8] intermediate accepted
    first_returns suffix_at_return

/-- This suffix succeeds in a fresh state, but that state is not the handoff. -/
theorem fresh_suffix : satisfies ((suffix 0 4).run handler 0)
    (fun value _ _ => value = true) (fun _ _ _ => False) [] := by
  simp [suffix, handler, PIR.Process.run, PIR.Execution.follow, satisfies]

theorem wrong_state_refused : ¬ (∀ value reached events,
    first.run handler 0 = ⟨.returned value, reached, events⟩ →
    intermediate value reached ([8] ++ events) →
    satisfies ((suffix 0 value).run handler reached)
      (fun value _ _ => value = true) (fun _ _ _ => False) ([8] ++ events)) := by
  intro assumed
  have bad := assumed 4 1 [1] rfl first_returns
  simp [suffix, handler, PIR.Process.run, PIR.Execution.follow, satisfies] at bad

#check_failure (show satisfies ((first.bind (suffix 0)).run handler 0)
    (fun value _ _ => value = true) (fun _ _ _ => False) [8] from
  deterministic_bind handler first (suffix 0) 0 [8] intermediate
    (fun value _ _ => value = true) first_returns (fun _ _ _ _ _ => fresh_suffix))

theorem wrong_state_stops :
    ((first.bind (suffix 0)).run handler 0).outcome = .stopped .reject := rfl

theorem stopped_prefix_refused : ¬ satisfies
    ((PIR.Process.halt .reject : PIR.Process effects Nat).run handler 0)
    intermediate (fun _ _ _ => False) [8] := by
  simp [PIR.Process.run, satisfies]

abbrev Observation := PIR.Execution Nat Nat Nat
abbrev Result := PIR.Execution Nat Nat Bool

/-- Preparation fails at zero; one is an explicit PIR stop. Other draws execute
the state-changing prefix. Neither kind of unsuccessful mass is conditioned out. -/
def sampledFirst : OptionT ProbComp Observation := OptionT.mk do
  let coin ← $ᵗ (Fin 7)
  if coin = 0 then pure none
  else pure (some ((if coin = 1 then .halt .exhausted else first).run handler 0))

/-- A missing result and a returned stop are distinct failure cases here too. -/
def sampledSuffix (value state : Nat) : OptionT ProbComp Result := OptionT.mk do
  let coin ← $ᵗ (Fin 5)
  if coin = 0 then pure none
  else pure (some ((if coin = 1 then .halt .reject else suffix 1 value).run handler state))

/-- Reuse the existing stopped/returned sequencing and event concatenation. -/
def continueExecution (observed : Observation) : OptionT ProbComp Result :=
  observed.followM sampledSuffix

def inScope (observed : Observation) : Prop :=
  observed.state = 0 ∨ observed.state = 1

def ready (observed : Observation) : Prop :=
  observed.outcome = .returned 4 ∧ observed.state = 1

def success (observed : Result) : Prop :=
  observed.outcome = .returned true ∧ observed.state = 1 ∧ observed.events = [1, 1]

theorem sampled_scope : ∀ observed ∈ support sampledFirst, inScope observed := by
  intro observed supported
  rw [OptionT.mem_support_iff] at supported
  obtain ⟨coin, _, branch⟩ := mem_support_bind_peel _ _ supported
  by_cases zero : coin = (0 : Fin 7)
  · simp [zero] at branch
  · by_cases one : coin = (1 : Fin 7)
    · simp [one, PIR.Process.run] at branch
      subst observed
      exact Or.inl rfl
    · simp [zero, one, first, handler, PIR.Process.run,
        PIR.Execution.follow] at branch
      subst observed
      exact Or.inr rfl

theorem sampled_prefix_failure :
    1 - Pr{let observed ← sampledFirst}[ready observed] = 2 / 7 := by
  rw [sampledFirst, OptionT.prEvent_mk, prEvent_bind_eq_sum_fintype]
  simp only [Fin.sum_univ_succ]
  simp only [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin]
  norm_num [Fin.sum_univ_succ, ready, first, handler, PIR.Process.run, PIR.Execution.follow]
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_sub_of_le]
  · repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num
  · rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
    repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num
  · norm_num

/-- Counting only returned unsuccessful observations loses the preparation
failure's additional `1/7` mass. -/
theorem sampled_returned_failure :
    Pr{let observed ← sampledFirst}[¬ ready observed] = 1 / 7 := by
  rw [sampledFirst, OptionT.prEvent_mk, prEvent_bind_eq_sum_fintype]
  simp only [Fin.sum_univ_succ]
  simp only [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin]
  norm_num [ready, first, handler, PIR.Process.run, PIR.Execution.follow, one_div]

theorem sampled_suffix_failure : ∀ observed ∈ support sampledFirst,
    inScope observed → ready observed →
    1 - Pr{let result ← continueExecution observed}[success result] ≤ 2 / 5 := by
  intro observed supported _ inside
  rw [OptionT.mem_support_iff] at supported
  obtain ⟨coin, _, branch⟩ := mem_support_bind_peel _ _ supported
  by_cases zero : coin = (0 : Fin 7)
  · simp [zero] at branch
  · by_cases one : coin = (1 : Fin 7)
    · simp [one, PIR.Process.run] at branch
      subst observed
      simp [ready] at inside
    · simp [zero, one, first, handler, PIR.Process.run,
        PIR.Execution.follow] at branch
      subst observed
      simp only [continueExecution, PIR.Execution.followM]
      rw [bind_pure_comp, prEvent_map, sampledSuffix, OptionT.prEvent_mk,
        prEvent_bind_eq_sum_fintype]
      simp only [Fin.sum_univ_succ]
      simp only [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin]
      norm_num [Fin.sum_univ_succ, success, suffix, handler, PIR.Process.run, PIR.Execution.follow]
      rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
      repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num

theorem nonzero_composition_bound :
    1 - Pr{let result ← sampledFirst >>= continueExecution}[success result] ≤ 2 / 7 + 2 / 5 :=
  probabilistic_bind sampledFirst continueExecution inScope ready success (2 / 7) (2 / 5)
    sampled_scope sampled_prefix_failure.le sampled_suffix_failure

/-- The same law also applies directly to `ProbComp`, observing the optional
result explicitly. This is totalization, without conditioning on success. -/
theorem probComp_composition_bound :
    1 - Pr{let result ← sampledFirst.run >>= fun observed =>
      observed.elim (pure none) (fun reached => (continueExecution reached).run)}[
        result.elim False success] ≤ 2 / 7 + 2 / 5 := by
  apply probabilistic_bind (m := ProbComp) sampledFirst.run
    (fun observed : Option Observation =>
      observed.elim (pure none) (fun reached => (continueExecution reached).run))
    (fun observed => observed.elim True inScope)
    (fun observed => observed.elim False ready) (fun result => result.elim False success)
    (2 / 7) (2 / 5)
  · intro observed supported
    cases observed with
    | none => trivial
    | some reached => exact sampled_scope reached ((OptionT.mem_support_iff _ _).mpr supported)
  · rw [← OptionT.prEvent_eq_run]
    exact sampled_prefix_failure.le
  · intro observed supported scopeHolds inside
    cases observed with
    | none => exact inside.elim
    | some reached =>
      simp only [Option.elim_some]
      rw [← OptionT.prEvent_eq_run]
      exact sampled_suffix_failure reached ((OptionT.mem_support_iff _ _).mpr supported) scopeHolds inside

theorem composition_failure :
    1 - Pr{let result ← sampledFirst >>= continueExecution}[success result] = 4 / 7 := by
  rw [OptionT.prEvent_eq_run, OptionT.run_bind]
  simp only [sampledFirst, OptionT.run_mk, Option.elimM, bind_assoc]
  rw [prEvent_bind_eq_sum_fintype]
  simp only [Fin.sum_univ_succ,
    SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin]
  norm_num [continueExecution, sampledSuffix, PIR.Execution.followM, first, suffix, handler,
    PIR.Process.run, PIR.Execution.follow, success]
  simp only [OracleComp.prEvent_bind_eq_tsum_prEvent ($ᵗ (Fin 5)), tsum_fintype, Fin.sum_univ_succ,
    SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin]
  norm_num [success, handler, PIR.Process.run, PIR.Execution.follow]
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_sub_of_le]
  · repeat first
      | rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      | rw [ENNReal.toReal_mul]
    norm_num
  · rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
    repeat first
      | rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      | rw [ENNReal.toReal_mul]
    norm_num
  · norm_num

/-- The pre-existing real private-coin baseline is imported from its compiled
module, rather than reconstructed or replaced by this finite control. -/
example (initial : Zkc.Construction.Domain.RuntimeState
    TestsSecurity.HonestSampling.carriers Unit) :
    ZkcSecurity.FiatShamir.HonestSampling.failure
      (Zkc.Construction.Domain.run .producer ZkcSecurity.FiatShamir.SampledCompiled.oracle
        PrivateProducerWP.CoinStop.producer initial
        (ZkcSecurity.FiatShamir.SampledCompiled.services TestsSecurity.HonestSampling.context
          [TestsSecurity.HonestSampling.port] []))
      (fun observed => ∃ value, observed.outcome = .returned value) = 1 / 7 :=
  PrivateProducerWP.CoinStop.failure initial

#print axioms deterministic_bind
#print axioms probabilistic_bind
#print axioms reached_state_composes
#print axioms wrong_state_refused
#print axioms nonzero_composition_bound
#print axioms probComp_composition_bound
#print axioms composition_failure
#print axioms PrivateProducerWP.CoinStop.failure

end TestsSecurity.HonestComposition
