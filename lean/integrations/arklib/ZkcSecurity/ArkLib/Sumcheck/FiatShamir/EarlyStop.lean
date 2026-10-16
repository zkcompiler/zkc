module

public import ZkcSecurity.ArkLib.Sumcheck.FiatShamir.FullPrefix

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Acceptance coupling between early rejection and full-prefix completion.
Only the acceptance probability is equated. Extra completion accesses can change
both the query log and cache; no equality of their final states is claimed. -/

namespace ZkcSecurity.ArkLib.Sumcheck.FiatShamir.FullPrefix

open Interaction.Oracle.Security
open OracleComp OracleSpec
open Zkc.Protocols.AlgebraicRounds (Message)
open Zkc.Protocols.Sumcheck.Common
open ZkcSecurity.ArkLib.FiatShamir

variable {Input F : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
variable [DecidableEq Input]

/-- The two guards execute before their respective oracle requests. -/
def earlyVerify (statement : Input → Statement F) (z : Input) (m n : Message F) :
    OracleComp (Oracle Input F) Bool := do
  if wireBoundary m = (statement z).claim then
    let first : F ← liftM ((Oracle Input F).query (.inl (z, m)))
    if wireBoundary n = wireEvaluate m first then
      let second : F ← liftM ((Oracle Input F).query (.inr (z, m, first, n)))
      pure (decide (wireEvaluate n second = evaluate (statement z).coefficients first second))
    else pure false
  else pure false

/-- Every completion runs both queries and then observes all three checks. -/
def completeVerify (statement : Input → Statement F) (z : Input) (m n : Message F) :
    OracleComp (Oracle Input F) Bool := do
  let first : F ← liftM ((Oracle Input F).query (.inl (z, m)))
  let second : F ← liftM ((Oracle Input F).query (.inr (z, m, first, n)))
  pure (decide (accepted (statement z) m first n second))

omit [DecidableEq Input] in
/-- The early verifier reaches at most two accesses, counting cache hits. -/
theorem earlyVerify_queryBound (statement : Input → Statement F) (z : Input) (m n : Message F) :
    IsTotalQueryBound (earlyVerify statement z m n) 2 := by
  by_cases first : wireBoundary m = (statement z).claim
  · simp only [earlyVerify, first, ite_true, isTotalQueryBound_query_bind_iff]
    refine ⟨by decide, fun challenge => ?_⟩
    by_cases second : wireBoundary n = wireEvaluate m challenge
    · simp only [second, ite_true, isTotalQueryBound_query_bind_iff]
      exact ⟨by decide, fun _ => trivial⟩
    · simp only [second, ite_false]
      trivial
  · simp only [earlyVerify, first, ite_false]
    trivial

omit [DecidableEq Input] in
/-- Completion always budgets two accesses, even for a failed first guard. -/
theorem completeVerify_queryBound (statement : Input → Statement F) (z : Input) (m n : Message F) :
    IsTotalQueryBound (completeVerify statement z m n) 2 :=
  ⟨by change 0 < 2; decide, fun _ => ⟨by change 0 < 1; decide, fun _ => trivial⟩⟩

/-- The comparison allows an arbitrary preexisting cache, including adversarial
prequeries and unrelated entries. Rejected continuations have zero acceptance. -/
theorem earlyVerify_acceptance (statement : Input → Statement F) (z : Input) (m n : Message F)
    (cache : (Oracle Input F).QueryCache) :
    Pr{let result ← (simulateQ randomOracle (earlyVerify statement z m n)).run' cache}[
      result = true] =
    Pr{let result ← (simulateQ randomOracle (completeVerify statement z m n)).run' cache}[
      result = true] := by
  by_cases firstCheck : wireBoundary m = (statement z).claim
  · simp only [earlyVerify, firstCheck, ite_true, completeVerify, simulateQ_bind,
      simulateQ_spec_query, simulateQ_pure, StateT.run'_eq, StateT.run_bind,
      StateT.run_pure, prEvent_map]
    apply prEvent_bind_congr
    rintro ⟨first, nextCache⟩
    by_cases secondCheck : wireBoundary n = wireEvaluate m first
    · simp [secondCheck, accepted, firstCheck, StateT.run_bind]
    · simp [secondCheck, accepted, firstCheck, simulateQ_pure, StateT.run_pure]
  · simp [earlyVerify, firstCheck, completeVerify, accepted, simulateQ_bind,
      simulateQ_pure, StateT.run'_eq, StateT.run_bind,
      StateT.run_pure]

/-- A native early-stopping verifier shares the adversary's live cache. -/
def earlyGame (statement : Input → Statement F) (adversary : Adversary Input F) :
    OracleComp (Oracle Input F) (Input × Bool) := do
  let (z, m, n, _) ← adversary
  let accepted ← earlyVerify statement z m n
  pure (z, accepted)

omit [DecidableEq Input] in
/-- Actual early verification uses at most `Q+2` queries. The security reduction
charges one additional salt-selection access, giving the conservative `Q+3`. -/
theorem earlyGame_queryBound (statement : Input → Statement F) (adversary : Adversary Input F)
    (Q : Nat) (queryBound : IsTotalQueryBound adversary Q) :
    IsTotalQueryBound (earlyGame statement adversary) (Q + 2) := by
  apply isTotalQueryBound_bind queryBound
  rintro ⟨z, m, n, witness⟩
  simpa only [← map_eq_pure_bind, IsTotalQueryBound, isQueryBound_map_iff] using
    earlyVerify_queryBound statement z m n

/-- Concrete completion experiment followed by the Boolean observation. -/
def completeGame (statement : Input → Statement F) (adversary : Adversary Input F) :
    OracleComp (Oracle Input F) (Input × Bool) := do
  let (z, m, n, _) ← adversary
  let accepted ← completeVerify statement z m n
  pure (z, accepted)

omit [DecidableEq Input] in
/-- Full-prefix completion is the existing generic experiment, with an explicit
Sumcheck acceptance observation. -/
theorem completeGame_eq (statement : Input → Statement F) (adversary : Adversary Input F) :
    completeGame statement adversary =
      (fun result => (result.1, decide (accepted (statement result.1)
        result.2.1.1 result.2.1.2.1 result.2.1.2.2.1 result.2.1.2.2.2.1))) <$>
      Prefix.execution adversary := by
  simp only [completeGame, Prefix.execution, map_eq_pure_bind, bind_assoc]
  apply bind_congr
  rintro ⟨z, m, n, witness⟩
  rfl

/-- The actual adversarial early-stop game and completed game have exactly equal
false-acceptance probabilities; state and query traces are deliberately excluded. -/
theorem earlyGame_acceptance (statement : Input → Statement F) (adversary : Adversary Input F) :
    Pr{let result ← (simulateQ randomOracle (earlyGame statement adversary)).run' ∅}[
      result.2 = true ∧ (statement result.1).claim ≠
        (polynomial (statement result.1).coefficients).booleanSum] =
    Pr{let result ← (simulateQ randomOracle (completeGame statement adversary)).run' ∅}[
      result.2 = true ∧ (statement result.1).claim ≠
        (polynomial (statement result.1).coefficients).booleanSum] := by
  simp only [earlyGame, completeGame, simulateQ_bind, simulateQ_pure, StateT.run'_eq,
    StateT.run_bind, StateT.run_pure, prEvent_map]
  apply prEvent_bind_congr
  rintro ⟨⟨z, m, n, witness⟩, cache⟩
  simp only [bind_assoc, pure_bind]
  by_cases falseClaim : (statement z).claim ≠ (polynomial (statement z).coefficients).booleanSum
  · simpa [falseClaim, StateT.run'_eq] using
      earlyVerify_acceptance statement z m n cache
  · simp [falseClaim]

/-- Full-prefix Fiat-Shamir soundness of the actual early-stopping query schedule. -/
theorem early_soundness (statement : Input → Statement F) (adversary : Adversary Input F)
    (Q : Nat) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (earlyGame statement adversary)).run' ∅}[
      result.2 = true ∧ (statement result.1).claim ≠
        (polynomial (statement result.1).coefficients).booleanSum] ≤
          (Q + 3 : ENNReal) * (2 / (Fintype.card F : ENNReal)) := by
  rw [earlyGame_acceptance, completeGame_eq, simulateQ_map]
  simpa only [StateT.run'_map', prEvent_map, decide_eq_true_eq, pathAccepted] using
    soundness statement adversary Q queryBound

end ZkcSecurity.ArkLib.Sumcheck.FiatShamir.FullPrefix
