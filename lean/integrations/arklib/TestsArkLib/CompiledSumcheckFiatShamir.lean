import ZkcArkLibExamples.CompiledSumcheckFiatShamir
import TestsArkLib.SumcheckFiatShamir

/-! Controls for the Fiat–Shamir theorems of the compiled Sumcheck proof Entry.

The subject is the actual compiled validator, read through its ideal meaning
under the Entry's checked occurrence context. The instance is the one-round
`ZMod 5` instance of the imported verifier's controls: raw table values
`[2, 1]` (extension `2 - r`, sum `3`), the false claim `0` and the cheating
proof `(0, 0)`.

* Every premise of `soundness` holds together, with bound `1 / 5`
  (`premises`), and the bound is attained on the compiled program: a prover
  that sends the cheating proof without any query is accepted with probability
  exactly `1 / 5` (`cheater_acceptance`). The compiled verifier asks the
  cheating proof's one challenge at the history its own context names
  (`cheat_compiled`).
* The compiled program itself, evaluated in the kernel without the
  construction equation, accepts the cheating proof exactly at the challenge
  `2` (`cheat_accepted_at_two`). The false-claim premise is necessary: for the
  true claim `3` it accepts the honest proof `(2, 1)` at every challenge
  (`honest_accepted`).
* The adaptive premises hold together with a binding of the vector, the claim
  and the count that determines the statement (`adaptive_premises`). The
  determining premise is necessary on the compiled program too: with one
  initial transcript for every statement, a prover that asks the challenge of
  `(0, 0)` first and then chooses a vector it fits is accepted on a false claim
  with probability `4 / 5`, above the `3 / 5` the adaptive bound gives for one
  query (`unbound_violates_bound`). This is why the adaptive theorems need a
  binding of the vector and count inputs, which the host binding model does not
  yet cover.
* The reduced-challenge corollary's premises hold with samples below `64`
  (`reduced_premises`). -/

namespace TestsSecurity.CompiledSumcheckFiatShamir
open OracleComp OracleSpec
open Zkc.Source Zkc.Construction ZkcExamples.Structured ZkcExamples.Construction
open Zkc.Polynomial.Multilinear
open ZkcSecurity.FiatShamir ZkcSecurity.Examples.SumcheckFiatShamir
open ZkcSecurity.Examples.CompiledSumcheckFiatShamir
open TestsSecurity.SumcheckFiatShamir (Scalar raw table decoded false_claim initial handle cheat
  honest cheater cheater_bound plain imported_plain cheatDecision cheatDecision_accepted binding
  binding_determined falseStatement adaptiveCheater unbound chosenTable chosenStatement
  weakDecision weak_event weak_exceeds_bound numbering)
open scoped ENNReal

noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

/-- Every premise of `soundness` holds together on the compiled Entry; the bound
is `1 / 5`. -/
theorem premises :
    Pr{let result ← (simulateQ randomOracle
        (cheater >>= compiledVerifier historyQuery raw 0 1 initial)).run' ∅}[
      Accepted (· = some true) result.1] ≤ 1 / 5 := by
  have bound := soundness 1 raw table decoded 0 false_claim initial cheater 0 cheater_bound
  simpa only [Nat.cast_zero, Nat.cast_one, zero_add, one_mul, ZMod.card, Nat.cast_ofNat]
    using bound

/-! ### The bound is attained on the compiled program -/

/-- The history at which the compiled verifier asks the cheating proof's
challenge: the initial transcript, both round messages and the challenge
occurrence, named by the Entry's checked context. -/
def cheatKey : History Scalar Scalar :=
  initial ++
    [.message (SumcheckProof.context.message
        (SumcheckVerifierLaws.lowSite SumcheckSourceVerifier.childContext)
        (SumcheckSourceVerifier.childContext.roles 0) SumcheckProof.context.validator)
      (.field "bls12-381.fr" 0)] ++
    [.message (SumcheckProof.context.message
        (SumcheckVerifierLaws.highSite SumcheckSourceVerifier.childContext)
        (SumcheckSourceVerifier.childContext.roles 0) SumcheckProof.context.validator)
      (.field "bls12-381.fr" 0)] ++
    [.challenge (SumcheckProof.context.query
      (SumcheckVerifierLaws.challengeSite SumcheckSourceVerifier.childContext)
      (.draw "bls12-381.fr"))]

/-- The compiled verifier asks one challenge on the cheating proof, at
`cheatKey`, and decides. -/
theorem cheat_compiled :
    compiledVerifier historyQuery raw 0 1 initial cheat = cheatDecision <$> historyQuery cheatKey := by
  rw [construction historyQuery raw 0 1 handle initial cheat, imported_plain]
  simp only [plain, validator, PIR.repeatN, verifierRound, afterLow, afterHigh, afterChallenge,
    terminal, decision, PIR.Process.bind, cheat, transform_eq_done, transform_eq_receive,
    transform_eq_query, transform_eq_send, Payload.value, ↓reduceIte, add_zero,
    List.nil_append]
  rfl

/-- The query-free cheating prover is accepted by the compiled verifier with
probability exactly `1 / 5`, the bound of `soundness`. -/
theorem cheater_acceptance :
    Pr{let result ← (simulateQ randomOracle
        (cheater >>= compiledVerifier historyQuery raw 0 1 initial)).run' ∅}[
      Accepted (· = some true) result.1] = 1 / 5 := by
  rw [TestsSecurity.SumcheckFiatShamir.cheater, pure_bind, cheat_compiled, simulateQ_map]
  simp only [historyQuery, simulateQ_spec_query, StateT.run'_eq, StateT.run_map,
    randomOracle.run_eq, QueryCache.empty_apply, map_bind, map_pure]
  change Pr{let answer ← $ᵗ Scalar}[Accepted (· = some true) (cheatDecision answer).1] = 1 / 5
  rw [prEvent_congr _ _ (fun answer => answer = 2) cheatDecision_accepted,
    SampleableType.prEvent_uniformSample_eq_singleton, ZMod.card, Nat.cast_ofNat, one_div]

/-- The compiled program itself, evaluated in the kernel with a constant
challenge and without the construction equation, accepts the cheating proof
exactly at the challenge `2`, as the transform of the imported verifier does. -/
theorem cheat_accepted_at_two (challenge : Scalar) :
    (compiledVerifier (F := Scalar) (G := Scalar) (m := Id) (fun _ => challenge) raw 0 1 initial
      cheat).1 = PIR.Outcome.returned (some (decide (challenge = 2))) := by
  revert challenge
  decide +kernel

/-- Without the false-claim premise the compiled program, evaluated in the
kernel, accepts the honest proof for the true claim `3` at every challenge. -/
theorem honest_accepted (challenge : Scalar) :
    (compiledVerifier (F := Scalar) (G := Scalar) (m := Id) (fun _ => challenge) raw 3 1 initial
      honest).1 = PIR.Outcome.returned (some true) := by
  revert challenge
  decide +kernel

/-! ### Adaptively chosen statements -/

/-- Every premise of `adaptive_soundness` holds together with the determining
binding of the vector, the claim and the count; the bound is `2 / 5`. -/
theorem adaptive_premises :
    Pr{let result ← (simulateQ randomOracle (adaptiveCheater >>= fun claimed =>
        (fun result => (claimed.1, result)) <$>
          compiledVerifier (decodedQuery (id : Scalar → Scalar)) claimed.1.raw claimed.1.claim
            claimed.1.count (binding claimed.1) claimed.2)).run' ∅}[
      result.1.claim ≠ result.1.raw.sum ∧ Accepted (· = some true) result.2.1] ≤ 2 / 5 := by
  have bound := adaptive_soundness (id : Scalar → Scalar) 0 balanced_id binding binding_determined
    adaptiveCheater 0 trivial
  simpa only [Nat.cast_zero, zero_add, add_zero, ZMod.card, Nat.cast_ofNat, mul_one_div]
    using bound

/-- Ask the compiled verifier's challenge of `(0, 0)` first, then choose a
statement it fits. -/
def weakProver :
    OracleComp (FieldOracle Scalar Scalar) (PublicStatement Scalar × Proof Scalar Scalar) := do
  let challenge ← historyQuery cheatKey
  pure (chosenStatement challenge, cheat)

theorem weakProver_bound : IsTotalQueryBound weakProver 1 :=
  isTotalQueryBound_query_bind_iff.mpr ⟨Nat.one_pos, fun _ => trivial⟩

/-- Without a determining binding, the compiled verifier decides the statement
chosen at `challenge` on `(0, 0)` with the one challenge it asks at `cheatKey`. -/
theorem weak_compiled (challenge : Scalar) :
    compiledVerifier (decodedQuery id) (chosenStatement challenge).raw
        (chosenStatement challenge).claim (chosenStatement challenge).count
        (unbound (chosenStatement challenge)) cheat =
      weakDecision challenge <$> liftM ((FieldOracle Scalar Scalar).query cheatKey) := by
  have admitted : (1 : ℕ) ≤ 2 := by decide
  rw [construction (decodedQuery id) _ _ _ handle _ cheat]
  simp only [chosenStatement, unbound]
  rw [importedValidator_eq 1 admitted _ (chosenTable challenge)
      (TestsSecurity.SumcheckFiatShamir.chosen_decoded challenge)]
  simp only [validator, PIR.repeatN, verifierRound, afterLow, afterHigh, afterChallenge,
    PIR.Process.bind, cheat, transform_eq_receive, Payload.value, List.nil_append]
  rfl

/-- The one-query prover is accepted by the compiled verifier on a false claim
with probability `4 / 5` when the initial transcript does not bind the
statement. -/
theorem weak_acceptance :
    Pr{let result ← (simulateQ randomOracle (weakProver >>= fun claimed =>
        (fun result => (claimed.1, result)) <$>
          compiledVerifier (decodedQuery (id : Scalar → Scalar)) claimed.1.raw claimed.1.claim
            claimed.1.count (unbound claimed.1) claimed.2)).run' ∅}[
      result.1.claim ≠ result.1.raw.sum ∧ Accepted (· = some true) result.2.1] = 4 / 5 := by
  simp only [weakProver, historyQuery, bind_assoc, pure_bind, weak_compiled, Functor.map_map,
    simulateQ_bind, simulateQ_map, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind,
    StateT.run_map, randomOracle.run_eq, QueryCache.empty_apply, QueryCache.cacheQuery_self,
    map_pure, pure_bind]
  change Pr{let challenge ← $ᵗ Scalar}[(chosenStatement challenge).claim ≠
      (chosenStatement challenge).raw.sum ∧
        Accepted (· = some true) (weakDecision challenge challenge).1] = 4 / 5
  rw [prEvent_congr _ _ (fun challenge => challenge ≠ 3) weak_event,
    SampleableType.prEvent_uniformSample]
  have count : (Finset.univ.filter fun challenge : Scalar => challenge ≠ 3).card = 4 := by
    decide +kernel
  rw [count, ZMod.card]
  rfl

/-- The adaptive conclusion fails on the compiled program without a determining
initial transcript: the one-query prover exceeds `(1 + 2) * (1 / 5 + 0)`. -/
theorem unbound_violates_bound :
    ¬ Pr{let result ← (simulateQ randomOracle (weakProver >>= fun claimed =>
        (fun result => (claimed.1, result)) <$>
          compiledVerifier (decodedQuery (id : Scalar → Scalar)) claimed.1.raw claimed.1.claim
            claimed.1.count (unbound claimed.1) claimed.2)).run' ∅}[
      result.1.claim ≠ result.1.raw.sum ∧ Accepted (· = some true) result.2.1] ≤
      ((1 : ℕ) + (2 : ℕ) : ENNReal) * (1 / 5 + 0) := fun bound =>
  absurd (weak_acceptance.symm.le.trans bound) (not_le.mpr weak_exceeds_bound)

/-- A prover choosing the false statement and the cheating proof, over the oracle
of uniform samples below `64`. -/
def wideCheater :
    OracleComp (Oracle Scalar Scalar (Fin 64)) (PublicStatement Scalar × Proof Scalar Scalar) :=
  pure (falseStatement, cheat)

/-- The premises of `reduced_soundness` hold with samples below `64`. -/
theorem reduced_premises :
    Pr{let result ← (simulateQ randomOracle (wideCheater >>= fun claimed =>
        (fun result => (claimed.1, result)) <$>
          compiledVerifier (decodedQuery (reduce numbering 64)) claimed.1.raw claimed.1.claim
            claimed.1.count (binding claimed.1) claimed.2)).run' ∅}[
      result.1.claim ≠ result.1.raw.sum ∧ Accepted (· = some true) result.2.1] ≤
      ((0 : ℕ) + 2) * (1 / (Fintype.card Scalar : ENNReal) + (Fintype.card Scalar : ENNReal) / 64) :=
  reduced_soundness numbering 64 binding binding_determined wideCheater 0 trivial

end TestsSecurity.CompiledSumcheckFiatShamir
