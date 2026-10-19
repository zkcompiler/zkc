import ZkcSecurity.FiatShamir.Upstream

/-! Controls for importing ArkLib's worst-case round-by-round soundness.

**Guessing.** A two-round ArkLib protocol: the prover sends a guess in `Fin 4`,
the verifier draws a challenge in `Fin 4` and accepts when the challenge equals
the guess. Every input is false (`language = ∅`). The verifier is pure and is
read through its guarded form (`guarded`). The state function is false before
the challenge and, at the full transcript, says whether the challenge equals the
guess (`stateFunction`); the worst-case bound at the challenge round is `1 / 4`
(`worstCase`). The import gives the process form's typed certificate, and the
typed engine bounds the transform's acceptance against a prover with `queries`
queries by `(queries + 1) / 4`, one challenge round (`guess_soundness`), for any
input the prover chooses after its queries too (`guess_adaptive_soundness`). The
experiment is not vacuous: a prover that sends a guess without querying is
accepted with probability exactly `1 / 4` (`guess_accepted`), the bound at zero
queries.

**Either guess.** A four-round protocol with two challenge rounds of unequal
error and a verifier that rejects by guard failure: the prover sends guesses
`g₀` and `g₁` in `Fin 4` before the challenges `c₀` and `c₁`, and the guard
passes when `c₀` has the parity of `g₀` or `c₁ = g₁` (`eitherGuarded`). The
state says whether a check already passed (`eitherState`); the first challenge
round escapes with probability `1 / 2` and the second with `1 / 4`
(`eitherWorstCase`). The weighted bound charges each round its own error: a
prover whose queries charge `proverCost` is accepted with probability at most
`proverCost + 1 / 2 + 1 / 4` (`either_soundness_weighted`), so at most `3 / 4`
without queries (`either_soundness_without_queries`), where the bound with the
largest error at every query, `(queries + 2) / 2`, is vacuous. A prover that
sends two guesses without querying is accepted with probability at least
`1 / 2` (`either_accepted`): the experiment accepts through all four rounds. -/

namespace TestsSecurity.UpstreamImports
open OracleComp OracleSpec ProtocolSpec
open ZkcSecurity.FiatShamir ZkcSecurity.FiatShamir.Typed ZkcSecurity.FiatShamir.Upstream
open scoped ENNReal NNReal

/-! ## Guessing -/

/-- A guess from the prover, then a challenge. -/
def pSpec : ProtocolSpec 2 := ⟨![.P_to_V, .V_to_P], fun _ => Fin 4⟩

instance challengeSampleable : ∀ index, SampleableType (pSpec.Challenge index) :=
  fun _ => inferInstanceAs (SampleableType (Fin 4))

instance typeDecidable : ∀ round, DecidableEq (pSpec.«Type» round) :=
  fun _ => inferInstanceAs (DecidableEq (Fin 4))

/-- The guess and the challenge of a full transcript. -/
def guessOf (transcript : FullTranscript pSpec) : Fin 4 := transcript 0
def challengeOf (transcript : FullTranscript pSpec) : Fin 4 := transcript 1

/-- Accept when the challenge equals the guess. -/
def verifier : Verifier []ₒ Unit Bool pSpec where
  verify _ transcript := pure (decide (challengeOf transcript = guessOf transcript))

def pureForm : verifier.PureForm :=
  ⟨fun _ transcript => decide (challengeOf transcript = guessOf transcript), fun _ _ => rfl⟩

/-- The pure verifier as a guarded one whose guard always passes. -/
abbrev guarded : verifier.GuardedForm := pureForm.toGuardedForm

def init : ProbComp Unit := pure ()

def impl : QueryImpl []ₒ (StateT Unit ProbComp) := fun query => nomatch query

/-- The guess of a transcript that has it. -/
def guessAt {round : Fin 3} (transcript : Transcript round pSpec) (inside : 0 < round.val) :
    Fin 4 :=
  transcript ⟨0, inside⟩

/-- False before the challenge; at the full transcript, whether the challenge
equals the guess. -/
def state (round : Fin 3) (_ : Unit) (transcript : Transcript round pSpec) : Prop :=
  if full : round.val = 2 then
    (transcript ⟨1, by omega⟩ : Fin 4) = (transcript ⟨0, by omega⟩ : Fin 4)
  else False

def stateFunction : verifier.StateFunction init impl ∅ {true} where
  toFun := state
  toFun_empty statement := by simp [state]
  toFun_next round message statement transcript _ value := by
    have first : round = 0 := by
      fin_cases round
      · rfl
      · simp [pSpec] at message
    subst first
    simp [state]
  toFun_full statement transcript false_ := by
    have different : challengeOf transcript ≠ guessOf transcript := by
      simp only [state, Fin.val_last, ↓reduceDIte] at false_
      exact false_
    exact prEvent_verdict_eq_zero init impl guarded statement transcript
      (by simp [guardedVerdict, Verifier.PureForm.toGuardedForm, Accepts, pureForm, different])

theorem worstCase : ∀ statement ∉ (∅ : Set Unit), ∀ index : pSpec.ChallengeIdx,
    ∀ transcript : Transcript index.1.castSucc pSpec,
      Pr{let challenge ← $ᵗ (pSpec.Challenge index)}[
        ¬ stateFunction index.1.castSucc statement transcript ∧
          stateFunction index.1.succ statement (transcript.concat challenge)] ≤
        (fun _ => (4⁻¹ : ℝ≥0)) index := by
  rintro statement - ⟨round, challengeRound⟩ transcript
  have second : round = 1 := by
    fin_cases round
    · simp [pSpec] at challengeRound
    · rfl
  subst second
  show _ ≤ ((4⁻¹ : ℝ≥0) : ℝ≥0∞)
  refine le_of_eq ((prEvent_congr _ _ (fun challenge : Fin 4 =>
    challenge = guessAt transcript Nat.zero_lt_one) fun challenge => ?_).trans ?_)
  · simp [stateFunction, state, guessAt, Transcript.concat, Fin.snoc]
    exact Iff.rfl
  · exact (SampleableType.prEvent_uniformSample_eq_singleton (α := Fin 4)
      (guessAt transcript Nat.zero_lt_one)).trans (by simp)

theorem sound : verifier.rbrSoundnessWorstCase init impl ∅ {true} fun _ => 4⁻¹ :=
  ⟨stateFunction, worstCase⟩

theorem challenges : Fintype.card pSpec.ChallengeIdx = 1 := by decide

/-- The transform of the process form accepts with probability at most
`(queries + 1) / 4` against every prover with `queries` queries. -/
theorem guess_soundness
    (prover : OracleComp (OracleSpec.ofFn (ByLast (Raw pSpec Unit))) (List (Message pSpec)))
    (queries : ℕ) (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (Typed.fixedExperiment (absorb pSpec Unit)
        (validator (guardedVerdict guarded) ()) (initial pSpec Unit ()) prover)).run' ∅}[
      Accepted (Accepts ({true} : Set Bool)) result.1] ≤ (queries + 1) * 4⁻¹ := by
  have bound := worstCase_soundness init impl guarded sound (bound := 4⁻¹)
    (fun _ => by simp) (statement := ()) (by simp) prover queries proverBound
  rw [challenges] at bound
  refine bound.trans (le_of_eq ?_)
  norm_num

theorem guess_adaptive_soundness
    (prover : OracleComp (OracleSpec.ofFn (ByLast (Raw pSpec Unit))) (Unit × List (Message pSpec)))
    (queries : ℕ) (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (Typed.experiment (absorb pSpec Unit)
        (validator (guardedVerdict guarded)) (initial pSpec Unit) prover)).run' ∅}[
      result.1 ∉ (∅ : Set Unit) ∧ Accepted (Accepts ({true} : Set Bool)) result.2.1] ≤
      (queries + 1) * 4⁻¹ := by
  have bound := worstCase_adaptive_soundness init impl guarded sound (bound := 4⁻¹)
    (fun _ => by simp) prover queries proverBound
  rw [challenges] at bound
  refine bound.trans (le_of_eq ?_)
  norm_num

/-- The history at which the transform reads the challenge after the guess. -/
def challengeKey (guess : Fin 4) : List (Event pSpec Unit) :=
  [.statement (), .message 0 guess, .challenge 1]

/-- With the proof `[guess]`, the transform asks the oracle once, at the history
ending with the challenge occurrence, and accepts when the answer is the guess. -/
theorem experiment_guess (guess : Fin 4) :
    Typed.fixedExperiment (R := ByLast (Raw pSpec Unit)) (absorb pSpec Unit)
        (validator (guardedVerdict guarded) ())
        (initial pSpec Unit ()) (pure [⟨0, guess⟩]) =
      answer (challengeKey guess) >>= fun raw =>
        pure (PIR.Outcome.returned (some (decide ((raw : Fin 4) = guess))), []) :=
  rfl

/-- A prover that sends a guess without querying is accepted with probability
exactly `1 / 4`: the soundness bound at zero queries is attained. -/
theorem guess_accepted (guess : Fin 4) :
    Pr{let result ← (simulateQ randomOracle (Typed.fixedExperiment (R := ByLast (Raw pSpec Unit))
        (absorb pSpec Unit)
        (validator (guardedVerdict guarded) ()) (initial pSpec Unit ())
        (pure [⟨0, guess⟩]))).run' ∅}[Accepted (Accepts ({true} : Set Bool)) result.1] = 4⁻¹ := by
  rw [experiment_guess, answer, simulateQ_bind, simulateQ_spec_query, StateT.run'_eq,
    StateT.run_bind, map_bind, randomOracle.run_eq]
  simp only [Accepted, Accepts, QueryCache.empty_apply, simulateQ_pure, StateT.run_pure, map_pure,
    bind_assoc, pure_bind, Set.mem_singleton_iff, decide_eq_true_iff]
  have singleton := SampleableType.prEvent_uniformSample_eq_singleton (α := Fin 4) guess
  rw [Fintype.card_fin, Nat.cast_ofNat] at singleton
  exact singleton

/-! ## Either guess -/

/-- Two guesses, each before its challenge. -/
def eitherSpec : ProtocolSpec 4 := ⟨![.P_to_V, .V_to_P, .P_to_V, .V_to_P], fun _ => Fin 4⟩

instance eitherSampleable : ∀ index, SampleableType (eitherSpec.Challenge index) :=
  fun _ => inferInstanceAs (SampleableType (Fin 4))

instance eitherDecidable : ∀ round, DecidableEq (eitherSpec.«Type» round) :=
  fun _ => inferInstanceAs (DecidableEq (Fin 4))

/-- The parity of a value. -/
def parity (value : Fin 4) : ℕ := value.val % 2

/-- A round's entry of a full transcript. -/
def entry (transcript : FullTranscript eitherSpec) (round : Fin 4) : Fin 4 := transcript round

/-- The guard: the first challenge has the first guess's parity, or the second
challenge equals the second guess. -/
def eitherCheck (transcript : FullTranscript eitherSpec) : Bool :=
  decide (parity (entry transcript 1) = parity (entry transcript 0) ∨
    entry transcript 3 = entry transcript 2)

/-- A verifier that fails unless the guard passes. -/
def eitherVerifier : Verifier []ₒ Unit Unit eitherSpec where
  verify _ transcript := if eitherCheck transcript then pure () else failure

def eitherGuarded : eitherVerifier.GuardedForm :=
  ⟨fun _ => eitherCheck, fun _ _ => (), fun _ _ => rfl⟩

/-- The first challenge round errs with `1 / 2`, the second with `1 / 4`. -/
noncomputable def eitherError (index : eitherSpec.ChallengeIdx) : ℝ≥0 :=
  if index.1 = 1 then 2⁻¹ else 4⁻¹

/-- Whether a check already passed. -/
def eitherState (round : Fin 5) (_ : Unit) (transcript : Transcript round eitherSpec) : Prop :=
  (if first : 2 ≤ round.val then
    parity (transcript ⟨1, by omega⟩) = parity (transcript ⟨0, by omega⟩) else False) ∨
  (if second : 4 ≤ round.val then
    (transcript ⟨3, by omega⟩ : Fin 4) = (transcript ⟨2, by omega⟩ : Fin 4) else False)

def eitherStateFunction : eitherVerifier.StateFunction init impl ∅ Set.univ where
  toFun := eitherState
  toFun_empty statement := by simp [eitherState]
  toFun_next round message statement transcript false_ value := by
    fin_cases round
    · simp [eitherState]
    · simp [eitherSpec] at message
    · exact false_
    · simp [eitherSpec] at message
  toFun_full statement transcript false_ := by
    have rejected : eitherCheck transcript = false := by
      have neither : ¬ (parity (entry transcript 1) = parity (entry transcript 0) ∨
          entry transcript 3 = entry transcript 2) := false_
      simpa [eitherCheck] using neither
    exact prEvent_verdict_eq_zero init impl eitherGuarded statement transcript
      (by simp [guardedVerdict, eitherGuarded, rejected, Accepts])

/-- At most two of the four values of `Fin 4` have a given parity. -/
theorem parity_count (bit : ℕ) :
    (Finset.univ.filter fun value : Fin 4 => parity value = bit).card ≤ 2 := by
  rcases Nat.lt_or_ge bit 2 with small | large
  · interval_cases bit <;> decide
  · have empty : (Finset.univ.filter fun value : Fin 4 => parity value = bit) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun value _ equal => by
        have below : value.val % 2 < 2 := Nat.mod_lt _ (by decide)
        unfold parity at equal
        omega
    simp [empty]

theorem half : (2 : ℝ≥0∞) / 4 = 2⁻¹ := by
  rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (by simp) (by simp), mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp),
    mul_one]

theorem eitherWorstCase : ∀ statement ∉ (∅ : Set Unit), ∀ index : eitherSpec.ChallengeIdx,
    ∀ transcript : Transcript index.1.castSucc eitherSpec,
      Pr{let challenge ← $ᵗ (eitherSpec.Challenge index)}[
        ¬ eitherStateFunction index.1.castSucc statement transcript ∧
          eitherStateFunction index.1.succ statement (transcript.concat challenge)] ≤
        eitherError index := by
  rintro statement - ⟨round, challengeRound⟩ transcript
  fin_cases round
  · simp [eitherSpec] at challengeRound
  · show _ ≤ ((2⁻¹ : ℝ≥0) : ℝ≥0∞)
    refine (prEvent_mono _ _ (fun challenge : Fin 4 =>
      parity challenge = parity (transcript ⟨0, Nat.zero_lt_one⟩))
        fun challenge escaping => ?_).trans ?_
    · have passed : parity challenge = parity (transcript ⟨0, Nat.zero_lt_one⟩) ∨ False :=
        escaping.2
      exact passed.resolve_right id
    · have count := SampleableType.prEvent_uniformSample (α := Fin 4)
        (fun challenge => parity challenge = parity (transcript ⟨0, Nat.zero_lt_one⟩))
      rw [Fintype.card_fin, Nat.cast_ofNat] at count
      refine (le_of_eq count).trans ?_
      rw [ENNReal.coe_inv_two, ← half]
      exact ENNReal.div_le_div_right (by exact_mod_cast parity_count _) 4
  · simp [eitherSpec] at challengeRound
  · show _ ≤ ((4⁻¹ : ℝ≥0) : ℝ≥0∞)
    refine (prEvent_mono _ _ (fun challenge : Fin 4 =>
      challenge = transcript ⟨2, Nat.lt_succ_self 2⟩) fun challenge escaping => ?_).trans ?_
    · obtain ⟨before, after⟩ := escaping
      have before' : ¬ (parity (transcript ⟨1, Nat.lt_succ_of_lt Nat.one_lt_two⟩) =
          parity (transcript ⟨0, Nat.zero_lt_succ 2⟩) ∨ False) := before
      have after' : parity (transcript ⟨1, Nat.lt_succ_of_lt Nat.one_lt_two⟩) =
          parity (transcript ⟨0, Nat.zero_lt_succ 2⟩) ∨
            (challenge : Fin 4) = transcript ⟨2, Nat.lt_succ_self 2⟩ := after
      exact after'.resolve_left fun same => before' (Or.inl same)
    · refine (SampleableType.prEvent_uniformSample_eq_singleton (α := Fin 4) _).trans_le ?_
      simp

theorem eitherSound :
    eitherVerifier.rbrSoundnessWorstCase init impl ∅ Set.univ eitherError :=
  ⟨eitherStateFunction, eitherWorstCase⟩

/-- The challenge rounds' errors sum to `1 / 2 + 1 / 4`. -/
theorem eitherError_sum :
    ∑ index : eitherSpec.ChallengeIdx, (eitherError index : ℝ≥0∞) = 2⁻¹ + 4⁻¹ := by
  rw [← sum_roundError, Fin.sum_univ_four]
  simp [roundError, eitherSpec, eitherError]

/-- The weighted bound: each challenge round is charged its own error. -/
theorem either_soundness_weighted
    (prover : OracleComp (OracleSpec.ofFn (ByLast (Raw eitherSpec Unit)))
      (List (Message eitherSpec)))
    (proverCost : ℝ≥0∞)
    (proverBound : WorstCaseCostBound prover
      ⟨keyError (eventError (StmtIn := Unit) eitherError)⟩ proverCost) :
    Pr{let result ← (simulateQ randomOracle (Typed.fixedExperiment (absorb eitherSpec Unit)
        (validator (guardedVerdict eitherGuarded) ()) (initial eitherSpec Unit ()) prover)).run'
        ∅}[Accepted (Accepts (Set.univ : Set Unit)) result.1] ≤ proverCost + (2⁻¹ + 4⁻¹) := by
  have bound := worstCase_soundness_weighted init impl eitherGuarded eitherSound (statement := ())
    (by simp) prover proverCost proverBound
  rwa [eitherError_sum] at bound

/-- Without queries the weighted bound is `3 / 4`; the bound with the largest
error at every query, `(0 + 2) / 2`, is vacuous. -/
theorem either_soundness_without_queries
    (prover : OracleComp (OracleSpec.ofFn (ByLast (Raw eitherSpec Unit)))
      (List (Message eitherSpec)))
    (proverBound : IsTotalQueryBound prover 0) :
    Pr{let result ← (simulateQ randomOracle (Typed.fixedExperiment (absorb eitherSpec Unit)
        (validator (guardedVerdict eitherGuarded) ()) (initial eitherSpec Unit ()) prover)).run'
        ∅}[Accepted (Accepts (Set.univ : Set Unit)) result.1] ≤ 2⁻¹ + 4⁻¹ := by
  have free := worstCaseCostBound_of_isTotalQueryBound
    (keyError (eventError (StmtIn := Unit) eitherError)) (bound := ⊤) (fun _ => le_top) prover 0
    proverBound
  rw [Nat.cast_zero, zero_mul] at free
  have bound := either_soundness_weighted prover 0 free
  rwa [zero_add] at bound

/-- The history at which the transform reads the first challenge. -/
def firstKey (first : Fin 4) : List (Event eitherSpec Unit) :=
  [.statement (), .message 0 first, .challenge 1]

/-- The history at which the transform reads the second challenge. -/
def secondKey (first second : Fin 4) : List (Event eitherSpec Unit) :=
  firstKey first ++ [.message 2 second, .challenge 3]

/-- With the proof `[first, second]`, the transform asks the oracle at the two
challenge occurrences and passes the guard when either check holds. -/
theorem experiment_either (first second : Fin 4) :
    Typed.fixedExperiment (R := ByLast (Raw eitherSpec Unit))
        (absorb eitherSpec Unit) (validator (guardedVerdict eitherGuarded) ())
        (initial eitherSpec Unit ()) (pure [⟨0, first⟩, ⟨2, second⟩]) =
      answer (firstKey first) >>= fun firstRaw =>
        answer (secondKey first second) >>= fun secondRaw =>
        pure (PIR.Outcome.returned (if decide (parity (firstRaw : Fin 4) = parity first ∨
          (secondRaw : Fin 4) = second) then some () else none), []) :=
  rfl

/-- A prover that sends two guesses without querying is accepted with
probability at least `1 / 2`: the experiment accepts through all four rounds,
below the weighted bound `3 / 4`. -/
theorem either_accepted (first second : Fin 4) :
    2⁻¹ ≤ Pr{let result ← (simulateQ randomOracle (Typed.fixedExperiment
        (R := ByLast (Raw eitherSpec Unit)) (absorb eitherSpec Unit)
        (validator (guardedVerdict eitherGuarded) ()) (initial eitherSpec Unit ())
        (pure [⟨0, first⟩, ⟨2, second⟩]))).run' ∅}[
      Accepted (Accepts (Set.univ : Set Unit)) result.1] := by
  have distinct : secondKey first second ≠ firstKey first := by simp [secondKey, firstKey]
  rw [experiment_either]
  simp only [answer, simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind,
    map_bind, randomOracle.run_eq, QueryCache.empty_apply, QueryCache.cacheQuery_of_ne _ _ distinct,
    simulateQ_pure, StateT.run_pure, map_pure, bind_assoc, pure_bind]
  have firstHalf : Pr{let x ← $ᵗ Fin 4}[parity x = parity first] = 2⁻¹ := by
    have count := SampleableType.prEvent_uniformSample (α := Fin 4)
      (fun x => parity x = parity first)
    rw [Fintype.card_fin, Nat.cast_ofNat] at count
    rw [count, ← half]
    fin_cases first <;> rfl
  have certain : Pr{let _ ← $ᵗ Fin 4}[True] = 1 := by
    simp only [SampleableType.prEvent_uniformSample, Finset.filter_true, Finset.card_univ]
    exact ENNReal.div_self (by simp) (by simp)
  have product := prEvent_bind_bind_and ($ᵗ Fin 4) ($ᵗ Fin 4)
    (fun x : Fin 4 => parity x = parity first) (fun _ : Fin 4 => True)
  rw [firstHalf, certain, mul_one] at product
  have lower := prEvent_mono
    (do let x ← ($ᵗ Fin 4 : ProbComp (Fin 4)); let y ← ($ᵗ Fin 4 : ProbComp (Fin 4)); pure (x, y))
    (fun z => parity z.1 = parity first ∧ True)
    (fun z => Accepted (Accepts (Set.univ : Set Unit)) (PIR.Outcome.returned
      (if decide (parity z.1 = parity first ∨ z.2 = second) = true then some () else none)))
    (fun z holds => by simp [Accepted, Accepts, holds.1])
  simp only [bind_assoc, pure_bind] at lower
  rw [product] at lower
  exact lower

end TestsSecurity.UpstreamImports
