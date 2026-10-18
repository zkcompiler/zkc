import ZkcSecurity.FiatShamir.Upstream

/-! Controls for importing ArkLib's worst-case round-by-round soundness.

A two-round ArkLib protocol: the prover sends a guess in `Fin 4`, the verifier
draws a challenge in `Fin 4` and accepts when the challenge equals the guess.
Every input is false (`language = ∅`). The state function is false before the
challenge and, at the full transcript, says whether the challenge equals the
guess (`stateFunction`); the worst-case bound at the challenge round is `1 / 4`
(`worstCase`). The import gives the process form's typed certificate, and the
typed engine bounds the transform's acceptance against a prover with `queries`
queries by `(queries + 2) / 4` (`guess_soundness`), for any input the prover
chooses after its queries too (`guess_adaptive_soundness`). -/

namespace TestsSecurity.UpstreamImports
open OracleComp OracleSpec ProtocolSpec
open ZkcSecurity.FiatShamir ZkcSecurity.FiatShamir.Typed ZkcSecurity.FiatShamir.Upstream
open scoped ENNReal NNReal

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

def init : ProbComp Unit := pure ()

def impl : QueryImpl []ₒ (StateT Unit ProbComp) := fun query => nomatch query

/-- The guess of a transcript that has it. -/
def guessAt {round : Fin 3} (transcript : Transcript round pSpec) (inside : 0 < round.val) : Fin 4 :=
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
    exact prEvent_verdict_eq_zero init impl pureForm statement transcript (by simp [pureForm, different])

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

/-- The transform of the process form accepts with probability at most
`(queries + 2) / 4` against every prover with `queries` queries. -/
theorem guess_soundness
    (prover : OracleComp (OracleSpec.ofFn (ByLast (Raw pSpec Unit))) (List (Message pSpec)))
    (queries : ℕ) (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (Typed.fixedExperiment (absorb pSpec Unit)
        (validator pureForm.verify ()) (initial pSpec Unit ()) prover)).run' ∅}[
      Accepted (· ∈ ({true} : Set Bool)) result.1] ≤ (queries + 2) * 4⁻¹ := by
  have bound := worstCase_soundness init impl pureForm sound (bound := 4⁻¹)
    (fun _ => by simp) (statement := ()) (by simp) prover queries proverBound
  refine (le_of_eq ?_).trans (bound.trans (le_of_eq ?_))
  · rfl
  · norm_num

theorem guess_adaptive_soundness
    (prover : OracleComp (OracleSpec.ofFn (ByLast (Raw pSpec Unit))) (Unit × List (Message pSpec)))
    (queries : ℕ) (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle (Typed.experiment (absorb pSpec Unit)
        (validator pureForm.verify) (initial pSpec Unit) prover)).run' ∅}[
      result.1 ∉ (∅ : Set Unit) ∧ Accepted (· ∈ ({true} : Set Bool)) result.2.1] ≤
      (queries + 2) * 4⁻¹ := by
  have bound := worstCase_adaptive_soundness init impl pureForm sound (bound := 4⁻¹)
    (fun _ => by simp) prover queries proverBound
  refine (le_of_eq ?_).trans (bound.trans (le_of_eq ?_))
  · rfl
  · norm_num

end TestsSecurity.UpstreamImports
