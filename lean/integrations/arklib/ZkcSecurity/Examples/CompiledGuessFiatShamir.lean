module

public import ZkcSecurity.FiatShamir.Realization
public import ZkcExamples.Construction.GuessProof

@[expose] public section

/-! Fiat–Shamir soundness of a compiled Entry from an imported ArkLib verifier.

The subject is the compiler's constructed validator for the guessing fixture's
`example::Proof` Entry (`ZkcExamples.Construction.GuessProof`): the prover sends
a guess, the verifier draws a field challenge, delivers it and accepts when the
guess plus the public offset is the challenge. Every offset is false: a prover
cannot predict the challenge.

The round-by-round argument is stated and proved in ArkLib's framework rather
than in the typed engine's certificate language. `verifier` is an ArkLib
verifier for the same protocol over the field `F`, written here, pure, with the
empty input language; `sound` is its worst-case round-by-round soundness
(`rbrSoundnessWorstCase`) with error `1 / |F|` at the challenge round, from a
state function (`Verifier.StateFunction`) that is false before the challenge and,
at the full transcript, says whether the guess plus the offset is the challenge.
Three proved links carry that certificate to the compiled verifier:

* Import. `Upstream.ofWorstCase` turns `sound` into a typed certificate of the
  ArkLib verifier's process form.
* Realization. The compiled Entry's original validator receives the guess,
  queries the challenge, delivers it and returns the same verdict, so it realizes
  the process form (`realizes`): the receive realizes the message round, the
  query realizes the challenge round with the identity bijection, and the
  delivery realizes no round. `Upstream.Realizes.certificate` gives the
  participant certificate (`certificate`), each challenge occurrence charged
  `1 / |F|`.
* Construction. For every challenge function the compiled verifier is the
  Fiat–Shamir transform of that original validator
  (`GuessProof.compiled_transform`).

`soundness` bounds the probability that the compiled verifier accepts, for a
fixed offset and initial transcript, in a random oracle on all typed histories,
against a prover with `Q` queries, by `(Q + 1) / |F|`. The bound is attained at
zero queries: a prover that sends a guess without querying is accepted with
probability exactly `1 / |F|` (`guess_accepted`).
-/

set_option autoImplicit false

namespace ZkcSecurity.Examples.CompiledGuessFiatShamir
open OracleComp OracleSpec ProtocolSpec
open Zkc.Source Zkc.Construction
open ZkcExamples.Construction
open ZkcSecurity.FiatShamir ZkcSecurity.FiatShamir.Upstream
open scoped ENNReal NNReal

section Imported
variable (F : Type)

/-- A guess from the prover, then a challenge, both field elements. -/
def pSpec : ProtocolSpec 2 := ⟨![.P_to_V, .V_to_P], fun _ => F⟩

variable {F} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]

instance challengeSampleable : ∀ index, SampleableType ((pSpec F).Challenge index) :=
  fun _ => inferInstanceAs (SampleableType F)

/-- A round's entry of a full transcript. -/
def entry (transcript : FullTranscript (pSpec F)) (round : Fin 2) : F := transcript round

/-- An entry of a partial transcript. -/
def entryUpTo {round : Fin 3} (transcript : Transcript round (pSpec F)) (index : Fin round.val) :
    F :=
  transcript index

/-- The ArkLib verifier: accept when the guess plus the offset is the challenge. -/
def verifier : Verifier []ₒ F Bool (pSpec F) where
  verify offset transcript := pure (decide (entry transcript 0 + offset = entry transcript 1))

def pureForm : (verifier (F := F)).PureForm :=
  ⟨fun offset transcript => decide (entry transcript 0 + offset = entry transcript 1),
    fun _ _ => rfl⟩

/-- The pure verifier as a guarded one whose guard always passes. -/
abbrev guarded : (verifier (F := F)).GuardedForm := pureForm.toGuardedForm

def init : ProbComp Unit := pure ()

def impl : QueryImpl []ₒ (StateT Unit ProbComp) := fun query => nomatch query

/-- False before the challenge; at the full transcript, whether the guess plus
the offset is the challenge. -/
def state (round : Fin 3) (offset : F) (transcript : Transcript round (pSpec F)) : Prop :=
  if full : round.val = 2 then
    entryUpTo transcript ⟨0, by omega⟩ + offset = entryUpTo transcript ⟨1, by omega⟩
  else False

def stateFunction : (verifier (F := F)).StateFunction init impl ∅ {true} where
  toFun := state
  toFun_empty offset := by simp [state]
  toFun_next round message offset transcript _ value := by
    have first : round = 0 := by
      fin_cases round
      · rfl
      · simp [pSpec] at message
    subst first
    simp [state]
  toFun_full offset transcript false_ := by
    have different : ¬ (entry transcript 0 + offset = entry transcript 1) := by
      simp only [state, Fin.val_last, ↓reduceDIte] at false_
      exact false_
    exact prEvent_verdict_eq_zero init impl guarded offset transcript
      (by simp [guardedVerdict, Verifier.PureForm.toGuardedForm, Accepts, pureForm, different])

/-- The error of the challenge round: one over the field size. -/
noncomputable def error : (pSpec F).ChallengeIdx → ℝ≥0 := fun _ => (Fintype.card F : ℝ≥0)⁻¹

theorem worstCase : ∀ offset ∉ (∅ : Set F), ∀ index : (pSpec F).ChallengeIdx,
    ∀ transcript : Transcript index.1.castSucc (pSpec F),
      Pr{let challenge ← $ᵗ ((pSpec F).Challenge index)}[
        ¬ stateFunction index.1.castSucc offset transcript ∧
          stateFunction index.1.succ offset (transcript.concat challenge)] ≤ error index := by
  rintro offset - ⟨round, challengeRound⟩ transcript
  have second : round = 1 := by
    fin_cases round
    · simp [pSpec] at challengeRound
    · rfl
  subst second
  refine (prEvent_mono _ _ (fun challenge : F =>
    challenge = entryUpTo transcript ⟨0, Nat.zero_lt_one⟩ + offset)
      fun challenge escaping => ?_).trans ?_
  · have holds : entryUpTo transcript ⟨0, Nat.zero_lt_one⟩ + offset = challenge := escaping.2
    exact holds.symm
  · refine (SampleableType.prEvent_uniformSample_eq_singleton (α := F) _).trans_le (le_of_eq ?_)
    rw [error, ENNReal.coe_inv (by simp [Fintype.card_ne_zero]), ENNReal.coe_natCast]

/-- Worst-case round-by-round soundness of the ArkLib verifier. -/
theorem sound : (verifier (F := F)).rbrSoundnessWorstCase init impl ∅ {true} error :=
  ⟨stateFunction, worstCase⟩

end Imported

section Compiled
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Each challenge occurrence of the participant interface is charged one over
the field size. -/
noncomputable def participantError : Zkc.Construction.Event F G → ℝ≥0∞ :=
  fun _ => ((Fintype.card F : ℝ≥0)⁻¹ : ℝ≥0)

omit [SampleableType F] in
/-- The compiled Entry's original validator realizes the process form of the
ArkLib verifier: the guess is the message round, the challenge the challenge
round, the delivery no round, and the returned verdicts are equal. -/
theorem realizes (offset : F) (handle : Nat) :
    Realizes GuessProof.context (error (F := F)) participantError Eq
      (validator (guardedVerdict guarded) offset) (GuessProof.verifier (G := G) offset handle) := by
  rw [GuessProof.verifier_correspondence]
  refine Realizes.receive rfl (fun value => value) fun guess => ?_
  refine Realizes.query rfl (Equiv.refl F) le_rfl fun challenge => ?_
  exact Realizes.send (Realizes.done rfl)

/-- The participant certificate of the compiled Entry's original validator,
imported from the ArkLib verifier's worst-case round-by-round soundness. -/
noncomputable def certificate :
    Typed.Certificate (interface (F := F) (G := G) GuessProof.context id) (· = some true)
      participantError :=
  Realizes.certificate GuessProof.context (error (F := F)) participantError Eq
    (fun _ _ related accepted => by
      subst related
      subst accepted
      rfl)
    (ofWorstCase init impl guarded sound)

theorem verifier_doomed (offset : F) (handle : Nat) :
    (certificate (F := F) (G := G)).doomed (GuessProof.verifier offset handle) :=
  ⟨_, ofWorstCase_doomed init impl guarded sound (statement := offset) (by simp),
    realizes offset handle⟩

omit [Fintype F] [SampleableType F] in
theorem verifier_queryBound (offset : F) (handle : Nat) :
    QueryBound (GuessProof.verifier (G := G) offset handle) 1 := by
  rw [GuessProof.verifier_correspondence]
  exact fun _ => ⟨Nat.one_pos, fun _ => trivial⟩

/-- The compiled verifier: the ideal meaning of the exported validator with the
challenge function `challenge`, on the offset, from the initial transcript
`initial`, read through the acceptance output the policy selects. -/
def compiledVerifier {m : Type → Type} [Monad m] (challenge : History F G → m F) (offset : F)
    (initial : History F G) (proof : Proof F G) : m (PIR.Outcome (Option Bool) × Proof F G) :=
  (fun result => (mapOutcome GuessProof.acceptance result.1, result.2)) <$>
    ideal GuessProof.context challenge GuessProof.table GuessProof.participant.returned
      GuessProof.participant.instructions ((GuessProof.inputs offset).map .data ++
        [.transcript initial]) proof

/-- Fiat–Shamir soundness of the compiled guessing verifier from the imported
ArkLib certificate. The prover is any oracle computation on the transcript oracle
making at most `queries` queries on every path; the offset and the initial
transcript are fixed. The compiled verifier accepts with probability at most
`(queries + 1) / |F|`. -/
theorem soundness (offset : F) (initial : History F G)
    (prover : OracleComp (FieldOracle F G) (Proof F G)) (queries : ℕ)
    (proverBound : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle
        (prover >>= compiledVerifier historyQuery offset initial)).run' ∅}[
      Accepted (· = some true) result.1] ≤ (queries + 1) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
  have image := acceptance_le_of_image GuessProof.context (GuessProof.verifier offset 0) initial
    (compiledVerifier historyQuery offset initial) id
    (fun proof => by
      rw [compiledVerifier, GuessProof.compiled_transform historyQuery offset 0 initial proof,
        id_map])
    (· = some true) (· = some true) (fun _ accepted => accepted) prover
  rw [experiment_eq] at image
  have bound := Typed.soundness (certificate (F := F) (G := G))
    (bound := ((Fintype.card F : ℝ≥0)⁻¹ : ℝ≥0))
    (fun _ => le_rfl) (GuessProof.verifier offset 0) (verifier_doomed offset 0) 1
    (QueryBound.typed GuessProof.context id _ 1 (verifier_queryBound offset 0)) initial prover
    queries proverBound
  rw [ENNReal.coe_inv (by simp [Fintype.card_ne_zero]), ENNReal.coe_natCast,
    Nat.cast_one] at bound
  exact image.trans bound

omit [Fintype F] [SampleableType F] in
/-- With the proof `[guess]`, the compiled verifier asks the challenge function
once, at the initial transcript followed by the guess message and the challenge
occurrence, and accepts when the guess plus the offset is the challenge. -/
theorem compiledVerifier_guess (offset guess : F) (initial : History F G) :
    compiledVerifier historyQuery offset initial [.field GuessProof.fieldDomain guess] =
      historyQuery (initial ++ [.message (GuessProof.context.message GuessProof.guessSite 0
          GuessProof.context.validator) (.field GuessProof.fieldDomain guess),
        .challenge (GuessProof.context.query GuessProof.challengeSite
          (.draw GuessProof.fieldDomain))]) >>= fun challenge =>
        pure (.returned (some (decide (guess + offset = challenge))), []) := by
  rw [compiledVerifier, GuessProof.compiled_transform historyQuery offset 0 initial,
    GuessProof.verifier_correspondence]
  simp [GuessProof.experiment, transform, Payload.value, Payload.ofValue]

/-- A prover that sends a guess without querying is accepted by the compiled
verifier with probability exactly `1 / |F|`: `soundness` is attained at zero
queries, so the compiled experiment accepts and the imported bound is tight
there. -/
theorem guess_accepted (offset guess : F) (initial : History F G) :
    Pr{let result ← (simulateQ randomOracle
        ((pure [.field GuessProof.fieldDomain guess] : OracleComp (FieldOracle F G) (Proof F G)) >>=
          compiledVerifier historyQuery offset initial)).run' ∅}[
      Accepted (· = some true) result.1] = (Fintype.card F : ℝ≥0∞)⁻¹ := by
  rw [pure_bind, compiledVerifier_guess, historyQuery, simulateQ_bind, simulateQ_spec_query,
    StateT.run'_eq, StateT.run_bind, map_bind, randomOracle.run_eq]
  simp only [Accepted, QueryCache.empty_apply, simulateQ_pure, StateT.run_pure, map_pure,
    bind_assoc, pure_bind, Option.some.injEq, decide_eq_true_eq]
  exact (prEvent_congr _ _ (fun challenge : F => challenge = guess + offset)
    fun _ => eq_comm).trans (SampleableType.prEvent_uniformSample_eq_singleton (α := F) _)

end Compiled

end ZkcSecurity.Examples.CompiledGuessFiatShamir
