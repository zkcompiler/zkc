module

public import VCVio.CryptoFoundations.SigmaProtocol.ChallengeRestriction
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.EvalDist.Sum

@[expose] public section

/-! Parallel composition of two Σ-protocols with one shared challenge.

The composed prover commits in both components, receives one challenge and
answers it in both; the verifier accepts when both components accept. The
statement and the witness are pairs, so the witnesses are independent: sharing
the challenge does not make them equal.

The premises are stated per property:

* perfect completeness and special soundness of the components compose with no
  further assumption;
* zero knowledge composes from *special* honest-verifier zero knowledge: for every
  fixed challenge, the honest commitment and response are distributed as a
  simulator that is given that challenge. VCVio's `PerfectHVZK` lets each
  simulator choose its own challenge, so two component simulators do not
  directly yield one transcript with a shared challenge. `SpecialHVZK.perfectHVZK`
  gives VCVio's form with the challenge-first simulator;
  `SpecialHVZK.of_perfectHVZK` recovers the per-challenge form from a
  challenge-first simulator over a finite challenge space.
-/

open OracleComp OracleSpec

namespace ZkcSecurity.VCVio.SigmaAnd

/-! ### Special honest-verifier zero knowledge -/

section Special

variable {Stmt Wit Commit State Chal Resp : Type} {rel : Stmt → Wit → Bool}

/-- The honest commitment and response for one fixed challenge. -/
def honestAt (σ : ChallengeVerifyProtocol Stmt Wit Commit State Chal Resp rel) (statement : Stmt)
    (witness : Wit) (challenge : Chal) : ProbComp (Commit × Resp) := do
  let (commitment, state) ← σ.commit statement witness
  let response ← σ.respond statement witness state challenge
  pure (commitment, response)

/-- Special honest-verifier zero knowledge: for every valid statement and
witness and every challenge, the honest commitment and response have exactly
the distribution of `simulate statement challenge`, which receives no witness.
Like VCVio's `PerfectHVZK`, it uses native equality in distribution (`=ᵈ`),
which compares the probabilities of every event. -/
def SpecialHVZK (σ : ChallengeVerifyProtocol Stmt Wit Commit State Chal Resp rel)
    (simulate : Stmt → Chal → ProbComp (Commit × Resp)) : Prop :=
  ∀ statement witness, rel statement witness = true → ∀ challenge,
    honestAt σ statement witness challenge =ᵈ simulate statement challenge

/-- The full transcript simulator that draws a uniform challenge first. -/
def challengeFirst [SampleableType Chal] (simulate : Stmt → Chal → ProbComp (Commit × Resp))
    (statement : Stmt) : ProbComp (Commit × Chal × Resp) := do
  let challenge ← $ᵗ Chal
  let (commitment, response) ← simulate statement challenge
  pure (commitment, challenge, response)

/-- A full transcript with the challenge placed between commitment and response. -/
def withChallenge (challenge : Chal) (result : Commit × Resp) : Commit × Chal × Resp :=
  (result.1, challenge, result.2)

theorem withChallenge_injective (challenge : Chal) :
    Function.Injective (withChallenge (Commit := Commit) (Resp := Resp) challenge) := by
  intro first second same
  simp only [withChallenge, Prod.mk.injEq] at same
  exact Prod.ext same.1 same.2.2

theorem challengeFirst_eq [SampleableType Chal] (simulate : Stmt → Chal → ProbComp (Commit × Resp))
    (statement : Stmt) :
    challengeFirst simulate statement =
      ($ᵗ Chal) >>= fun challenge => withChallenge challenge <$> simulate statement challenge := by
  unfold challengeFirst withChallenge
  simp [monad_norm]

/-- The honest commitment is drawn independently of the uniform challenge that
follows it, so the real transcript can draw the challenge first. -/
theorem evalSPMF_realTranscript [SampleableType Chal]
    (σ : ChallengeVerifyProtocol Stmt Wit Commit State Chal Resp rel) (statement : Stmt)
    (witness : Wit) :
    σ.realTranscript statement witness =ᵈ (($ᵗ Chal) >>= fun challenge =>
        withChallenge challenge <$> honestAt σ statement witness challenge) := by
  unfold ChallengeVerifyProtocol.realTranscript honestAt withChallenge
  simpa only [monad_norm, Function.comp_def] using OracleComp.EvalDistEq.bind_bind_swap
    (σ.commit statement witness) ($ᵗ Chal) (fun committed challenge => do
      let response ← σ.respond statement witness committed.2 challenge
      pure (committed.1, challenge, response))

/-- Special HVZK gives VCVio's perfect HVZK with the challenge-first simulator. -/
theorem SpecialHVZK.perfectHVZK [SampleableType Chal]
    {σ : ChallengeVerifyProtocol Stmt Wit Commit State Chal Resp rel}
    {simulate : Stmt → Chal → ProbComp (Commit × Resp)} (special : SpecialHVZK σ simulate) :
    σ.PerfectHVZK (challengeFirst simulate) := by
  intro statement witness valid
  rw [challengeFirst_eq]
  refine (evalSPMF_realTranscript σ statement witness).trans ?_
  refine EvalDistEq.bind_right _ fun challenge => ?_
  exact EvalDistEq.map (special statement witness valid challenge) _

/-- Over a finite challenge space, a challenge-first transcript assigns each
transcript with challenge `challenge` the uniform weight of that challenge times
the per-challenge probability of its commitment and response. -/
theorem probOutput_challengeFirst [SampleableType Chal] [Fintype Chal]
    (computation : Chal → ProbComp (Commit × Resp)) (challenge : Chal) (result : Commit × Resp) :
    Pr{let x ← (($ᵗ Chal) >>= fun drawn =>
        withChallenge drawn <$> computation drawn)}[x = withChallenge challenge result] =
      (Fintype.card Chal : ENNReal)⁻¹ * Pr{let x ← computation challenge}[x = result] := by
  classical
  rw [OracleComp.prEvent_bind_eq_tsum, tsum_eq_single challenge]
  · rw [SampleableType.prEvent_uniformSample_eq_singleton,
      prEvent_map_injective _ (withChallenge_injective challenge)]
  · intro other different
    rw [prEvent_map]
    simp [withChallenge, different]

/-- Conversely, over a finite challenge space, perfect HVZK with a
challenge-first simulator gives special HVZK: conditioning on each challenge,
which has positive uniform weight, separates the two transcript distributions. -/
theorem SpecialHVZK.of_perfectHVZK [SampleableType Chal] [Fintype Chal]
    {σ : ChallengeVerifyProtocol Stmt Wit Commit State Chal Resp rel}
    {simulate : Stmt → Chal → ProbComp (Commit × Resp)}
    (perfect : σ.PerfectHVZK (challengeFirst simulate)) : SpecialHVZK σ simulate := by
  intro statement witness valid challenge
  classical
  have total := (evalSPMF_realTranscript σ statement witness).symm.trans
    (perfect statement witness valid)
  rw [challengeFirst_eq] at total
  apply EvalDistEq.of_forall_prEvent_eq
  intro event
  have weighted := total.prEvent_eq (fun transcript =>
    transcript.2.1 = challenge ∧ event (transcript.1, transcript.2.2))
  have conditioned (computation : Chal → ProbComp (Commit × Resp)) :
      Pr{let transcript ← (($ᵗ Chal) >>= fun drawn =>
          withChallenge drawn <$> computation drawn)}[
        transcript.2.1 = challenge ∧ event (transcript.1, transcript.2.2)] =
        (Fintype.card Chal : ENNReal)⁻¹ * Pr{let result ← computation challenge}[event result] := by
    rw [OracleComp.prEvent_bind_eq_tsum, tsum_eq_single challenge]
    · rw [SampleableType.prEvent_uniformSample_eq_singleton, prEvent_map]
      simp only [withChallenge, true_and]
    · intro other different
      rw [prEvent_map]
      simp [withChallenge, different]
  rw [conditioned, conditioned] at weighted
  have positive : (Fintype.card Chal : ENNReal)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have finite : (Fintype.card Chal : ENNReal)⁻¹ ≠ ⊤ := by
    simp [Fintype.card_ne_zero]
  exact (ENNReal.mul_right_inj positive finite).mp weighted

end Special

/-! ### The composition -/

variable {Stmt₁ Wit₁ Commit₁ State₁ Resp₁ Stmt₂ Wit₂ Commit₂ State₂ Resp₂ Chal : Type}
  {rel₁ : Stmt₁ → Wit₁ → Bool} {rel₂ : Stmt₂ → Wit₂ → Bool}

/-- Each statement holds with its own witness. -/
def andRelation (rel₁ : Stmt₁ → Wit₁ → Bool) (rel₂ : Stmt₂ → Wit₂ → Bool) :
    Stmt₁ × Stmt₂ → Wit₁ × Wit₂ → Bool :=
  fun statement witness => rel₁ statement.1 witness.1 && rel₂ statement.2 witness.2

/-- Parallel composition with one shared challenge. The extractor runs both
component extractors on the same two challenges. -/
def and (first : SigmaProtocol Stmt₁ Wit₁ Commit₁ State₁ Chal Resp₁ rel₁)
    (second : SigmaProtocol Stmt₂ Wit₂ Commit₂ State₂ Chal Resp₂ rel₂) :
    SigmaProtocol (Stmt₁ × Stmt₂) (Wit₁ × Wit₂) (Commit₁ × Commit₂) (State₁ × State₂) Chal
      (Resp₁ × Resp₂) (andRelation rel₁ rel₂) where
  commit statement witness := do
    let (commitment₁, state₁) ← first.commit statement.1 witness.1
    let (commitment₂, state₂) ← second.commit statement.2 witness.2
    pure ((commitment₁, commitment₂), (state₁, state₂))
  respond statement witness state challenge := do
    let response₁ ← first.respond statement.1 witness.1 state.1 challenge
    let response₂ ← second.respond statement.2 witness.2 state.2 challenge
    pure (response₁, response₂)
  verify statement commitment challenge response :=
    first.verify statement.1 commitment.1 challenge response.1 &&
      second.verify statement.2 commitment.2 challenge response.2
  sim statement := do
    let commitment₁ ← first.sim statement.1
    let commitment₂ ← second.sim statement.2
    pure (commitment₁, commitment₂)
  extract challenge₁ response₁ challenge₂ response₂ := do
    let witness₁ ← first.extract challenge₁ response₁.1 challenge₂ response₂.1
    let witness₂ ← second.extract challenge₁ response₁.2 challenge₂ response₂.2
    pure (witness₁, witness₂)

/-- Both component simulators receive the same challenge. -/
def simulateAnd (simulate₁ : Stmt₁ → Chal → ProbComp (Commit₁ × Resp₁))
    (simulate₂ : Stmt₂ → Chal → ProbComp (Commit₂ × Resp₂)) (statement : Stmt₁ × Stmt₂)
    (challenge : Chal) : ProbComp ((Commit₁ × Commit₂) × (Resp₁ × Resp₂)) := do
  let (commitment₁, response₁) ← simulate₁ statement.1 challenge
  let (commitment₂, response₂) ← simulate₂ statement.2 challenge
  pure ((commitment₁, commitment₂), (response₁, response₂))

variable (first : SigmaProtocol Stmt₁ Wit₁ Commit₁ State₁ Chal Resp₁ rel₁)
  (second : SigmaProtocol Stmt₂ Wit₂ Commit₂ State₂ Chal Resp₂ rel₂)

theorem verify_iff (statement : Stmt₁ × Stmt₂) (commitment : Commit₁ × Commit₂) (challenge : Chal)
    (response : Resp₁ × Resp₂) :
    (and first second).verify statement commitment challenge response = true ↔
      first.verify statement.1 commitment.1 challenge response.1 = true ∧
        second.verify statement.2 commitment.2 challenge response.2 = true := by
  simp [and]

/-- Completeness composes: every supported honest response of each component
is accepted for every challenge. -/
theorem perfectlyComplete [SampleableType Chal] (complete₁ : first.PerfectlyComplete)
    (complete₂ : second.PerfectlyComplete) : (and first second).PerfectlyComplete := by
  intro statement witness valid
  simp only [andRelation, Bool.and_eq_true] at valid
  apply (evalDist_apply_setOf_eq_one_iff_forall_mem_support _ (· = true)).mpr
  intro accepted reached
  simp only [and, mem_support_bind_iff, mem_support_pure_iff] at reached
  obtain ⟨⟨⟨commitment₁, commitment₂⟩, ⟨state₁, state₂⟩⟩, committed, challenge, _,
    ⟨response₁, response₂⟩, responded, rfl⟩ := reached
  obtain ⟨⟨commitment₁', state₁'⟩, committed₁, ⟨commitment₂', state₂'⟩, committed₂, same⟩ := committed
  simp only [Prod.mk.injEq] at same
  obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := same
  obtain ⟨response₁', responded₁, response₂', responded₂, same⟩ := responded
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  simp only [Bool.and_eq_true]
  exact ⟨complete₁.verify _ _ valid.1 _ _ committed₁ challenge _ responded₁,
    complete₂.verify _ _ valid.2 _ _ committed₂ challenge _ responded₂⟩

/-- Special soundness composes: both components see the same two distinct
challenges, so each component extractor returns a witness of its statement. -/
theorem speciallySound (sound₁ : first.SpeciallySound) (sound₂ : second.SpeciallySound) :
    (and first second).SpeciallySound := by
  intro statement commitment challenge₁ challenge₂ response₁ response₂ distinct accepted₁ accepted₂
    witness extracted
  rw [verify_iff] at accepted₁ accepted₂
  simp only [and, mem_support_bind_iff, mem_support_pure_iff] at extracted
  obtain ⟨witness₁, extracted₁, witness₂, extracted₂, rfl⟩ := extracted
  simp only [andRelation, Bool.and_eq_true]
  exact ⟨sound₁ statement.1 commitment.1 challenge₁ challenge₂ response₁.1 response₂.1 distinct
      accepted₁.1 accepted₂.1 witness₁ extracted₁,
    sound₂ statement.2 commitment.2 challenge₁ challenge₂ response₁.2 response₂.2 distinct
      accepted₁.2 accepted₂.2 witness₂ extracted₂⟩

/-- Special HVZK composes under one shared challenge: the second component's
commitment is drawn independently of the first component's response. -/
theorem specialHVZK {simulate₁ : Stmt₁ → Chal → ProbComp (Commit₁ × Resp₁)}
    {simulate₂ : Stmt₂ → Chal → ProbComp (Commit₂ × Resp₂)}
    (special₁ : SpecialHVZK first.toChallengeVerifyProtocol simulate₁)
    (special₂ : SpecialHVZK second.toChallengeVerifyProtocol simulate₂) :
    SpecialHVZK (and first second).toChallengeVerifyProtocol (simulateAnd simulate₁ simulate₂) := by
  intro statement witness valid challenge
  simp only [andRelation, Bool.and_eq_true] at valid
  have separated : honestAt (and first second).toChallengeVerifyProtocol statement witness challenge =ᵈ (honestAt first.toChallengeVerifyProtocol statement.1 witness.1 challenge >>= fun result₁ =>
        honestAt second.toChallengeVerifyProtocol statement.2 witness.2 challenge >>= fun result₂ =>
          pure ((result₁.1, result₂.1), (result₁.2, result₂.2))) := by
    unfold honestAt and
    simp only [bind_assoc, pure_bind]
    refine EvalDistEq.bind_right _ fun committed₁ => ?_
    exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
  refine separated.trans ?_
  unfold simulateAnd
  exact (special₁ statement.1 witness.1 valid.1 challenge).bind fun result₁ =>
    (special₂ statement.2 witness.2 valid.2 challenge).bind fun result₂ => .rfl

end ZkcSecurity.VCVio.SigmaAnd
