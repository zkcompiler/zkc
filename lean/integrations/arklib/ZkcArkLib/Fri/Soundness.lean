module

public import ZkcArkLib.Fri.Correspondence

@[expose] public section

/-! # Round-by-round soundness of `fri::LowDegree` at the ideal interpretation

The certificate has the persistent bad-event form of ArkLib PR #992's FRI analysis, which
follows Garreta–Mohnblatt–Wagner, *A Simplified Round-by-round Soundness Proof of FRI*
(ePrint 2025/1993). A state of the interaction is doomed when the committed initial word is at
relative distance at least `δ` from the Reed–Solomon code of degree below `2^(t + R)` on the
initial coset and no earlier challenge has escaped. Prover messages (committed words, the final
coefficients, openings) leave this state unchanged, since escape events depend only on the word
committed before a challenge and on that challenge. The challenge sites and their errors are:

* folding round `r`, one uniform field challenge: it escapes when the word committed before it
  loses the ability to lift large agreement sets through the fold
  (`FoldingAgreementFailure`); the error `foldError r` bounds this for every committed word;
* the query block, one compound challenge of all `s` positions: from a doomed state it escapes
  only by acceptance, with probability at most `(1 - min θ δ)^s` (`FoldTrace.query_soundness`).

`RoundByRound` states these obligations. `roundByRound` derives them from the proximity premise
`FoldingProximity`, the mutual correlated agreement of the line generator on each folded code,
kept as a named hypothesis. `RoundByRound.soundness` bounds the probability that the verifier
accepts while the committed initial word is far, against every adaptive and randomized prover, by
the sum of the site errors; `soundness` composes the two.
-/

namespace ZkcSecurity.ArkLib.Fri

open Domain OracleComp ProximityGap CoreDefinitions
open _root_.Fri (FoldTrace FoldingAgreementFailure)

variable {F : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]

/-- The proximity premise: along the folds starting at `D`, the line generator has mutual
correlated agreement on each folded Reed–Solomon code at radius `θ`, with error `error r` at
folding round `r`. The code after the fold has degree below `2^(t + R)` when `R` folds follow. -/
def FoldingProximity (t : ℕ) (θ : ℝ) :
    {m : ℕ} → SmoothCosetFftDomain m F → (R : ℕ) → (ℕ → ENNReal) → Prop
  | 0, _, _, _ => True
  | _ + 1, _, 0, _ => True
  | m + 1, D, R + 1, error =>
      mcaError (univariatePowersGenerator F (2 ^ 1 - 1))
          (ReedSolomon.code (D.subdomain 1 : Fin (2 ^ (m + 1 - 1)) ↪ F) (degreeBound R (2 ^ t))) θ ≤
        error 0 ∧
      FoldingProximity t θ (D.subdomain 1) R fun round => error (round + 1)

/-- The folding sites of the certificate: at every round and for every committed word, a fresh
uniform challenge escapes with probability at most the round's error. -/
def FoldingEscapes (t : ℕ) (θ : ℝ) :
    {m : ℕ} → SmoothCosetFftDomain m F → (R : ℕ) → (ℕ → ENNReal) → Prop
  | 0, _, _, _ => True
  | _ + 1, _, 0, _ => True
  | m + 1, D, R + 1, error =>
      (∀ word : Fin (2 ^ (m + 1)) → F,
        Pr{let beta ← $ᵗ F}[FoldingAgreementFailure D word 1 (degreeBound R (2 ^ t)) θ beta] ≤
          error 0) ∧
      FoldingEscapes t θ (D.subdomain 1) R fun round => error (round + 1)

/-- Relative distance at least `δ` from every codeword of degree below `d` on `D`. -/
def Far {m : ℕ} (D : SmoothCosetFftDomain m F) (d : ℕ) (δ : ℝ) (word : Fin (2 ^ m) → F) : Prop :=
  ∀ u ∈ ReedSolomon.code (D : Fin (2 ^ m) ↪ F) d, δ ≤ (Code.relHammingDist word u : ℝ)

/-- The round-by-round soundness certificate of `fri::LowDegree` at the ideal interpretation,
with explicit errors per challenge site: `fold` for the folding rounds, `query` for the compound
query challenge. -/
structure RoundByRound (roots : ℕ → F) (t : ℕ) (shift : F) {n : ℕ} (R s : ℕ)
    (D : SmoothCosetFftDomain n F) (θ δ : ℝ) (foldError : ℕ → ENNReal) (queryError : ENNReal) :
    Prop where
  fold : FoldingEscapes t θ D R foldError
  query : ∀ layers : Layers F n R, (toTrace t D layers).Safe θ →
    Far D (degreeBound R (2 ^ t)) δ (toTrace t D layers).initial →
    Pr{let positions ← $ᵗ (Fin s → Fin (2 ^ n))}[verify roots t shift layers positions = true] ≤
      queryError

/-- ArkLib's folding bound turns the proximity premise into the folding sites' obligations. -/
theorem foldingEscapes_of_proximity (t : ℕ) (θ : ℝ) :
    ∀ {m : ℕ} (D : SmoothCosetFftDomain m F) (R : ℕ) (error : ℕ → ENNReal),
      FoldingProximity t θ D R error → FoldingEscapes t θ D R error
  | 0, _, _, _, _ => by simp [FoldingEscapes]
  | _ + 1, _, 0, _, _ => by simp [FoldingEscapes]
  | m + 1, D, R + 1, error, hproximity => by
      obtain ⟨head, tail⟩ := hproximity
      exact ⟨fun word => (_root_.Fri.foldingAgreementFailure_prob_le_powers D word
          (degreeBound_pos (by positivity) R) θ).trans head,
        foldingEscapes_of_proximity t θ (D.subdomain 1) R _ tail⟩

omit [Fintype F] [SampleableType F] in
/-- The query obligation for any verifier whose acceptance implies acceptance of a safe trace in
ArkLib's sense, with positions drawn in another encoding related to natural-order indices by an
equivalence (for example a bit-reversed layout). The uniform draw of encoded positions is the
uniform draw of natural positions. -/
theorem query_escape_le_of_accepts {m d s : ℕ} {D : SmoothCosetFftDomain m F}
    (trace : FoldTrace D d) (θ δ : ℝ) (hsafe : trace.Safe θ)
    (hfar : Far D d δ trace.initial) {Positions : Type} [SampleableType Positions]
    (encoding : Positions ≃ (Fin s → Fin (2 ^ m))) (accepts : Positions → Prop)
    (hsound : ∀ positions, accepts positions → trace.Accepts (encoding positions)) :
    Pr{let positions ← $ᵗ Positions}[accepts positions] ≤ ENNReal.ofReal (1 - min θ δ) ^ s := by
  calc Pr{let positions ← $ᵗ Positions}[accepts positions]
      ≤ Pr{let positions ← $ᵗ Positions}[trace.Accepts (encoding positions)] :=
        prEvent_mono _ _ _ hsound
    _ = Pr{let natural ← $ᵗ (Fin s → Fin (2 ^ m))}[trace.Accepts natural] :=
        SampleableType.prEvent_uniformSample_equiv encoding _
    _ ≤ ENNReal.ofReal (1 - min θ δ) ^ s := trace.query_soundness θ δ s hsafe hfar

omit [Fintype F] [SampleableType F] in
/-- The query obligation: on a safe trace whose initial word is far, the verifier accepts the
compound query draw with probability at most `(1 - min θ δ)^s`. -/
theorem query_escape_le (roots : ℕ → F) (t : ℕ) {n R : ℕ} (s : ℕ)
    (D : SmoothCosetFftDomain (n + 1) F) (shift : F)
    (hD : ∀ i : Fin (2 ^ (n + 1)), D i = point roots shift (n + 1) i)
    (hcompat : Compatible roots (n + 1) (R + 1)) (θ δ : ℝ) (layers : Layers F (n + 1) (R + 1))
    (hsafe : (toTrace t D layers).Safe θ)
    (hfar : Far D (degreeBound (R + 1) (2 ^ t)) δ (toTrace t D layers).initial) :
    Pr{let positions ← $ᵗ (Fin s → Fin (2 ^ (n + 1)))}[
      verify roots t shift layers positions = true] ≤ ENNReal.ofReal (1 - min θ δ) ^ s :=
  (prEvent_mono _ _ _ fun positions h =>
      accepts_of_verify roots t D shift hD hcompat layers positions h).trans
    ((toTrace t D layers).query_soundness θ δ s hsafe hfar)

/-- The certificate, from the proximity premise. -/
theorem roundByRound (roots : ℕ → F) (t : ℕ) {n R : ℕ} (s : ℕ)
    (D : SmoothCosetFftDomain (n + 1) F) (shift : F)
    (hD : ∀ i : Fin (2 ^ (n + 1)), D i = point roots shift (n + 1) i)
    (hcompat : Compatible roots (n + 1) (R + 1)) (θ δ : ℝ) (foldError : ℕ → ENNReal)
    (hproximity : FoldingProximity t θ D (R + 1) foldError) :
    RoundByRound roots t shift (R + 1) s D θ δ foldError (ENNReal.ofReal (1 - min θ δ) ^ s) where
  fold := foldingEscapes_of_proximity t θ D (R + 1) foldError hproximity
  query layers hsafe hfar := query_escape_le roots t s D shift hD hcompat θ δ layers hsafe hfar

omit [Fintype F] in
/-- The folding rounds escape with probability at most the sum of their errors, against any
strategy, from any committed word. -/
theorem commit_escape_le (t : ℕ) (θ : ℝ) {m R : ℕ} (strategy : Strategy F m R) :
    ∀ (D : SmoothCosetFftDomain m F) (error : ℕ → ENNReal), FoldingEscapes t θ D R error →
      ∀ word : Fin (2 ^ m) → F,
        Pr{let layers ← commit strategy word}[¬ (toTrace t D layers).Safe θ] ≤
          ∑ round ∈ Finset.range R, error round := by
  induction strategy with
  | @last m final =>
      intro D error hescapes word
      obtain ⟨head, _⟩ := hescapes
      simp only [commit, bind_assoc, pure_bind, toTrace, FoldTrace.Safe, and_true, not_not,
        Finset.sum_range_one]
      exact head word
  | @fold m R next rest ih =>
      intro D error hescapes word
      obtain ⟨head, tail⟩ := hescapes
      simp only [commit]
      refine (prEvent_bind_le_prEvent_add _ _
        (fun beta => FoldingAgreementFailure D word 1 (degreeBound (R + 1) (2 ^ t)) θ beta) _
        (ε := ∑ round ∈ Finset.range (R + 1), error (round + 1))
        fun beta hgood => ?_).trans ?_
      · simp only [bind_assoc, pure_bind, toTrace, FoldTrace.Safe, hgood, not_false_eq_true,
          true_and]
        exact ih beta (D.subdomain 1) _ tail (next beta)
      · calc _ ≤ error 0 + ∑ round ∈ Finset.range (R + 1), error (round + 1) :=
              add_le_add (head word) le_rfl
          _ = ∑ round ∈ Finset.range (R + 2), error round := by
              rw [Finset.sum_range_succ' _ (R + 1)]
              ring

omit [Fintype F] in
/-- The certificate bounds acceptance with a far committed initial word, for every adaptive and
randomized prover: at most the folding errors plus the query error. -/
theorem RoundByRound.soundness {roots : ℕ → F} {t : ℕ} {shift : F} {n R : ℕ} {s : ℕ}
    {D : SmoothCosetFftDomain n F} {θ δ : ℝ} {foldError : ℕ → ENNReal} {queryError : ENNReal}
    (certificate : RoundByRound roots t shift R s D θ δ foldError queryError)
    (prover : ProbComp ((Fin (2 ^ n) → F) × Strategy F n R)) :
    Pr{let result ← experiment roots t shift s prover}[
      result.2 = true ∧ Far D (degreeBound R (2 ^ t)) δ (toTrace t D result.1).initial] ≤
      (∑ round ∈ Finset.range R, foldError round) + queryError := by
  unfold experiment
  refine prEvent_bind_le_of_forall_le _ _ _ fun start => ?_
  refine (prEvent_bind_le_prEvent_add _ _ (fun layers => ¬ (toTrace t D layers).Safe θ) _
    (ε := queryError) fun layers hsafe => ?_).trans
      (add_le_add (commit_escape_le t θ _ D foldError certificate.fold _) le_rfl)
  simp only [not_not] at hsafe
  simp only [bind_assoc, pure_bind]
  rw [prEvent_positions]
  by_cases hfar : Far D (degreeBound R (2 ^ t)) δ (toTrace t D layers).initial
  · simp only [hfar, and_true]
    exact certificate.query layers hsafe hfar
  · simp [hfar]

/-- Round-by-round soundness of `fri::LowDegree` at the ideal interpretation: from the proximity
premise, every adaptive and randomized prover makes the verifier accept with a committed initial
word at relative distance at least `δ` from the code with probability at most
`∑ r < R, foldError r + (1 - min θ δ)^s`. -/
theorem soundness (roots : ℕ → F) (t : ℕ) {n R : ℕ} (s : ℕ)
    (D : SmoothCosetFftDomain (n + 1) F) (shift : F)
    (hD : ∀ i : Fin (2 ^ (n + 1)), D i = point roots shift (n + 1) i)
    (hcompat : Compatible roots (n + 1) (R + 1)) (θ δ : ℝ) (foldError : ℕ → ENNReal)
    (hproximity : FoldingProximity t θ D (R + 1) foldError)
    (prover : ProbComp ((Fin (2 ^ (n + 1)) → F) × Strategy F (n + 1) (R + 1))) :
    Pr{let result ← experiment roots t shift s prover}[
      result.2 = true ∧ Far D (degreeBound (R + 1) (2 ^ t)) δ (toTrace t D result.1).initial] ≤
      (∑ round ∈ Finset.range (R + 1), foldError round) + ENNReal.ofReal (1 - min θ δ) ^ s :=
  (roundByRound roots t s D shift hD hcompat θ δ foldError hproximity).soundness prover

end ZkcSecurity.ArkLib.Fri
