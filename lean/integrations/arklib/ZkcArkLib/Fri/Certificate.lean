module

public import ZkcArkLib.Fri.UniqueDecoding
public import Zkc.Semantics.Execution

@[expose] public section

/-! # The FRI certificate over the verifier's residual processes

`Soundness` states the certificate of `fri::LowDegree` over committed transcripts. This module
states it over the residual processes of the verifier, after the first commitment, in the shape
of a typed Fiat–Shamir certificate: a doomed set of residuals that received prover messages
cannot leave and that contains no accepting result, with an error for every query site, bounding
the probability that a uniform answer of the site's sort leaves the set.

The verifier runs over the operations `Operation`: a folding challenge (a field element), a
committed word (read as the vector it commits to), the final coefficient vector, and the query
block (all positions together). `afterCommit word` is the verifier once the initial word is
committed. The doomed residuals (`Doomed`) are those reached while the initial word is at
relative distance at least `δ` from the code and no folding challenge has escaped. Each carries
what its future transcripts will satisfy: their initial word is far, and their completed rounds
are safe exactly when the remaining rounds are. Doomed residuals before a folding challenge also
carry the remaining folding sites' obligations.

`certificate` proves every local obligation (`Step`):

* a doomed result rejects;
* prover messages leave the set unchanged;
* folding challenge `r` leaves it with probability at most `foldError r`;
* the query block leaves it with probability at most `(1 - min θ δ)^s`, under the uniform law of
  `Fin s → Fin (2^n)`.

`afterCommit_doomed` places the verifier after a far initial word in the set. A Fiat–Shamir
consumer reads the initial word as the statement and its commitment as the initial transcript; it
answers each query site with its own decoding, and the uniform law here is the ideal law of the
site's sort.
-/

namespace ZkcSecurity.ArkLib.Fri

open Domain OracleComp
open _root_.Fri (FoldTrace FoldingAgreementFailure)

/-- The verifier's operations after the first commitment. -/
inductive Operation where
  /-- The folding challenge of a round. -/
  | fold (round : ℕ)
  /-- The committed word of a round, of size `2 ^ logSize`. -/
  | word (round logSize : ℕ)
  /-- The final coefficient vector. -/
  | final
  /-- The query block: all `count` positions in `[0, 2 ^ logSize)` together. -/
  | positions (logSize count : ℕ)
  deriving DecidableEq

/-- The reply types of the operations. -/
def Operation.Reply (F : Type) : Operation → Type
  | .fold _ => F
  | .word _ logSize => Fin (2 ^ logSize) → F
  | .final => List F
  | .positions logSize count => Fin count → Fin (2 ^ logSize)

/-- The operation signature of the verifier. -/
def operations (F : Type) : PIR.Signature := ⟨Operation, Operation.Reply F⟩

/-- The error of each query site: `foldError r` for the folding challenge of round `r` and
`queryError` for the query block. Prover messages have no error. -/
def siteError (foldError : ℕ → ENNReal) (queryError : ENNReal) : Operation → ENNReal
  | .fold round => foldError round
  | .positions _ _ => queryError
  | _ => 0

section Certificate

variable {F : Type} [Field F] [DecidableEq F]

/-- The local obligations of a doomed set over the verifier's operations, with every query
answered by a uniform value of its sort and the verifier accepting exactly on `true`. -/
def Step [SampleableType F] (doomed : PIR.Proc (operations F) Bool → Prop)
    (error : Operation → ENNReal) : PIR.Proc (operations F) Bool → Prop
  | .done accepted => accepted = false
  | .halt _ => True
  | .call (.fold round) next =>
      Pr{let beta ← $ᵗ F}[¬ doomed (next beta)] ≤ error (.fold round)
  | .call (.positions logSize count) next =>
      Pr{let positions ← $ᵗ (Fin count → Fin (2 ^ logSize))}[¬ doomed (next positions)] ≤
        error (.positions logSize count)
  | .call (.word _ _) next => ∀ value, doomed (next value)
  | .call .final next => ∀ value, doomed (next value)

/-- A round-by-round certificate over the verifier's residual processes: a doomed set whose every
member meets its local obligation. -/
structure Certificate [SampleableType F] (error : Operation → ENNReal) where
  doomed : PIR.Proc (operations F) Bool → Prop
  step : ∀ process, doomed process → Step doomed error process

variable (roots : ℕ → F) (t : ℕ) (shift : F) {n R₀ : ℕ} (s : ℕ)

/-- After the final coefficients: the coefficient bound (lines 120–121), then the query block and
the checks. -/
def queryPhase (layers : Layers F n R₀) : PIR.Proc (operations F) Bool :=
  .call (.positions n s) fun positions => .done (verify roots t shift layers positions)

/-- Receiving the final coefficient vector, which completes the transcript `assemble`. -/
def finalPhase (assemble : List F → Layers F n R₀) : PIR.Proc (operations F) Bool :=
  .call .final fun coefficients =>
    if bounded t coefficients then queryPhase roots t shift s (assemble coefficients)
    else .halt .reject

/-- The commit phase from the committed word of round `round`, of size `2^(m + 1)` with `R + 1`
folds left: the folding challenge, then the next committed word, or the final coefficients after
the last fold. `wrap` completes the transcript from the remaining rounds. -/
def foldPhase : {m R : ℕ} → ℕ → (Layers F (m + 1) (R + 1) → Layers F n R₀) →
    (Fin (2 ^ (m + 1)) → F) → PIR.Proc (operations F) Bool
  | _, 0, round, wrap, word => .call (.fold round) fun beta =>
      finalPhase roots t shift s fun coefficients => wrap (.fold word beta (.final coefficients))
  | m + 1, _ + 1, round, wrap, word => .call (.fold round) fun beta =>
      .call (.word (round + 1) (m + 1)) fun next =>
        foldPhase (round + 1) (fun rest => wrap (.fold word beta rest)) next
  | 0, _ + 1, round, _, _ => .call (.fold round) fun _ => .halt .refused

/-- The verifier once the initial word, of size `2^(m + 1)` with `R + 1` folds, is committed. -/
def afterCommit {m R : ℕ} (word : Fin (2 ^ (m + 1)) → F) : PIR.Proc (operations F) Bool :=
  foldPhase (n := m + 1) (R₀ := R + 1) roots t shift s 0 id word

variable [SampleableType F]

/-- The doomed residuals: the initial word of every completion is far, completed rounds are safe
exactly when the remaining rounds are, and the remaining folding sites meet their errors. -/
inductive Doomed (D : SmoothCosetFftDomain n F) (θ δ : ℝ) (error : ℕ → ENNReal) :
    PIR.Proc (operations F) Bool → Prop
  | halt (stop : PIR.Stop) : Doomed D θ δ error (.halt stop)
  | rejected : Doomed D θ δ error (.done false)
  | fold {m R : ℕ} (round : ℕ) (domain : SmoothCosetFftDomain (m + 1) F)
      (wrap : Layers F (m + 1) (R + 1) → Layers F n R₀) (word : Fin (2 ^ (m + 1)) → F)
      (far : ∀ beta rest,
        Far D (degreeBound R₀ (2 ^ t)) δ (toTrace t D (wrap (.fold word beta rest))).initial)
      (safe : ∀ beta rest, (toTrace t D (wrap (.fold word beta rest))).Safe θ ↔
        (toTrace t domain (.fold word beta rest)).Safe θ)
      (escapes : FoldingEscapes t θ domain (R + 1) fun later => error (round + later)) :
      Doomed D θ δ error (foldPhase roots t shift s round wrap word)
  | word {m R : ℕ} (round : ℕ) (domain : SmoothCosetFftDomain (m + 1) F)
      (wrap : Layers F (m + 1) (R + 1) → Layers F n R₀)
      (far : ∀ word beta rest,
        Far D (degreeBound R₀ (2 ^ t)) δ (toTrace t D (wrap (.fold word beta rest))).initial)
      (safe : ∀ word beta rest, (toTrace t D (wrap (.fold word beta rest))).Safe θ ↔
        (toTrace t domain (.fold word beta rest)).Safe θ)
      (escapes : FoldingEscapes t θ domain (R + 1) fun later => error (round + later)) :
      Doomed D θ δ error (.call (.word round (m + 1)) fun next =>
        foldPhase roots t shift s round wrap next)
  | final (assemble : List F → Layers F n R₀)
      (far : ∀ coefficients,
        Far D (degreeBound R₀ (2 ^ t)) δ (toTrace t D (assemble coefficients)).initial)
      (safe : ∀ coefficients, (toTrace t D (assemble coefficients)).Safe θ) :
      Doomed D θ δ error (finalPhase roots t shift s assemble)
  | positions (layers : Layers F n R₀)
      (far : Far D (degreeBound R₀ (2 ^ t)) δ (toTrace t D layers).initial)
      (safe : (toTrace t D layers).Safe θ) :
      Doomed D θ δ error (queryPhase roots t shift s layers)

variable {roots t shift s}

omit [SampleableType F] in
theorem foldPhase_last {m : ℕ} (round : ℕ) (wrap : Layers F (m + 1) 1 → Layers F n R₀)
    (word : Fin (2 ^ (m + 1)) → F) :
    foldPhase roots t shift s round wrap word = .call (.fold round) fun beta =>
      finalPhase roots t shift s fun coefficients => wrap (.fold word beta (.final coefficients)) := by
  simp only [foldPhase]

omit [SampleableType F] in
theorem foldPhase_next {m R : ℕ} (round : ℕ)
    (wrap : Layers F (m + 1 + 1) (R + 1 + 1) → Layers F n R₀) (word : Fin (2 ^ (m + 1 + 1)) → F) :
    foldPhase roots t shift s round wrap word = .call (.fold round) fun beta =>
      .call (.word (round + 1) (m + 1)) fun next =>
        foldPhase roots t shift s (round + 1) (fun rest => wrap (.fold word beta rest)) next := by
  simp only [foldPhase]

omit [SampleableType F] in
theorem foldPhase_exhausted {R : ℕ} (round : ℕ) (wrap : Layers F 1 (R + 1 + 1) → Layers F n R₀)
    (word : Fin (2 ^ 1) → F) :
    foldPhase roots t shift s round wrap word = .call (.fold round) fun _ => .halt .refused := by
  simp only [foldPhase]

/-- Without an escape, a folding challenge leaves the residual doomed. -/
theorem doomed_after_fold {N K : ℕ} {D : SmoothCosetFftDomain (N + 1) F} {θ δ : ℝ}
    {error : ℕ → ENNReal} {m R : ℕ} (round : ℕ) (domain : SmoothCosetFftDomain (m + 1) F)
    (wrap : Layers F (m + 1) (R + 1) → Layers F (N + 1) (K + 1)) (word : Fin (2 ^ (m + 1)) → F)
    (far : ∀ beta rest,
      Far D (degreeBound (K + 1) (2 ^ t)) δ (toTrace t D (wrap (.fold word beta rest))).initial)
    (safe : ∀ beta rest, (toTrace t D (wrap (.fold word beta rest))).Safe θ ↔
      (toTrace t domain (.fold word beta rest)).Safe θ)
    (escapes : FoldingEscapes t θ domain (R + 1) fun later => error (round + later)) (beta : F)
    (stays : ¬ FoldingAgreementFailure domain word 1 (degreeBound R (2 ^ t)) θ beta) :
    ∃ next, foldPhase roots t shift s round wrap word = .call (.fold round) next ∧
      Doomed (R₀ := K + 1) roots t shift s D θ δ error (next beta) := by
  cases R with
  | zero =>
      refine ⟨fun beta => finalPhase roots t shift s fun coefficients =>
          wrap (.fold word beta (.final coefficients)), foldPhase_last round wrap word,
        Doomed.final _ (fun coefficients => far beta (.final coefficients))
          (fun coefficients => (safe beta (.final coefficients)).mpr ?_)⟩
      simp only [toTrace, FoldTrace.Safe, and_true]
      exact stays
  | succ R =>
      cases m with
      | zero => exact ⟨fun _ => .halt .refused, foldPhase_exhausted round wrap word, Doomed.halt _⟩
      | succ m =>
          have shifted : (fun later => error (round + 1 + later)) =
              fun later => (fun later => error (round + later)) (later + 1) := by
            funext later
            congr 1
            omega
          obtain ⟨_, tail⟩ := escapes
          refine ⟨fun beta => .call (.word (round + 1) (m + 1)) fun next =>
              foldPhase roots t shift s (round + 1) (fun rest => wrap (.fold word beta rest)) next,
            foldPhase_next round wrap word,
            Doomed.word (round + 1) (domain.subdomain 1)
              (fun rest => wrap (.fold word beta rest))
              (fun next later rest => far beta (.fold next later rest))
              (fun next later rest => (safe beta (.fold next later rest)).trans ?_)
              (by rw [shifted]; exact tail)⟩
          simp only [toTrace, FoldTrace.Safe]
          exact ⟨fun inside => inside.2, fun inside => ⟨stays, inside⟩⟩

/-- The local obligations of every doomed residual: `Doomed` is a round-by-round certificate with
the folding errors `error` and the query block error `(1 - min θ δ)^s`. -/
theorem certificate {N K : ℕ} (D : SmoothCosetFftDomain (N + 1) F)
    (hD : ∀ i : Fin (2 ^ (N + 1)), D i = point roots shift (N + 1) i)
    (hcompat : Compatible roots (N + 1) (K + 1)) (θ δ : ℝ) (error : ℕ → ENNReal) :
    ∀ process, Doomed (R₀ := K + 1) roots t shift s D θ δ error process →
      Step (Doomed (R₀ := K + 1) roots t shift s D θ δ error)
        (siteError error (ENNReal.ofReal (1 - min θ δ) ^ s)) process := by
  intro process doomed
  cases doomed with
  | halt stop => trivial
  | rejected => rfl
  | @fold m R round domain wrap word far safe escapes =>
      have bound : Pr{let beta ← $ᵗ F}[
          FoldingAgreementFailure domain word 1 (degreeBound R (2 ^ t)) θ beta] ≤ error round := by
        cases R with
        | zero =>
            obtain ⟨head, _⟩ := escapes
            simpa using head word
        | succ R =>
            cases m with
            | zero =>
                obtain ⟨head, _⟩ := escapes
                simpa using head word
            | succ m =>
                obtain ⟨head, _⟩ := escapes
                simpa using head word
      obtain ⟨next, unfolded, -⟩ :
          ∃ next, foldPhase roots t shift s round wrap word = .call (.fold round) next ∧ True := by
        cases R with
        | zero => exact ⟨_, foldPhase_last round wrap word, trivial⟩
        | succ R => cases m with
          | zero => exact ⟨_, foldPhase_exhausted round wrap word, trivial⟩
          | succ m => exact ⟨_, foldPhase_next round wrap word, trivial⟩
      rw [unfolded]
      refine (prEvent_mono _ _ _ fun beta outside => ?_).trans bound
      by_contra stays
      obtain ⟨next', unfolded', doomed⟩ :=
        doomed_after_fold round domain wrap word far safe escapes beta stays
      rw [unfolded] at unfolded'
      cases unfolded'
      exact outside doomed
  | @word m R round domain wrap far safe escapes =>
      exact fun next => Doomed.fold round domain wrap next (far next) (safe next) escapes
  | final assemble far safe =>
      intro coefficients
      change Doomed (R₀ := K + 1) roots t shift s D θ δ error
        (if bounded t coefficients then queryPhase roots t shift s (assemble coefficients)
          else .halt .reject)
      split
      · exact Doomed.positions _ (far coefficients) (safe coefficients)
      · exact Doomed.halt _
  | positions layers far safe =>
      refine (prEvent_mono _ _ (fun positions => verify roots t shift layers positions = true)
        fun positions outside => ?_).trans
          (query_escape_le roots t s D shift hD hcompat θ δ layers safe far)
      cases accepted : verify roots t shift layers positions
      · simp only [accepted] at outside
        exact absurd Doomed.rejected outside
      · rfl

/-- The verifier after a far initial word is doomed, given the folding sites' obligations. -/
theorem afterCommit_doomed {N K : ℕ} (D : SmoothCosetFftDomain (N + 1) F) (θ δ : ℝ)
    (error : ℕ → ENNReal) (escapes : FoldingEscapes t θ D (K + 1) error)
    (word : Fin (2 ^ (N + 1)) → F) (far : Far D (degreeBound (K + 1) (2 ^ t)) δ word) :
    Doomed (R₀ := K + 1) roots t shift s D θ δ error (afterCommit (R := K) roots t shift s word) :=
  Doomed.fold 0 D id word (fun _ _ => far) (fun _ _ => Iff.rfl) (by simpa using escapes)

/-- The certificate as a structure. -/
def doomedCertificate {N K : ℕ} (D : SmoothCosetFftDomain (N + 1) F)
    (hD : ∀ i : Fin (2 ^ (N + 1)), D i = point roots shift (N + 1) i)
    (hcompat : Compatible roots (N + 1) (K + 1)) (θ δ : ℝ) (error : ℕ → ENNReal) :
    Certificate (F := F) (siteError error (ENNReal.ofReal (1 - min θ δ) ^ s)) where
  doomed := Doomed (n := N + 1) (R₀ := K + 1) roots t shift s D θ δ error
  step := certificate D hD hcompat θ δ error

/-- The verifier after a far initial word is doomed, from the proximity premise. -/
theorem afterCommit_doomed_of_proximity [Fintype F] {N K : ℕ} (D : SmoothCosetFftDomain (N + 1) F)
    (θ δ : ℝ) (error : ℕ → ENNReal) (proximity : FoldingProximity t θ D (K + 1) error)
    (word : Fin (2 ^ (N + 1)) → F) (far : Far D (degreeBound (K + 1) (2 ^ t)) δ word) :
    Doomed (R₀ := K + 1) roots t shift s D θ δ error (afterCommit (R := K) roots t shift s word) :=
  afterCommit_doomed D θ δ error (foldingEscapes_of_proximity t θ D (K + 1) error proximity) word far

/-- In the unique-decoding regime, the verifier after a far initial word is doomed with the
folding errors `uniqueDecodingError F (N + 1)`: folding round `r` errs at most
`2^(N - r) / |F|`. -/
theorem afterCommit_doomed_uniqueDecoding [Fintype F] {N K : ℕ}
    (D : SmoothCosetFftDomain (N + 1) F) (θ : NNReal) (positive : 0 < θ)
    (size : degreeBound (K + 1) (2 ^ t) ≤ 2 ^ (N + 1))
    (radius : θ ≤ ((1 : NNReal) - (degreeBound (K + 1) (2 ^ t) : NNReal) /
      (2 ^ (N + 1) : NNReal)) / 2) (δ : ℝ)
    (word : Fin (2 ^ (N + 1)) → F) (far : Far D (degreeBound (K + 1) (2 ^ t)) δ word) :
    Doomed (R₀ := K + 1) roots t shift s D θ δ (uniqueDecodingError F (N + 1))
      (afterCommit (R := K) roots t shift s word) :=
  afterCommit_doomed_of_proximity D θ δ _
    (foldingProximity_uniqueDecoding t θ positive D (K + 1) size radius) word far

end Certificate

end ZkcSecurity.ArkLib.Fri
