module

public import ZkcArkLib.Fri.Correspondence

@[expose] public section

/-! # Completeness of `fri::LowDegree` on codewords

The honest prover folds its word with each challenge (`coset::fold`, line 115) and, after the last
fold, sends the coefficients of the folded word's interpolant (`interpolate_coefficients`, lines
118–119). With `R + 1` folds of a codeword of degree below `2^(t + R + 1)`, each fold is a codeword
of half the degree (ArkLib's `foldWord_mem_code_of_mem_code`), so the last fold is the evaluation
of a polynomial of degree below `2^t`, whose `2^t` coefficients meet the bound. `honest_commit` shows that every run
of the honest commit phase on such a codeword gives honestly folded layers with bounded final
coefficients; `honest_accepted` concludes that the verifier then accepts every query position, for
every folding challenge.

The honest final message here lists exactly `2^t` coefficients, padding with zeros. The verifier
reads the final message only through its length, which must be at most `2^t`, and the polynomial
it defines, so every list of at most `2^t` coefficients of the same polynomial is accepted alike.
-/

namespace ZkcSecurity.ArkLib.Fri

open Domain OracleComp
open _root_.Fri (FoldTrace)
open _root_.ProximityGap (foldWord)

variable {F : Type} [Field F]

/-- The first `2^t` coefficients of `p`, ascending. -/
noncomputable def coefficientsBelow (t : ℕ) (p : Polynomial F) : List F :=
  (List.range (2 ^ t)).map p.coeff

theorem coeff_toPolynomial : ∀ (coefficients : List F) (index : ℕ),
    (toPolynomial coefficients).coeff index = coefficients.getD index 0
  | [], index => by simp [toPolynomial]
  | coefficient :: rest, 0 => by simp [toPolynomial]
  | coefficient :: rest, index + 1 => by
      simp [toPolynomial, Polynomial.coeff_X_mul, coeff_toPolynomial rest index]

theorem toPolynomial_coefficientsBelow {t : ℕ} {p : Polynomial F} (degree : p.natDegree < 2 ^ t) :
    toPolynomial (coefficientsBelow t p) = p := by
  ext index
  rw [coeff_toPolynomial, coefficientsBelow, List.getD_eq_getElem?_getD]
  by_cases below : index < 2 ^ t
  · simp [below]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp [below]

theorem bounded_coefficientsBelow (t : ℕ) (p : Polynomial F) :
    bounded t (coefficientsBelow t p) = true := by
  simp [bounded, coefficientsBelow]

/-- The honest final message for a word on `D`: the first `2^t` coefficients of a polynomial of
degree below `2^t` that the word evaluates, when there is one. -/
noncomputable def finalCoefficients (t : ℕ) {m : ℕ} (D : SmoothCosetFftDomain m F)
    (word : Fin (2 ^ m) → F) : List F := by
  classical
  exact if found : ∃ p : Polynomial F, p.natDegree < 2 ^ t ∧ ∀ j, p.eval (D j) = word j then
    coefficientsBelow t (Classical.choose found)
  else []

/-- On a codeword of degree below `2^t`, the honest final message evaluates to the word and meets
the bound. -/
theorem finalCoefficients_spec (t : ℕ) {m : ℕ} (D : SmoothCosetFftDomain m F)
    (word : Fin (2 ^ m) → F) (codeword : word ∈ ReedSolomon.code (D : Fin (2 ^ m) ↪ F) (2 ^ t)) :
    (fun j => evaluate (finalCoefficients t D word) (D j)) = word ∧
      bounded t (finalCoefficients t D word) = true := by
  classical
  obtain ⟨p, degree, rfl⟩ := ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero.mp codeword
  have found : ∃ q : Polynomial F, q.natDegree < 2 ^ t ∧
      ∀ j, q.eval (D j) = ReedSolomon.evalOnPoints (D : Fin (2 ^ m) ↪ F) p j :=
    ⟨p, degree, fun j => rfl⟩
  unfold finalCoefficients
  split
  · rename_i exists_found
    have chosen := Classical.choose_spec exists_found
    refine ⟨?_, bounded_coefficientsBelow t _⟩
    funext j
    rw [evaluate_eq, toPolynomial_coefficientsBelow chosen.1, chosen.2]
  · exact absurd found ‹_›

variable [DecidableEq F]

/-- Folding a codeword of degree below `2^(t + R + 1)` gives a codeword of degree below
`2^(t + R)` on the first subdomain. -/
theorem fold_mem_code (t : ℕ) {m R : ℕ} (rate : t + R ≤ m) (D : SmoothCosetFftDomain (m + 1) F)
    (word : Fin (2 ^ (m + 1)) → F)
    (codeword : word ∈ ReedSolomon.code (D : Fin (2 ^ (m + 1)) ↪ F) (degreeBound (R + 1) (2 ^ t)))
    (beta : F) :
    foldWord D word 1 beta ∈
      ReedSolomon.code (D.subdomain 1 : Fin (2 ^ (m + 1 - 1)) ↪ F) (degreeBound R (2 ^ t)) := by
  have context : _root_.ProximityGap.FoldingContext 1 (t + R + 1) (m + 1) :=
    { k_ge_1 := le_rfl, k_le_d := by omega, d_le_n := by omega }
  rw [degreeBound_eq, ← pow_add, show R + 1 + t = t + R + 1 by omega] at codeword
  have folded := _root_.ProximityGap.foldWord_mem_code_of_mem_code (k := 1) (α := beta) codeword
  rw [degreeBound_eq, ← pow_add, show R + t = t + R + 1 - 1 by omega]
  exact folded

/-- The honest prover on `D` with `R + 1` folds: commit ArkLib's fold of the current word, and
after the last fold send the honest final message for the folded word. -/
noncomputable def honest (t : ℕ) : {m R : ℕ} → R ≤ m → SmoothCosetFftDomain (m + 1) F →
    (Fin (2 ^ (m + 1)) → F) → Strategy F (m + 1) (R + 1)
  | _, 0, _, D, word => .last fun beta => finalCoefficients t (D.subdomain 1) (foldWord D word 1 beta)
  | _ + 1, _ + 1, folds, D, word => .fold (fun beta => foldWord D word 1 beta)
      (fun beta => honest t (by omega) (D.subdomain 1) (foldWord D word 1 beta))
  | 0, _ + 1, folds, _, _ => absurd folds (by omega)

variable [SampleableType F]

/-- Every run of the honest commit phase on a codeword of degree below `2^(t + R + 1)` gives
honestly folded layers that start at the codeword and whose final coefficients meet the bound. -/
theorem honest_commit (t : ℕ) :
    ∀ {m R : ℕ} (rate : t + R ≤ m) (D : SmoothCosetFftDomain (m + 1) F)
      (word : Fin (2 ^ (m + 1)) → F),
      word ∈ ReedSolomon.code (D : Fin (2 ^ (m + 1)) ↪ F) (degreeBound (R + 1) (2 ^ t)) →
      ∀ layers ∈ support (commit (honest (R := R) t (by omega) D word) word),
        (toTrace t D layers).initial = word ∧ Honest t D layers ∧
          bounded t layers.coefficients = true
  | m, 0, rate, D, word, codeword, layers, member => by
      simp only [honest, commit, support_bind, support_uniformSample, Set.mem_univ,
        support_pure, Set.iUnion_true, Set.mem_iUnion, Set.mem_singleton_iff] at member
      obtain ⟨beta, rfl⟩ := member
      have final := finalCoefficients_spec t (D.subdomain 1) (foldWord D word 1 beta)
        (by simpa [degreeBound] using fold_mem_code t rate D word codeword beta)
      exact ⟨rfl, ⟨by simpa [toTrace, FoldTrace.initial] using final.1, trivial⟩, final.2⟩
  | 0, R + 1, rate, _, _, _, _, _ => absurd rate (by omega)
  | m + 1, R + 1, rate, D, word, codeword, layers, member => by
      simp only [honest, commit, support_bind, support_uniformSample, Set.mem_univ,
        support_pure, Set.iUnion_true, Set.mem_iUnion, Set.mem_singleton_iff] at member
      obtain ⟨beta, rest, inner, rfl⟩ := member
      obtain ⟨initial, honestRest, boundedRest⟩ := honest_commit t (by omega) (D.subdomain 1)
        (foldWord D word 1 beta) (fold_mem_code t rate D word codeword beta) rest inner
      exact ⟨rfl, ⟨initial, honestRest⟩, boundedRest⟩

/-- Completeness on codewords: the verifier accepts every query position of every run of the
honest commit phase on a codeword of degree below `2^(t + R + 1)`. -/
theorem honest_accepted (roots : ℕ → F) (t : ℕ) {n R s : ℕ} (rate : t + R ≤ n)
    (D : SmoothCosetFftDomain (n + 1) F) (shift : F)
    (hD : ∀ i : Fin (2 ^ (n + 1)), D i = point roots shift (n + 1) i)
    (hcompat : Compatible roots (n + 1) (R + 1)) (word : Fin (2 ^ (n + 1)) → F)
    (codeword : word ∈ ReedSolomon.code (D : Fin (2 ^ (n + 1)) ↪ F) (degreeBound (R + 1) (2 ^ t)))
    (layers : Layers F (n + 1) (R + 1))
    (member : layers ∈ support (commit (honest (R := R) t (by omega) D word) word))
    (positions : Fin s → Fin (2 ^ (n + 1))) :
    verify roots t shift layers positions = true := by
  obtain ⟨-, honestLayers, boundedLayers⟩ := honest_commit t rate D word codeword layers member
  exact verify_of_honest roots t D shift hD hcompat layers honestLayers boundedLayers positions

end ZkcSecurity.ArkLib.Fri
