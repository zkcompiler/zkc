module

public import ZkcArkLib.Fri.Protocol

@[expose] public section

/-! # `fri::LowDegree` checks are ArkLib's FRI query checks

ArkLib PR #992's query analysis reads a commitment transcript as a `FoldTrace`: the committed
words with their folding challenges, ending at a final word that must lie in its Reed–Solomon
code. `toTrace` builds that trace from the library's committed transcript, on ArkLib domains
whose points are the library's coset points, with the evaluations of the final polynomial as the
final word.

`walk_iff` shows that one query's checks in `fri::LowDegree` accept exactly at the positions
`FoldTrace.accepting` admits: `remainder(position, half)` is ArkLib's folding index map,
`folded_value` is ArkLib's binary fold (`foldWord_k_1_of_sq_roots`), the chain check compares a
word with the previous fold at the same point, and the terminal check compares the final
polynomial with the last fold. `verify_iff` lifts this to all queries, and
`accepts_of_verify` adds the coefficient bound, which places the final word in its code.
-/

namespace ZkcSecurity.ArkLib.Fri

open Domain
open _root_.Fri (FoldTrace)

variable {F : Type} [Field F]

/-- The degree bound of a trace with `R` binary folds ending at degree bound `d`, built the
way `FoldTrace.step` indexes it. -/
def degreeBound : ℕ → ℕ → ℕ
  | 0, d => d
  | R + 1, d => 2 ^ 1 * degreeBound R d

theorem degreeBound_eq (R d : ℕ) : degreeBound R d = 2 ^ R * d := by
  induction R with
  | zero => simp [degreeBound]
  | succ R ih => rw [degreeBound, ih, pow_succ]; ring

theorem degreeBound_pos {d : ℕ} (hd : 0 < d) (R : ℕ) : 0 < degreeBound R d := by
  rw [degreeBound_eq]
  positivity

/-- The ascending coefficient list as a polynomial. -/
noncomputable def toPolynomial : List F → Polynomial F
  | [] => 0
  | coefficient :: rest => Polynomial.C coefficient + Polynomial.X * toPolynomial rest

theorem evaluate_eq (coefficients : List F) (x : F) :
    evaluate coefficients x = (toPolynomial coefficients).eval x := by
  induction coefficients with
  | nil => simp [evaluate, toPolynomial]
  | cons coefficient rest ih =>
      rw [toPolynomial, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_X, ← ih]
      rfl

theorem degree_toPolynomial_lt (coefficients : List F) :
    (toPolynomial coefficients).degree < coefficients.length := by
  induction coefficients with
  | nil => simp [toPolynomial]
  | cons coefficient rest ih =>
      rw [Polynomial.degree_lt_iff_coeff_zero] at ih ⊢
      intro index hindex
      simp only [List.length_cons] at hindex
      obtain ⟨index, rfl⟩ : ∃ previous, index = previous + 1 := ⟨index - 1, by omega⟩
      rw [toPolynomial, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul,
        ih index (by omega)]
      simp

/-- The algebraic trace of a committed transcript on ArkLib domains starting at `D`: the
committed words with their challenges, ending at the final polynomial's evaluations on the last
domain. Its degree bound is that of `R` binary folds ending below `2^t`. -/
def toTrace (t : ℕ) : {m R : ℕ} → (D : SmoothCosetFftDomain m F) → Layers F m R →
    FoldTrace D (degreeBound R (2 ^ t))
  | _, _, D, .final coefficients => .terminal fun j => evaluate coefficients (D j)
  | _, R + 1, D, .fold word beta rest =>
      .step (by omega) (degreeBound_pos (by positivity) _) word beta (toTrace t (D.subdomain 1) rest)

/-- The initial word of the trace of a transcript that folds at least once. -/
@[simp]
theorem toTrace_fold_initial (t : ℕ) {m R : ℕ} (D : SmoothCosetFftDomain (m + 1) F)
    (word : Fin (2 ^ (m + 1)) → F) (beta : F) (rest : Layers F m R) :
    (toTrace t D (.fold word beta rest)).initial = word := rfl

/-- `remainder(position, half)` is ArkLib's folding index map. -/
theorem lowHalf_eq {m : ℕ} (position : Fin (2 ^ (m + 1))) :
    lowHalf position = CosetFftDomainClass.sqFoldMapGen (n := m + 1) (i := 1) position := rfl

omit [Field F] in
/-- `select_half` reads the word at the query position itself. -/
theorem selectHalf_eq {m : ℕ} (word : Fin (2 ^ (m + 1)) → F) (position : Fin (2 ^ (m + 1))) :
    selectHalf (word (lowIndex (lowHalf position))) (word (highIndex (lowHalf position)))
      position.val (2 ^ m) = word position := by
  unfold selectHalf
  split_ifs with h
  · congr 1
    apply Fin.ext
    simp [lowIndex, lowHalf, Nat.mod_eq_of_lt h]
  · congr 1
    apply Fin.ext
    have hlt : position.val < 2 ^ m * 2 := lt_of_lt_of_eq position.isLt (pow_succ 2 m)
    have hmod : position.val % 2 ^ m = position.val - 2 ^ m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    change position.val % 2 ^ m + 2 ^ m = position.val
    omega

/-- Domain points along the folds: if `D` is the size-`2^(m + 1)` coset with shift `shift`, its
first subdomain is the size-`2^m` coset with the squared shift, under a compatible root family. -/
theorem subdomain_point (roots : ℕ → F) {m : ℕ} (D : SmoothCosetFftDomain (m + 1) F)
    (shift : F) (hD : ∀ i : Fin (2 ^ (m + 1)), D i = point roots shift (m + 1) i)
    (hroots : roots (m + 1) ^ 2 = roots m) :
    ∀ j : Fin (2 ^ m), D.subdomain 1 j = point roots (shift * shift) m j := by
  intro j
  rw [subdomain_one_apply D shift (roots (m + 1)) (fun i => hD i) j, hroots]
  rfl

/-- The roots used along `R` folds from log size `m` are compatible. -/
def Compatible (roots : ℕ → F) (m R : ℕ) : Prop :=
  ∀ k, m - R ≤ k → k < m → roots (k + 1) ^ 2 = roots k

theorem Compatible.tail {roots : ℕ → F} {m R : ℕ} (h : Compatible roots (m + 1) (R + 1)) :
    Compatible roots m R :=
  fun k hlow hhigh => h k (by omega) (by omega)

theorem Compatible.head {roots : ℕ → F} {m R : ℕ} (h : Compatible roots (m + 1) (R + 1)) :
    roots (m + 1) ^ 2 = roots m :=
  h m (by omega) (by omega)

/-- Powers of one root form a compatible family: with `roots m = ω ^ 2 ^ (n - m)`, as the
installed KoalaBear convention takes `ω = 1791270792` and `n = 24`, the roots of log order at
most `n` are compatible. -/
theorem compatible_powers (ω : F) (n R : ℕ) : Compatible (fun m => ω ^ 2 ^ (n - m)) n R := by
  intro k _ hk
  simp only [← pow_mul, ← pow_succ]
  congr 2
  omega

/-- The final word of the trace lies in its code when at most `2^t` coefficients were sent. -/
theorem finalInCode_of_bounded (t : ℕ) :
    ∀ {m R : ℕ} (D : SmoothCosetFftDomain m F) (layers : Layers F m R),
      bounded t layers.coefficients = true → (toTrace t D layers).FinalInCode
  | m, _, D, .final coefficients, hbound => by
      have hlength : coefficients.length ≤ 2 ^ t := Nat.lt_succ_iff.mp (of_decide_eq_true hbound)
      simp only [toTrace, FoldTrace.FinalInCode, degreeBound]
      have hdeg : (toPolynomial coefficients).degree < (2 ^ t : ℕ) :=
        lt_of_lt_of_le (degree_toPolynomial_lt coefficients) (by exact_mod_cast hlength)
      have hcode := ReedSolomon.evalOnPoints_mem_code_of_degree_lt
        (α := (D : Fin (2 ^ m) ↪ F)) hdeg
      convert hcode using 1
      funext j
      simp [ReedSolomon.evalOnPoints, evaluate_eq]
  | _, _, D, .fold _ _ rest, hbound => by
      simp only [toTrace, FoldTrace.FinalInCode]
      exact finalInCode_of_bounded t (D.subdomain 1) rest hbound

/-- The value kept at the first round of a query is the initial word at its position. -/
theorem firstValue_eq {m R : ℕ} (word : Fin (2 ^ (m + 1)) → F) (beta : F) (rest : Layers F m R)
    (position : Fin (2 ^ (m + 1))) :
    firstValue (.fold word beta rest) position = word position := by
  simp only [firstValue]
  exact selectHalf_eq word position

variable [DecidableEq F]

/-- `fold_value` with the prepared inverses is ArkLib's binary fold at the paired point. -/
theorem foldedValue_eq (roots : ℕ → F) {m : ℕ} (D : SmoothCosetFftDomain (m + 1) F) (shift : F)
    (hD : ∀ i : Fin (2 ^ (m + 1)), D i = point roots shift (m + 1) i)
    (word : Fin (2 ^ (m + 1)) → F) (beta : F) (low : Fin (2 ^ m)) :
    foldedValue roots (word (lowIndex low)) (word (highIndex low)) shift (m + 1) low.val beta =
      _root_.ProximityGap.foldWord D word 1 beta low := by
  have hpair := pair_sq D low
  have hne : lowIndex low ≠ highIndex low := by
    intro h
    have := congrArg Fin.val h
    simp [lowIndex, highIndex] at this
  rw [_root_.ProximityGap.foldWord_k_1_of_sq_roots hne hpair.1 hpair.2]
  have hx : point roots shift (m + 1) low.val = D (lowIndex low) := (hD (lowIndex low)).symm
  simp only [foldedValue, foldValue, hx, one_add_one_eq_two, div_eq_mul_inv, mul_inv]
  ring

/-- One folding round of a query: the chain check at the query position, then the next round at
`remainder(position, half)` expecting ArkLib's fold of the pair. -/
theorem walk_fold (roots : ℕ → F) {m R : ℕ} (D : SmoothCosetFftDomain (m + 1) F) (shift : F)
    (hD : ∀ i : Fin (2 ^ (m + 1)), D i = point roots shift (m + 1) i)
    (word : Fin (2 ^ (m + 1)) → F) (beta : F) (rest : Layers F m R)
    (position : Fin (2 ^ (m + 1))) (expected : F) (round : ℕ) :
    walk roots (.fold word beta rest) shift position expected round =
      (chain round (word position) expected &&
        walk roots rest (shift * shift) (lowHalf position)
          (_root_.ProximityGap.foldWord D word 1 beta (lowHalf position)) (round + 1)) := by
  simp only [walk, selectHalf_eq, foldedValue_eq roots D shift hD]

/-- A position is accepting at a folding step when ArkLib's fold of its pair is the next word at
`remainder(position, half)`, which is accepting in turn. -/
theorem mem_accepting_fold (t : ℕ) {m R : ℕ} (D : SmoothCosetFftDomain (m + 1) F)
    (word : Fin (2 ^ (m + 1)) → F) (beta : F) (rest : Layers F m R)
    (position : Fin (2 ^ (m + 1))) :
    position ∈ (toTrace t D (.fold word beta rest)).accepting ↔
      _root_.ProximityGap.foldWord D word 1 beta (lowHalf position) =
          (toTrace t (D.subdomain 1) rest).initial (lowHalf position) ∧
        lowHalf position ∈ (toTrace t (D.subdomain 1) rest).accepting := by
  simp only [toTrace, FoldTrace.accepting]
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rfl

/-- Checks after the first round: a query accepts from `position` with expected value
`expected` exactly when the current word there is `expected` and `position` is accepting. -/
theorem walk_iff (roots : ℕ → F) (t : ℕ) :
    ∀ {m R : ℕ} (layers : Layers F m R) (D : SmoothCosetFftDomain m F) (shift : F),
      (∀ i : Fin (2 ^ m), D i = point roots shift m i) → Compatible roots m R →
      ∀ (position : Fin (2 ^ m)) (expected : F) (round : ℕ), round ≠ 0 →
        (walk roots layers shift position expected round = true ↔
          (toTrace t D layers).initial position = expected ∧
            position ∈ (toTrace t D layers).accepting)
  | _, _, .final coefficients, D, shift, hD, _, position, expected, round, _ => by
      simp only [walk, toTrace, terminal, FoldTrace.initial, FoldTrace.accepting, hD,
        Finset.mem_univ, and_true]
      exact decide_eq_true_iff
  | m + 1, R + 1, .fold word beta rest, D, shift, hD, hcompat, position, expected, round,
      hround => by
      have hrest := walk_iff roots t rest (D.subdomain 1) (shift * shift)
        (subdomain_point roots D shift hD hcompat.head) hcompat.tail
      rw [walk_fold roots D shift hD, mem_accepting_fold, toTrace_fold_initial]
      simp only [Bool.and_eq_true, chain, hround, ↓reduceIte, decide_eq_true_eq,
        hrest _ _ (round + 1) (Nat.succ_ne_zero _)]
      constructor <;> (rintro ⟨hfirst, hnext, hmem⟩; exact ⟨hfirst, hnext.symm, hmem⟩)

/-- The first round has no chain check: a query accepts from round zero exactly when its
position is accepting. -/
theorem walk_first_iff (roots : ℕ → F) (t : ℕ) {m R : ℕ} (D : SmoothCosetFftDomain (m + 1) F)
    (shift : F) (hD : ∀ i : Fin (2 ^ (m + 1)), D i = point roots shift (m + 1) i)
    (hcompat : Compatible roots (m + 1) (R + 1)) (word : Fin (2 ^ (m + 1)) → F) (beta : F)
    (rest : Layers F m R) (position : Fin (2 ^ (m + 1))) (expected : F) :
    walk roots (.fold word beta rest) shift position expected 0 = true ↔
      position ∈ (toTrace t D (.fold word beta rest)).accepting := by
  have hrest := walk_iff roots t rest (D.subdomain 1) (shift * shift)
    (subdomain_point roots D shift hD hcompat.head) hcompat.tail
  rw [walk_fold roots D shift hD, mem_accepting_fold]
  simp only [Bool.and_eq_true, chain, ↓reduceIte, true_and, hrest _ _ 1 one_ne_zero]
  constructor <;> (rintro ⟨hnext, hmem⟩; exact ⟨hnext.symm, hmem⟩)

/-- The library verifier accepts exactly when the coefficient bound holds and every query
position is accepting in the trace. -/
theorem verify_iff (roots : ℕ → F) (t : ℕ) {n R s : ℕ} (D : SmoothCosetFftDomain (n + 1) F)
    (shift : F) (hD : ∀ i : Fin (2 ^ (n + 1)), D i = point roots shift (n + 1) i)
    (hcompat : Compatible roots (n + 1) (R + 1)) (layers : Layers F (n + 1) (R + 1))
    (positions : Fin s → Fin (2 ^ (n + 1))) :
    verify roots t shift layers positions = true ↔
      bounded t layers.coefficients = true ∧
        ∀ query, positions query ∈ (toTrace t D layers).accepting := by
  cases layers with
  | fold word beta rest =>
      simp only [verify, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
        walk_first_iff roots t D shift hD hcompat word beta rest]

/-- Acceptance by the library verifier is acceptance of the trace in ArkLib's sense. -/
theorem accepts_of_verify (roots : ℕ → F) (t : ℕ) {n R s : ℕ} (D : SmoothCosetFftDomain (n + 1) F)
    (shift : F) (hD : ∀ i : Fin (2 ^ (n + 1)), D i = point roots shift (n + 1) i)
    (hcompat : Compatible roots (n + 1) (R + 1)) (layers : Layers F (n + 1) (R + 1))
    (positions : Fin s → Fin (2 ^ (n + 1)))
    (haccept : verify roots t shift layers positions = true) :
    (toTrace t D layers).Accepts positions := by
  rw [verify_iff roots t D shift hD hcompat] at haccept
  exact ⟨finalInCode_of_bounded t D layers haccept.1, haccept.2⟩

/-- Honestly folded layers on the domains starting at `D`: each committed word after the first,
and the final polynomial's evaluations, are ArkLib's fold of the previous word. -/
def Honest (t : ℕ) : {m R : ℕ} → SmoothCosetFftDomain m F → Layers F m R → Prop
  | _, _, _, .final _ => True
  | _, _, D, .fold word beta rest =>
      (toTrace t (D.subdomain 1) rest).initial = _root_.ProximityGap.foldWord D word 1 beta ∧
        Honest t (D.subdomain 1) rest

/-- Every position is accepting in the trace of honestly folded layers. -/
theorem mem_accepting_of_honest (t : ℕ) :
    ∀ {m R : ℕ} (D : SmoothCosetFftDomain m F) (layers : Layers F m R), Honest t D layers →
      ∀ position, position ∈ (toTrace t D layers).accepting
  | _, _, _, .final _, _, _ => by simp [toTrace, FoldTrace.accepting]
  | _, _, D, .fold word beta rest, hhonest, position => by
      obtain ⟨hfold, hrest⟩ := hhonest
      rw [mem_accepting_fold, hfold]
      exact ⟨rfl, mem_accepting_of_honest t (D.subdomain 1) rest hrest _⟩

/-- The checks are consistent with honest folding: the library verifier accepts honestly folded
layers at every query position when at most `2^t` coefficients were sent. -/
theorem verify_of_honest (roots : ℕ → F) (t : ℕ) {n R s : ℕ}
    (D : SmoothCosetFftDomain (n + 1) F) (shift : F)
    (hD : ∀ i : Fin (2 ^ (n + 1)), D i = point roots shift (n + 1) i)
    (hcompat : Compatible roots (n + 1) (R + 1)) (layers : Layers F (n + 1) (R + 1))
    (hhonest : Honest t D layers) (hbound : bounded t layers.coefficients = true)
    (positions : Fin s → Fin (2 ^ (n + 1))) :
    verify roots t shift layers positions = true :=
  (verify_iff roots t D shift hD hcompat layers positions).mpr
    ⟨hbound, fun _ => mem_accepting_of_honest t D layers hhonest _⟩

end ZkcSecurity.ArkLib.Fri
