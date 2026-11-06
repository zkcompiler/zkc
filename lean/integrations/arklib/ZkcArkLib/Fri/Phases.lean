module

public import ZkcArkLib.Fri.SourceCalculations
public import Zkc.Semantics.Execution

/-!
# Mathematical boundaries of binary FRI phases

This companion uses the existing `Layers`; it does not interpret source syntax. Words in
different layers are arbitrary. `path` follows Check's direct selected read and virtual fold,
and `firstPath` peels the first fold exactly as Check does. The exact transmitted coefficient
length is stronger than the historical `bounded` guard. Acceptance is transferred only in
that direction. Numerical failure, source frames, role masks and handle association are
separate obligations of the source connection.
-/

@[expose] public section

set_option autoImplicit false

namespace ZkcSecurity.ArkLib.Fri.Phases

open Zkc.Source.Structured

variable {F : Type} [Field F] [DecidableEq F]

/-- The coefficient list on the wire, before normalization, has exactly this length. -/
def exactCoefficients (t : ℕ) (cs : List F) : Bool := decide (cs.length = 2 ^ t)

/-- Check after its peeled first fold: read the selected layer value, compare it with the
previous virtual fold, then read the next virtual fold at the reduced position. -/
def path (roots : ℕ → F) : {m R : ℕ} → Layers F m R → F → Fin (2 ^ m) → F → Bool
  | m, _, .final cs, shift, position, expected =>
      decide (terminal roots cs shift m position = expected)
  | m + 1, _, .fold word beta rest, shift, position, expected =>
      decide (word position = expected) &&
        path roots rest (shift * shift) (lowHalf position)
          (foldedValue roots (word (lowIndex (lowHalf position)))
            (word (highIndex (lowHalf position))) shift (m + 1) (lowHalf position) beta)

/-- The initial selected value is an output, not a comparison with an invented initial value. -/
def firstPath (roots : ℕ → F) {m R : ℕ} (layers : Layers F (m + 1) (R + 1))
    (shift : F) (position : Fin (2 ^ (m + 1))) : Bool :=
  match layers with
  | .fold word beta rest =>
      path roots rest (shift * shift) (lowHalf position)
        (foldedValue roots (word (lowIndex (lowHalf position)))
          (word (highIndex (lowHalf position))) shift (m + 1) (lowHalf position) beta)

/-- Only a successful-state mathematical acceptance predicate, not a source execution equation. -/
def accepts (roots : ℕ → F) (t : ℕ) {m R s : ℕ}
    (layers : Layers F (m + 1) (R + 1)) (shift : F)
    (positions : Fin s → Fin (2 ^ (m + 1))) : Bool :=
  exactCoefficients t layers.coefficients &&
    (List.finRange s).all (fun q ↦ firstPath roots layers shift (positions q))

/-- The full successful mathematical result retains positions and initial values. -/
structure Result (F : Type) (n s : ℕ) where
  accepted : Bool
  positions : Fin s → Fin (2 ^ n)
  valuesV : Fin s → F

/-- Query disables association. This does not inspect an unused association vector. -/
def query (roots : ℕ → F) (t : ℕ) {m R s : ℕ}
    (layers : Layers F (m + 1) (R + 1)) (shift : F)
    (positions : Fin s → Fin (2 ^ (m + 1))) : PIR.Outcome (Result F (m + 1) s) :=
  if accepts roots t layers shift positions then
    .returned ⟨true, positions, values layers positions⟩
  else .stopped .reject

/-- Source association is by query ordinal, including repeated positions. -/
def associated {n R s : ℕ} (layers : Layers F n R)
    (positions : Fin s → Fin (2 ^ n)) (first : Fin s → F) : Prop :=
  values layers positions = first

theorem path_eq_walk (roots : ℕ → F) :
    ∀ {m R : ℕ} (layers : Layers F m R) (shift : F) (position : Fin (2 ^ m))
      (expected : F) (round : ℕ), round ≠ 0 →
      path roots layers shift position expected = walk roots layers shift position expected round
  | _, _, .final _, _, _, _, _, _ => rfl
  | _, _, .fold word beta rest, shift, position, expected, round, positive => by
      simp only [path, walk, selectHalf_eq, chain, positive, ↓reduceIte]
      rw [path_eq_walk roots rest _ _ _ (round + 1) (by omega)]

theorem firstPath_eq_walk (roots : ℕ → F) {m R : ℕ}
    (layers : Layers F (m + 1) (R + 1)) (shift : F)
    (position : Fin (2 ^ (m + 1))) :
    firstPath roots layers shift position = walk roots layers shift position 0 0 := by
  cases layers with
  | fold word beta rest =>
      simp only [firstPath, walk, chain, ↓reduceIte, Bool.true_and]
      exact path_eq_walk roots rest _ _ _ 1 one_ne_zero

/-- Exact length dominates the old bound; the two wire predicates are not equivalent. -/
theorem accepts_implies_verify (roots : ℕ → F) (t : ℕ) {m R s : ℕ}
    (layers : Layers F (m + 1) (R + 1)) (shift : F)
    (positions : Fin s → Fin (2 ^ (m + 1)))
    (accepted : accepts roots t layers shift positions = true) :
    verify roots t shift layers positions = true := by
  simp only [accepts, Bool.and_eq_true, exactCoefficients, decide_eq_true_eq] at accepted
  simp only [verify, Bool.and_eq_true]
  refine ⟨exact_coefficients_imply_old_bound t _ accepted.1, ?_⟩
  simpa only [firstPath_eq_walk] using accepted.2

/-- The source-facing acceptance seam into the existing ArkLib trace mathematics. -/
theorem accepts_trace (roots : ℕ → F) (t : ℕ) {m R s : ℕ}
    (D : Domain.SmoothCosetFftDomain (m + 1) F) (shift : F)
    (geometry : ∀ i : Fin (2 ^ (m + 1)), D i = point roots shift (m + 1) i)
    (compatible : Compatible roots (m + 1) (R + 1))
    (layers : Layers F (m + 1) (R + 1)) (positions : Fin s → Fin (2 ^ (m + 1)))
    (accepted : accepts roots t layers shift positions = true) :
    (toTrace t D layers).Accepts positions :=
  accepts_of_verify roots t D shift geometry compatible layers positions
    (accepts_implies_verify roots t layers shift positions accepted)

theorem query_returned {roots : ℕ → F} {t m R s : ℕ}
    {layers : Layers F (m + 1) (R + 1)} {shift : F}
    {positions : Fin s → Fin (2 ^ (m + 1))} {result : Result F (m + 1) s}
    (returned : query roots t layers shift positions = .returned result) :
    accepts roots t layers shift positions = true ∧ result.accepted = true ∧
      result.positions = positions ∧ result.valuesV = values layers positions := by
  unfold query at returned
  split at returned
  · rename_i h
    cases returned
    exact ⟨h, rfl, rfl, rfl⟩
  · cases returned

theorem query_values {roots : ℕ → F} {t m R s : ℕ}
    (word : Fin (2 ^ (m + 1)) → F) (beta : F) (rest : Layers F m R) {shift : F}
    {positions : Fin s → Fin (2 ^ (m + 1))} {result : Result F (m + 1) s}
    (returned : query roots t (.fold word beta rest) shift positions = .returned result) :
    result.valuesV = fun q ↦ word (positions q) := by
  rw [(query_returned returned).2.2.2]
  funext q
  exact firstValue_eq word beta rest (positions q)

/-- A typed successful position boundary. Raw lists remain visible until both guards pass. -/
structure BoundPositions (n s : ℕ) where
  raw : List ℕ
  length_eq : raw.length = s
  bounded : ∀ p ∈ raw, p < 2 ^ n

def BoundPositions.at {n s : ℕ} (positions : BoundPositions n s) (q : Fin s) : Fin (2 ^ n) :=
  ⟨positions.raw[q.val]'(by rw [positions.length_eq]; exact q.isLt),
    positions.bounded _ (List.getElem_mem _)⟩

/-- Bind checks length before bounds; it supplies no distributional conclusion. Numeric
collection ingress and role-local failures must be installed by the source association. -/
def bindQueries (n s : ℕ) (positions : List ℕ) : PIR.Outcome (BoundPositions n s) :=
  if length_eq : positions.length = s then
    if bounded : ∀ p ∈ positions, p < 2 ^ n then
      .returned ⟨positions, length_eq, bounded⟩
    else .stopped .reject
  else .stopped .reject

theorem bindQueries_returned {n s : ℕ} {raw : List ℕ} {positions : BoundPositions n s}
    (returned : bindQueries n s raw = .returned positions) : positions.raw = raw := by
  unfold bindQueries at returned
  split at returned
  · split at returned
    · cases returned
      rfl
    · cases returned
  · cases returned

/-- Repeated reductions agree with reduction modulo the later domain, in natural order. -/
theorem reduce_position (p a b : ℕ) (order : a ≤ b) :
    (p % 2 ^ b) % 2 ^ a = p % 2 ^ a := by
  exact Nat.mod_mod_of_dvd p (pow_dvd_pow 2 order)

/-- Source round arithmetic is ordinary arithmetic under its admitted profile. -/
theorem round_indices {n R step : ℕ} (size : n ≤ 63) (rounds : R ≤ n)
    (positive : 1 ≤ R) (inside : step < R - 1) :
    wrappingSubtract R 1 = R - 1 ∧ wrappingAdd step 1 = step + 1 ∧ step + 1 < R := by
  have limit : R < wordModulus := by
    have : 63 < wordModulus := by decide
    omega
  refine ⟨wrappingSubtract_of_le limit positive, ?_, by omega⟩
  exact Nat.mod_eq_of_lt (by omega)

end ZkcSecurity.ArkLib.Fri.Phases
