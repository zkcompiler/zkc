module

public import ZkcSecurity.ArkLib.Fri.Domain

@[expose] public section

/-! # `fri::LowDegree` at the ideal interpretation

This module transcribes the verifier of `fri::LowDegree` (`libraries/protocols/polynomial/fri/lib.zkc`) as a
public-coin interactive oracle proof, reading every commitment as the vector it commits to.
`lean/docs/spec/fri-security.md` relates each definition to its source lines.

The interaction, for static parameters `LogSize = n`, `TerminalLog = t`, `Rounds = R` and
`Queries = s`, is:

* the prover commits the initial word, a size-`2^n` vector in the coset's logical order;
* for each of the `R` folding rounds, the verifier draws a uniform field challenge, and the prover
  commits the next word (a vector of half the size), except after the last round, where it sends
  the final coefficient vector instead;
* the verifier checks that at most `2^t` coefficients were sent;
* the verifier draws all `s` query positions, uniform in `[0, 2^n)`, before any opening;
* for each position it reads both halves of each round's pair, checks consecutive folds and the
  final polynomial's value, and keeps the first-round value.

Ideal commitments: `oracle::check(root, 1, size, position, row, path)` holds exactly when `row`
is the one-element row of the committed vector at `position`, and the committed vector has the
expected length. A prover that commits a vector of another length, or opens another row, is
rejected at its first opening, so the model's words have the expected sizes and the verifier reads
committed values directly.

`commit` and `experiment` run the interaction against an adaptive prover strategy with uniform
challenges. `drawPositions` is the source's loop of `s` index draws; `prEvent_positions` shows
that it gives every event of the positions its probability under the uniform draw of all `s`
positions together, so the query phase is one compound challenge at the interactive level. How a
Fiat–Shamir transcript produces these draws, including the decoding of an index from a field
element and the treatment of the `s` draws as one block, is outside this module.
-/

namespace ZkcSecurity.ArkLib.Fri

open OracleComp

variable {F : Type} [Field F]

/-! ## Scalar helpers, in source order -/

/-- `bounded` (`lib.zkc` lines 30–33): at most `2^t` coefficients. -/
def bounded (t : ℕ) (coefficients : List F) : Bool :=
  decide (coefficients.length < 2 ^ t + 1)

/-- `polynomial::evaluate(polynomial::from_coefficients(c), x)`: ascending coefficients. -/
def evaluate (coefficients : List F) (x : F) : F :=
  coefficients.foldr (fun coefficient value => coefficient + x * value) 0

/-- `terminal` (lines 34–39): the final polynomial at a coset point. -/
def terminal (roots : ℕ → F) (coefficients : List F) (shift : F) (m position : ℕ) : F :=
  evaluate coefficients (point roots shift m position)

/-- `fold_value` (lines 42–45), with caller-prepared inverses of two and of the point. -/
def foldValue (low high beta inverseTwo inverseX : F) : F :=
  (low + high) * inverseTwo + beta * (low - high) * inverseTwo * inverseX

/-- `folded_value` (lines 48–54): the fold of the pair at `position` and `position + 2^(m-1)` of
the size-`2^m` coset, which in logical order holds `x` and `-x`. -/
def foldedValue (roots : ℕ → F) (low high shift : F) (m position : ℕ) (beta : F) : F :=
  let x := point roots shift m position
  foldValue low high beta (1 + 1)⁻¹ x⁻¹

/-- `chain` (lines 55–57): from the second round on, the selected value must be the previous
round's fold. -/
def chain [DecidableEq F] (round : ℕ) (selected expected : F) : Bool :=
  if round = 0 then true else decide (selected = expected)

/-- `select_half` (lines 61–63). -/
def selectHalf (low high : F) (position half : ℕ) : F :=
  if position < half then low else high

/-! ## Committed transcripts -/

/-- The commit phase's messages and challenges (lines 104–119), outermost round first: each
committed word in logical order with its folding challenge, then the final coefficient vector.
`Layers F m R` starts at a size-`2^m` word and has `R` folds. -/
inductive Layers (F : Type) : ℕ → ℕ → Type where
  | final {m : ℕ} (coefficients : List F) : Layers F m 0
  | fold {m R : ℕ} (word : Fin (2 ^ (m + 1)) → F) (beta : F) (rest : Layers F m R) :
      Layers F (m + 1) (R + 1)

namespace Layers

/-- The final coefficient vector. -/
def coefficients : {m R : ℕ} → Layers F m R → List F
  | _, _, .final coefficients => coefficients
  | _, _, .fold _ _ rest => rest.coefficients

end Layers

/-- The two indices of the pair at `low` in a size-`2^(m + 1)` vector: `low` and `low + 2^m`. -/
def lowIndex {m : ℕ} (low : Fin (2 ^ m)) : Fin (2 ^ (m + 1)) :=
  ⟨low.val, by have := low.isLt; rw [pow_succ]; omega⟩

/-- See `lowIndex`. -/
def highIndex {m : ℕ} (low : Fin (2 ^ m)) : Fin (2 ^ (m + 1)) :=
  ⟨low.val + 2 ^ m, by have := low.isLt; rw [pow_succ]; omega⟩

/-- `remainder(position, half)` for a position of a size-`2^(m + 1)` vector. -/
def lowHalf {m : ℕ} (position : Fin (2 ^ (m + 1))) : Fin (2 ^ m) :=
  ⟨position.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩

/-- One query's checks (lines 133–176) from round `round` on, at `position` of the current
size-`2^m` coset with shift `shift`, where `expected` is the previous round's fold. At a folding
round it reads both halves of the pair, checks the chain, and moves to `remainder(position, half)`
of the halved coset with the squared shift; at the end it checks the final polynomial. -/
def walk [DecidableEq F] (roots : ℕ → F) {m R : ℕ} (layers : Layers F m R) (shift : F)
    (position : Fin (2 ^ m)) (expected : F) (round : ℕ) : Bool :=
  match m, R, layers, position with
  | m, _, .final coefficients, position =>
      decide (terminal roots coefficients shift m position.val = expected)
  | m + 1, _, .fold word beta rest, position =>
      let low := lowHalf position
      let lowValue := word (lowIndex low)
      let highValue := word (highIndex low)
      let selected := selectHalf lowValue highValue position.val (2 ^ m)
      chain round selected expected &&
        walk roots rest (shift * shift) low
          (foldedValue roots lowValue highValue shift (m + 1) low.val beta) (round + 1)

/-- The value `selected` at the first round of a query (line 162): the initial word at the
query position. -/
def firstValue {m R : ℕ} (layers : Layers F m R) (position : Fin (2 ^ m)) : F :=
  match m, R, layers, position with
  | _, _, .final _, _ => 0
  | m + 1, _, .fold word _ _, position =>
      selectHalf (word (lowIndex (lowHalf position))) (word (highIndex (lowHalf position)))
        position.val (2 ^ m)

/-- The verifier's acceptance (lines 120–177) for a committed transcript and drawn positions:
the coefficient bound, then every query's checks from round zero with expected value zero. -/
def verify [DecidableEq F] (roots : ℕ → F) (t : ℕ) (shift : F) {n R s : ℕ}
    (layers : Layers F n R) (positions : Fin s → Fin (2 ^ n)) : Bool :=
  bounded t layers.coefficients &&
    (List.finRange s).all fun query => walk roots layers shift (positions query) 0 0

/-- `valuesV` (lines 162–163): the first-round value of each query, in query order. -/
def values {n R s : ℕ} (layers : Layers F n R) (positions : Fin s → Fin (2 ^ n)) : Fin s → F :=
  fun query => firstValue layers (positions query)

/-! ## The interaction -/

/-- An adaptive prover strategy for the commit phase, after it has committed a size-`2^m` word
with `R` folds left. On each folding challenge it commits the next word, or after the last fold
sends the final coefficient vector. Private randomness is a distribution over strategies. -/
inductive Strategy (F : Type) : ℕ → ℕ → Type where
  | last {m : ℕ} (final : F → List F) : Strategy F (m + 1) 1
  | fold {m R : ℕ} (next : F → Fin (2 ^ m) → F) (rest : F → Strategy F m (R + 1)) :
      Strategy F (m + 1) (R + 2)

variable [SampleableType F]

/-- The commit phase against a strategy, from a committed word: each folding challenge is a
fresh uniform field element. -/
def commit : {m R : ℕ} → Strategy F m R → (Fin (2 ^ m) → F) → ProbComp (Layers F m R)
  | _, _, .last final, word => do
      let beta ← $ᵗ F
      pure (.fold word beta (.final (final beta)))
  | _, _, .fold next rest, word => do
      let beta ← $ᵗ F
      let layers ← commit (rest beta) (next beta)
      pure (.fold word beta layers)

/-- The query draws (lines 125–132): `s` uniform positions in `[0, 2^n)`, drawn one after another
and appended to the list of positions (`indices::append`). The verifier sends each position to
the prover; no prover message comes between the draws. -/
def drawPositions (n : ℕ) : (s : ℕ) → ProbComp (Vector (Fin (2 ^ n)) s)
  | 0 => pure #v[]
  | s + 1 => Vector.push <$> drawPositions n s <*> $ᵗ (Fin (2 ^ n))

/-- `indices::get(positions, query)` (lines 134–135). -/
def positionAt {n s : ℕ} (positions : Vector (Fin (2 ^ n)) s) (query : Fin s) : Fin (2 ^ n) :=
  positions[query.val]

/-- The whole interaction: the prover's initial word and strategy, the commit phase, the query
draws, and the verifier's acceptance, with the committed transcript. -/
def experiment [DecidableEq F] (roots : ℕ → F) (t : ℕ) (shift : F) {n R : ℕ} (s : ℕ)
    (prover : ProbComp ((Fin (2 ^ n) → F) × Strategy F n R)) :
    ProbComp (Layers F n R × Bool) := do
  let start ← prover
  let layers ← commit start.2 start.1
  let positions ← positionAt <$> drawPositions n s
  pure (layers, verify roots t shift layers positions)

open MeasureTheory ProbabilityTheory in
/-- The source loop's draws are uniform on vectors of positions. -/
theorem evalDist_drawPositions (n : ℕ) :
    ∀ (s : ℕ) [MeasurableSpace (Vector (Fin (2 ^ n)) s)]
      [MeasurableSingletonClass (Vector (Fin (2 ^ n)) s)],
      𝒟[drawPositions n s] = uniformOn Set.univ := by
  intro s
  induction s with
  | zero =>
      intro _ _
      let : Unique (Vector (Fin (2 ^ n)) 0) := ⟨⟨#v[]⟩, fun x ↦ by ext i; omega⟩
      let : Fintype (Vector (Fin (2 ^ n)) 0) := Fintype.ofFinite _
      apply Measure.ext_of_singleton
      intro x
      simp [drawPositions, Subsingleton.elim x #v[], uniformOn_univ_apply_singleton]
  | succ s ih =>
      intro _ _
      let : MeasurableSpace (Vector (Fin (2 ^ n)) s) := ⊤
      let : MeasurableSpace (Fin (2 ^ n)) := ⊤
      exact evalDist_seq_map_eq_uniformOn _ ($ᵗ (Fin (2 ^ n))) Vector.push ih
        SampleableType.evalDist_uniformSample Measurable.of_discrete
        ⟨fun x y h ↦ Prod.ext (Vector.push_eq_push.mp h).2 (Vector.push_eq_push.mp h).1,
          fun x ↦ ⟨(x.pop, x.back), Vector.push_pop_back x⟩⟩

/-- The query phase is one compound challenge: the source loop's `s` consecutive uniform index
draws, read by `indices::get`, give every event of the positions the probability it has under the
uniform draw of all `s` positions together. This holds at the interactive level, where only the
verifier's own sends of the drawn positions separate the draws. -/
theorem prEvent_positions (n s : ℕ) (event : (Fin s → Fin (2 ^ n)) → Prop) :
    Pr{let positions ← positionAt <$> drawPositions n s}[event positions] =
      Pr{let positions ← $ᵗ (Fin s → Fin (2 ^ n))}[event positions] := by
  rw [show ($ᵗ (Fin s → Fin (2 ^ n))) = positionAt <$> SampleableType.vector (Fin (2 ^ n)) s from rfl,
    prEvent_map, prEvent_map]
  exact prEvent_congr_of_evalDist_eq _ _
    (by rw [evalDist_drawPositions, SampleableType.evalDist_vector]) _

end ZkcSecurity.ArkLib.Fri
