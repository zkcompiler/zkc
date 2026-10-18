module

public import ZkcSecurity.ArkLib.Sumcheck.Domain
public import ZkcSecurity.ArkLib.Sumcheck.Multilinear.Table
public import ArkLib.ProofSystem.Sumcheck.Interaction.ProtocolSoundness
public import Zkc.Protocols.Gkr.Circuit

@[expose] public section

/-! The Sumcheck of one GKR layer as an ArkLib Sumcheck statement.

A layer's gate polynomial over `(x, y)` is
`add~(x, y) (V~(x) + V~(y)) + mul~(x, y) V~(x) V~(y)` for wiring tables already
restricted at the layer's point. It is the sum of two products of multilinear
extensions, so every variable has degree at most two (`gatePolynomial`), and its
Boolean sum is the extension of the layer at that point (`gatePolynomial_sum`,
from `Zkc.Protocols.Gkr.extension_layer`).

`FalseClaim` states that a claim at a prefix of challenges is false: ArkLib's
closed round relation of the polynomial fails. A false initial claim is false
at the empty prefix (`falseClaim_initial`); after a received round polynomial
passes the round check, a fresh uniform challenge makes the claim true with
probability at most `2 / |F|` (`falseClaim_successor`, ArkLib's
`MultivariateRound.uniform_successor_soundness` at degree two); and a false claim
at a complete point differs from the polynomial's value there
(`falseClaim_terminal`).
-/

set_option autoImplicit false

namespace ZkcSecurity.ArkLib.Gkr
open Zkc.Polynomial Zkc.Polynomial.Multilinear Zkc.Protocols.Gkr
open ZkcSecurity.ArkLib.Sumcheck ZkcSecurity.ArkLib.Sumcheck.Multilinear
open _root_.Sumcheck.Interaction
open scoped ENNReal

variable {F : Type} [Field F] {w : Nat}

/-- The gate polynomial of a layer, for wiring tables restricted at its point. -/
noncomputable def gatePolynomial (add mul : Table F (w + w)) (below : Table F w) :
    MvPolynomial (Fin (w + w)) F :=
  Multilinear.statement add * Multilinear.statement (sumTable below) +
    Multilinear.statement mul * Multilinear.statement (productTable below)

theorem gatePolynomial_degree (add mul : Table F (w + w)) (below : Table F w) (i : Fin (w + w)) :
    (gatePolynomial add mul below).degreeOf i ≤ 2 := by
  have linear (table : Table F (w + w)) : (Multilinear.statement table).degreeOf i ≤ 1 :=
    (MvPolynomial.mem_restrictDegree_iff_degreeOf_le _ _).mp (statement_degree table) i
  unfold gatePolynomial
  refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
  · exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (Nat.add_le_add (linear _) (linear _))
  · exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (Nat.add_le_add (linear _) (linear _))

/-- The gate polynomial as an ArkLib Sumcheck statement of degree two. -/
noncomputable def gateStatement (add mul : Table F (w + w)) (below : Table F w) :
    _root_.Sumcheck.Spec.OracleStatement F (w + w) 2 () :=
  ⟨gatePolynomial add mul below,
    (MvPolynomial.mem_restrictDegree_iff_degreeOf_le _ _).mpr (gatePolynomial_degree add mul below)⟩

theorem gatePolynomial_eval (add mul : Table F (w + w)) (below : Table F w) (point : Fin (w + w) → F) :
    MvPolynomial.eval point (gatePolynomial add mul below) =
      extension (w + w) add point * extension (w + w) (sumTable below) point +
        extension (w + w) mul point * extension (w + w) (productTable below) point := by
  simp only [gatePolynomial, MvPolynomial.eval_add, MvPolynomial.eval_mul,
    Multilinear.statement_evaluate]

/-- The gate polynomial at a concatenated point `(x, y)`. -/
theorem gatePolynomial_point (add mul : Table F (w + w)) (below : Table F w) (left right : Fin w → F) :
    MvPolynomial.eval (Quadratic.point w left right) (gatePolynomial add mul below) =
      extension (w + w) add (Quadratic.point w left right) *
          (extension w below left + extension w below right) +
        extension (w + w) mul (Quadratic.point w left right) *
          (extension w below left * extension w below right) := by
  rw [gatePolynomial_eval, extension_sumTable, extension_productTable]

/-- The Boolean sum of the gate polynomial is the Boolean sum of the gate table. -/
theorem gatePolynomial_sum (add mul : Table F (w + w)) (below : Table F w) :
    (∑ point ∈ (Finset.univ.map (boolEmbedding F)) ^ᶠ (w + w),
      MvPolynomial.eval point (gatePolynomial add mul below)) = booleanSum (gates add mul below) := by
  rw [domain_sum, cubeSum_booleanPoint]
  congr 1
  funext bits
  simp only [gatePolynomial_eval, extension_boolean, gates]

/-- ArkLib's realized polynomial oracle of a gate statement. -/
noncomputable abbrev behavior (statement : _root_.Sumcheck.Spec.OracleStatement F (w + w) 2 ()) :=
  (MultivariateRound.polynomialFamily F (w + w) 2).behaviorOfRealizations (fun _ => statement)

/-- `claim` is false at the challenge prefix `point`: ArkLib's closed round
relation fails for the statement summed over the remaining Boolean coordinates. -/
def FalseClaim (statement : _root_.Sumcheck.Spec.OracleStatement F (w + w) 2 ()) (point : List F)
    (claim : F) : Prop :=
  ∃ (i : Fin (w + w + 1)) (round : _root_.Sumcheck.Spec.StatementRound F (w + w) i),
    point.length = i ∧ round.target = claim ∧ round.challenges = coordinates i point ∧
    ¬ MultivariateRound.closedRelation F (w + w) 2 (boolEmbedding F) i ⟨round, behavior statement⟩

/-- A claim other than the Boolean sum is false at the empty prefix. -/
theorem falseClaim_initial (statement : _root_.Sumcheck.Spec.OracleStatement F (w + w) 2 ())
    (claim : F)
    (different : claim ≠ ∑ point ∈ (Finset.univ.map (boolEmbedding F)) ^ᶠ (w + w),
      MvPolynomial.eval point statement.val) :
    FalseClaim statement [] claim := by
  refine ⟨0, ⟨claim, Fin.elim0⟩, rfl, rfl, funext fun index => index.elim0, ?_⟩
  change ¬ (∑ point ∈ (Finset.univ.map (boolEmbedding F)) ^ᶠ (w + w),
    MvPolynomial.eval (Fin.append Fin.elim0 point ∘ Fin.cast (by omega)) statement.val) = claim
  simp only [Fin.append_left_nil _ _ rfl, Function.comp_def, Fin.cast_cast, Fin.cast_eq_self]
  exact fun same => different same.symm

/-- A false claim at a complete point differs from the statement's value there. -/
theorem falseClaim_terminal (statement : _root_.Sumcheck.Spec.OracleStatement F (w + w) 2 ())
    (point : List F) (claim : F) (wrong : FalseClaim statement point claim)
    (complete : point.length = w + w) :
    MvPolynomial.eval (coordinates (w + w) point) statement.val ≠ claim := by
  obtain ⟨index, round, sized, target, challenges, notClosed⟩ := wrong
  have last : index = Fin.last (w + w) := Fin.ext (by simp [← sized, complete])
  subst last
  rw [MultivariateRound.closedRelation_last_iff] at notClosed
  intro evaluates
  apply notClosed
  change MvPolynomial.eval round.challenges statement.val = round.target
  rw [challenges, target]
  exact evaluates

theorem snoc_coordinates (point : List F) (challenge : F) {length : Nat}
    (sized : point.length = length) :
    Fin.snoc (α := fun _ => F) (coordinates length point) challenge =
      coordinates (length + 1) (point ++ [challenge]) := by
  funext index
  refine Fin.lastCases ?_ (fun earlier => ?_) index
  · simp [coordinates, sized]
  · have bound : earlier.val < point.length := sized ▸ earlier.isLt
    simp [coordinates, List.getElem?_append_left bound]

variable [Fintype F] [SampleableType F]

/-- Per-round soundness, from ArkLib's single-round successor bound at degree
two: after received coefficients `(c0, c1, c2)` pass the round check
`claim = 2 c0 + c1 + c2`, a fresh uniform challenge `r` makes the claim
`c0 + r (c1 + r c2)` true with probability at most `2 / |F|`. -/
theorem falseClaim_successor (statement : _root_.Sumcheck.Spec.OracleStatement F (w + w) 2 ())
    (point : List F) (claim c0 c1 c2 : F) (wrong : FalseClaim statement point claim)
    (incomplete : point.length < w + w) (checked : claim = c0 + c0 + c1 + c2) :
    Pr{let challenge ← $ᵗ F}[
      ¬ FalseClaim statement (point ++ [challenge]) (c0 + challenge * (c1 + challenge * c2))] ≤
      2 / (Fintype.card F : ENNReal) := by
  obtain ⟨index, round, sized, target, challenges, notClosed⟩ := wrong
  obtain ⟨position, rfl⟩ : ∃ position : Fin (w + w), position.castSucc = index :=
    Fin.exists_castSucc_eq.mpr (fun last => by
      rw [last] at sized
      simp at sized
      omega)
  let coefficients : Zkc.Protocols.AlgebraicRounds.Message F := ⟨c0, c1, c2⟩
  have passes : ((Finset.univ.map (boolEmbedding F)).toList.map
      (fun x => (message coefficients).val.eval x)).sum = round.target := by
    have evaluated : (fun x => (message coefficients).val.eval x) =
        Zkc.Protocols.Sumcheck.Common.wireEvaluate coefficients :=
      funext (message_evaluate coefficients)
    rw [evaluated, target, checked]
    exact booleanDomain_sum coefficients
  have bound := MultivariateRound.uniform_successor_soundness (w + w) 2 F (boolEmbedding F) position
    round statement (message coefficients) notClosed passes
  rw [Nat.cast_ofNat] at bound
  refine (prEvent_mono _ _ _ (fun challenge escaped => ?_)).trans bound
  by_contra notClosed'
  apply escaped
  refine ⟨position.succ, ⟨(message coefficients).val.eval challenge,
    Fin.snoc round.challenges challenge⟩, ?_, ?_, ?_, notClosed'⟩
  · simp [sized]
  · rw [message_evaluate]
    simp only [Zkc.Protocols.Sumcheck.Common.wireEvaluate, coefficients]
    ring
  · change Fin.snoc (α := fun _ => F) round.challenges challenge =
      coordinates (position.val + 1) (point ++ [challenge])
    rw [challenges]
    exact snoc_coordinates point challenge sized

end ZkcSecurity.ArkLib.Gkr
