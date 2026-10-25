module

public import ZkcSecurity.Families.Sumcheck.Reference
public import Zkc.Polynomial.Multilinear.Restriction

@[expose] public section

/-! A degree-two reference retains two multilinear factors. Restriction folds
each factor separately, including when both factors initially coincide.
Collapsing their pointwise product into one multilinear table is unsound. -/

set_option autoImplicit false

namespace ZkcSecurity.Families.Sumcheck.FactorReference

open Zkc.Polynomial Zkc.Polynomial.Multilinear

variable {F : Type} [Field F]

/-- The cube sum of the product of extensions agrees with the product's Boolean
table on the cube. This equation alone does not identify off-cube extensions. -/
theorem cubeSum_product (n : Nat) (left right : Table F n) :
    cubeSum n (fun point => extension n left point * extension n right point) =
      booleanSum (fun bits => left bits * right bits) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change cubeSum n (fun tail => extension (n + 1) left (Fin.cons 0 tail) *
        extension (n + 1) right (Fin.cons 0 tail)) +
        cubeSum n (fun tail => extension (n + 1) left (Fin.cons 1 tail) *
        extension (n + 1) right (Fin.cons 1 tail)) = _
      have low (table : Table F (n + 1)) (tail : Fin n → F) :
          extension (n + 1) table (Fin.cons 0 tail) = extension n (half table false) tail := by
        simp only [extension, Fin.cons_zero, Fin.cons_succ, Function.comp_def,
          sub_zero, one_mul, zero_mul, add_zero]
        rfl
      have high (table : Table F (n + 1)) (tail : Fin n → F) :
          extension (n + 1) table (Fin.cons 1 tail) = extension n (half table true) tail := by
        simp only [extension, Fin.cons_zero, Fin.cons_succ, Function.comp_def,
          sub_self, zero_mul, one_mul, zero_add]
        rfl
      simp only [low, high, ih]
      rfl

theorem product_total {n : Nat} (left right : Table F n) :
    (productCoefficients n left right).booleanSum =
      booleanSum (fun bits => left bits * right bits) := by
  change cubeSum n (fun point => (productCoefficients n left right).eval point) = _
  simp only [productCoefficients_eval]
  exact cubeSum_product n left right

/-- The reference polynomial is taken from the existing coefficient bridge;
the state keeps the factors needed for all future off-cube observations. -/
noncomputable abbrev data (F : Type) [Field F] : Reference F where
  State n := Table F n × Table F n
  total s := booleanSum (fun bits => s.1 bits * s.2 bits)
  restrict s r := (fixFirst s.1 r, fixFirst s.2 r)
  polynomial s := Zkc.Protocols.Sumcheck.messagePolynomial
    (Zkc.Protocols.Sumcheck.roundPolynomial (productCoefficients _ s.1 s.2))
  admissible _ := True

theorem evaluation {n : Nat} (s : (data F).State (n + 1)) (r : F) :
    ((data F).polynomial s).eval r = (data F).total ((data F).restrict s r) := by
  change (Zkc.Protocols.Sumcheck.messagePolynomial
    (Zkc.Protocols.Sumcheck.roundPolynomial (productCoefficients _ s.1 s.2))).eval r = _
  rw [Zkc.Protocols.Sumcheck.messagePolynomial_eval, Zkc.Protocols.Sumcheck.round_evaluate]
  change cubeSum n (fun tail => ((productCoefficients _ s.1 s.2).restrict r).eval tail) = _
  simp only [Quadratic.eval_restrict, productCoefficients_eval]
  change cubeSum n (fun tail => extension (n + 1) s.1 (Fin.cons r tail) *
    extension (n + 1) s.2 (Fin.cons r tail)) = _
  simp only [← extension_fixFirst]
  exact cubeSum_product n (fixFirst s.1 r) (fixFirst s.2 r)

theorem laws : ReferenceLaws (data F) 2 where
  degree_le _ _ := Zkc.Protocols.Sumcheck.messagePolynomial_degree _
  boundary_eq s _ := by
    rw [boundaryPoly, evaluation, evaluation]
    change booleanSum (fun bits => fixFirst s.1 0 bits * fixFirst s.2 0 bits) +
      booleanSum (fun bits => fixFirst s.1 1 bits * fixFirst s.2 1 bits) = _
    rw [fixFirst_zero, fixFirst_zero, fixFirst_one, fixFirst_one]
    rfl
  evaluation_eq s r _ := evaluation s r
  restriction_closed _ _ _ := trivial

theorem honest_polynomial {n : Nat} (s : (data F).State (n + 1)) :
    (Message.coefficients F).polynomial
      (Zkc.Protocols.Sumcheck.roundPolynomial (productCoefficients _ s.1 s.2)) =
      (data F).polynomial s := rfl

/-- Future observations preserve the product of the original extensions, not
the extension of their Boolean product table. -/
theorem restriction_extension {n : Nat} (s : (data F).State (n + 1)) (r : F)
    (tail : Fin n → F) :
    extension n ((data F).restrict s r).1 tail *
      extension n ((data F).restrict s r).2 tail =
      extension (n + 1) s.1 (Fin.cons r tail) * extension (n + 1) s.2 (Fin.cons r tail) := by
  change extension n (fixFirst s.1 r) tail * extension n (fixFirst s.2 r) tail = _
  rw [extension_fixFirst, extension_fixFirst]

theorem restrictPrefix_factors {n : Nat} (count : Nat)
    (s : (data F).State (n + count)) (challenges : Fin count → F) :
    (data F).restrictPrefix count s challenges =
      (fixPrefix count s.1 challenges, fixPrefix count s.2 challenges) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      exact ih ((data F).restrict s (challenges 0)) (challenges ∘ Fin.succ)

/-- The retained factors preserve off-cube observations after every permitted
future prefix, not just after one update or at Boolean vertices. -/
theorem prefix_extension {n : Nat} (count : Nat) (s : (data F).State (n + count))
    (challenges : Fin count → F) (tail : Fin n → F) :
    extension n ((data F).restrictPrefix count s challenges).1 tail *
      extension n ((data F).restrictPrefix count s challenges).2 tail =
      extension (n + count) s.1 (Quadratic.point count challenges tail) *
        extension (n + count) s.2 (Quadratic.point count challenges tail) := by
  rw [restrictPrefix_factors]
  change extension n (fixPrefix count s.1 challenges) tail *
    extension n (fixPrefix count s.2 challenges) tail = _
  rw [extension_fixPrefix, extension_fixPrefix]

/-- A caller's extra weight is independent of the active challenge. No syntax
annotation or weighted-degree calculation proves this condition. -/
def ActiveIndependent {n : Nat} (weight : F → Table F n) : Prop :=
  ∀ r bits, weight r bits = weight 0 bits

/-- With active-variable independence, two affine factors give a quadratic
weighted marginal. The coefficients reuse the core degree-two decoder. -/
def weightedMessage {n : Nat} (weight : Table F n) (left right : Table F (n + 1)) :
    Zkc.Protocols.AlgebraicRounds.Message F :=
  let a := half left false
  let da := fun bits => half left true bits - a bits
  let b := half right false
  let db := fun bits => half right true bits - b bits
  ⟨booleanSum (fun bits => weight bits * (a bits * b bits)),
    booleanSum (fun bits => weight bits * (a bits * db bits + da bits * b bits)),
    booleanSum (fun bits => weight bits * (da bits * db bits))⟩

theorem weighted_evaluation {n : Nat} (weight : F → Table F n)
    (independent : ActiveIndependent weight) (left right : Table F (n + 1)) (r : F) :
    (weightedMessage (weight 0) left right).evaluate r =
      booleanSum (fun bits => weight r bits * (fixFirst left r bits * fixFirst right r bits)) := by
  simp only [weightedMessage, Zkc.Protocols.AlgebraicRounds.Message.evaluate]
  rw [mul_comm _ r, mul_comm _ (r * r)]
  rw [← booleanSum_scale, ← booleanSum_scale, ← booleanSum_add, ← booleanSum_add]
  congr 1
  funext bits
  rw [independent r bits]
  simp only [fixFirst]
  ring

theorem weighted_degree {n : Nat} (weight : Table F n) (left right : Table F (n + 1)) :
    (Zkc.Protocols.Sumcheck.messagePolynomial (weightedMessage weight left right)).natDegree ≤ 2 :=
  Zkc.Protocols.Sumcheck.messagePolynomial_degree _

end ZkcSecurity.Families.Sumcheck.FactorReference
