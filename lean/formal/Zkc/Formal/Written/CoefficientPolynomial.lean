module

public import Zkc.Formal.Written.PolynomialBounds
public import Zkc.Formal.Interactive.CoefficientMembers
public import Zkc.Formal.Interactive.PairRound
import Mathlib.Tactic.ComputeDegree

@[expose] public section
namespace Zkc.Formal.Written.CoefficientPolynomial
open Polynomial Interactive.Sumcheck

variable {F : Type} [Field F]

/-- Interpretation of the specification member `line(m.0, m.0 + m.1)`. -/
noncomputable def polynomial (m : F × F) : F[X] := PolynomialBounds.linear (Coefficients.decode F m)

theorem normalForm (m : F × F) : polynomial m = C m.1 + X * C m.2 := by
  change C m.1 + X * C (m.1 + m.2 - m.1) = _
  simp

theorem degree (m : F × F) : (polynomial m).natDegree ≤ 1 := by
  rw [normalForm]
  compute_degree

theorem atPoint (m : F × F) (r : F) : (polynomial m).eval r = m.1 + r * m.2 := by
  rw [normalForm]
  simp only [eval_add, eval_mul, eval_C, eval_X]

theorem ends (m : F × F) : (polynomial m).eval 0 + (polynomial m).eval 1 = m.1 + (m.1 + m.2) := by
  simp [atPoint]

/-- The honest message encodes the same line as the sums of the two halves. -/
theorem ofEndpoints (u v : F) : polynomial (u, v - u) = PolynomialBounds.linear (u, v) := by
  simp [normalForm, PolynomialBounds.linear]

/-- A false boundary separates the received line from any degree-one reference polynomial. -/
theorem agreements [DecidableEq F] (m : F × F) (reference : F[X]) (bounded : reference.natDegree ≤ 1)
    (apart : m.1 + (m.1 + m.2) ≠ reference.eval 0 + reference.eval 1)
    (points : List F) (distinct : points.Nodup) :
    points.countP (fun r => decide (m.1 + r * m.2 = reference.eval r)) ≤ 1 := by
  have different : polynomial m ≠ reference := fun eq => apart ((ends m).symm.trans (eq ▸ rfl))
  simpa only [atPoint] using PolynomialBounds.agreements_le (polynomial m) reference 1
    (degree m) bounded different points distinct

open Zkc.Core ReductionRound
variable {V : Vocabulary} {rows : ScalarRows V} {hs : Headers V} {defs : Defs V hs}
variable {msg st out : V.Ty} {ops : ReductionRound.Members hs rows.scalarTy msg st out}

/-- At the actual operations of a checked occurrence, the source line and its two verifier
laws have their ordinary polynomial meaning for every received message. -/
theorem installed (laws : PairLaws rows defs ops Coefficients.decode)
    (M : Model V) [Field (rows.F M)] (math : rows.Arithmetic M) (m : M.Val msg) (r : rows.F M) :
    let p := polynomial (endpoints rows M laws.aligned m)
    localOp M (Defs.fnTable M defs) ops.boundary (.cons m .nil) = .done (.cons (p.eval 0 + p.eval 1) .nil) ∧
    localOp M (Defs.fnTable M defs) ops.evaluate (.cons m (.cons r .nil)) = .done (.cons (p.eval r) .nil) := by
  dsimp only
  rw [laws.boundary M math, laws.evaluate M math, ends, atPoint, line_normalForm]
  constructor
  · rfl
  · simp [Coefficients.decode, Coefficients.expression, LineExpression.decode, EndpointExpression.eval]

end Zkc.Formal.Written.CoefficientPolynomial
