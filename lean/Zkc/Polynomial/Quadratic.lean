import Zkc.Polynomial.BooleanCube
import Mathlib.Tactic.Ring

/-! Fixed polynomials with per-coordinate degree at most two.

The type indexes the number of ordered coordinates. A node stores the three
coefficient polynomials for its first coordinate. Evaluation and Boolean-cube
summation define the object before any query or materialization algorithm.
This is a logical coefficient representation, not a prescribed native layout.
-/

set_option autoImplicit false

namespace Zkc.Polynomial

inductive Quadratic (F : Type) : Nat → Type where
  | constant : F → Quadratic F 0
  | node {n : Nat} : Quadratic F n → Quadratic F n → Quadratic F n → Quadratic F (n + 1)
  deriving Repr

namespace Quadratic

variable {F : Type} {n : Nat}

def eval [Semiring F] : {n : Nat} → Quadratic F n → (Fin n → F) → F
  | 0, .constant c, _ => c
  | _ + 1, .node a b c, point =>
      eval a (point ∘ Fin.succ) + point 0 * eval b (point ∘ Fin.succ) +
        (point 0 * point 0) * eval c (point ∘ Fin.succ)

def add [Add F] : {n : Nat} → Quadratic F n → Quadratic F n → Quadratic F n
  | 0, .constant a, .constant b => .constant (a + b)
  | _ + 1, .node a b c, .node d e f => .node (add a d) (add b e) (add c f)

def scale [Mul F] (r : F) : {n : Nat} → Quadratic F n → Quadratic F n
  | 0, .constant a => .constant (r * a)
  | _ + 1, .node a b c => .node (scale r a) (scale r b) (scale r c)

variable [CommSemiring F]

theorem eval_add (p q : Quadratic F n) (point : Fin n → F) :
    (add p q).eval point = p.eval point + q.eval point := by
  induction p with
  | constant a => cases q; rfl
  | node a b c ia ib ic =>
      cases q
      simp only [add, eval, ia, ib, ic]
      ring

theorem eval_scale (r : F) (p : Quadratic F n) (point : Fin n → F) :
    (scale r p).eval point = r * p.eval point := by
  induction p with
  | constant a => rfl
  | node a b c ia ib ic =>
      simp only [scale, eval, ia, ib, ic]
      ring

/-- Partially evaluate the first coordinate and retain the remaining polynomial. -/
def restrict (p : Quadratic F (n + 1)) (r : F) : Quadratic F n :=
  match p with
  | .node a b c => add (add a (scale r b)) (scale (r * r) c)

theorem eval_restrict (p : Quadratic F (n + 1)) (r : F) (tail : Fin n → F) :
    (p.restrict r).eval tail = p.eval (Fin.cons r tail) := by
  cases p
  simp [restrict, eval_add, eval_scale, eval, Function.comp_def]

def booleanSum (p : Quadratic F n) : F := cubeSum n p.eval

theorem booleanSum_add (p q : Quadratic F n) :
    (add p q).booleanSum = p.booleanSum + q.booleanSum := by
  change cubeSum n (fun point => (add p q).eval point) = _
  simp only [eval_add, cubeSum_add]
  rfl

theorem booleanSum_scale (r : F) (p : Quadratic F n) :
    (scale r p).booleanSum = r * p.booleanSum := by
  change cubeSum n (fun point => (scale r p).eval point) = _
  simp only [eval_scale, cubeSum_scale]
  rfl

theorem booleanSum_split (p : Quadratic F (n + 1)) :
    p.booleanSum = (p.restrict 0).booleanSum + (p.restrict 1).booleanSum := by
  change cubeSum n (fun tail => p.eval (Fin.cons 0 tail)) +
      cubeSum n (fun tail => p.eval (Fin.cons 1 tail)) =
    cubeSum n (fun tail => (p.restrict 0).eval tail) +
      cubeSum n (fun tail => (p.restrict 1).eval tail)
  simp only [eval_restrict]

theorem booleanSum_restrict (a b c : Quadratic F n) (r : F) :
    ((node a b c).restrict r).booleanSum =
      a.booleanSum + r * b.booleanSum + (r * r) * c.booleanSum := by
  simp only [restrict, booleanSum_add, booleanSum_scale]

/-- Materialize an initial segment in its declared order. The final coordinate
array is independent of the later query, which is supplied only to evaluation. -/
def materialize : (m : Nat) → Quadratic F (n + m) → (Fin m → F) → Quadratic F n
  | 0, p, _ => p
  | m + 1, p, fixed => materialize m (p.restrict (fixed 0)) (fixed ∘ Fin.succ)

/-- Independently evaluate by substituting the same ordered fixed on demand. -/
def recompute : (m : Nat) → Quadratic F (n + m) → (Fin m → F) → (Fin n → F) → F
  | 0, p, _, tail => p.eval tail
  | m + 1, .node a b c, fixed, tail =>
      recompute m a (fixed ∘ Fin.succ) tail +
      fixed 0 * recompute m b (fixed ∘ Fin.succ) tail +
      (fixed 0 * fixed 0) * recompute m c (fixed ∘ Fin.succ) tail

/-- The full point follows the fixed in the order in which it is substituted. -/
def point : (m : Nat) → (Fin m → F) → (Fin n → F) → Fin (n + m) → F
  | 0, _, tail => tail
  | m + 1, fixed, tail => Fin.cons (fixed 0) (point m (fixed ∘ Fin.succ) tail)

theorem recompute_eval (m : Nat) (p : Quadratic F (n + m))
    (fixed : Fin m → F) (tail : Fin n → F) :
    recompute m p fixed tail = p.eval (point m fixed tail) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      cases p
      simp [recompute, point, eval, ih, Function.comp_def]

theorem materialize_eval (m : Nat) (p : Quadratic F (n + m))
    (fixed : Fin m → F) (tail : Fin n → F) :
    (materialize m p fixed).eval tail = p.eval (point m fixed tail) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [materialize, ih, eval_restrict, point]

theorem materialize_recompute (m : Nat) (p : Quadratic F (n + m))
    (fixed : Fin m → F) (tail : Fin n → F) :
    (materialize m p fixed).eval tail = recompute m p fixed tail := by
  rw [materialize_eval, recompute_eval]

end Quadratic
end Zkc.Polynomial
