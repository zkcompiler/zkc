import Zkc.Polynomial.Multilinear

/-! Source meaning for sums of ordered table-factor occurrences.

The source accepts arbitrary factor lists. This reference compiler accepts at
most two occurrences per term, including repeated identifiers. Refusal of a
longer list is a limitation of this degree-two profile, not a semantic error.
-/

set_option autoImplicit false

namespace Zkc.Polynomial.TableExpression

open Multilinear

abbrev Term (F J : Type) := F × List J
abbrev Expression (F J : Type) := List (Term F J)

variable {F J : Type} [CommRing F] {n : Nat}

def factors (tables : J → Table F n) (point : Fin n → F) : List J → F
  | [] => 1
  | j :: rest => extension n (tables j) point * factors tables point rest

def eval (tables : J → Table F n) (point : Fin n → F) : Expression F J → F
  | [] => 0
  | (coefficient, occurrences) :: rest =>
      coefficient * factors tables point occurrences + eval tables point rest

def sum (tables : J → Table F n) (source : Expression F J) : F :=
  cubeSum n (fun point => eval tables point source)

def compileFactors (tables : J → Table F n) : List J → Option (Quadratic F n)
  | [] => some (coefficients n (fun _ => 1))
  | [j] => some (coefficients n (tables j))
  | [j, k] => some (productCoefficients n (tables j) (tables k))
  | _ => none

theorem compileFactors_eval (tables : J → Table F n) (occurrences : List J)
    (p : Quadratic F n) (accepted : compileFactors tables occurrences = some p)
    (point : Fin n → F) : p.eval point = factors tables point occurrences := by
  cases occurrences with
  | nil =>
      cases accepted
      simp [factors, coefficients_eval, extension_one]
  | cons j rest =>
      cases rest with
      | nil =>
          cases accepted
          simp [factors, coefficients_eval]
      | cons k rest =>
          cases rest with
          | nil =>
              cases accepted
              simp [factors, productCoefficients_eval]
          | cons l rest => contradiction

def compile (tables : J → Table F n) : Expression F J → Option (Quadratic F n)
  | [] => some ((coefficients n (fun _ => 1)).scale 0)
  | (coefficient, occurrences) :: rest => do
      let term ← compileFactors tables occurrences
      let tail ← compile tables rest
      return Quadratic.add (term.scale coefficient) tail

theorem compile_eval (tables : J → Table F n) (source : Expression F J)
    (p : Quadratic F n) (accepted : compile tables source = some p)
    (point : Fin n → F) : p.eval point = eval tables point source := by
  induction source generalizing p with
  | nil =>
      cases accepted
      simp [Quadratic.eval_scale, eval]
  | cons term rest ih =>
      rcases term with ⟨coefficient, occurrences⟩
      cases termCompiled : compileFactors tables occurrences with
      | none => simp [compile, termCompiled] at accepted
      | some term =>
          cases tailCompiled : compile tables rest with
          | none => simp [compile, termCompiled, tailCompiled] at accepted
          | some tail =>
              simp [compile, termCompiled, tailCompiled] at accepted
              subst p
              simp only [Quadratic.eval_add, Quadratic.eval_scale, eval,
                compileFactors_eval tables occurrences term termCompiled point,
                ih tail tailCompiled]

theorem compile_sum (tables : J → Table F n) (source : Expression F J)
    (p : Quadratic F n) (accepted : compile tables source = some p) :
    p.booleanSum = sum tables source := by
  unfold Quadratic.booleanSum sum
  congr 1
  funext point
  exact compile_eval tables source p accepted point

/-- The same declared input cells feed both source meaning and compilation. -/
def inputTables (values : J → Fin (2 ^ n) → F) : J → Table F n :=
  fun j => ofVector (values j)

theorem input_cell (values : J → Fin (2 ^ n) → F) (j : J) (position : Fin (2 ^ n)) :
    extension n (inputTables values j) (booleanPoint (vertex n position)) = values j position := by
  rw [extension_boolean, inputTables, ofVector_vertex]

end Zkc.Polynomial.TableExpression
