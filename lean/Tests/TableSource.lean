import Zkc.Protocols.Sumcheck.TableSource
import Mathlib.Algebra.Field.ZMod

/-! Table inputs, axis order, multiplicity and complete execution controls. -/

set_option autoImplicit false

namespace Tests.TableSource

open PIR Zkc.Polynomial Zkc.Protocols.Sumcheck
open Multilinear TableExpression
open Zkc.Protocols.AlgebraicRounds (Message)

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
abbrev F := ZMod 5

def values : Unit → Fin (2 ^ 1) → F := fun _ i => if i.val = 0 then 0 else 1
def square : Expression F Unit := [(1, [(), ()])]
def sourcePolynomial : Quadratic F 1 :=
  (compile (inputTables values) square).get (by rfl)

theorem compiled : compile (inputTables values) square = some sourcePolynomial := rfl

example : sourcePolynomial.eval (fun _ => 2) = 4 := by decide

/-- Deduplicating occurrences changes the original polynomial away from the cube. -/
example : eval (inputTables values) (fun _ => 2) square = 4 ∧
    eval (inputTables values) (fun _ => 2) [(1, [()])] = 2 := by decide

/-- Extending the pointwise product also loses the square, despite Boolean agreement. -/
example : extension 1 (fun bits => inputTables values () bits * inputTables values () bits)
    (fun _ => 2) = 2 := by decide

example : compile (inputTables values) [(1, [(), (), ()])] = none := rfl

def distinctCells : Fin (2 ^ 2) → F := fun i => i.val

/-- The first axis selects the half; swapping axes accesses another actual cell. -/
example : ofVector distinctCells (Fin.cons true (Fin.cons false Fin.elim0)) = 2 ∧
    ofVector distinctCells (Fin.cons false (Fin.cons true Fin.elim0)) = 1 := by decide

def send (state : Nat) : Message F × Nat := (⟨0, 0, 1⟩, state + 1)
def react (state : Nat) (_ : F) : Nat := state + 10

example : TableSource.run values square send react 1 0 [2, 3] =
    ⟨.returned true, (11, [3]), [.message ⟨0, 0, 1⟩, .challenge 2]⟩ := by rfl

/-- A stopped draw retains the already issued message and changed prover state. -/
example : TableSource.run values square send react 1 0 [] =
    ⟨.stopped .exhausted, (1, []), [.message ⟨0, 0, 1⟩]⟩ := by rfl

example : TableSource.run values square send react 2 0 [2, 3] =
    ⟨.stopped .reject, (1, [2, 3]), [.message ⟨0, 0, 1⟩, .reject]⟩ := by rfl

example : TableSource.run values [(1, [(), (), ()])] send react 1 0 [2, 3] =
    ⟨.stopped .refused, (0, [2, 3]), []⟩ := rfl

/-- A zero-dimensional table still contains its one actual constant cell. -/
example : TableSource.run (n := 0) (fun (_ : Unit) _ => (3 : F)) [(1, [()])]
    send react 3 0 [2] = ⟨.returned true, (0, [2]), []⟩ := by rfl

/-- The empty sum and empty product have different meanings. -/
example : TableSource.run values [] send react 0 0 [2] =
    ⟨.stopped .reject, (1, [2]), [.message ⟨0, 0, 1⟩, .reject]⟩ := by rfl
example : eval (inputTables values) (fun _ => 2) [] = 0 ∧
    eval (inputTables values) (fun _ => 2) [(1, [])] = 1 := by decide

/-- The false-statement premise uses the actual source, not an unrelated coefficient input. -/
example (claim : F) (falseClaim : claim ≠ sum (inputTables values) square) :
    TableSource.acceptance values square send react claim 0 ≤ (2 * (1 : ℚ)) / Fintype.card F :=
  TableSource.soundness values square sourcePolynomial compiled send react claim 0 falseClaim

end Tests.TableSource
