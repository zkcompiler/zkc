import ZkcSecurity.Examples.Components.GkrRoundsReference
import Mathlib.Tactic.NormNum

namespace TestsSecurity.GkrRoundsReference
open Zkc.Polynomial.Multilinear
open ZkcSecurity.Examples.Components.GkrRoundsReference
open Zkc.Protocols.AlgebraicRounds

def bit : Table ℚ 1 := fun point => if point 0 then 1 else 0
def zero : Table ℚ 1 := fun _ => 0
def cubicState : State ℚ 1 := ⟨zero, bit, bit, bit⟩

theorem cubic_refuses : ¬ admissible cubicState := by
  rintro ⟨left | right, _⟩
  · have same := left 1 (fun i => Fin.elim0 i)
    norm_num [cubicState, bit, fixFirst, half] at same
  · have same := right 1 (fun i => Fin.elim0 i)
    norm_num [cubicState, bit, fixFirst, half] at same

theorem cubic_off_cube : (message cubicState).evaluate 2 ≠ total (restrict cubicState 2) := by
  norm_num [message, pointMessage, cubicState, zero, bit, Gate.message,
    Gate.value, Gate.quadratic, Zkc.Protocols.AlgebraicRounds.Message.evaluate,
    total, restrict, booleanSum, fixFirst, half]

theorem zero_prefix (s : State ℚ 1) :
    (data ℚ).restrictPrefix 0 s (fun i => Fin.elim0 i) = s := rfl

theorem arbitrary_prefix {F : Type} [Field F] {n : Nat} (count : Nat)
    (s : State F (n + count)) (challenges : Fin count → F) (allowed : admissible s) :
    (data F).admissible ((data F).restrictPrefix count s challenges) :=
  prefix_admissible count s challenges allowed

#print axioms ZkcSecurity.Examples.Components.GkrRoundsReference.laws
end TestsSecurity.GkrRoundsReference
