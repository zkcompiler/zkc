import ZkcSecurity.Bindings.Gkr.RoundsReference
import ZkcSecurity.Families.Sumcheck.Round
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

open OracleComp OracleSpec
open scoped ENNReal

/-- Use the very same escape theorem as the endpoint-pair Sumcheck client.
The GKR author supplies the gate reference invariant. The installed triple
decoder already supplies the attacker's polynomial and its degree. -/
theorem gate_arbitrary_triple {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {n : Nat} (state : State F (n + 1)) (allowed : admissible state) (claim : F)
    (wrong : claim ≠ total state) (triple : F × F × F)
    (checked : (ZkcSecurity.Families.Sumcheck.Message.coefficientTriples F).boundary triple = claim) :
    Pr{let r ← $ᵗ F}[(ZkcSecurity.Families.Sumcheck.Message.coefficientTriples F).evaluate triple r =
      total (restrict state r)] ≤ 2 / (Fintype.card F : ℝ≥0∞) := by
  simpa only [data, max_self, Nat.cast_ofNat] using
    ZkcSecurity.Families.Sumcheck.escape_uniform_le laws ZkcSecurity.Families.Sumcheck.Message.coefficientTriples_laws
      state allowed claim wrong triple checked

#print axioms gate_arbitrary_triple
#print axioms ZkcSecurity.Examples.Components.GkrRoundsReference.laws
end TestsSecurity.GkrRoundsReference
