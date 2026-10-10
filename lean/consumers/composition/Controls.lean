import Composition.Claims
import Composition.Machine
import Mathlib.Algebra.Field.ZMod
import Zkc.Protocols.Sumcheck.Security
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! Kernel-checked controls. The table oracle below is a test terminal, not a
PCS implementation. The machine fixtures exercise the integer encoding. -/

set_option autoImplicit false

namespace Composition.Controls

open Zkc.Polynomial Zkc.Probability Zkc.Protocols.Sumcheck
open Claims Machine

abbrev F := ZMod 17
instance : Fact (Nat.Prime 17) := ⟨by decide⟩

def tables : Bool → Table F 2
  | false => .fork (.fork (.leaf 0) (.leaf 2)) (.fork (.leaf 1) (.leaf 3))
  | true => .fork (.fork (.leaf 1) (.leaf 4)) (.fork (.leaf 2) (.leaf 5))

def point (x y : F) : Fin 2 → F := Fin.cons x (Fin.cons y Fin.elim0)
def firstClaim : Claim Bool F 2 := ⟨false, point 0 1, 2⟩
def secondClaim : Claim Bool F 2 := ⟨true, point 1 0, 2⟩

def oracle (claims : List (Claim Bool F 2)) : Bool :=
  claims.all fun c => decide ((tables c.object).eval c.point = c.value)

theorem oracle_iff (claims : List (Claim Bool F 2)) : oracle claims = true ↔ AllHold tables claims := by
  simp [oracle, List.all_eq_true, AllHold, Holds]

theorem honest_two_points_all_coins (α : F) (coins : AdaptiveTape.Tape F 2) :
    accepted firstClaim secondClaim α (honest (aggregate tables firstClaim secondClaim α)) coins
      ((tables false).eval (tapePoint 2 coins), (tables true).eval (tapePoint 2 coins)) oracle = true :=
  honest_complete tables firstClaim secondClaim (by unfold Holds; decide) α coins oracle
    (fun claims valid => (oracle_iff claims).mpr valid)

theorem two_rounds_receipt :
    ((Claims.rounds 2 (scalar firstClaim secondClaim 3)).run
      (Zkc.Protocols.Sumcheck.Execution.handler Security.honestSend Security.honestReact)
      (⟨2, aggregate tables firstClaim secondClaim 3⟩, [2, 5])).outcome =
      .returned ⟨point 2 5, (aggregate tables firstClaim secondClaim 3).eval (point 2 5)⟩ := by
  erw [show ([2, 5] : List F) = tapeList 2 (2, 5, ()) from rfl, Claims.rounds_outcome,
    Security.honest_strategy]
  have same : scalar firstClaim secondClaim (3 : F) =
      (aggregate tables firstClaim secondClaim 3).booleanSum := by decide
  erw [same, (verify_iff_final _ _ _ _).mp
    (completeness (aggregate tables firstClaim secondClaim 3) (2, 5, ()))]
  rfl

theorem changed_identity_is_false : ¬ Holds tables { firstClaim with object := true } := by unfold Holds; decide

theorem permuted_point_is_false : ¬ Holds tables { firstClaim with point := point 1 0 } := by unfold Holds; decide

theorem dropped_obligation_hides_falsehood :
    AllHold tables [⟨false, point 0 0, 0⟩] ∧
    ¬ AllHold tables [⟨false, point 0 0, 0⟩, ⟨true, point 0 0, 0⟩] := by
  simp [AllHold, Holds, tables, Table.eval, point]

theorem fixed_bad_claims_can_cancel :
    BatchCollision tables { firstClaim with value := 3 } { secondClaim with value := 1 } (1 : F) := by
  constructor
  · unfold Holds; decide
  · decide

theorem adaptive_claims_always_cancel (α : F) :
    BatchCollision (fun _ : Bool => Table.leaf (0 : F))
      ⟨false, Fin.elim0, -α⟩ ⟨true, Fin.elim0, 1⟩ α := by
  constructor
  · simp [Holds, Table.eval]
  · simp [scalar, aggregate_sum, Table.eval]

def badSend (state : Unit) : Zkc.Protocols.AlgebraicRounds.Message F × Unit := (⟨0, 0, 0⟩, state)

theorem bad_boundary_keeps_tape :
    ((Claims.rounds 2 (1 : F)).run
      (Zkc.Protocols.Sumcheck.Execution.handler badSend (fun s _ => s)) ((), [2, 5])).state = ((), [2, 5]) := by
  rfl

theorem second_round_exhaustion_retains_first_challenge :
    let receipt := (Claims.rounds 2 (scalar firstClaim secondClaim 3)).run
      (Zkc.Protocols.Sumcheck.Execution.handler Security.honestSend Security.honestReact)
      (⟨2, aggregate tables firstClaim secondClaim 3⟩, [2])
    receipt.outcome = .stopped .exhausted ∧ receipt.events.length = 3 := by
  constructor <;> rfl

def mem (a b : Nat) : Fin 2 → Nat := Fin.cons a (Fin.cons b Fin.elim0)
def row (pc acc a b : Nat) : Row 2 := ⟨pc, acc, mem a b⟩

def program : List (Instruction 8 2) :=
  [.advice, .add 7, .store 0, .add 1, .branchZero 7, .load 0, .halt, .load 1, .halt]

def statement : Statement 8 2 :=
  ⟨program, 6, 0, Fin.cons 0 (Fin.cons 3 Fin.elim0), 3, Fin.cons 7 (Fin.cons 3 Fin.elim0)⟩

def encoded : EncodedWitness 2 :=
  ⟨0, row 0 0 0 3,
    [row 1 0 0 3, row 2 7 0 3, row 3 7 7 3, row 4 0 7 3, row 7 0 7 3, row 8 3 7 3]⟩

theorem honest_trace_constraints : Constraints statement encoded := by
  constructor
  · decide
  · apply congrArg (Row.mk 0 0)
    funext i
    fin_cases i <;> rfl
  · decide
  · intro r member
    simp only [encoded, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold InRange <;> decide
  · simp only [encoded, List.isChain_cons_cons, List.isChain_singleton, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, 0, by decide, rfl⟩
    · refine ⟨rfl, rfl, ?_⟩
      funext i
      fin_cases i <;> rfl
    · exact ⟨rfl, rfl, 1, by decide, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
  · rfl
  · rfl
  · decide

theorem honest_trace_has_execution : ∃ witness, ValidExecution (by decide : 0 < 8) statement witness :=
  encoding_soundness (by decide) statement encoded honest_trace_constraints

theorem stale_read_rejected : ¬ Local program 0 (row 7 0 7 3) (row 8 0 7 3) := by
  intro h
  have impossible : (0 : Nat) = 3 := h.2.2
  omega

theorem wrong_store_rejected : ¬ Local program 0 (row 2 7 0 3) (row 3 7 0 3) := by
  intro h
  have impossible : (0 : Nat) = 7 := congrFun h.2.2 0
  omega

theorem disconnected_pc_rejected : ¬ Local program 0 (row 4 0 7 3) (row 5 0 7 3) := by
  intro h
  have impossible : (5 : Nat) = 7 := h.1
  omega

theorem wrong_advice_rejected : ¬ Local program 0 (row 0 0 0 3) (row 1 1 0 3) := by
  intro h
  have impossible : (1 : Nat) = 0 := h.2.1
  omega

theorem wrong_carry_rejected : ¬ (7 + 1 = 0 + 8 * (0 : Nat)) := by decide

theorem missing_range_admits_unwrapped_word :
    Local program 0 (row 3 7 7 3) (row 4 8 7 3) ∧ ¬ InRange (W := 8) (row 4 8 7 3) := by
  exact ⟨⟨rfl, rfl, 0, by decide, rfl⟩, by unfold InRange; decide⟩

theorem substituted_program_rejected :
    ¬ Constraints { statement with program := [.halt] } encoded := by
  intro h
  have edge := (List.isChain_cons_cons.mp h.transitions).1
  exact edge

theorem wrong_final_output_rejected : ¬ Constraints { statement with output := 4 } encoded := by
  intro h
  have impossible : (3 : Nat) = 4 := h.output
  omega

theorem wrong_final_memory_rejected :
    ¬ Constraints { statement with finalMemory := fun _ => 0 } encoded := by
  intro h
  have impossible : (7 : Nat) = 0 := congrFun h.memory 0
  omega

theorem insufficient_bound_rejected : ¬ Constraints { statement with bound := 5 } encoded := by
  intro h
  have impossible : 6 ≤ 5 := h.bound
  omega

theorem prefix_is_not_completion :
    ¬ Constraints { statement with bound := 0, output := 0, finalMemory := statement.initialMemory }
      ⟨0, row 0 0 0 3, []⟩ := by
  intro h
  have impossible : some (Instruction.advice : Instruction 8 2) = some .halt := h.halt
  cases impossible

theorem small_constraint_modulus_is_unsound :
    (0 : ZMod 7) + 0 = 7 + (8 : ZMod 7) * 0 ∧
      ¬ (0 + 0 = 7 + 8 * (0 : Nat)) := by
  decide

/-- Injective encoding of each word alone does not rule out wraparound of
the whole addition equation: all four words fit below both 8 and 11. -/
theorem injective_words_still_allow_equation_wrap :
    (7 : ZMod 11) + 7 = 3 + (8 : ZMod 11) * 0 ∧
      ¬ (7 + 7 = 3 + 8 * (0 : Nat)) := by
  decide

end Composition.Controls
