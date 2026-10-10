import Zkc.Compiler.Arithmetic.Dag
import Mathlib.Tactic.Ring

/-! A size obstruction for expanding the existing arithmetic DAG certificates.

This is a theorem about syntax occurrences, not a wall-clock or allocation
benchmark. Physical sharing, recursion strategy and serialization matter too.
-/

set_option autoImplicit false

namespace Improvement.Sharing

open Zkc.Source.LocalArithmetic
open Zkc.Compiler.Arithmetic.Dag

def chain : Nat → DAG
  | 0 => [.input 0]
  | n + 1 => .add 0 0 :: chain n

def tree : Nat → Expr
  | 0 => .input 0
  | n + 1 => .add (tree n) (tree n)

def occurrences : Expr → Nat
  | .lit _ | .input _ | .mem _ => 1
  | .add x y | .mul x y => 1 + occurrences x + occurrences y
  | .mod x _ => 1 + occurrences x

theorem chain_length (n : Nat) : (chain n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [chain, ih]

theorem chain_formed (n : Nat) : wellFormed (chain n) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [chain, wellFormed, bounded, chain_length, ih]

theorem expand_head (n : Nat) : (expand (chain n)).head? = some (tree n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [chain, expand, expandOne, List.head?_cons, tree]
    have head : (expand (chain n))[0]? = some (tree n) := by
      simpa only [List.head?_eq_getElem?] using ih
    rw [head]
    rfl

/-- Raw availability remains linear in the number of graph nodes. This equality
does not turn expanded-root comparison into a sharing-preserving algorithm. -/
theorem raw_inputs (n : Nat) (available : Nat → Bool) :
    (chain n).all (Instr.checkInputs available) = available 0 := by
  induction n with
  | zero => simp [chain, Instr.checkInputs]
  | succ n ih => simp [chain, Instr.checkInputs, ih]

theorem expanded_size (n : Nat) : occurrences (tree n) + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tree, occurrences]
    calc
      1 + occurrences (tree n) + occurrences (tree n) + 1 =
          (occurrences (tree n) + 1) * 2 := by ring
      _ = 2 ^ (n + 1) * 2 := by rw [ih]
      _ = 2 ^ (n + 1 + 1) := (pow_succ _ _).symm

/-- The exponential family satisfies the current checker, including actual
source/site binding and raw input admission. It is not a malformed DAG trick. -/
theorem accepted_family (n : Nat) (source : String)
    (site : Zkc.Semantics.OperationContract.Site) :
    check ⟨source, site, tree n⟩ ⟨source, site, chain n⟩ (fun _ => some 7) = true := by
  simp only [check, chain_formed, expand_head, raw_inputs]
  simp

theorem evaluates_as_doubling (n : Nat) (env : Env) (memory : Memory) :
    (tree n).eval env memory = 2 ^ n * env 0 := by
  induction n with
  | zero => simp [tree, Expr.eval]
  | succ n ih => simp [tree, Expr.eval, ih, pow_succ]; ring

theorem twenty_step_sizes :
    (chain 20).length = 21 ∧ occurrences (tree 20) + 1 = 2097152 := by
  constructor
  · exact chain_length 20
  · simpa using expanded_size 20

end Improvement.Sharing
