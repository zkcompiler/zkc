import Zkc.Protocols.ScalarBytecode.Schedules
import Zkc.Realization.InstructionComposition
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.StreamingFamily
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Schedules

def execBlocks (hash : Hash) : List (List Instr) → Tail → Terminal Tail Event :=
  runBlocks (tailStep hash)

theorem flatten_execution (hash : Hash) (blocks : List (List Instr)) (s : Tail) :
    run (tailStep hash) blocks.flatten s = execBlocks hash blocks s :=
  flatten_run_blocks (tailStep hash) (no_incomplete_halt hash) blocks s

def base (i : Nat) := i * (i + 2)

def word (i j : Nat) : List Instr :=
  [⟨base i + 2*j, .read, .binding, .binding, Zkc.Protocols.ScalarBytecode.Parameters.modulus, [], "coefficient", 0⟩,
   ⟨base i + 2*j+1, .absorb, .reg 0, .binding, 0, [], "coefficient", 0⟩]

def round (i : Nat) : List Instr :=
  ((List.range (i+1)).map (word i)).flatten ++
  [⟨base i + 2*(i+1), .draw, .binding, .binding, 0, [], "challenge", 1⟩]

def finish (n : Nat) : List Instr :=
  [⟨base n, .expectEnd, .binding, .binding, 0, [], "end", 0⟩,
   ⟨base n+1, .accept, .binding, .binding, 0, [], "accept", 0⟩]

def blocks (n : Nat) := (List.range n).map round ++ [finish n]
def instantiate (n : Nat) := (blocks n).flatten

/-- Public n changes actual rounds/control. This is a mathematical streaming
    family in Zkc.Protocols.ScalarBytecode.Execution's semantics; no existing Sumcheck generator is claimed. -/
theorem family_execution (n : Nat) (hash : Hash) (s : Tail) :
    run (tailStep hash) (instantiate n) s = execBlocks hash (blocks n) s :=
  flatten_execution hash (blocks n) s

/-- Formation of a typed coefficient uses the same generated word occurrence.
    Each vector member remains an individual read and absorb. -/
def coefficientSite (i : Nat) (j : Fin (i+1)) : Nat := base i + 2*j.val

theorem coefficient_occurrence (i : Nat) (j : Fin (i+1)) :
    (word i j.val).head? = some
      ⟨coefficientSite i j, .read, .binding, .binding, Zkc.Protocols.ScalarBytecode.Parameters.modulus, [], "coefficient", 0⟩ := rfl

theorem round_length (i : Nat) : (round i).length = 2*(i+1)+1 := by
  simp [round, word, List.length_flatten, Function.comp_def, Nat.mul_comm]

theorem base_successor (i : Nat) : base (i+1) = base i + (2*(i+1)+1) := by
  unfold base
  ring

theorem all_sites_contiguous (n : Nat) :
    (instantiate n).map Instr.site = List.range (base n + 2) := by
  -- The constructive occurrence law is proved through each generated range.
  have hw : ∀ i, (round i).map Instr.site =
      (List.range (2*(i+1)+1)).map (fun j => base i+j) := by
    intro i
    simp only [round, List.map_append, List.map_cons, List.map_nil]
    have hwords : ∀ k, (((List.range k).map (word i)).flatten).map Instr.site =
        (List.range (2*k)).map (fun j => base i+j) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
          List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append]
        rw [ih]
        have hk : 2*(k+1) = (2*k+1)+1 := by omega
        rw [hk, List.range_succ, List.range_succ]
        simp [word, List.append_assoc, Nat.add_assoc]
    rw [hwords]
    rw [List.range_succ]
    simp
  have hb : ∀ k, (((List.range k).map round).flatten).map Instr.site = List.range (base k) := by
    intro k
    induction k with
    | zero => simp [base]
    | succ k ih =>
      simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
        List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.map_append]
      rw [ih, hw, base_successor]
      exact List.range_add.symm
  simp only [instantiate, blocks, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.map_append]
  rw [hb]
  simp [finish, List.range_succ, List.append_assoc]

theorem instance_length (n : Nat) : (instantiate n).length = base n + 2 := by
  have h := congrArg List.length (all_sites_contiguous n)
  simpa using h

theorem sites_unique (n : Nat) : ((instantiate n).map Instr.site).Nodup := by
  rw [all_sites_contiguous]
  exact List.nodup_range

/-- A list-cap preflight only. This is not the Foundation cumulative body,
    encoding, schema-depth or evaluator-resource admission check. -/
def boundedInstance (cap n : Nat) : Option (List Instr) :=
  if base n + 2 ≤ cap then some (instantiate n) else none

theorem admitted_list_bound (cap n : Nat) (ops : List Instr)
    (h : boundedInstance cap n = some ops) : ops.length ≤ cap := by
  unfold boundedInstance at h
  split at h
  · cases h
    simpa [instance_length] using ‹base n + 2 ≤ cap›
  · cases h

theorem fixed_sumcheck_blocks (hash : Hash) (s : Tail) :
    run (tailStep hash) sumcheck s =
      execBlocks hash [sumcheck.take 13, sumcheck.drop 13] s := by
  have h := flatten_execution hash [sumcheck.take 13, sumcheck.drop 13] s
  simpa using h

theorem fixed_schnorr_blocks (hash : Hash) (s : Tail) :
    run (tailStep hash) schnorr s =
      execBlocks hash [schnorr.take 5, schnorr.drop 5] s := by
  have h := flatten_execution hash [schnorr.take 5, schnorr.drop 5] s
  simpa using h

def initial (bs : Bytes) : Tail := ⟨bs,0,⟨fun _ => 0,[],0⟩⟩

end Zkc.Protocols.ScalarBytecode.StreamingFamily
