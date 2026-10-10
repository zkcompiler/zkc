import Zkc.Modules.Installation

set_option autoImplicit false

namespace Zkc.Modules.Allocation
open Zkc.Modules.Factor Zkc.Modules.FactorState Zkc.Modules.FactorBinding Zkc.Modules.Installation
variable {K : Type}

/-- A monotone allocator for this experiment's own names. Nat is unbounded;
    the live allocation quota is checked separately. There is no deallocation. -/
structure Pool where
  next : Nat
  issued : List Nat
  deriving DecidableEq, Repr

def Pool.Good (p : Pool) := ∀ i ∈ p.issued, i < p.next
def empty : Pool := ⟨0,[]⟩
def chosen (p : Pool) : Namespace := ⟨p.next,0⟩
def advance (p : Pool) : Pool := ⟨p.next+1,p.next :: p.issued⟩

theorem empty_good : empty.Good := by simp [Pool.Good,empty]
theorem advance_good (p : Pool) (h : p.Good) : (advance p).Good := by
  intro i hi
  simp only [advance,List.mem_cons] at hi
  rcases hi with rfl | hi
  · simp [advance]
  · have := h i hi; simp only [advance]; omega

theorem chosen_fresh (p : Pool) (h : p.Good) (i : Nat) (hi : i ∈ p.issued) :
    (⟨i,0⟩ : Namespace) ≠ chosen p := by
  intro he
  have eq := congrArg Namespace.instanceId he
  have lt := h i hi
  simp only [chosen] at eq
  omega

def renamed (p : Pool) (r : Request K) : Request K := {r with namespaceId := chosen p}

structure Result (K : Type) where
  pool : Pool
  allocated : Option Namespace
  returned : Returned K Event

/-- Failure consumes no name and changes no World. This policy is proved for
    this pure allocator, not assumed of arbitrary native providers. -/
def allocate (quota capacity : Nat) (p : Pool) (r : Request K) (s : World K) : Result K :=
  if p.issued.length < quota then
    let out := execute capacity (renamed p r) s
    if out.success then ⟨advance p,some (chosen p),out⟩ else ⟨p,none,out⟩
  else ⟨p,none,⟨false,s,[.rejected (chosen p)]⟩⟩

theorem allocation_good (quota capacity : Nat) (p : Pool) (r : Request K) (s : World K)
    (h : p.Good) : (allocate quota capacity p r s).pool.Good := by
  by_cases room : p.issued.length < quota
  · cases hs : (execute capacity (renamed p r) s).success <;>
      simp [allocate,room,hs,advance_good p h,h]
  · simp [allocate,room,h]

theorem allocation_justifies (quota capacity : Nat) (p : Pool) (r : Request K) (s : World K) :
    Justifies ((contract (renamed p r)).post (allocate quota capacity p r s).returned.success)
      s (allocate quota capacity p r s).returned.world := by
  by_cases room : p.issued.length < quota
  · cases hs : (execute capacity (renamed p r) s).success <;>
      simpa [allocate,room,hs] using execute_satisfies capacity (renamed p r) s trivial
  · simpa [allocate,room,contract] using failure_justifies s

theorem execute_success_world (capacity : Nat) (r : Request K) (s : World K)
    (ok : (execute capacity r s).success = true) : (execute capacity r s).world = patch r s := by
  by_cases h : (r.admitted && decide (r.captured.length ≤ capacity)) = true
  · simp only [execute,if_pos h]
  · simp only [execute,if_neg h] at ok
    contradiction

theorem execute_failure_world (capacity : Nat) (r : Request K) (s : World K)
    (no : (execute capacity r s).success = false) : (execute capacity r s).world = s := by
  by_cases h : (r.admitted && decide (r.captured.length ≤ capacity)) = true
  · simp only [execute,if_pos h] at no
    contradiction
  · simp only [execute,if_neg h]

theorem allocation_success (quota capacity : Nat) (p : Pool) (r : Request K) (s : World K)
    (ok : (allocate quota capacity p r s).returned.success = true) :
    (allocate quota capacity p r s).pool = advance p ∧
    (allocate quota capacity p r s).allocated = some (chosen p) ∧
    (allocate quota capacity p r s).returned.world = patch (renamed p r) s := by
  by_cases room : p.issued.length < quota
  · cases hs : (execute capacity (renamed p r) s).success with
    | false => simp [allocate,room,hs] at ok
    | true => simp [allocate,room,hs,execute_success_world capacity (renamed p r) s hs]
  · simp [allocate,room] at ok

theorem allocation_failure (quota capacity : Nat) (p : Pool) (r : Request K) (s : World K)
    (no : (allocate quota capacity p r s).returned.success = false) :
    (allocate quota capacity p r s).pool = p ∧
    (allocate quota capacity p r s).allocated = none ∧
    (allocate quota capacity p r s).returned.world = s := by
  by_cases room : p.issued.length < quota
  · cases hs : (execute capacity (renamed p r) s).success with
    | false => simp [allocate,room,hs,execute_failure_world capacity (renamed p r) s hs]
    | true => simp [allocate,room,hs] at no
  · simp [allocate,room]

theorem allocated_some (quota cap : Nat) (p : Pool) (r : Request K) (s : World K)
    (n : Namespace) (h : (allocate quota cap p r s).allocated = some n) :
    n = chosen p ∧ (allocate quota cap p r s).returned.world = patch (renamed p r) s ∧
      (renamed p r).admitted = true := by
  by_cases room : p.issued.length < quota
  · cases hs : (execute cap (renamed p r) s).success with
    | false => simp [allocate,room,hs] at h
    | true =>
      have hn : n = chosen p := by simpa [allocate,room,hs] using h.symm
      refine ⟨hn,?_,?_⟩
      · simp [allocate,room,hs,execute_success_world cap (renamed p r) s hs]
      · by_cases hg : ((renamed p r).admitted && decide ((renamed p r).captured.length ≤ cap)) = true
        · have hboth : (renamed p r).admitted = true ∧ (renamed p r).captured.length ≤ cap := by simpa using hg
          exact hboth.1
        · simp only [execute,if_neg hg] at hs
          contradiction
  · simp [allocate,room] at h

theorem allocated_none (quota cap : Nat) (p : Pool) (r : Request K) (s : World K)
    (h : (allocate quota cap p r s).allocated = none) :
    (allocate quota cap p r s).returned.world = s := by
  cases hs : (allocate quota cap p r s).returned.success with
  | false => exact (allocation_failure quota cap p r s hs).2.2
  | true => rw [(allocation_success quota cap p r s hs).2.1] at h; contradiction

theorem allocated_some_pool (quota cap : Nat) (p : Pool) (r : Request K) (s : World K)
    (n : Namespace) (h : (allocate quota cap p r s).allocated = some n) :
    (allocate quota cap p r s).pool = advance p := by
  cases hs : (allocate quota cap p r s).returned.success with
  | false => rw [(allocation_failure quota cap p r s hs).2.1] at h; contradiction
  | true => exact (allocation_success quota cap p r s hs).1

theorem allocated_none_pool (quota cap : Nat) (p : Pool) (r : Request K) (s : World K)
    (h : (allocate quota cap p r s).allocated = none) :
    (allocate quota cap p r s).pool = p := by
  cases hs : (allocate quota cap p r s).returned.success with
  | false => exact (allocation_failure quota cap p r s hs).1
  | true => rw [(allocation_success quota cap p r s hs).2.1] at h; contradiction

theorem old_fact_preserved (quota capacity : Nat) (p : Pool) (r : Request K) (s : World K)
    (good : p.Good) (i : Nat) (issued : i ∈ p.issued) (f : Fact)
    (valid : Means s.values (fact ⟨i,0⟩ f)) :
    Means (allocate quota capacity p r s).returned.world.values (fact ⟨i,0⟩ f) := by
  cases h : (allocate quota capacity p r s).returned.success with
  | false => rw [(allocation_failure quota capacity p r s h).2.2]; exact valid
  | true =>
    rw [(allocation_success quota capacity p r s h).2.2]
    exact other_fact_preserved (renamed p r) s ⟨i,0⟩ f (chosen_fresh p good i issued) valid

end Zkc.Modules.Allocation
