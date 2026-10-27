module

public import ZkcSecurity.Families.Proximity.Permutation
public import ZkcSecurity.Commitment.Verifier
public import Zkc.Semantics.Interaction

@[expose] public section

/-! A virtual positional table over the existing committed-table read descriptor.
The word is a logical reference used only in the agreement theorem; executable
access receives a handle and index, never a materialized word. This is an exact
typed `PIR.Process` binding, not a frontend descriptor export or an FRI theorem. -/

set_option autoImplicit false
namespace ZkcSecurity.Realizations.Oracle.Permutation

open ZkcSecurity.Commitment ZkcSecurity.Families.Proximity

variable {J : PIR.Signature} {Shape Value : Type} {size : ℕ}

/-- Finite words as the partial positional tables already used by commitments. -/
def positionalTable (word : Fin size → Value) : Table Value := fun position =>
  if below : position < size then some (word ⟨position, below⟩) else none

@[simp] theorem positionalTable_at (word : Fin size → Value) (index : Fin size) :
    positionalTable word index.val = some (word index) := by
  simp [positionalTable, index.isLt]

/-- Exactly one existing typed read, at the same handle and the permuted index.
There are no base calls, commitments, transcript requests or challenge draws. -/
def read (permutation : Equiv.Perm (Fin size)) (handle : ℕ) (index : Fin size) :
    PIR.Process (committed J Shape Value) Value :=
  .call (.read handle (permutation index).val) .done

theorem read_eq (permutation : Equiv.Perm (Fin size)) (handle : ℕ) (index : Fin size) :
    read (J := J) (Shape := Shape) (Value := Value) permutation handle index =
      .call (.read handle (permutation index).val) .done := rfl

/-- The partial readback square ties the actual input table to the permuted
logical word. The reference table is not an executable parameter. -/
theorem lookup_agrees (permutation : Equiv.Perm (Fin size)) (word : Fin size → Value)
    (tables : List (Table Value)) (handle : ℕ)
    (found : tables[handle]? = some (positionalTable word)) (index : Fin size) :
    lookup tables handle (permutation index).val = some (reindex permutation word index) := by
  simp [lookup, found, reindex]

/-- Honest value simulation through the actual ideal committed-table reading. -/
theorem withTables_read (words : Words J Shape Value)
    (permutation : Equiv.Perm (Fin size)) (word : Fin size → Value)
    (tables : List (Table Value)) (handle : ℕ)
    (found : tables[handle]? = some (positionalTable word)) (index : Fin size) :
    withTables words tables (read permutation handle index) =
      .done (reindex permutation word index) := by
  simp only [read, withTables, lookup_agrees permutation word tables handle found index]

/-- Uniform upper bound on interface reads, independent of all returned values. -/
theorem read_within_one (permutation : Equiv.Perm (Fin size)) (handle : ℕ) (index : Fin size) :
    PIR.Within 1 (read (J := J) (Shape := Shape) (Value := Value) permutation handle index) := by
  intro reply
  trivial

/-- The bound cannot be zero, even when an oracle or a cache already knows the value. -/
theorem read_not_within_zero (permutation : Equiv.Perm (Fin size)) (handle : ℕ)
    (index : Fin size) :
    ¬ PIR.Within 0 (read (J := J) (Shape := Shape) (Value := Value) permutation handle index) :=
  fun impossible => impossible

/-- Exact one-operation simulation retains every handler outcome, stopped
prefix, state and event. The adapter adds nothing around the underlying read. -/
theorem run_read {State Event : Type} (handler : PIR.Handler (committed J Shape Value) State Event)
    (permutation : Equiv.Perm (Fin size)) (handle : ℕ) (index : Fin size) (state : State) :
    (read permutation handle index).run handler state =
      handler (.read handle (permutation index).val) state := by
  exact PIR.Execution.follow_return _

/-- In the ideal reading a live read is pure: all base-handler state, including
any retained cache, and its event trace are preserved, without a No premise. -/
theorem ideal_frame {State Event : Type} (handler : PIR.Handler J State Event)
    (words : Words J Shape Value) (permutation : Equiv.Perm (Fin size))
    (word : Fin size → Value) (tables : List (Table Value)) (handle : ℕ)
    (found : tables[handle]? = some (positionalTable word)) (index : Fin size) (state : State) :
    (withTables words tables (read permutation handle index)).run handler state =
      ⟨.returned (reindex permutation word index), state, []⟩ := by
  rw [withTables_read words permutation word tables handle found index]
  rfl

/-- Missing handles and positions retain the existing rejection semantics. -/
theorem withTables_read_missing (words : Words J Shape Value)
    (permutation : Equiv.Perm (Fin size)) (tables : List (Table Value)) (handle : ℕ)
    (index : Fin size) (missing : lookup tables handle (permutation index).val = none) :
    withTables words tables (read permutation handle index) = .halt .reject := by
  simp only [read, withTables, missing]

end ZkcSecurity.Realizations.Oracle.Permutation
