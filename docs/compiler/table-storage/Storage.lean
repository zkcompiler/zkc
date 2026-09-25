import Mathlib.Data.Nat.Basic
import Lean

/-! Logical handle-resolution obligations for C1. This is not a Rust heap model.
The native relation must additionally validate sort, layout and payload meaning. -/
set_option autoImplicit false
namespace C1Storage

structure Handle where
  session : Nat
  slot : Nat
  generation : Nat
  deriving DecidableEq, Repr

structure Entry (A : Type) where
  generation : Nat
  payload : A

structure Arena (A : Type) where
  session : Nat
  slots : Nat → Option (Entry A)

def resolve {A : Type} (arena : Arena A) (handle : Handle) : Option A := do
  if arena.session ≠ handle.session then none
  else
    let entry ← arena.slots handle.slot
    if entry.generation = handle.generation then some entry.payload else none

def Represents {A : Type} (arena : Arena A) (handle : Handle) (value : A) : Prop :=
  resolve arena handle = some value

theorem foreign_refused {A : Type} (arena : Arena A) (handle : Handle)
    (foreign : arena.session ≠ handle.session) : resolve arena handle = none := by
  simp [resolve, foreign]

theorem stale_refused {A : Type} (arena : Arena A) (handle : Handle) (entry : Entry A)
    (present : arena.slots handle.slot = some entry)
    (stale : entry.generation ≠ handle.generation) : resolve arena handle = none := by
  simp [resolve, present, stale]

theorem live_resolves {A : Type} (arena : Arena A) (handle : Handle) (entry : Entry A)
    (session : arena.session = handle.session)
    (present : arena.slots handle.slot = some entry)
    (generation : entry.generation = handle.generation) :
    Represents arena handle entry.payload := by
  simp [Represents, resolve, session, present, generation]

/-- Every surviving alias needs this frame, not just the operation's new result. -/
theorem frame {A : Type} (before after : Arena A) (handle : Handle) (value : A)
    (session : before.session = after.session)
    (slot : before.slots handle.slot = after.slots handle.slot)
    (old : Represents before handle value) : Represents after handle value := by
  simpa [Represents, resolve, ← session, ← slot] using old

def sample : Arena Nat := ⟨4, fun slot => if slot = 0 then some ⟨8, 17⟩ else none⟩
theorem valid_control : resolve sample ⟨4, 0, 8⟩ = some 17 := by decide
theorem foreign_control : resolve sample ⟨5, 0, 8⟩ = none := by decide
theorem stale_control : resolve sample ⟨4, 0, 7⟩ = none := by decide
theorem missing_control : resolve sample ⟨4, 1, 8⟩ = none := by decide

end C1Storage

run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if (`C1Storage).isPrefixOf name then
      count := count + 1
      if info.isTheorem then theorems := theorems + 1
      for axiomName in ← Lean.collectAxioms name do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "C1 storage unexpected axiom: {name}: {axiomName}"
  unless count > 0 ∧ theorems > 0 do throwError "C1 storage empty audit"
  Lean.logInfo m!"C1-STORAGE-AUDIT-PASS declarations={count} theorems={theorems}"
