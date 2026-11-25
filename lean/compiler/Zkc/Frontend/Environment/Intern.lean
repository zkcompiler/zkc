module

public import Std.Data.TreeMap.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Interned values

A table that gives each distinct value one number and one stored copy. A closed type and a
static value are compared and hashed by structure; interning them makes the key of a request a
few numbers and lets every use of a type share one object.
-/

namespace Zkc.Frontend

/-- Numbered values and hash buckets both use persistent trees. Extending a snapshot copies
only its search paths. Values with the same hash share a bucket and are compared by equality. -/
structure Interner (α : Type) [BEq α] [Hashable α] where
  values : Std.TreeMap Nat α := {}
  index : Std.TreeMap UInt64 (List (α × Nat)) := {}

namespace Interner

variable {α : Type} [BEq α] [Hashable α]

instance : Inhabited (Interner α) := ⟨{}⟩

/-- The number of a value and its stored copy, entering it when it is new. -/
def intern (interner : Interner α) (value : α) : Interner α × Nat × α :=
  let valueHash := hash value
  let bucket := interner.index.getD valueHash []
  match bucket.find? (·.1 == value) with
  | some (stored, id) => (interner, id, stored)
  | none =>
    let id := interner.values.size
    let values := interner.values.insert id value
    let index := interner.index.insert valueHash ((value, id) :: bucket)
    (⟨values, index⟩, id, value)

def find? (interner : Interner α) (value : α) : Option Nat := do
  let bucket ← interner.index[hash value]?
  return (← bucket.find? (·.1 == value)).2

def get? (interner : Interner α) (id : Nat) : Option α := interner.values[id]?

def size (interner : Interner α) : Nat := interner.values.size

end Interner

end Zkc.Frontend
