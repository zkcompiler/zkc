module

public import Std.Data.HashMap

@[expose] public section

set_option autoImplicit false

/-!
# Interned values

A table that gives each distinct value one number and one stored copy. A closed type and a
static value are compared and hashed by structure; interning them makes the key of a request a
few numbers and lets every use of a type share one object.
-/

namespace Zkc.Frontend

structure Interner (α : Type) [BEq α] [Hashable α] where
  values : Array α := #[]
  index : Std.HashMap α Nat := {}

namespace Interner

variable {α : Type} [BEq α] [Hashable α]

instance : Inhabited (Interner α) := ⟨{}⟩

/-- The number of a value and its stored copy, entering it when it is new. -/
def intern (interner : Interner α) (value : α) : Interner α × Nat × α :=
  match interner.index[value]? with
  | some id => (interner, id, (interner.values[id]?).getD value)
  | none =>
    let id := interner.values.size
    ({ values := interner.values.push value, index := interner.index.insert value id }, id, value)

def find? (interner : Interner α) (value : α) : Option Nat := interner.index[value]?

def get? (interner : Interner α) (id : Nat) : Option α := interner.values[id]?

def size (interner : Interner α) : Nat := interner.values.size

end Interner

end Zkc.Frontend
