import Clean.Circuit.Operations

/-! Flatten Clean operations by structural recursion. Upstream
`NestedOperations.toFlat` is well-founded recursion, which the kernel does not
evaluate on concrete circuits. This flattening does, and `flatten_eq_toFlat`
identifies it with upstream `Operations.toFlat`; every semantic statement of
this package is phrased with the upstream definitions.
-/

set_option autoImplicit false

namespace ZkcClean

section Nested

variable {F : Type}

mutual
def flattenNested : NestedOperations F → List (FlatOperation F)
  | .single operation => [operation]
  | .nested group => flattenGroup group

def flattenGroup : String × List (NestedOperations F) → List (FlatOperation F)
  | (_, children) => flattenChildren children

def flattenChildren : List (NestedOperations F) → List (FlatOperation F)
  | [] => []
  | child :: rest => flattenNested child ++ flattenChildren rest
end

mutual
theorem flattenNested_eq : (nested : NestedOperations F) →
    flattenNested nested = nested.toFlat
  | .single operation => by rw [flattenNested, NestedOperations.toFlat]
  | .nested group => by rw [flattenNested, flattenGroup_eq group]

theorem flattenGroup_eq : (group : String × List (NestedOperations F)) →
    flattenGroup group = (NestedOperations.nested group).toFlat
  | (name, children) => by
      rw [flattenGroup, flattenChildren_eq children, NestedOperations.toFlat]

theorem flattenChildren_eq : (children : List (NestedOperations F)) →
    flattenChildren children = children.flatMap NestedOperations.toFlat
  | [] => rfl
  | child :: rest => by
      rw [flattenChildren, flattenNested_eq child, flattenChildren_eq rest, List.flatMap_cons]
end

end Nested

variable {F : Type} [FiniteField F]

/-- `Operations.toFlat` with the structural nested flattening. -/
def flatten : Operations F → List (FlatOperation F)
  | [] => []
  | .witness m compute :: rest => .witness m compute :: flatten rest
  | .assert e :: rest => .assert e :: flatten rest
  | .lookup l :: rest => .lookup l :: flatten rest
  | .interact i :: rest => .interact i :: flatten rest
  | .subcircuit s :: rest => flattenNested s.ops ++ flatten rest

theorem flatten_eq_toFlat (operations : Operations F) :
    flatten operations = operations.toFlat := by
  induction operations using Operations.induct with
  | empty => rfl
  | witness m compute rest ih => rw [flatten, ih, Operations.toFlat_witness]
  | assert e rest ih => rw [flatten, ih, Operations.toFlat_assert]
  | lookup l rest ih => rw [flatten, ih, Operations.toFlat_lookup]
  | interact i rest ih => rw [flatten, ih, Operations.toFlat_interact]
  | subcircuit s rest ih => rw [flatten, ih, flattenNested_eq, Operations.toFlat_subcircuit]

theorem constraints_flatten (operations : Operations F) :
    FlatOperation.constraints (flatten operations) = operations.constraints := by
  rw [flatten_eq_toFlat, Operations.constraints_toFlat]

theorem lookups_flatten (operations : Operations F) :
    FlatOperation.lookups (flatten operations) = operations.lookups := by
  rw [flatten_eq_toFlat, Operations.lookups_toFlat]

theorem interactions_flatten (operations : Operations F) :
    FlatOperation.interactions (flatten operations) = operations.interactions := by
  rw [flatten_eq_toFlat, Operations.interactions_toFlat]

end ZkcClean
