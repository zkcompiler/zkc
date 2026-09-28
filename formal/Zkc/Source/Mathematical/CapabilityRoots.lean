import Zkc.Source.Mathematical.Protocol

/-! Certificates tying a closed capability environment to one actual root table.
The generic protocol syntax also serves templates, so this provenance is a
separate closed-subject invariant. Roles in both environments use the same
module coordinates. Binding may weaken permissions but preserves root identity.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.Protocol

variable {Role Service : Type}

/-- Each root's identity is its authored table position. -/
def RootTable (table : List (Capability Role Service)) : Prop :=
  table.map Capability.root = List.range table.length

/-- A capability refers to the service and permissions at its actual root
position. This proof rules out forged services, widened permissions and roots
outside the admitted table. -/
def RootedIn (table : List (Capability Role Service)) (capability : Capability Role Service) : Prop :=
  ∃ entry, table[capability.root]? = some entry ∧ entry.service = capability.service ∧
    ∀ role ∈ capability.roles, role ∈ entry.roles

def Rooted (table capabilities : List (Capability Role Service)) : Prop :=
  ∀ {capability}, Var capabilities capability → RootedIn table capability

private theorem variable_lookup {α : Type} {values : List α} {value : α}
    (reference : Var values value) : values[reference.index]? = some value := by
  induction reference with
  | here => rfl
  | there reference ih => simpa [Var.index] using ih

private theorem variable_bound {α : Type} {values : List α} {value : α}
    (reference : Var values value) : reference.index < values.length := by
  induction reference with
  | here => simp [Var.index]
  | there reference ih => simpa [Var.index] using ih

theorem RootTable.root_index {table : List (Capability Role Service)} (wellFormed : RootTable table)
    {capability} (reference : Var table capability) : capability.root = reference.index := by
  have lookup : (table.map Capability.root)[reference.index]? = some capability.root := by
    simp [List.getElem?_map, variable_lookup reference]
  rw [wellFormed] at lookup
  have bound := variable_bound reference
  simpa [List.getElem?_range, bound] using lookup.symm

theorem RootTable.rooted {table : List (Capability Role Service)} (wellFormed : RootTable table) : Rooted table table := by
  intro capability reference
  refine ⟨capability, ?_, rfl, fun _ member => member⟩
  rw [wellFormed.root_index reference]
  exact variable_lookup reference

theorem RootedIn.service_functional {table : List (Capability Role Service)} {first second}
    (left : RootedIn table first) (right : RootedIn table second) (same : first.root = second.root) :
    first.service = second.service := by
  obtain ⟨entry, lookup, service, _⟩ := left
  obtain ⟨other, selected, otherService, _⟩ := right
  rw [same] at lookup
  have equal := Option.some.inj (lookup.symm.trans selected)
  subst other
  exact service.symm.trans otherService

/-- Permissions and root identities determine the complete environment. -/
theorem capabilities_eq {first second : List (Capability Role Service)}
    (permissions : first.map Capability.toPermission = second.map Capability.toPermission)
    (roots : first.map Capability.root = second.map Capability.root) : first = second := by
  induction first generalizing second with
  | nil => cases second <;> simp_all
  | cons first rest ih =>
      cases second with
      | nil => simp at permissions
      | cons second tail =>
          simp only [List.map_cons, List.cons.injEq] at permissions roots
          have equal : first = second := by
            cases first
            cases second
            simp_all
          exact congr (congrArg List.cons equal) (ih permissions.2 roots.2)

variable {vocabulary : Vocabulary}

theorem CapabilityBindings.roots_eq_indices {table : List (Capability Role vocabulary.Service)}
    {required} (wellFormed : RootTable table)
    (bindings : CapabilityBindings (vocabulary := vocabulary) table required) : bindings.roots = bindings.indices := by
  induction bindings with
  | nil => rfl
  | cons first rest ih =>
      simp only [roots, indices]
      exact congr (congrArg List.cons (wellFormed.root_index first.operand)) ih

theorem CapabilityBindings.bound_rooted {table available : List (Capability Role vocabulary.Service)}
    {required} (rooted : Rooted table available)
    (bindings : CapabilityBindings (vocabulary := vocabulary) available required) : Rooted table bindings.bound := by
  induction bindings with
  | nil => intro capability reference; cases reference
  | cons first rest ih =>
      intro capability reference
      cases reference with
      | here =>
          obtain ⟨entry, lookup, service, permitted⟩ := rooted first.operand
          exact ⟨entry, lookup, service, fun role member => permitted role (first.covers role member)⟩
      | there reference => exact ih reference

theorem CapabilityBindings.bound_eq {available : List (Capability Role vocabulary.Service)}
    {required} (bindings : CapabilityBindings (vocabulary := vocabulary) available required)
    (target : List (Capability Role vocabulary.Service))
    (permissions : target.map Capability.toPermission = required)
    (roots : bindings.roots = target.map Capability.root) : bindings.bound = target :=
  capabilities_eq (bindings.bound_permissions.trans permissions.symm) (bindings.bound_roots.trans roots)

end Zkc.Source.Mathematical.Protocol
