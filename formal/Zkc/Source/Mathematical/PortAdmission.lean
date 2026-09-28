import Zkc.Source.Mathematical.TypeAdmission
import Zkc.Source.Mathematical.RoleResolution

/-! Canonical role availability and certified type selection for written ports.
Availability is ordered, duplicate-free and bounded by the definition's local
role count. An empty set is a valid value with no available role component.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.PortAdmission

structure Roles (arity lower : Nat) (raw : List (Raw.Reference .role)) where
  values : List Nat
  erasure : values = raw.map (·.index)
  ordered : values.Pairwise (· < ·)
  bounds : ∀ value ∈ values, lower ≤ value ∧ value < arity

inductive Error where
  | resource | role
  | binding (reason : String)
  | type (reason : TypeAdmission.Error)
  deriving DecidableEq, Repr

private def consume (amount : Nat := 1) : StateT Nat (Except Error) Unit := do
  let remaining ← get
  if amount > remaining then throw .resource
  set (remaining - amount)

def roles (arity lower : Nat) : (raw : List (Raw.Reference .role)) →
    StateT Nat (Except Error) (Roles arity lower raw)
  | [] => return ⟨[], rfl, .nil, by simp⟩
  | first :: rest => do
      consume
      if low : lower ≤ first.index then
        if high : first.index < arity then
          let tail ← roles arity (first.index + 1) rest
          return ⟨first.index :: tail.values, by simp [tail.erasure],
            .cons (fun value member => Nat.lt_of_lt_of_le (Nat.lt_succ_self first.index) (tail.bounds value member).1)
              tail.ordered,
            by
              intro value member
              rcases List.mem_cons.mp member with same | member
              · subst value; exact ⟨low, high⟩
              · exact ⟨Nat.le_trans low (Nat.le_trans (Nat.le_succ first.index) (tail.bounds value member).1),
                  (tail.bounds value member).2⟩⟩
        else throw .role
      else throw .role

theorem Roles.nodup {arity lower raw} (checked : Roles arity lower raw) : checked.values.Nodup :=
  checked.ordered.imp (fun bound => Nat.ne_of_lt bound)

structure Decoded {domains : Nat} (meaning : TypeSyntax.Interpretation domains)
    {rawTypes : List Raw.TypeTemplate} (table : TypeAdmission.Table meaning rawTypes)
    (statics roleCount : Nat) (source : Raw.Port) where
  available : Roles roleCount 0 source.roles
  type : TypeAdmission.Decoded meaning table statics source.type

def Decoded.port {domains meaning rawTypes table statics roleCount source}
    (checked : Decoded (domains := domains) meaning (rawTypes := rawTypes) table statics roleCount source) :
    Port Nat (TypeExpansion.Shape domains statics) := ⟨checked.available.values, checked.type.expanded.shape⟩

def decode {domains : Nat} (meaning : TypeSyntax.Interpretation domains)
    {rawTypes : List Raw.TypeTemplate} (table : TypeAdmission.Table meaning rawTypes)
    (statics roleCount : Nat) (source : Raw.Port) :
    StateT Nat (Except Error) (Decoded meaning table statics roleCount source) := do
  let available ← roles roleCount 0 source.roles
  let type ← fun budget => (TypeAdmission.use meaning table statics source.type budget).mapError Error.type
  return ⟨available, type⟩

/-- Canonical local availability and its exact image under a positional role
binding. Ports and capability permissions share this formation rule. -/
structure Availability (binding : RoleResolution.Binding) (source : List (Raw.Reference .role)) where
  available : Roles binding.roles.length 0 source
  mapped : RoleResolution.Composed binding source.length source
  ordered : mapped.binding.participants.Pairwise (· < ·)

theorem Availability.image {binding source} (checked : Availability binding source) (role : Nat) :
    role ∈ checked.mapped.binding.participants ↔
      ∃ reference ∈ source, binding.roles[reference.index]? = some role := by
  simpa [RoleResolution.Binding.participants, RoleResolution.Composed.binding] using
    checked.mapped.selection.image role

def availability (binding : RoleResolution.Binding) (source : List (Raw.Reference .role)) :
    StateT Nat (Except Error) (Availability binding source) := do
  let available ← roles binding.roles.length 0 source
  let mapped ← fun remaining =>
    (RoleResolution.compose binding source.length source remaining).mapError Error.binding
  consume (source.length * (source.length + 1))
  if ordered : mapped.binding.participants.Pairwise (· < ·) then
    return ⟨available, mapped, ordered⟩
  else throw .role

/-- An instantiated port keeps the canonical local availability, the actual
positional role map, and the substituted type with its formation certificate. -/
structure Instantiated {domains : Nat} (meaning : TypeSyntax.Interpretation domains)
    {rawTypes : List Raw.TypeTemplate} (table : TypeAdmission.Table meaning rawTypes)
    {arity target : Nat} (parameters : Fin arity → Static.Expression target)
    (binding : RoleResolution.Binding) (source : Raw.Port) extends Availability binding source.roles where
  type : TypeAdmission.Instantiated meaning table parameters source.type

def Instantiated.port {domains meaning rawTypes table arity target parameters binding source}
    (checked : Instantiated (domains := domains) meaning (rawTypes := rawTypes) table
      (arity := arity) (target := target) parameters binding source) :
    Port Nat (TypeExpansion.Shape domains target) := ⟨checked.mapped.binding.participants, checked.type.expanded.shape⟩

theorem Instantiated.image {domains meaning rawTypes table arity target parameters binding source}
    (checked : Instantiated (domains := domains) meaning (rawTypes := rawTypes) table
      (arity := arity) (target := target) parameters binding source) (role : Nat) :
    role ∈ checked.port.roles ↔ ∃ reference ∈ source.roles, binding.roles[reference.index]? = some role := by
  simpa [Instantiated.port, RoleResolution.Binding.participants, RoleResolution.Composed.binding] using
    checked.mapped.selection.image role

def instantiate {domains : Nat} (meaning : TypeSyntax.Interpretation domains)
    {rawTypes : List Raw.TypeTemplate} (table : TypeAdmission.Table meaning rawTypes)
    {arity target : Nat} (parameters : Fin arity → Static.Expression target)
    (binding : RoleResolution.Binding) (source : Raw.Port) :
    StateT Nat (Except Error) (Instantiated meaning table parameters binding source) := do
  let available ← availability binding source.roles
  let type ← fun remaining =>
    (TypeAdmission.instantiate meaning table parameters source.type remaining).mapError Error.type
  return ⟨available, type⟩

end Zkc.Source.Mathematical.PortAdmission
