import Tests.MathematicalResolvedTypes

set_option autoImplicit false
namespace Tests.MathematicalRoleInstantiation
open Zkc.Source.Mathematical

def parent : RoleResolution.Binding := ⟨[4, 1, 3], by decide⟩

def composition : Except String (List Nat) :=
  (do
    let module ← RoleResolution.initial 5
    let caller ← RoleResolution.compose module 3 [⟨4⟩, ⟨1⟩, ⟨3⟩]
    let callee ← RoleResolution.compose caller.binding 2 [⟨1⟩, ⟨0⟩]
    return callee.binding.roles).run' 1000

private def asString {α E : Type} [Repr E] (action : StateT Nat (Except E) α) : StateT Nat (Except String) α :=
  fun remaining => (action remaining).mapError (fun error => toString (repr error))

def port (roles : List (Raw.Reference .role)) : Except String (List Nat × Bool) :=
  (show StateT Nat (Except String) (List Nat × Bool) from do
    let table ← asString (TypeAdmission.declarations MathematicalTypes.emptyMeaning (fun _ => false)
      MathematicalResolvedTypes.templates)
    let result ← asString (PortAdmission.instantiate MathematicalTypes.emptyMeaning table
      (fun _ : Fin 1 => (.literal ⟨8, by decide⟩ : Static.Expression 0)) parent
      ⟨roles, ⟨⟨1⟩, [.parameter 0]⟩⟩)
    let closed ← asString (TypeAdmission.use MathematicalTypes.emptyMeaning table 0 ⟨⟨1⟩, [.literal 8]⟩)
    return (result.port.roles, decide (result.port.ty = closed.expanded.shape))).run' 1000000

-- Instantiated role availability is exactly the image of the written local
-- availability. This does not rely on a monotone caller role tuple.
example {domains meaning rawTypes table arity target parameters binding source}
    (checked : PortAdmission.Instantiated (domains := domains) meaning (rawTypes := rawTypes) table
      (arity := arity) (target := target) parameters binding source) (role : Nat) :
    role ∈ checked.port.roles ↔ ∃ reference ∈ source.roles, binding.roles[reference.index]? = some role :=
  checked.image role

def refusal (arity : Nat) (roles : List (Raw.Reference .role)) (code : String) : Bool :=
  match (RoleResolution.compose parent arity roles).run' 1000 with
  | .error error => error == code
  | .ok _ => false

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds (match composition with | .ok roles => roles == [1, 4] | .error _ => false)
    "compose two positional role bindings"
  checks.holds (match port [⟨0⟩, ⟨2⟩] with | .ok (roles, same) => roles == [3, 4] && same | .error _ => false)
    "sort the availability image and substitute the type"
  checks.holds (match port [] with | .ok (roles, same) => roles.isEmpty && same | .error _ => false)
    "empty availability survives instantiation"
  checks.holds (!(port [⟨2⟩, ⟨0⟩]).isOk) "sorting the image cannot repair malformed local availability"
  checks.holds (!(port [⟨3⟩]).isOk) "port role outside the definition's local scope"
  checks.holds (refusal 2 [⟨1⟩, ⟨1⟩] "role-alias") "role bindings must remain injective"
  checks.holds (refusal 2 [⟨0⟩] "role-arity") "exact callee role arity"
  checks.holds (refusal 1 [⟨3⟩] "role-scope") "role binding cannot add a foreign role"
  checks.holds (!(RoleResolution.initial 1000000000 |>.run' 1000).isOk)
    "module role allocation charges its size first"
  checks.finish "mathematical role and port instantiation"

#eval run
end Tests.MathematicalRoleInstantiation
