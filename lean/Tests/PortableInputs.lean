import Tools.Interactive.ReferenceAdmission

/-! Entry resource aliases and cross-role use are rejected independently of
body execution. Immutable key identities may be shared by both roles. -/
set_option autoImplicit false
namespace Tests.PortableInputs
open Tools.Interactive Tools.Interactive.Reference

private def location (role : String) : Location :=
  ⟨"session", "main", ⟨"root", [], "entry", role⟩, none, #[]⟩

private def boundary (role : String) (resource : Resource) (values : List Value) : String :=
  let action : RunM Unit := do
    recordBoundary (location role) values
    activateRole role
  match (action.run { resources := [resource] }).1 with
  | .error fault => fault.detail
  | .ok _ => "ok"

example : boundary "P" ⟨"coins", "P", none, 2, .rng [3], 0, 0⟩
    [.rng "coins" 0, .rng "coins" 0] = "capability-alias" := by native_decide
example : boundary "P" ⟨"nonce", "P", none, 2, .nonce (.issued 7), 0, 0⟩
    [.nonce "nonce" 0, .nonce "nonce" 0] = "capability-alias" := by native_decide
example : boundary "V" ⟨"coins", "P", none, 2, .rng [3], 0, 0⟩
    [.rng "coins" 0] = "capability-domain" := by native_decide

private def sharedKey : Bool :=
  let key : CommitmentIdentity := ⟨2, ByteArray.mk (Array.replicate 32 0), ByteArray.mk (Array.replicate 32 0)⟩
  let action : RunM Unit := do
    recordBoundary (location "P") [.verifierKey key]
    activateRole "P"
    recordBoundary (location "V") [.verifierKey key]
    activateRole "V"
  (action.run { setupKeys := [("P", [key]), ("V", [key])] }).1.isOk
example : sharedKey = true := by native_decide
end Tests.PortableInputs
