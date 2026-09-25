import Tools.Interactive.ReferenceRuntime
import Tools.Interactive.ReferenceAdmission
import Tests.Checks

/-! Executable independent resource-unit nominal and ownership discriminators.
No native/compiler result is used to select the expected signatures or failures. -/
set_option autoImplicit false
namespace Tests.ResourceUnit
open Tools.Interactive Tools.Interactive.Reference

private def request (contract : String) : Result TypedLocal.Request :=
  TypedLocal.resolveRequest [⟨"op", contract, ["Slot.A"], ""⟩] "site" "op" []

private def exercise : RunM Unit := do
  let location := Location.plain "session" "root" "unit" "P"
  let value ← createResourceUnit location "Slot.A"
  let passed ← compute location (← checked location (request "resource_unit.pass")) [value]
  let [next] := passed | failAt location "refused" "test-arity"
  let result ← compute location (← checked location (request "resource_unit.consume")) [next]
  require location result.isEmpty "test-unit-result"
  require location (← get).resources.isEmpty "test-consumed"

private def aliasUse : RunM Unit := do
  let location := Location.plain "session" "root" "unit" "P"
  let value ← createResourceUnit location "Slot.A"
  recordBoundary location [value, value]
  activateRole "P"

private def stale : RunM Unit := do
  let location := Location.plain "session" "root" "unit" "P"
  let value ← createResourceUnit location "Slot.A"
  let _ ← compute location (← checked location (request "resource_unit.pass")) [value]
  let _ ← compute location (← checked location (request "resource_unit.consume")) [value]
  pure ()

private def wrongOwner : RunM Unit := do
  let location := Location.plain "session" "root" "unit" "P"
  let value ← createResourceUnit location "Slot.A"
  recordBoundary (Location.plain "session" "root" "unit" "V") [value]
  activateRole "V"

private def errorCode (action : RunM Unit) : String :=
  match (action.run {}).1 with | .error fault => fault.detail | .ok _ => "success"

def run : IO Unit := do
  let checks ← Tests.Checks.start
  checks.holds (affine "resource_unit:Slot.A" && !duplicable "resource_unit:Slot.A" &&
    discardable "resource_unit:Slot.A" && !serializable "resource_unit:Slot.A") "permissions"
  checks.holds ((Bindings.valueType false "resource_unit:Slot.A").isOk) "nominal-logical"
  checks.holds ((Bindings.valueType true "resource_unit:Slot.A@logical.resource_unit/1").isOk) "nominal-physical"
  checks.holds (!(Bindings.valueType true "resource_unit:Slot.A@host.resource/1").isOk) "wrong-representation"
  checks.holds (!(Bindings.valueType false "resource_unit:0bad").isOk) "bad-domain"
  checks.holds (!(Bindings.resolve true ⟨"op", "resource_unit.create", ["Slot.A"], "arkworks/resource_unit.create"⟩).isOk) "wrong-provider"
  checks.holds (errorCode exercise == "success") "create-pass-consume"
  checks.holds (errorCode aliasUse == "capability-alias") "alias-refusal"
  checks.holds (errorCode stale == "capability-stale") "stale-refusal"
  checks.holds (errorCode wrongOwner == "capability-domain") "owner-refusal"
  let value := Value.resourceUnit "Slot.A" "unit" 0
  checks.holds (!value.public && value.size == 0 && !value.wire.isOk) "zero-payload-no-codec"
  checks.finish "logical resource-unit admission and execution"

#eval run
end Tests.ResourceUnit
