import Tools.Interactive.ReferenceState

/-! Logical resource admission at source boundaries, without physical frame IDs.

Joint traversal can visit a transparent child before its participant is polled.
Record its first invalid boundary, then report it when that role next acts or is
drained at completion. These checks only read role-owned state. No later action
of the same role can execute before the pending failure, and other roles cannot
change that resource. Keeping one fault per role avoids a growing boundary queue.
-/

set_option autoImplicit false

namespace Tools.Interactive.Reference

private def validate (state : State) (location : Location) (values : List Value) : Result Unit := do
  values.forM Value.validate
  let values := values.flatMap Value.leaves
  -- Native value validation runs over all arguments before frame-domain checks.
  for value in values do
    if let some (kind, identity, generation) := value.capability then
      let some resource := state.resources.find? (·.identity == identity) | throw "capability-unissued"
      ensure (resource.generation == generation) "capability-stale"
      ensure (resource.payload.kind == kind) "capability-kind"
      ensure (resource.payload.domain == value.ty.identity) "capability-identity"
    authorized state location.scope.role value
  let mut seen : List Name := []
  for value in values do
    if let some (_, identity, _) := value.capability then
      let some resource := state.resources.find? (·.identity == identity) | throw "capability-unissued"
      ensure (resource.owner == location.scope.role &&
        resource.boundInstance.all (· == location.scope.binding)) "capability-domain"
      ensure (!(seen.contains identity)) "capability-alias"
      seen := identity :: seen

def recordBoundary (location : Location) (values : List Value) : RunM Unit := do
  let state ← get
  if state.pendingFaults.any (fun pair => pair.1 == location.scope.role) then return
  if let .error detail := validate state location values then
    let fault : Fault := ⟨"refused", detail, location⟩
    set { state with pendingFaults := (location.scope.role, fault) :: state.pendingFaults }

def activateRole (role : Name) : RunM Unit := do
  if let some (_, fault) := (← get).pendingFaults.find? (fun pair => pair.1 == role) then throw fault

end Tools.Interactive.Reference
