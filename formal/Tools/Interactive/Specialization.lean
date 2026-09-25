import Tools.Interactive.Configuration
import Tools.Interactive.Explicit

/-! Nominal specialization for independent source meaning. Callable names remain
the source configuration names; private binding names have no semantic role. -/

set_option autoImplicit false

namespace Tools.Interactive.Generic

private def freshBinding (used : Std.HashSet Name) (next : Nat) : Result (Name × Nat) := do
  for i in [next:next + used.size + 1] do
    let name := s!"reference_binding_{i}"
    if !(used.contains name) then return (name, i + 1)
  throw "reference-symbol-limit"

private def restoreControl (operations : List Instruction) : Nat → List Instruction → Result (List Instruction)
  | 0, _ => .error "body-depth-limit"
  | depth + 1, code => code.mapM fun instruction => do
      match instruction with
      | .op site _ _ _ _ =>
        lookup site (operations.filterMap fun i => match i with
          | .op site .. | .call site .. => some (site, i) | _ => none)
      | .localMatch site input captures arms outputs =>
        return .localMatch site input captures (← arms.mapM fun (label, payload, nested) => do
          return (label, payload, ← restoreControl operations depth nested)) outputs
      | .conditional site condition captures yes no outputs =>
        return .conditional site condition captures (← restoreControl operations depth yes) (← restoreControl operations depth no) outputs
      | .forLoop site induction lower upper carried captures nested outputs =>
        return .forLoop site induction lower upper carried captures (← restoreControl operations depth nested) outputs
      | other => return other

def specialize (configuration : Configuration) (checked : CheckedDefinition)
    (reserved : List Name := []) (callees : List (Name × Name) := []) : Result (Explicit.Function × List OperationBinding) := do
  let definition := checked.definition
  ensure (configuration.definition == definition.name) "generic-configuration-definition"
  consistent checked configuration.arguments
  let args ← configuration.closedArguments definition
  let arguments ← definition.arguments.mapM fun (name, ty) => do
    return (name, (← specializeType args ty).spelling)
  let results ← definition.results.mapM fun ty => do return (← specializeType args ty).spelling
  let mut bindings := []
  let mut body := []
  let mut used : Std.HashSet Name := Std.HashSet.ofList reserved
  let mut next := 0
  for op in definition.operations do
    if op.application then
      body := body ++ [.call op.site (← lookup op.site callees) op.inputs op.outputs]
      continue
    let (name, successor) ← freshBinding used next
    used := used.insert name
    next := successor
    let binding := OperationBinding.mk name op.contract (← op.arguments.mapM (termIdentity args))
      ((configuration.implementations.lookup op.site).getD "")
    let _ ← Bindings.resolve false binding
    let attrs ← if op.contract == "field.constant" || op.contract == "vector.constant" then do
        if op.contract == "field.constant" then
          ensure (op.attributes.length == 1) "generic-field-literal"
        let modulus ← Bindings.scalarModulus (binding.arguments.headD "")
        op.attributes.mapM fun text => do
          let some value := text.toNat? | throw "generic-field-literal"
          pure (toString (value % modulus))
      else pure op.attributes
    bindings := bindings ++ [binding]
    body := body ++ [.op op.site name attrs op.inputs op.outputs]
  let code := Tools.Interactive.Function.mk configuration.name arguments results (some (← restoreControl body limits.depth definition.instructions))
  return (⟨code, some ⟨definition.name, args⟩⟩, bindings)

end Tools.Interactive.Generic
