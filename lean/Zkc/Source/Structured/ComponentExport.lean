module

public import Zkc.Source.Structured.ComponentRoutes
public import Zkc.Source.Structured.ContractElaboration

@[expose] public section

/-! Strict current-version seam and per-call proposal decoding and checking. -/
namespace Zkc.Source.Structured.ComponentExport
open Lean

structure Export where
  proposals : List CallProposal
  seams : List SeamRow
  deriving Repr

def route : Nat → Json → Except String SeamRoute
  | 0, _ => .error "component-seam-depth"
  | fuel + 1, json => do
    match ← Format.array json with
    | [.str "input", port, role] => return .input (← Format.natural port) (← Format.string role)
    | [.str "result", site, port, role] =>
      return .result (← Format.string site) (← Format.natural port) (← Format.string role)
    | [.str "repeat_input", site, port, role] =>
      return .repeatInput (← Format.string site) (← Format.natural port) (← Format.string role)
    | [.str "repeat_result", site, port, role] =>
      return .repeatResult (← Format.string site) (← Format.natural port) (← Format.string role)
    | [.str "pure", operation, position, port, role, arguments] =>
      return .pure (← Format.descriptor operation) (← Format.refs position)
        (← Format.natural port) (← Format.string role) (← (← Format.array arguments).mapM (route fuel))
    | [.str "terminal", operation, position, port, role, arguments] =>
      return .terminal (← Format.descriptor operation) (← Format.refs position)
        (← Format.natural port) (← Format.string role) (← (← Format.array arguments).mapM (route fuel))
    | [.str "action", operation, position, port, role, arguments] =>
      return .action (← Format.descriptor operation) (← Format.refs position)
        (← Format.natural port) (← Format.string role) (← (← Format.array arguments).mapM (route fuel))
    | _ => throw "component-seam-route"

def endpoint (json : Json) : Except String SeamEndpoint := do
  match ← Format.array json with
  | [.str "argument", site, port] => return .argument (← Format.string site) (← Format.natural port)
  | [.str "output", port, .str "residual"] => return .residual (← Format.natural port)
  | [.str "output", port, clause] => return .output (← Format.natural port) (← Format.natural clause)
  | [.str "guard", site, role] => return .guard (← Format.string site) (← Format.string role)
  | [.str "repeat_init", site, port, role] =>
    return .repeatInit (← Format.string site) (← Format.natural port) (← Format.string role)
    | [.str "repeat_input", site, port, role] =>
      return .repeatInput (← Format.string site) (← Format.natural port) (← Format.string role)
  | [.str "yield", site, port, role] =>
    return .yield (← Format.string site) (← Format.natural port) (← Format.string role)
  | [.str "repeat_result", site, port, role] =>
    return .repeatResult (← Format.string site) (← Format.natural port) (← Format.string role)
  | _ => throw "component-seam-endpoint"

def seam (json : Json) : Except String SeamRow := do
  let [caller, target, kind, routes] ← Format.array json | throw "component-seam-row"
  let kind ← match kind with
    | .str "direct" => pure SeamKind.direct
    | .str "pure" => pure SeamKind.pure
    | .str "terminal" => pure SeamKind.terminal
    | .str "method" => pure SeamKind.method
    | _ => throw "component-seam-kind"
  return ⟨← Format.string caller, ← endpoint target, kind, ← (← Format.array routes).mapM (route 65)⟩

def source : Nat → Json → Except String InstantiationSource
  | 0, _ => .error "component-instantiation"
  | fuel + 1, json => do
    match ← Format.array json with
    | [.str "open"] => return .open
    | [.str "operand", port, role] => return .operand (← Format.natural port) (← Format.string role)
    | [.str "parameter", selector] => return .parameter (← Format.contractSelector selector)
    | [.str "witness", selector] => return .witness (← Format.contractSelector selector)
    | [.str "result", site, port, role] =>
      return .result (← Format.string site) (← Format.natural port) (← Format.string role)
    | [.str "math", helper, port, arguments] =>
      return .math (← Format.string helper) (← Format.natural port)
        (← (← Format.array arguments).mapM (source fuel))
    | _ => throw "component-instantiation"

def slot (json : Json) : Except String InstantiationSlot := do
  let [purpose, selector, value] ← Format.array json | throw "component-instantiation"
  let purpose ← Format.string purpose
  unless ["parameter", "witness"].contains purpose do throw "component-instantiation"
  return ⟨purpose, ← Format.contractSelector selector, ← source 65 value⟩

def proposal (json : Json) : Except String CallProposal := do
  let [caller, site, callee, operands, roles, slots] ← Format.array json | throw "component-instantiation"
  return ⟨← Format.string caller, ← Format.string site, ← Format.string callee,
    ← Format.refs operands, ← Format.strings roles, ← (← Format.array slots).mapM slot⟩

def decode (proposals seams : Json) : Except String Export := do
  return ⟨← (← Format.array proposals 100000).mapM proposal,
    ← (← Format.array seams 100000).mapM seam⟩

def selectedType (owner : Function) (selector : ContractSelector) : Except String Ty := do
  let interface ← requireSome owner.interface "component-instantiation"
  let (types, scopes) := match selector.direction with
    | .input => (owner.inputs, interface.inputScopes)
    | .output => (owner.outputs, interface.outputScopes)
  unless (scopes[selector.port]?.getD []).contains selector.role do throw "component-instantiation"
  requireSome types[selector.port]? "component-instantiation"

/-- Every relevant application constrains the role. A shared logical slot does
not gain access to another clause's private statement copy. -/
def roleSets (snapshot : Snapshot) (call : CallProposal) (slot : InstantiationSlot) :
    Except String (List (List String)) := do
  let callee ← ComponentRoutes.function snapshot call.callee
  let interface ← requireSome callee.interface "component-instantiation"
  let actual := fun role => (interface.roles.zip call.roles).lookup role |>.getD ""
  let mut sets := []
  for clause in (← ComponentRoutes.contract snapshot call.callee).clauses do
    for application in clause.subject :: clause.residual.toList do
      let relation ← requireSome (snapshot.relations.find? (·.name == application.relation)) "component-instantiation"
      let ports := application.selectors.zip relation.purposes
      if ports.any (fun (selector, purpose) => selector == slot.selector && purpose == slot.purpose) then
        sets := sets ++ [ports.filterMap fun (selector, purpose) =>
          if purpose == "statement" then some (actual selector.role) else none]
  return sets

def checkSource (snapshot : Snapshot) (context : ComponentRoutes.ProposalContext)
    (allowed : List (List String)) : Nat → Ty → InstantiationSource → Except String Unit
  | 0, _, _ => .error "component-instantiation"
  | fuel + 1, expected, value => do
    let permit := fun role => !allowed.isEmpty && allowed.all (List.contains · role)
    match value with
    | .open => pure ()
    | .operand port role =>
      let callee ← ComponentRoutes.function snapshot context.proposal.callee
      let interface ← requireSome callee.interface "component-instantiation"
      let scopes := (interface.inputScopes[port]?.getD []).map fun formal =>
        (interface.roles.zip context.proposal.roles).lookup formal |>.getD ""
      unless callee.inputs[port]? == some expected && scopes.contains role && permit role do
        throw "component-instantiation"
    | .parameter selector | .witness selector =>
      unless selector.direction == .input && permit selector.role do throw "component-instantiation"
      if (← selectedType context.caller selector) != expected then throw "component-instantiation"
      let purpose := match value with | .parameter _ => "parameter" | _ => "witness"
      unless (← ComponentRoutes.slots snapshot context.caller.name).any
          (fun slot => slot.purpose == purpose && slot.selector == selector) do throw "component-instantiation"
    | .result site port role =>
      let [action] := context.visible.filter (·.site == site) | throw "component-instantiation"
      unless action.types[port]? == some expected &&
          (action.scopes[port]?.getD []).contains role && permit role do throw "component-instantiation"
    | .math name port arguments =>
      let helper ← (ComponentRoutes.function snapshot name).mapError (fun _ => "component-instantiation")
      unless helper.kind == .math && helper.outputs[port]? == some expected &&
          helper.inputs.length == arguments.length do throw "component-instantiation"
      for (type, argument) in helper.inputs.zip arguments do
        if argument == .open then throw "component-instantiation"
        checkSource snapshot context allowed fuel type argument

/-- Structural association only. Semantic obligations are deliberately not
made true by a successful wire check. The imported body is still authoritative. -/
def check (snapshot : Snapshot) (wire : Export) : Except String Unit := do
  let derived ← ComponentRoutes.derive snapshot
  if derived.seams != wire.seams then throw "component-seam-association"
  if derived.calls.length != wire.proposals.length then throw "component-instantiation"
  for (context, proposed) in derived.calls.zip wire.proposals do
    let canonical := context.proposal
    unless { proposed with slots := canonical.slots } == canonical &&
        proposed.slots.map (fun slot => (slot.purpose, slot.selector)) ==
          canonical.slots.map (fun slot => (slot.purpose, slot.selector)) do
      throw "component-instantiation"
    for slot in proposed.slots do
      let callee ← ComponentRoutes.function snapshot proposed.callee
      let type ← selectedType callee slot.selector
      checkSource snapshot context (← roleSets snapshot proposed slot) 65 type slot.source

/-- A kernel-facing exact association. Generated clients retain the equality,
not an external tool's status string. This certifies no mathematical law. -/
structure Associated (snapshot : Snapshot) (wire : Export) where
  derived : ComponentRoutes.Result
  recomputed : ComponentRoutes.derive snapshot = .ok derived
  seams : derived.seams = wire.seams
  proposals : check snapshot wire = .ok ()

end Zkc.Source.Structured.ComponentExport
