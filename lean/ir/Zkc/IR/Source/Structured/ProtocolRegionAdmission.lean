module

public import Zkc.IR.Source.Structured.ProtocolAdmission

@[expose] public section

namespace Zkc.Source.Structured

/-- Entry and isolated callback exits are distinct even when both have an empty tuple. -/
inductive ProtocolExit where
  | entryReturn | regionYield
  deriving DecidableEq, Repr

/-- Placement is checked before lexical input/service resolution. -/
def checkProtocolPlacement : ProtocolExit → Descriptor → Except String Unit
  | .regionYield, .statement .. => .error "structured-statement-placement"
  | _, _ => .ok ()

/-- Validate the complete retained ABI before entering an isolated callback.
The maximum limits dynamic permission; it never skips static checking. -/
def resolveRepeatSpec (interface : ProtocolInterface) (arguments results : List Ty)
    (carried maximum : Nat) (roles : List String) (scopes : List (List String)) :
    Except String RepeatSpec := do
  if carried > 512 || maximum > 1048576 then throw "structured-number-limit"
  if carried >= arguments.length || arguments.head? != some .index then
    throw "structured-protocol-signature"
  let state := (arguments.drop 1).take carried
  let captures := arguments.drop (1 + carried)
  if results != state || state.any (fun type => type.isForeignHandle && !type.isOracleFamily) then
    throw "structured-protocol-signature"
  -- A repeated callback receives its captures at every iteration: an affine
  -- custody permission can only be carried as state.
  if captures.any Ty.isCustody then throw "structured-custody-capture"
  let roles ← resolveScope interface.roles roles
  let stateScopes ← scopes.mapM (resolveScope interface.roles)
  if stateScopes.length != carried then throw "structured-scope-count"
  if !stateScopes.all (fun scope => scope.all roles.contains) then throw "structured-scope"
  if (state.zip stateScopes).any (fun (type, scope) => type.isCustody && scope.length != 1) then
    throw "structured-custody-holder"
  return ⟨state, captures, roles, stateScopes, maximum⟩

/-- Boolean selection has no carried state and admits each stored arm. -/
def resolveBranchSpec (interface : ProtocolInterface) (arguments results : List Ty)
    (roles : List String) (scopes : List (List String)) : Except String BranchSpec := do
  if arguments.head? != some .boolean ||
      results.any (fun type ↦ type.isForeignHandle && !type.isOracleFamily) then
    throw "structured-protocol-signature"
  let selected ← resolveScope interface.roles roles
  let scopes ← scopes.mapM (resolveScope interface.roles)
  if scopes.length != results.length then throw "structured-scope-count"
  if !scopes.all (fun scope ↦ scope.all selected.contains) then throw "structured-scope"
  if (results.zip scopes).any (fun (type, scope) ↦ type.isCustody && scope.length != 1) then
    throw "structured-custody-holder"
  return ⟨arguments.drop 1, results, selected, scopes⟩

/-- Only immutable service captures inherit protocol-input authority. Induction,
state and copyable data captures never become lexical entry ports. -/
def captureServiceOrigins (types : List Ty) (operands : List Nat)
    (origins : List (Option Nat)) : List (Option Nat) :=
  (types.zip operands).map fun (type, operand) =>
    if type.isService then (origins[operand]?).getD none else none

def checkActiveRoles (active selected : List Nat) : Except String Unit := do
  if !selected.all active.contains then throw "structured-repeat-role"

/-- This check is independent of inferred availability, including nullary
calculations. A nested action or application cannot enlarge the active roster.
Source lowering and direct typed-carrier analysis are separate public inputs,
so both intentionally validate this condition. -/
def checkProtocolRoles (active : List Nat) (op : ProtocolOp) : Except String Unit := do
  let selected := match op with
    | .oracle operation _ => match operation with
      | .input _ holder receivers _ | .send _ holder receivers _ |
        .components _ holder receivers | .virtual _ holder receivers => holder :: receivers
      | .query _ (some owner) | .contents _ owner => [owner]
      | .sequenceAppend _ _ roles | .sequenceAt _ _ roles => roles
      | _ => []
    | .localCall _ _ owner _ | .guard owner _ | .draw owner .. | .query owner .. => [owner]
    | .exchange _ sender receiver _ => [sender, receiver]
    | .restrict _ roles | .assemble _ roles | .protocolApply _ roles _ => roles
    | .repeat spec _ => spec.roles
    | .branch spec _ => spec.roles
    | _ => []
  checkActiveRoles active selected

/-- Service capture origin is exactly the earlier lexical origin, never its
new callback position or a fresh service identity. -/
theorem captureServiceOrigins_service (contract : String) (operand : Nat)
    (types : List Ty) (operands : List Nat) (origins : List (Option Nat)) :
    captureServiceOrigins (.service contract :: types) (operand :: operands) origins =
      (origins[operand]?).getD none :: captureServiceOrigins types operands origins := rfl

theorem captureServiceOrigins_data (type : Ty) (notService : type.isService = false)
    (operand : Nat) (types : List Ty) (operands : List Nat) (origins : List (Option Nat)) :
    captureServiceOrigins (type :: types) (operand :: operands) origins =
      none :: captureServiceOrigins types operands origins := by
  simp [captureServiceOrigins, notService]

theorem captureServiceOrigins_inherited (types : List Ty) (operands : List Nat)
    (origins : List (Option Nat)) : captureServiceOrigins types operands origins ⊆ none :: origins := by
  intro value member
  obtain ⟨⟨type, operand⟩, _, rfl⟩ := List.mem_map.mp member
  dsimp only
  split
  · cases found : origins[operand]? with
    | none => simp
    | some value =>
      simp only [Option.getD_some]
      exact List.mem_cons_of_mem _ (List.mem_of_getElem? found)
  · exact List.mem_cons_self

theorem resolveRepeatSpec_fields {interface : ProtocolInterface} {arguments results : List Ty}
    {carried maximum : Nat} {roles : List String} {scopes : List (List String)}
    {spec : RepeatSpec}
    (accepted : resolveRepeatSpec interface arguments results carried maximum roles scopes = .ok spec) :
    spec.maximum = maximum ∧ maximum ≤ 1048576 ∧ carried < arguments.length ∧
      arguments.head? = some .index ∧ spec.state = (arguments.drop 1).take carried ∧
      spec.captures = arguments.drop (1 + carried) ∧ results = spec.state ∧
      spec.state.any (fun type => type.isForeignHandle && !type.isOracleFamily) = false ∧
      resolveScope interface.roles roles = .ok spec.roles ∧
      scopes.mapM (resolveScope interface.roles) = .ok spec.stateScopes ∧
      spec.stateScopes.length = carried ∧
      spec.stateScopes.all (fun scope => scope.all spec.roles.contains) = true := by
  unfold resolveRepeatSpec at accepted
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  repeat' first | contradiction | split at accepted
  all_goals
    cases accepted
    simp_all
    assumption

/-- Successful role checking retains the subset condition used for a callback. -/
theorem checkProtocolRoles_repeat {active : List Nat} {spec : RepeatSpec} {site : String}
    (accepted : checkProtocolRoles active (.repeat spec site) = .ok ()) :
    spec.roles.all active.contains = true := by
  cases h : spec.roles.all active.contains <;> simp [checkProtocolRoles, checkActiveRoles, h] at accepted ⊢

/-- No bound or data-origin choice can make a callback statement admissible. -/
theorem checkProtocolPlacement_statement (relation : String) (selectors : List String) (acceptance : Nat)
    (target : Option String := none) :
    checkProtocolPlacement .regionYield (.statement relation selectors acceptance target) =
      .error "structured-statement-placement" := rfl

/-- One callback ABI and lexical transfer. Fresh parameters (induction and
carried state) have no entry-port authority; immutable captures may inherit it. -/
structure ProtocolCallbackSpec where
  fresh : List Ty
  captures : List Ty
  outputs : List Ty
  roles : List Nat
  captureOffset : Nat
  deriving DecidableEq, Repr

def ProtocolCallbackSpec.inputs (spec : ProtocolCallbackSpec) := spec.fresh ++ spec.captures

def ProtocolOp.callbackSpecs : ProtocolOp → List ProtocolCallbackSpec
  | .repeat spec _ =>
    [⟨.index :: spec.state, spec.captures, spec.state, spec.roles, 1 + spec.state.length⟩]
  | .branch spec _ =>
    let arm : ProtocolCallbackSpec := ⟨[], spec.captures, spec.outputs, spec.roles, 1⟩
    [arm, arm]
  | _ => []

def ProtocolCallbackSpec.origins (spec : ProtocolCallbackSpec) (operands : List Nat)
    (origins : List (Option Nat)) : List (Option Nat) :=
  List.replicate spec.fresh.length none ++
    captureServiceOrigins spec.captures (operands.drop spec.captureOffset) origins

def ProtocolCallbackSpec.facts (spec : ProtocolCallbackSpec) (operands identities : List Nat)
    (facts : Facts) : Facts :=
  if facts.isEmpty then [] else
  let captures := (operands.drop spec.captureOffset).map (fun operand ↦ identities[operand]?)
  captures.zipIdx.flatMap fun (index, i) ↦ captures.zipIdx.filterMap fun (container, j) ↦
    match index, container with
    | some index, some container =>
      if facts.contains (index, container) then
        some (spec.fresh.length + i, spec.fresh.length + j)
      else none
    | _, _ => none

theorem ProtocolCallbackSpec.origins_inherited (spec : ProtocolCallbackSpec)
    (operands : List Nat) (origins : List (Option Nat)) :
    spec.origins operands origins ⊆ none :: origins := by
  intro value member
  rcases List.mem_append.mp member with fresh | captured
  · have same := (List.mem_replicate.mp fresh).2
    subst value
    exact List.mem_cons_self
  · exact captureServiceOrigins_inherited _ _ _ captured

theorem ProtocolOp.callbackSpecs_nonempty_regions {op : ProtocolOp} {spec : ProtocolCallbackSpec}
    (member : spec ∈ op.callbackSpecs) : op.regions ≠ [] := by
  cases op <;> simp_all [callbackSpecs, regions]

end Zkc.Source.Structured
