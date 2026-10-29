module

public import Zkc.Source.Structured.ProtocolAdmission

@[expose] public section

namespace Zkc.Source.Structured

/-- Entry and repeat exits are distinct even when both have an empty tuple. -/
inductive ProtocolExit where
  | entryReturn | repeatYield
  deriving DecidableEq, Repr

/-- Placement is checked before lexical input/service resolution. -/
def checkProtocolPlacement : ProtocolExit → Descriptor → Except String Unit
  | .repeatYield, .statement .. => .error "structured-statement-placement"
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
  if results != state || state.any Ty.isHandle then throw "structured-protocol-signature"
  let roles ← resolveScope interface.roles roles
  let stateScopes ← scopes.mapM (resolveScope interface.roles)
  if stateScopes.length != carried then throw "structured-scope-count"
  if !stateScopes.all (fun scope => scope.all roles.contains) then throw "structured-scope"
  return ⟨state, captures, roles, stateScopes, maximum⟩

/-- Only immutable service captures inherit protocol-input authority. Induction,
state and copyable data captures never become lexical entry ports. -/
def repeatCaptureOrigins (types : List Ty) (operands : List Nat)
    (origins : List (Option Nat)) : List (Option Nat) :=
  (types.zip operands).map fun (type, operand) =>
    if type.isService then (origins[operand]?).getD none else none

def repeatOrigins (spec : RepeatSpec) (operands : List Nat)
    (origins : List (Option Nat)) : List (Option Nat) :=
  none :: (List.replicate spec.state.length none ++
    repeatCaptureOrigins spec.captures (operands.drop (1 + spec.state.length)) origins)

/-- Data facts have a separate identity space. Rebase only pairs whose two
identities are explicitly captured; state and induction get fresh identities.
Admitted protocol roots currently supply no initial facts. This generic transfer
also handles explicit fact environments without asserting a state invariant. -/
def repeatFacts (spec : RepeatSpec) (operands identities : List Nat) (facts : Facts) : Facts :=
  if facts.isEmpty then [] else
  let captures := (operands.drop (1 + spec.state.length)).map
    (fun operand => identities[operand]?)
  captures.zipIdx.flatMap fun (index, i) => captures.zipIdx.filterMap fun (container, j) =>
    match index, container with
    | some index, some container =>
      if facts.contains (index, container) then
        some (1 + spec.state.length + i, 1 + spec.state.length + j)
      else none
    | _, _ => none

def checkActiveRoles (active selected : List Nat) : Except String Unit := do
  if !selected.all active.contains then throw "structured-repeat-role"

/-- This check is independent of inferred availability, including nullary
calculations. A nested action or application cannot enlarge the active roster.
Source lowering and direct typed-carrier analysis are separate public inputs,
so both intentionally validate this condition. -/
def checkProtocolRoles (active : List Nat) (op : ProtocolOp) : Except String Unit := do
  let selected := match op with
    | .localCall _ _ owner _ | .guard owner _ | .draw owner .. => [owner]
    | .exchange _ sender receiver _ => [sender, receiver]
    | .restrict _ roles | .assemble _ roles | .protocolApply _ roles _ => roles
    | .repeat spec _ => spec.roles
    | _ => []
  checkActiveRoles active selected

/-- Service capture origin is exactly the earlier lexical origin, never its
new callback position or a fresh service identity. -/
theorem repeatCaptureOrigins_service (contract : String) (operand : Nat)
    (types : List Ty) (operands : List Nat) (origins : List (Option Nat)) :
    repeatCaptureOrigins (.service contract :: types) (operand :: operands) origins =
      (origins[operand]?).getD none :: repeatCaptureOrigins types operands origins := rfl

theorem repeatCaptureOrigins_data (type : Ty) (notService : type.isService = false)
    (operand : Nat) (types : List Ty) (operands : List Nat) (origins : List (Option Nat)) :
    repeatCaptureOrigins (type :: types) (operand :: operands) origins =
      none :: repeatCaptureOrigins types operands origins := by
  simp [repeatCaptureOrigins, notService]

theorem repeatOrigins_state (spec : RepeatSpec) (operands : List Nat)
    (origins : List (Option Nat)) :
    (repeatOrigins spec operands origins).take (1 + spec.state.length) =
      List.replicate (1 + spec.state.length) none := by
  simp [repeatOrigins, Nat.add_comm, List.replicate_succ]

theorem repeatCaptureOrigins_inherited (types : List Ty) (operands : List Nat)
    (origins : List (Option Nat)) : repeatCaptureOrigins types operands origins ⊆ none :: origins := by
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

theorem repeatOrigins_inherited (spec : RepeatSpec) (operands : List Nat)
    (origins : List (Option Nat)) : repeatOrigins spec operands origins ⊆ none :: origins := by
  intro value member
  simp only [repeatOrigins, List.mem_cons, List.mem_append] at member
  rcases member with rfl | state | capture
  · exact List.mem_cons_self
  · have same := (List.mem_replicate.mp state).2
    subst value
    exact List.mem_cons_self
  · exact repeatCaptureOrigins_inherited _ _ _ capture

theorem resolveRepeatSpec_fields {interface : ProtocolInterface} {arguments results : List Ty}
    {carried maximum : Nat} {roles : List String} {scopes : List (List String)}
    {spec : RepeatSpec}
    (accepted : resolveRepeatSpec interface arguments results carried maximum roles scopes = .ok spec) :
    spec.maximum = maximum ∧ maximum ≤ 1048576 ∧ carried < arguments.length ∧
      arguments.head? = some .index ∧ spec.state = (arguments.drop 1).take carried ∧
      spec.captures = arguments.drop (1 + carried) ∧ results = spec.state ∧
      spec.state.any Ty.isHandle = false ∧
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
    checkProtocolPlacement .repeatYield (.statement relation selectors acceptance target) =
      .error "structured-statement-placement" := rfl



end Zkc.Source.Structured
