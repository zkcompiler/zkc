module

public import Zkc.Construction.Uniform.Rule
public import Zkc.Construction.Structured
public import Zkc.Source.Structured.Vocabulary
public import Zkc.Source.Structured.Algebra
public import Zkc.Source.Structured.Import
public import Zkc.Source.Structured.Meaning
public import Zkc.Source.Component

@[expose] public section

/-! The transcript-construction rule applied to an original structured export.

`checkExport` requires the export to name the original's source digest and
entry with native framing. It reads the original entry's role roster, port types
and scopes; checks that the exported policy publishes exactly the validator's
data inputs, that these are the exported validator's data inputs, that the
replaced service is a validator service input, that the selected acceptance
output is a Boolean validator output which every retained statement of the
entry selects, and that the exported outputs are the validator's outputs; derives
the occurrence context from the roster, the policy and the replaced service's
contract; and runs the construction rule. Public coverage is a deployment
requirement: the host's initial binding absorbs exactly these inputs, in this
order (`publicValues`, which reads scalar inputs only; vector, index and count
inputs are bound by typed public-value binding events,
`Zkc.Construction.PublicBinding`, which this rule does not derive).
-/

set_option autoImplicit false

namespace Zkc.Construction.Uniform
open Zkc.Source

/-- The original entry's protocol signature and roster. -/
def entryInterface (original : Structured.Snapshot) :
    Option (List Structured.Ty × Structured.ProtocolInterface) :=
  match original.definitions.find? (·.name == original.entry) with
  | some (.function function) => function.interface.map (function.inputs, ·)
  | _ => none

/-- The original entry's outputs and the acceptance indices of the statements
retained at the top level of its body. -/
def entryOutputs (original : Structured.Snapshot) :
    Option (List Structured.Ty × List Nat) :=
  match original.definitions.find? (·.name == original.entry) with
  | some (.function function) =>
      match function.body with
      | .block instructions _ =>
          some (function.outputs, instructions.filterMap fun instruction =>
            match instruction with
            | .instruction (.statement _ _ acceptance _) _ _ _ _ => some acceptance
            | _ => none)
  | _ => none

/-- Original output positions available to `role`, in original order. -/
def roleOutputs (scopes : List (List String)) (role : String) : List Nat :=
  (scopes.zipIdx.filter fun (scope, _) => scope.contains role).map (·.2)

/-- Original input positions available to `role` that carry data rather than a
service reference, in original order. -/
def dataInputs (inputs : List Structured.Ty) (scopes : List (List String)) (role : String) :
    List Nat :=
  ((inputs.zip scopes).zipIdx.filter fun ((ty, scope), _) =>
    scope.contains role && !(ty matches .service _)).map (·.2)

/-- The data sort of an original port type: every type except a service. -/
def dataSort? : Structured.Ty → Option Structured.Ty
  | .service _ => none
  | ty => some ty

/-- The occurrence context fixed by the policy, the original roster and the
replaced service's contract and the typed request its challenges carry. Only
the installed native construction with one replaced service is admitted. -/
def Context.ofPolicy (policy : Policy) (roles : List String) (contract : String)
    (request : Option Request) : Option Context :=
  match policy.services with
  | [service] =>
      if policy.construction = "" ∧ service < 1024 ∧ policy.producer ∈ roles ∧
          policy.validator ∈ roles ∧ policy.producer ≠ policy.validator ∧
          policy.draws.Nodup then
        some (Zkc.Construction.Context.fiatShamir policy.entry roles (roles.idxOf policy.producer)
          (roles.idxOf policy.validator) service contract request policy.suite policy.draws)
      else none
  | _ => none

/-- The context of an export checked against its original entry: same entry;
the policy publishes exactly the validator's data inputs, which are the
exported data inputs with the same sorts; the replaced service is a validator
service input of the original, whose contract the challenges must carry. The
typed request is the draw of the export's challenge field: it is read from the
export under check, and the construction check ties every challenge's field to
the original's contract, which determines the draw. A method with operands must
take its request from the original or an authenticated policy instead, since a
request read from the export under check would certify itself. -/
def exportContext (original : Structured.Snapshot) (participant : Participant) : Option Context :=
  match entryInterface original with
  | some (inputs, interface) =>
      let policy := participant.policy
      match policy.services with
      | [service] =>
          match inputs[service]?, interface.inputScopes[service]? with
          | some (.service contract), some scope =>
              if policy.entry = original.entry ∧ scope.contains policy.validator ∧
                  policy.publicInputs = dataInputs inputs interface.inputScopes policy.validator ∧
                  participant.inputs.dropLast.map some =
                    policy.publicInputs.map (fun index =>
                      (inputs[index]? >>= dataSort?).map ValueSort.data) then
                Context.ofPolicy policy interface.roles contract
                  ((Instruction.challengeFieldList participant.instructions).map Request.draw)
              else none
          | _, _ => none
      | _ => none
  | none => none

/-- Where the exported validator returns the selected acceptance output: its
position among the validator's original outputs. The export must name the
original's source digest with native framing, the selected output must be a
Boolean validator output selected by every retained statement of the entry, and
the exported outputs must be the validator's outputs followed by the final
transcript. -/
def exportAcceptance (original : Structured.Snapshot) (participant : Participant) :
    Option Nat :=
  match entryInterface original, entryOutputs original with
  | some (_, interface), some (outputs, statements) =>
      let policy := participant.policy
      let validatorOutputs := roleOutputs interface.outputScopes policy.validator
      if participant.source = original.source ∧ policy.format = "zkc.framed/0" ∧
          outputs[policy.acceptance]? = some .boolean ∧
          policy.acceptance ∈ validatorOutputs ∧
          statements.all (· = policy.acceptance) ∧
          participant.outputs.dropLast.map some =
            validatorOutputs.map (fun index => (outputs[index]? >>= dataSort?).map ValueSort.data) then
        some (validatorOutputs.idxOf policy.acceptance)
      else none
  | _, _ => none

/-- The complete per-compile construction check of a constructed validator
against its original export. -/
def checkExport (original : Structured.Snapshot) (participant : Participant) : Except String Unit :=
  match exportContext original participant, exportAcceptance original participant with
  | some context, some _ => check context participant
  | none, _ => .error "construction-context"
  | some _, none => .error "construction-acceptance"

theorem checkExport_sound {original : Structured.Snapshot} {participant : Participant}
    (accepted : checkExport original participant = .ok ()) :
    ∃ context, exportContext original participant = some context ∧
      check context participant = .ok () := by
  unfold checkExport at accepted
  split at accepted
  · rename_i context _ found _
    exact ⟨context, found, accepted⟩
  · cases accepted
  · cases accepted

/-- The closed table of an admitted program's checked helpers. It interprets
the helper calls of the program's exported participants: a call names a helper
of the original program and is invoked at its checked signature. -/
abbrev helperTable (program : Structured.Program) (F G : Type) [CommRing F] [AddCommGroup G]
    [Module F G] [DecidableEq F] [DecidableEq G] : Structured.Meanings F G :=
  Zkc.Construction.helperTable program F G

/-- A present scalar component of an original input, as transcript data. -/
def componentPayload {F G : Type} : (ty : Structured.Ty) →
    Component (Structured.assignment F G) ty → Option (Payload F G)
  | .boolean, some value => some (.boolean value)
  | .field domain, some value => some (.field domain value)
  | .group domain, some value => some (.group domain value)
  | _, _ => none

/-- The original inputs a participant holds, by original position. -/
def inputPayloads {F G : Type} : {tys : List Structured.Ty} →
    Values (Component (Structured.assignment F G)) tys → List (Option (Payload F G))
  | [], .nil => []
  | ty :: _, .cons value rest => componentPayload ty value :: inputPayloads rest

/-- The values the host binds for an invocation: the original input values at
the policy's public input positions, in order. -/
def publicValues {F G : Type} (policy : Policy) (values : Nat → Option (Payload F G)) :
    Option (List (Payload F G)) :=
  policy.publicInputs.mapM values

end Zkc.Construction.Uniform
