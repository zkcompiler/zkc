module

public import Zkc.Source.Structured.Import
public import Zkc.Source.Structured.Meaning

@[expose] public section

namespace Zkc.Source.Structured

/-- Retained applications have no implicit closed expansion, even for one role. -/
theorem ProtocolOp.closed_protocolApply (signature : ProtocolSignature)
    (roles : List Nat) (site : String) :
    (ProtocolOp.protocolApply signature roles site).closed = .error "structured-open-profile" := rfl

theorem closedRootTree_apply_refused (signature : ProtocolSignature)
    (roles : List Nat) (site : String) (args : List Nat) (results : List Ty)
    (next : RawRegion Ty ProtocolOp) :
    closedRootTree (.letOp (.protocolApply signature roles site) args results .nil next) =
      .error "structured-open-profile" := rfl

/-- A repeat callback is outside the closed profile even at maximum zero.
The callback-tree diagnostic precedes the operation projection diagnostic. -/
theorem closedRootTree_repeat_refused (spec : RepeatSpec) (site : String)
    (args : List Nat) (results inputs outputs : List Ty)
    (body next : RawRegion Ty ProtocolOp) (rest : RawRegions Ty ProtocolOp) :
    closedRootTree (.letOp (.repeat spec site) args results
      (.cons inputs outputs body rest) next) = .error "structured-protocol-region" := rfl

/-- Produce an explicit closed view of an already admitted whole unit.
Every protocol remains outside the helper table. The stored root is obtained
only by the checked operation projection of the actual entry tree. Dormant
protocols may contain applications and repeats; reachable ones are refused. -/
def Program.closedPayload (program : Program) : Except String Payload := do
  let unit := program.payload
  let root := unit.entry
  if root.roles.length != 1 || !(root.inputs ++ root.outputs).all Ty.closedValue then
    throw "structured-open-profile"
  if root.inputScopes ≠ List.replicate root.inputs.length [0] ∨
      root.outputScopes ≠ List.replicate root.outputs.length [0] then
    throw "structured-closed-scopes"
  if !unit.definitions.all (fun definition =>
      (definition.inputs ++ definition.outputs).all Ty.closedValue &&
      definition.raw.operations.all Op.closedValues) then throw "structured-closed-type"
  let raw ← closedRootTree root.raw
  match formed : raw.elaborate (dialect := dialect) root.inputs root.outputs with
  | .error _ => throw "structured-closed-formation"
  | .ok body =>
    let entry : ClosedRoot := ⟨root.name, root.inputs, root.outputs, raw, body, formed⟩
    if linked : ∀ helper ∈ entry.helpers, helper ∈ unit.definitions.map CheckedDefinition.helper then
      return ⟨unit.definitions, entry, unit.linked, linked⟩
    else throw "structured-closed-link"

/-- A computational projection with its exact provenance, never a closed
interpretation of arbitrary open nodes. -/
structure ClosedProgram where
  subject : Program
  payload : Payload
  projected : subject.closedPayload = .ok payload

abbrev ClosedProgram.snapshot (program : ClosedProgram) : Snapshot := program.subject.snapshot

def checkClosed (snapshot : Snapshot) : Except String ClosedProgram :=
  match check snapshot with
  | .error code => .error code
  | .ok subject => match projected : subject.closedPayload with
    | .error code => .error code
    | .ok payload => .ok ⟨subject, payload, projected⟩

abbrev ClosedImported (snapshot : Snapshot) := Verification.Imported checkClosed snapshot

def closedImportedOfIsOk (snapshot : Snapshot) (accepted : (checkClosed snapshot).isOk = true) :
    ClosedImported snapshot :=
  match result : checkClosed snapshot with
  | .ok program => ⟨program, result⟩
  | .error error => False.elim (by simp [result, Except.isOk, Except.toBool] at accepted)

/-- Recover ordinary whole-unit admission from the existing closed admission,
without evaluating the checker a second time. -/
def ClosedImported.subject {snapshot : Snapshot} (imported : ClosedImported snapshot) :
    Imported snapshot := ⟨imported.program.subject, by
  have admitted := imported.admitted
  cases checked : check snapshot with
  | error error => simp [checkClosed, checked] at admitted
  | ok subject =>
    simp only [checkClosed, checked] at admitted
    split at admitted
    · contradiction
    · have same := Except.ok.inj admitted
      rw [← same]⟩

theorem ClosedImported.exactSubject {snapshot : Snapshot} (imported : ClosedImported snapshot) :
    imported.program.snapshot = snapshot := imported.subject.exactSubject

def ClosedProgram.denote (program : ClosedProgram) (F G : Type) [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (inputs : Values (assignment F G) program.payload.entry.inputs) :
    Closed (Values (assignment F G) program.payload.entry.outputs) :=
  program.payload.denote F G inputs

end Zkc.Source.Structured
