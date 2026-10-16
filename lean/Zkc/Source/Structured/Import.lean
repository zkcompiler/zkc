module

public import Zkc.Source.Structured.OpenAdmission
public import Zkc.Source.Structured.Availability
public import Zkc.Specification

@[expose] public section

namespace Zkc.Source.Structured

structure UnitPayload where
  definitions : List CheckedDefinition
  protocols : List CheckedProtocol
  entryIndex : Fin protocols.length
  linked : DeclarationsLinked [] definitions
  rootsLinked : ∀ root ∈ protocols, ∀ helper ∈ root.helpers,
    helper ∈ definitions.map CheckedDefinition.helper
  available : checkUnitAvailability definitions protocols = .ok ()

def UnitPayload.entry (payload : UnitPayload) : CheckedProtocol :=
  payload.protocols.get payload.entryIndex

def check_payload (snapshot : Snapshot) : Except String UnitPayload := do
  if !Format.digestValid snapshot.source || !validString snapshot.entry then
    throw "structured-identity"
  if snapshot.domains.length > 128 || snapshot.relations.length > 128 || snapshot.bindings.length > 128 ||
      snapshot.definitions.length > 128 then throw "structured-table-limit"
  let names := snapshot.domains.map (·.name) ++ snapshot.relations.map (·.name) ++
    snapshot.bindings.map (·.name) ++ snapshot.definitions.map (·.name)
  if names.eraseDups.length != names.length then throw "structured-duplicate-symbol"
  if !snapshot.definitions.all Definition.headerValid || !snapshot.relations.all Relation.valid then
    throw "structured-header"
  if !snapshot.bindings.all Binding.valid then throw "structured-binding"
  if !snapshot.instructionsWithin 4096 then throw "structured-instruction-limit"
  if snapshot.domains.any (fun domain => domain.inputs.any Ty.isService) then
    throw "structured-service-use"
  let domains ← snapshot.domains.mapM Domain.resolve
  let summaries ← snapshot.identitySummaries
  let definitions ← (snapshot.definitions.filter (·.kind != .protocol)).mapM
    (checkDefinition snapshot domains summaries)
  let ordered ← orderDefinitions definitions.length definitions []
  let definitions := ordered.map (·.definition)
  let functions := snapshot.definitions.filterMap fun definition => match definition with
    | .function f => if f.kind == .protocol then some f else none
    | .finite _ => none
  let protocols ← functions.mapM (checkProtocol snapshot domains summaries)
  if linked : DeclarationsLinked [] definitions then
    if rootsLinked : ∀ root ∈ protocols, ∀ helper ∈ root.helpers,
        helper ∈ definitions.map CheckedDefinition.helper then
      let entryIndex := protocols.findIdx (·.name == snapshot.entry)
      if entryPresent : entryIndex < protocols.length then
        match available : checkUnitAvailability definitions protocols with
        | .error code => throw code
        | .ok () => return ⟨definitions, protocols, ⟨entryIndex, entryPresent⟩,
            linked, rootsLinked, available⟩
      else throw "structured-entry"
    else throw "structured-root-link"
  else throw "structured-helper-link"

structure Program where
  snapshot : Snapshot
  payload : UnitPayload

def check (snapshot : Snapshot) : Except String Program :=
  match check_payload snapshot with
  | .error error => .error error
  | .ok payload => .ok ⟨snapshot, payload⟩

/-- Exact raw constructor data is the proof subject, including metadata that
logical execution does not observe. The digest's relation to MLIR is external. -/
abbrev Imported (snapshot : Snapshot) := Verification.Imported check snapshot

/-- Convenience constructor for externally generated, transparent snapshot data.
Concrete clients can discharge the Boolean premise with `decide +kernel`. -/
def importedOfIsOk (snapshot : Snapshot) (accepted : (check snapshot).isOk = true) :
    Imported snapshot :=
  match result : check snapshot with
  | .ok program => ⟨program, result⟩
  | .error error => False.elim (by simp [result, Except.isOk, Except.toBool] at accepted)

theorem check_parts (snapshot : Snapshot) (payload : UnitPayload)
    (accepted : check_payload snapshot = .ok payload) :
    check snapshot = .ok ⟨snapshot, payload⟩ := by
  simp [check, accepted]

/-- Inversion of successful admission: retain the exact snapshot and the
successful computational checks. This does not prove their semantic soundness. -/
theorem check_ok_inversion {snapshot : Snapshot} {program : Program}
    (accepted : check snapshot = .ok program) :
    program.snapshot = snapshot ∧ check_payload snapshot = .ok program.payload := by
  cases h : check_payload snapshot with
  | error error => simp [check, h] at accepted
  | ok payload =>
    have same : (⟨snapshot, payload⟩ : Program) = program := by simpa [check, h] using accepted
    cases same
    exact ⟨rfl, rfl⟩

theorem Imported.exactSubject {snapshot : Snapshot} (imported : Imported snapshot) :
    imported.program.snapshot = snapshot := (check_ok_inversion imported.admitted).1

theorem Imported.admission {snapshot : Snapshot} (imported : Imported snapshot) :
    check_payload snapshot = .ok imported.program.payload := (check_ok_inversion imported.admitted).2

def decode (text : String) : Except String Program := do
  check (← Format.snapshot (← Format.parse text))

end Zkc.Source.Structured
