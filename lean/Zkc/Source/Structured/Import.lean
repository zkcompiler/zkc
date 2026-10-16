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
  realizationClosed : PreparationClosed .realization definitions (preparationHelpers .realization definitions)
  mapClosed : PreparationClosed .map definitions (preparationHelpers .map definitions)

def UnitPayload.entry (payload : UnitPayload) : CheckedProtocol :=
  payload.protocols.get payload.entryIndex

/-- Every retained preparation selects its exact Math root signature from the
corresponding checked closure. This is structural evidence, not a return law. -/
def PreparationRootsSelected (retained : List Definition)
    (definitions : List CheckedDefinition) : Prop :=
  ∀ definition ∈ retained, match definition with
    | .realization declaration =>
      declaration.helperSpec ∈ preparationHelpers .realization definitions
    | .map declaration =>
      declaration.spec.helper ∈ preparationHelpers .map definitions
    | _ => True

instance preparationRootsSelectedDecidable (retained : List Definition)
    (definitions : List CheckedDefinition) : Decidable (PreparationRootsSelected retained definitions) := by
  unfold PreparationRootsSelected
  refine @List.decidableBAll Definition _ ?_ retained
  intro definition
  cases definition <;> infer_instance

/-- Check all retained declarations, including unused roots, in source order.
Keep profile diagnostics at this sole selected-operation/type admission boundary. -/
def checkPreparationRoots (retained : List Definition)
    (realizationHelpers mapHelpers : List Helper) : Except String Unit := do
  match retained with
  | [] => pure ()
  | definition :: rest =>
    match definition with
    | .realization declaration =>
      if declaration.helperSpec ∉ realizationHelpers then
        throw PreparationProfile.realization.error
    | .map declaration =>
      if declaration.spec.helper ∉ mapHelpers then
        throw PreparationProfile.map.error
    | _ => pure ()
    checkPreparationRoots rest realizationHelpers mapHelpers

theorem checkPreparationRoots_ok {retained : List Definition}
    {definitions : List CheckedDefinition}
    (accepted : checkPreparationRoots retained (preparationHelpers .realization definitions)
      (preparationHelpers .map definitions) = .ok ()) :
    PreparationRootsSelected retained definitions := by
  induction retained with
  | nil => simp [PreparationRootsSelected]
  | cons definition rest ih =>
    cases definition <;>
      simp only [checkPreparationRoots, bind, Except.bind] at accepted
    all_goals
      simp only [PreparationRootsSelected, List.mem_cons, forall_eq_or_imp]
    all_goals first
      | exact ⟨trivial, ih accepted⟩
      | split at accepted
        · contradiction
        · exact ⟨by simpa using ‹¬¬_›, ih accepted⟩

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
  let realizationHelpers := preparationHelpers .realization definitions
  let mapHelpers := preparationHelpers .map definitions
  checkPreparationRoots snapshot.definitions realizationHelpers mapHelpers
  let functions := snapshot.definitions.filterMap fun definition => match definition with
    | .function f => if f.kind == .protocol then some f else none
    | .finite _ | .realization _ | .map _ => none
  let protocols ← functions.mapM (checkProtocol snapshot domains summaries)
  if realizationClosed : PreparationClosed .realization definitions realizationHelpers then
    if mapClosed : PreparationClosed .map definitions mapHelpers then
      if linked : DeclarationsLinked [] definitions then
        if rootsLinked : ∀ root ∈ protocols, ∀ helper ∈ root.helpers,
            helper ∈ definitions.map CheckedDefinition.helper then
          let entryIndex := protocols.findIdx (·.name == snapshot.entry)
          if entryPresent : entryIndex < protocols.length then
            match available : checkUnitAvailability definitions protocols with
            | .error code => throw code
            | .ok () => return ⟨definitions, protocols, ⟨entryIndex, entryPresent⟩,
                linked, rootsLinked, available, realizationClosed, mapClosed⟩
          else throw "structured-entry"
        else throw "structured-root-link"
      else throw "structured-helper-link"
    else throw "structured-map-closure"
  else throw "structured-realization-closure"

/-- Successful whole-unit admission retains exact root selection without adding
metadata to the checked payload. No retained-to-checked body association is asserted. -/
theorem check_payload_preparationRoots {snapshot : Snapshot} {payload : UnitPayload}
    (accepted : check_payload snapshot = .ok payload) :
    PreparationRootsSelected snapshot.definitions payload.definitions := by
  unfold check_payload at accepted
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  by_cases identity : (!Format.digestValid snapshot.source || !validString snapshot.entry) = true
  · simp only [identity, ↓reduceIte] at accepted
    contradiction
  simp only [identity] at accepted
  by_cases tables : (decide (snapshot.domains.length > 128) || decide (snapshot.relations.length > 128) || decide (snapshot.bindings.length > 128) || decide (snapshot.definitions.length > 128)) = true
  · simp only [tables, ↓reduceIte] at accepted
    contradiction
  simp only [tables] at accepted
  by_cases duplicates : ((snapshot.domains.map (·.name) ++ snapshot.relations.map (·.name) ++ snapshot.bindings.map (·.name) ++ snapshot.definitions.map (·.name)).eraseDups.length != (snapshot.domains.map (·.name) ++ snapshot.relations.map (·.name) ++ snapshot.bindings.map (·.name) ++ snapshot.definitions.map (·.name)).length) = true
  · simp only [duplicates, ↓reduceIte] at accepted
    contradiction
  simp only [duplicates] at accepted
  by_cases headers : (!snapshot.definitions.all Definition.headerValid || !snapshot.relations.all Relation.valid) = true
  · simp only [headers, ↓reduceIte] at accepted
    contradiction
  simp only [headers] at accepted
  by_cases bindings : (!snapshot.bindings.all Binding.valid) = true
  · simp only [bindings, ↓reduceIte] at accepted
    contradiction
  simp only [bindings] at accepted
  by_cases instructions : (!snapshot.instructionsWithin 4096) = true
  · simp only [instructions, ↓reduceIte] at accepted
    contradiction
  simp only [instructions] at accepted
  by_cases services : (snapshot.domains.any (fun domain => domain.inputs.any Ty.isService)) = true
  · simp only [services, ↓reduceIte] at accepted
    contradiction
  simp only [services] at accepted
  repeat' first
    | contradiction
    | split at accepted
  all_goals
    cases accepted
    apply checkPreparationRoots_ok
    assumption

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

theorem check_preparationRoots {snapshot : Snapshot} {program : Program}
    (accepted : check snapshot = .ok program) :
    PreparationRootsSelected snapshot.definitions program.payload.definitions :=
  check_payload_preparationRoots (check_ok_inversion accepted).2

theorem Imported.preparationRoots {snapshot : Snapshot} (imported : Imported snapshot) :
    PreparationRootsSelected snapshot.definitions imported.program.payload.definitions :=
  check_preparationRoots imported.admitted

theorem Imported.realizationRootSelected {snapshot : Snapshot} (imported : Imported snapshot)
    {declaration : RealizationDeclaration}
    (declared : .realization declaration ∈ snapshot.definitions) :
    declaration.helperSpec ∈ preparationHelpers .realization imported.program.payload.definitions :=
  imported.preparationRoots (.realization declaration) declared

theorem Imported.mapRootSelected {snapshot : Snapshot} (imported : Imported snapshot)
    {declaration : MapDeclaration} (declared : .map declaration ∈ snapshot.definitions) :
    declaration.spec.helper ∈ preparationHelpers .map imported.program.payload.definitions :=
  imported.preparationRoots (.map declaration) declared

def decode (text : String) : Except String Program := do
  check (← Format.snapshot (← Format.parse text))

end Zkc.Source.Structured
