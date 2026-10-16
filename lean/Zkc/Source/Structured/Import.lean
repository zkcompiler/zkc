module

public import Zkc.Source.Structured.ContractAdmission
public import Zkc.Source.Structured.Availability
public import Zkc.Source.Structured.ApplicationMetadata
public import Zkc.Specification

@[expose] public section

namespace Zkc.Source.Structured

structure UnitPayload where
  definitions : List CheckedDefinition
  protocols : List CheckedProtocol
  entryIndex : Fin protocols.length
  linked : DeclarationsLinked [] definitions
  protocolsLinked : ProtocolDeclarationsLinked
    (definitions.map CheckedDefinition.helper) [] protocols
  available : checkUnitAvailability definitions protocols = .ok ()
  realizationClosed : PreparationClosed .realization definitions (preparationHelpers .realization definitions)
  mapClosed : PreparationClosed .map definitions (preparationHelpers .map definitions)

theorem UnitPayload.rootsLinked (payload : UnitPayload) :
    ∀ root ∈ payload.protocols, ∀ helper ∈ root.helpers,
      helper ∈ payload.definitions.map CheckedDefinition.helper :=
  payload.protocolsLinked.helpers

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

/-- Canonical metadata/header phase, shared by admission and exact phase proofs. -/
def checkUnitHeaders (snapshot : Snapshot) :
    Except String (List DomainSpec × List ProtocolSignature × IdentitySummaries) := do
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
  let headers ← collectProtocolHeaders snapshot
  checkContracts snapshot headers
  let summaries ← snapshot.identitySummaries
  return (domains, headers, summaries)

def checkUnitHelpers (snapshot : Snapshot) (domains : List DomainSpec)
    (summaries : IdentitySummaries) : Except String (List OrderedDefinition) := do
  let definitions ← (snapshot.definitions.filter (·.kind != .protocol)).mapM
    (checkDefinition snapshot domains summaries)
  let ordered ← orderDefinitions definitions.length definitions []
  let definitions := ordered.map (·.definition)
  checkPreparationRoots snapshot.definitions
    (preparationHelpers .realization definitions) (preparationHelpers .map definitions)
  return ordered

def checkUnitProtocols (snapshot : Snapshot) (domains : List DomainSpec)
    (summaries : IdentitySummaries) (headers : List ProtocolSignature)
    (helpers : List OrderedDefinition) : Except String (List CheckedProtocol) := do
  let protocols ← snapshot.protocolFunctions.mapM (fun function =>
    checkProtocol snapshot domains summaries function headers)
  let ordered ← orderProtocols helpers protocols.length protocols []
  return ordered.map (·.definition)

def checkApplicationMetadata (snapshot : Snapshot) : Except String Unit := do
  let _ ← checkNativeApplicationBudgets snapshot
  checkEffectiveProtocolSites snapshot

def linkUnitPayload (snapshot : Snapshot) (ordered : List OrderedDefinition)
    (protocols : List CheckedProtocol) : Except String UnitPayload := do
  let definitions := ordered.map (·.definition)
  let realizationHelpers := preparationHelpers .realization definitions
  let mapHelpers := preparationHelpers .map definitions
  if realizationClosed : PreparationClosed .realization definitions realizationHelpers then
    if mapClosed : PreparationClosed .map definitions mapHelpers then
      if linked : DeclarationsLinked [] definitions then
        if protocolsLinked : ProtocolDeclarationsLinked
            (definitions.map CheckedDefinition.helper) [] protocols then
          let entryIndex := protocols.findIdx (·.name == snapshot.entry)
          if entryPresent : entryIndex < protocols.length then
            match available : checkUnitAvailability definitions protocols with
            | .error code => throw code
            | .ok () => return ⟨definitions, protocols, ⟨entryIndex, entryPresent⟩,
                linked, protocolsLinked, available, realizationClosed, mapClosed⟩
          else throw "structured-entry"
        else throw "structured-root-link"
      else throw "structured-helper-link"
    else throw "structured-map-closure"
  else throw "structured-realization-closure"

/-- One checker composed from named canonical phases, without a semantic cache. -/
def check_payload (snapshot : Snapshot) : Except String UnitPayload := do
  let (domains, headers, summaries) ← checkUnitHeaders snapshot
  let helpers ← checkUnitHelpers snapshot domains summaries
  let protocols ← checkUnitProtocols snapshot domains summaries headers helpers
  checkApplicationMetadata snapshot
  linkUnitPayload snapshot helpers protocols

/-- Compose literal, named phase equations without repeating complete admission
in every dependent body-view type. All five equations remain kernel obligations. -/
theorem check_payload_of_phases {snapshot : Snapshot} {payload : UnitPayload}
    {domains : List DomainSpec} {headers : List ProtocolSignature} {summaries : IdentitySummaries}
    {helpers : List OrderedDefinition} {protocols : List CheckedProtocol}
    (headerEq : checkUnitHeaders snapshot = .ok (domains, headers, summaries))
    (helperEq : checkUnitHelpers snapshot domains summaries = .ok helpers)
    (protocolEq : checkUnitProtocols snapshot domains summaries headers helpers = .ok protocols)
    (metadataEq : checkApplicationMetadata snapshot = .ok ())
    (linked : linkUnitPayload snapshot helpers protocols = .ok payload) :
    check_payload snapshot = .ok payload := by
  simp only [check_payload, headerEq, helperEq, protocolEq, metadataEq, linked, bind, Except.bind]

theorem checkUnitHelpers_preparationRoots {snapshot : Snapshot} {domains : List DomainSpec}
    {summaries : IdentitySummaries} {ordered : List OrderedDefinition}
    (accepted : checkUnitHelpers snapshot domains summaries = .ok ordered) :
    PreparationRootsSelected snapshot.definitions (ordered.map (·.definition)) := by
  unfold checkUnitHelpers at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  repeat' first | contradiction | split at accepted
  all_goals
    cases accepted
    exact checkPreparationRoots_ok (by assumption)

theorem checkUnitProtocols_sources {snapshot : Snapshot} {domains : List DomainSpec}
    {summaries : IdentitySummaries} {headers : List ProtocolSignature}
    {helpers : List OrderedDefinition} {protocols : List CheckedProtocol}
    (accepted : checkUnitProtocols snapshot domains summaries headers helpers = .ok protocols) :
    ∃ formed, snapshot.protocolFunctions.mapM (fun function =>
      checkProtocol snapshot domains summaries function headers) = .ok formed ∧
      protocols.Perm formed := by
  unfold checkUnitProtocols at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  repeat' first | contradiction | split at accepted
  all_goals
    cases accepted
    refine ⟨_, by assumption, ?_⟩
    exact orderProtocols_perm (by assumption)

theorem linkUnitPayload_fields {snapshot : Snapshot} {ordered : List OrderedDefinition}
    {protocols : List CheckedProtocol} {payload : UnitPayload}
    (accepted : linkUnitPayload snapshot ordered protocols = .ok payload) :
    payload.definitions = ordered.map (·.definition) ∧ payload.protocols = protocols ∧
    payload.entry.name = snapshot.entry := by
  unfold linkUnitPayload at accepted
  simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  repeat' first | contradiction | split at accepted
  all_goals
    cases accepted
    refine ⟨rfl, rfl, ?_⟩
    exact of_decide_eq_true (List.findIdx_getElem (p := fun p : CheckedProtocol => p.name == snapshot.entry))

/-- Successful admission exposes the actual phases, not assumed correspondence. -/
theorem check_payload_stages {snapshot : Snapshot} {payload : UnitPayload}
    (accepted : check_payload snapshot = .ok payload) :
    ∃ domains headers summaries helpers protocols,
      checkUnitHeaders snapshot = .ok (domains, headers, summaries) ∧
      checkUnitHelpers snapshot domains summaries = .ok helpers ∧
      checkUnitProtocols snapshot domains summaries headers helpers = .ok protocols ∧
      checkApplicationMetadata snapshot = .ok () ∧
      linkUnitPayload snapshot helpers protocols = .ok payload := by
  unfold check_payload at accepted
  simp only [bind, Except.bind] at accepted
  repeat' first | contradiction | split at accepted
  all_goals exact ⟨_, _, _, _, _, by assumption, by assumption, by assumption, by assumption, accepted⟩

theorem check_payload_preparationRoots {snapshot : Snapshot} {payload : UnitPayload}
    (accepted : check_payload snapshot = .ok payload) :
    PreparationRootsSelected snapshot.definitions payload.definitions := by
  obtain ⟨_, _, _, _, _, _, helpers, _, _, linked⟩ := check_payload_stages accepted
  rw [(linkUnitPayload_fields linked).1]
  exact checkUnitHelpers_preparationRoots helpers

/-- Successful list checking gives total source association in both directions. -/
theorem checkedMap_sources {α β : Type} {checkOne : α → Except String β}
    {source : List α} {checked : List β} (accepted : source.mapM checkOne = .ok checked) :
    (∀ value ∈ checked, ∃ original ∈ source, checkOne original = .ok value) ∧
    (∀ original ∈ source, ∃ value ∈ checked, checkOne original = .ok value) := by
  induction source generalizing checked with
  | nil =>
    have empty : checked = [] := by simpa only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] using accepted.symm
    subst checked
    simp
  | cons head tail ih =>
    simp only [List.mapM_cons, bind, Except.bind] at accepted
    cases headEq : checkOne head with
    | error error => simp [headEq] at accepted
    | ok value =>
      cases tailEq : tail.mapM checkOne with
      | error error => simp [headEq, tailEq] at accepted
      | ok values =>
        have same : value :: values = checked := by simpa only [headEq, tailEq, Except.bind, pure, Except.pure, Except.ok.injEq] using accepted
        subst checked
        obtain ⟨backward, forward⟩ := ih tailEq
        constructor
        · intro result member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨head, by simp, headEq⟩
          · obtain ⟨original, member, equation⟩ := backward result member
            exact ⟨original, List.mem_cons_of_mem _ member, equation⟩
        · intro original member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨value, by simp, headEq⟩
          · obtain ⟨result, member, equation⟩ := forward original member
            exact ⟨result, List.mem_cons_of_mem _ member, equation⟩

/-- Original functions and complete lowered declarations are associated; source
order remains original while checked order is only a permutation. -/
theorem check_payload_protocolSources {snapshot : Snapshot} {payload : UnitPayload}
    (accepted : check_payload snapshot = .ok payload) :
    ∃ domains headers summaries,
      checkUnitHeaders snapshot = .ok (domains, headers, summaries) ∧
      (∀ definition ∈ payload.protocols, ∃ function ∈ snapshot.protocolFunctions,
        checkProtocol snapshot domains summaries function headers = .ok definition) ∧
      (∀ function ∈ snapshot.protocolFunctions, ∃ definition ∈ payload.protocols,
        checkProtocol snapshot domains summaries function headers = .ok definition) := by
  obtain ⟨domains, headers, summaries, helpers, protocols, headerEq, _, protocolEq, _, linked⟩ :=
    check_payload_stages accepted
  obtain ⟨formed, formation, permutation⟩ := checkUnitProtocols_sources protocolEq
  obtain ⟨backward, forward⟩ := checkedMap_sources formation
  rw [← (linkUnitPayload_fields linked).2.1] at permutation
  refine ⟨domains, headers, summaries, headerEq, ?_, ?_⟩
  · intro definition member
    exact backward definition (permutation.mem_iff.mp member)
  · intro function member
    obtain ⟨definition, member, equation⟩ := forward function member
    exact ⟨definition, permutation.mem_iff.mpr member, equation⟩

theorem checkApplicationMetadata_checks {snapshot : Snapshot}
    (accepted : checkApplicationMetadata snapshot = .ok ()) :
    (∃ summaries, checkNativeApplicationBudgets snapshot = .ok summaries) ∧
    checkEffectiveProtocolSites snapshot = .ok () := by
  unfold checkApplicationMetadata at accepted
  cases native : checkNativeApplicationBudgets snapshot with
  | error error => simp [native, Except.bind, bind] at accepted
  | ok summaries =>
    exact ⟨⟨summaries, rfl⟩, by simpa [native, Except.bind, bind] using accepted⟩

/-- Compose independently kernel-checked metadata phases without normalizing the
unused successful summary table inside every caller's admission equality. -/
theorem checkApplicationMetadata_of_checks {snapshot : Snapshot}
    (native : (checkNativeApplicationBudgets snapshot).isOk = true)
    (effective : checkEffectiveProtocolSites snapshot = .ok ()) :
    checkApplicationMetadata snapshot = .ok () := by
  cases result : checkNativeApplicationBudgets snapshot with
  | error error => simp [result, Except.isOk, Except.toBool] at native
  | ok summaries => simp [checkApplicationMetadata, result, effective, Except.bind, bind]

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

/-- Every checked protocol is the exact lowering of an original protocol,
including its resolved ordered roster/scopes and complete raw body. -/
theorem Imported.protocolSource {snapshot : Snapshot} (imported : Imported snapshot)
    {definition : CheckedProtocol} (member : definition ∈ imported.program.payload.protocols) :
    ∃ function domains headers summaries,
      .function function ∈ snapshot.definitions ∧ function.kind = .protocol ∧
      checkUnitHeaders snapshot = .ok (domains, headers, summaries) ∧
      checkProtocol snapshot domains summaries function headers = .ok definition ∧
      resolveProtocolSignature function = .ok definition.signature ∧
      lowerProtocol snapshot domains summaries headers function definition.signature = .ok definition.raw := by
  obtain ⟨domains, headers, summaries, headerEq, backward, _⟩ :=
    check_payload_protocolSources imported.admission
  obtain ⟨function, original, checked⟩ := backward definition member
  obtain ⟨retained, kind⟩ := Snapshot.mem_protocolFunctions.mp original
  exact ⟨function, domains, headers, summaries, retained, kind, headerEq, checked,
    (checkProtocol_exact checked).1, (checkProtocol_exact checked).2⟩

/-- Callback-free compatibility preserves the exact top-level instruction and
SSA-offset witness. The explicit flatness premise is checked in the kernel at
concrete call sites; recursive consumers use protocolApplication_recursive. -/
theorem Imported.protocolApplication {snapshot : Snapshot} (imported : Imported snapshot)
    {definition : CheckedProtocol} (member : definition ∈ imported.program.payload.protocols)
    {signature : ProtocolSignature} {indices : List Nat} {site : String}
    (occurs : .protocolApply signature indices site ∈ definition.raw.operations)
    (flat : definition.raw.operations.all (fun op => op.regions.isEmpty) = true := by decide +kernel) :
    ∃ function domains headers summaries interface instructions terminal offset name roles operands regions,
      .function function ∈ snapshot.definitions ∧ function.kind = .protocol ∧
      checkUnitHeaders snapshot = .ok (domains, headers, summaries) ∧
      checkProtocol snapshot domains summaries function headers = .ok definition ∧
      function.interface = some interface ∧ definition.roles = interface.roles ∧
      function.body = .block instructions terminal ∧
      .instruction (.protocolApply name roles) operands signature.outputs regions site ∈ instructions ∧
      validProtocolIdentifier site = true ∧
      resolveProtocolApplication snapshot headers interface name roles = .ok (signature, indices) ∧
      (∀ type scope operand, ((type, scope), operand) ∈
          (signature.inputs.zip signature.inputScopes).zip operands → type.isService = true →
        ∃ input, operand = offset + input ∧ input < function.inputs.length ∧
          function.inputs[input]? = some type ∧
          (scope.map (fun role => indices[role]?.getD 0)).length = 1 ∧
          definition.inputScopes[input]? = some (scope.map (fun role => indices[role]?.getD 0))) := by
  obtain ⟨function, domains, headers, summaries, retained, kind, headerEq, checked,
    signatureEq, lowered⟩ := imported.protocolSource member
  obtain ⟨interface, instructions, terminal, offset, name, roles, operands, regions,
    interfaceEq, bodyEq, instruction, siteValid, resolved, services⟩ :=
    lowerProtocol_application lowered occurs flat
  obtain ⟨originalInterface, originalEq, _, roster, _⟩ := resolveProtocolSignature_fields signatureEq
  have same : originalInterface = interface := Option.some.inj (originalEq.symm.trans interfaceEq)
  subst originalInterface
  exact ⟨function, domains, headers, summaries, interface, instructions, terminal,
    offset, name, roles, operands, regions, retained, kind, headerEq, checked,
    interfaceEq, roster, bodyEq, instruction, siteValid, resolved, services⟩

/-- Recursive inversion provides an inherited lexical environment with bounded
original service inputs, exact contracts and mapped owners. This existential
consequence does not identify the environment of a particular lowering path. -/
theorem Imported.protocolApplication_source {snapshot : Snapshot} (imported : Imported snapshot)
    {definition : CheckedProtocol} (member : definition ∈ imported.program.payload.protocols)
    {signature : ProtocolSignature} {indices : List Nat} {site : String}
    (occurs : .protocolApply signature indices site ∈ definition.raw.operations) :
    ∃ function domains headers summaries interface context, ∃ origins : List (Option Nat), ∃ name roles operands regions,
      .instruction (.protocolApply name roles) operands signature.outputs regions site ∈
        function.body.storedInstructions ∧
      .function function ∈ snapshot.definitions ∧ function.kind = .protocol ∧
      checkUnitHeaders snapshot = .ok (domains, headers, summaries) ∧
      checkProtocol snapshot domains summaries function headers = .ok definition ∧
      function.interface = some interface ∧ definition.roles = interface.roles ∧
      validProtocolIdentifier site = true ∧
      resolveProtocolApplication snapshot headers interface name roles = .ok (signature, indices) ∧
      typesAt context operands = .ok signature.inputs ∧
      (∀ type scope operand, ((type, scope), operand) ∈
          (signature.inputs.zip signature.inputScopes).zip operands → type.isService = true →
        ∃ input, origins[operand]? = some (some input) ∧ input < function.inputs.length ∧
          function.inputs[input]? = some type ∧
          (scope.map (fun role => indices[role]?.getD 0)).length = 1 ∧
          definition.inputScopes[input]? = some (scope.map (fun role => indices[role]?.getD 0))) := by
  obtain ⟨function, domains, headers, summaries, retained, kind, headerEq, checked,
    signatureEq, lowered⟩ := imported.protocolSource member
  obtain ⟨interface, context, origins, name, roles, operands, regions, source, interfaceEq, validSite,
    resolved, types, services⟩ := lowerProtocol_application_source lowered occurs
  obtain ⟨originalInterface, originalEq, _, roster, _⟩ := resolveProtocolSignature_fields signatureEq
  have same : originalInterface = interface := Option.some.inj (originalEq.symm.trans interfaceEq)
  subst originalInterface
  exact ⟨function, domains, headers, summaries, interface, context, origins, name, roles,
    operands, regions, source, retained, kind, headerEq, checked, interfaceEq, roster, validSite, resolved, types, services⟩


/-- Compatibility consequence retaining the original recursive origin ABI. -/
theorem Imported.protocolApplication_recursive {snapshot : Snapshot} (imported : Imported snapshot)
    {definition : CheckedProtocol} (member : definition ∈ imported.program.payload.protocols)
    {signature : ProtocolSignature} {indices : List Nat} {site : String}
    (occurs : .protocolApply signature indices site ∈ definition.raw.operations) :
    ∃ function domains headers summaries interface context, ∃ origins : List (Option Nat), ∃ name roles operands,
      .function function ∈ snapshot.definitions ∧ function.kind = .protocol ∧
      checkUnitHeaders snapshot = .ok (domains, headers, summaries) ∧
      checkProtocol snapshot domains summaries function headers = .ok definition ∧
      function.interface = some interface ∧ definition.roles = interface.roles ∧
      validProtocolIdentifier site = true ∧
      resolveProtocolApplication snapshot headers interface name roles = .ok (signature, indices) ∧
      typesAt context operands = .ok signature.inputs ∧
      (∀ type scope operand, ((type, scope), operand) ∈
          (signature.inputs.zip signature.inputScopes).zip operands → type.isService = true →
        ∃ input, origins[operand]? = some (some input) ∧ input < function.inputs.length ∧
          function.inputs[input]? = some type ∧
          (scope.map (fun role => indices[role]?.getD 0)).length = 1 ∧
          definition.inputScopes[input]? = some (scope.map (fun role => indices[role]?.getD 0))) := by
  obtain ⟨function, domains, headers, summaries, retained, kind, headerEq, checked,
    signatureEq, lowered⟩ := imported.protocolSource member
  obtain ⟨interface, context, origins, name, roles, operands, interfaceEq, validSite,
    resolved, types, services⟩ := lowerProtocol_application_recursive lowered occurs
  obtain ⟨originalInterface, originalEq, _, roster, _⟩ := resolveProtocolSignature_fields signatureEq
  have same : originalInterface = interface := Option.some.inj (originalEq.symm.trans interfaceEq)
  subst originalInterface
  exact ⟨function, domains, headers, summaries, interface, context, origins, name, roles,
    operands, retained, kind, headerEq, checked, interfaceEq, roster, validSite, resolved, types, services⟩

/-- Finite role validity follows from every admitted raw occurrence, including
applications inside repeat callbacks. -/
theorem Imported.protocolApplication_roles {snapshot : Snapshot} (imported : Imported snapshot)
    {definition : CheckedProtocol} (member : definition ∈ imported.program.payload.protocols)
    {signature : ProtocolSignature} {indices : List Nat} {site : String}
    (occurs : .protocolApply signature indices site ∈ definition.raw.operations) :
    indices.length = signature.roles.length ∧
      (∀ role ∈ indices, role < definition.roles.length) ∧ indices.Nodup := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, roster, _, resolved, _, _⟩ :=
    imported.protocolApplication_recursive member occurs
  rw [roster]
  exact resolveProtocolApplication_roles resolved

/-- The actual resolved source callee passes the statement-free source check;
this is not inferred from its signature, and includes calls inside callbacks. -/
theorem Imported.protocolApplication_callee {snapshot : Snapshot} (imported : Imported snapshot)
    {definition : CheckedProtocol} (member : definition ∈ imported.program.payload.protocols)
    {signature : ProtocolSignature} {indices : List Nat} {site : String}
    (occurs : .protocolApply signature indices site ∈ definition.raw.operations) :
    ∃ name function instructions terminal,
      lookupDefinition snapshot name = .ok (.function function) ∧
      (Definition.function function).acceptsEdge .protocolApply = true ∧
      resolveProtocolSignature function = .ok signature ∧
      function.body = .block instructions terminal ∧
      instructions.any (fun (.instruction descriptor _ _ _ _) =>
        match descriptor with | .statement .. => true | _ => false) = false := by
  obtain ⟨_, _, _, _, _, _, _, name, _, _, _, _, _, _, _, _, _, resolved, _, _⟩ :=
    imported.protocolApplication_recursive member occurs
  obtain ⟨function, instructions, terminal, lookup, edge, signatureEq, _, bodyEq, statements, _⟩ :=
    resolveProtocolApplication_source resolved
  exact ⟨name, function, instructions, terminal, lookup, edge, signatureEq, bodyEq, statements⟩

/-- The payload is a permutation of the complete results of checking original
protocols in source order. This preserves bodies and multiplicities, not merely
names or signatures. -/
theorem Imported.protocolPermutation {snapshot : Snapshot} (imported : Imported snapshot) :
    ∃ domains headers summaries formed,
      checkUnitHeaders snapshot = .ok (domains, headers, summaries) ∧
      snapshot.protocolFunctions.mapM (fun function =>
        checkProtocol snapshot domains summaries function headers) = .ok formed ∧
      imported.program.payload.protocols.Perm formed := by
  obtain ⟨domains, headers, summaries, _, _, headerEq, _, protocolEq, _, linked⟩ :=
    check_payload_stages imported.admission
  obtain ⟨formed, formation, permutation⟩ := checkUnitProtocols_sources protocolEq
  refine ⟨domains, headers, summaries, formed, headerEq, formation, ?_⟩
  rw [(linkUnitPayload_fields linked).2.1]
  exact permutation

/-- Every original protocol's actual full body check has a deterministic result
present in the payload. Uniqueness here concerns result identity, not occurrence
count; `protocolPermutation` separately preserves source multiplicities. -/
theorem Imported.protocolChecked {snapshot : Snapshot} (imported : Imported snapshot)
    {function : Function} (member : .function function ∈ snapshot.definitions)
    (kind : function.kind = .protocol) :
    ∃ domains headers summaries,
      checkUnitHeaders snapshot = .ok (domains, headers, summaries) ∧
      ∃ definition, definition ∈ imported.program.payload.protocols ∧
        checkProtocol snapshot domains summaries function headers = .ok definition ∧
        ∀ other, other ∈ imported.program.payload.protocols →
          checkProtocol snapshot domains summaries function headers = .ok other → other = definition := by
  obtain ⟨domains, headers, summaries, headerEq, _, forward⟩ :=
    check_payload_protocolSources imported.admission
  obtain ⟨definition, present, checked⟩ := forward function
    (Snapshot.mem_protocolFunctions.mpr ⟨member, kind⟩)
  refine ⟨domains, headers, summaries, headerEq, definition, present, checked, ?_⟩
  intro other _ evidence
  exact Except.ok.inj (evidence.symm.trans checked)

/-- Every resolved callee's complete stored source body is statement-free.
Top-level freedom comes from the application resolver; callback freedom comes
from that original declaration's successful lowering in the complete unit. -/
theorem Imported.protocolApplication_callee_statementFree {snapshot : Snapshot}
    (imported : Imported snapshot) {definition : CheckedProtocol}
    (member : definition ∈ imported.program.payload.protocols)
    {signature : ProtocolSignature} {indices : List Nat} {site : String}
    (occurs : .protocolApply signature indices site ∈ definition.raw.operations) :
    ∃ name function,
      lookupDefinition snapshot name = .ok (.function function) ∧
      (Definition.function function).acceptsEdge .protocolApply = true ∧
      resolveProtocolSignature function = .ok signature ∧
      function.body.storedInstructions.any Instruction.isStatement = false := by
  obtain ⟨name, function, instructions, terminal, lookup, edge, signatureEq, bodyEq, topFree⟩ :=
    imported.protocolApplication_callee member occurs
  have retained : .function function ∈ snapshot.definitions := by
    unfold lookupDefinition requireSome at lookup
    cases found : snapshot.definitions.find? (·.name == name) with
    | none => simp [found] at lookup
    | some original =>
      simp only [found] at lookup
      cases Except.ok.inj lookup
      exact List.mem_of_find?_eq_some found
  have kind : function.kind = .protocol := by
    have valid : function.kind = .protocol ∧ function.visibility = .publicDef := by
      simpa only [Definition.acceptsEdge, Bool.and_eq_true, beq_iff_eq] using edge
    exact valid.1
  obtain ⟨domains, headers, summaries, _, checked, _, admitted, _⟩ :=
    imported.protocolChecked retained kind
  have lowered := (checkProtocol_exact admitted).2
  refine ⟨name, function, lookup, edge, signatureEq, lowerProtocol_statementFree lowered ?_⟩
  rw [bodyEq, Block.topLevelInstructions]
  simp only [List.any_eq_false] at topFree ⊢
  intro instruction present
  have absent := topFree instruction present
  cases instruction with
  | instruction descriptor _ _ _ _ => cases descriptor <;> first | rfl | exact absent

theorem Imported.protocolSelection {snapshot : Snapshot} (imported : Imported snapshot) :
    imported.program.payload.entry.name = snapshot.entry := by
  obtain ⟨_, _, _, _, _, _, _, _, _, linked⟩ := check_payload_stages imported.admission
  exact (linkUnitPayload_fields linked).2.2

theorem Imported.nativeApplicationBudgets {snapshot : Snapshot} (imported : Imported snapshot) :
    ∃ summaries, checkNativeApplicationBudgets snapshot = .ok summaries := by
  obtain ⟨_, _, _, _, _, _, _, _, metadata, _⟩ := check_payload_stages imported.admission
  exact (checkApplicationMetadata_checks metadata).1

theorem Imported.effectiveProtocolSites {snapshot : Snapshot} (imported : Imported snapshot) :
    checkEffectiveProtocolSites snapshot = .ok () := by
  obtain ⟨_, _, _, _, _, _, _, _, metadata, _⟩ := check_payload_stages imported.admission
  exact (checkApplicationMetadata_checks metadata).2

def decode (text : String) : Except String Program := do
  check (← Format.snapshot (← Format.parse text))

end Zkc.Source.Structured
