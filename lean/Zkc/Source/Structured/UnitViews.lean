module

public import Zkc.Source.Structured.HelperSources
public import Zkc.Source.Structured.Association
public import Zkc.Source.Structured.OpenLaws
public import Zkc.Source.Structured.ClosedProfile
public import Zkc.Source.KernelRfl
public meta import Lean.Elab.Command

@[expose] public section

/-! Literal checked units from authored typed bodies.

A unit's checked payload is written as literal declarations built from typed
bodies, and named kernel equations show that each admission phase of the
retained snapshot produces exactly that payload. `structured_views` emits
these declarations; `structured_associations` emits each body's membership,
full signature and raw-tree association. The commands only produce syntax:
every emitted definition and phase equation is elaborated and kernel-checked as
if it had been written by hand. Declaration order and nesting depth are
computed by running the admission orderers on the authored bodies; that choice
is not trusted. A stale or mistyped body is rejected because the kernel checks
each phase equation against the retained snapshot. -/

namespace Zkc.Source.Structured

/-- A checked declaration whose raw tree is the erasure of its typed body. -/
abbrev CheckedDefinition.ofBody (helper : Helper)
    (body : Region dialect helper.inputs helper.outputs) : CheckedDefinition :=
  ⟨helper.name, helper.kind, helper.inputs, helper.outputs, body.erase, body, body.elaborate_erase⟩

/-- A protocol tree whose raw tree is the erasure of its typed body. -/
abbrev CheckedProtocol.ofBody (signature : ProtocolSignature)
    (body : Region protocolDialect signature.inputs signature.outputs) : CheckedProtocol where
  toProtocolSignature := signature
  raw := body.erase
  body := body
  formed := body.elaborate_erase

/-- The optional-component view of an associated body, from its association. -/
theorem UnitPayload.component_body_of_bodyIn {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (payload : UnitPayload) {helper : Helper}
    {body : Region dialect helper.inputs helper.outputs}
    (association : BodyIn payload.definitions helper body)
    (args : Values (Component (assignment F G)) helper.inputs) :
    invoke (payload.tables F G).components helper args =
      body.component (Evaluation.meaning (observedSites F G) (payload.tables F G).closed)
        (Evaluation.componentOperation (observedSites F G) (payload.tables F G)) args.get := by
  obtain ⟨definition, member, signature, exactRaw⟩ := association
  exact payload.component_body_view_as definition member helper signature body exactRaw args

/-- Final linking of a literal payload reuses its stored obligations; it does
not re-run availability or preparation normalization. -/
theorem linkUnitPayload_of_payload (snapshot : Snapshot) (ordered : List OrderedDefinition)
    (payload : UnitPayload)
    (definitionsEq : ordered.map (·.definition) = payload.definitions)
    (entryEq : payload.protocols.findIdx (·.name == snapshot.entry) = payload.entryIndex.val) :
    linkUnitPayload snapshot ordered payload.protocols = .ok payload := by
  unfold linkUnitPayload
  rw [definitionsEq]
  simp only [payload.realizationClosed, payload.mapClosed, payload.linked,
    payload.protocolsLinked, entryEq, payload.entryIndex.isLt, ↓reduceDIte]
  split
  · rename_i code unavailable
    have available := payload.available
    rw [unavailable] at available
    cases available
  · rfl

/-- Compose separately checked protocol trees with the dependency orderer. -/
theorem checkUnitProtocols_of_checked {snapshot : Snapshot} {domains : List DomainSpec}
    {summaries : IdentitySummaries} {headers : List ProtocolSignature}
    {helpers : List OrderedDefinition} (checked : List CheckedProtocol)
    {protocols : List CheckedProtocol}
    (sources : snapshot.protocolFunctions.mapM
      (fun function => checkProtocol snapshot domains summaries function headers) = .ok checked)
    (order : (orderProtocols helpers checked.length checked []).map
      (fun ordered => ordered.map (·.definition)) = .ok protocols) :
    checkUnitProtocols snapshot domains summaries headers helpers = .ok protocols := by
  cases ordering : orderProtocols helpers checked.length checked [] with
  | error error => simp [ordering, Except.map] at order
  | ok ordered =>
    simp only [ordering, Except.map, Except.ok.injEq] at order
    simp only [checkUnitProtocols, sources, ordering, order, bind, Except.bind, pure, Except.pure]

/-- Closed admission from whole-unit admission and the checked closed projection. -/
theorem checkClosed_of_check {snapshot : Snapshot} {subject : Program} {payload : Payload}
    (admitted : check snapshot = .ok subject) (projected : subject.closedPayload = .ok payload) :
    checkClosed snapshot = .ok ⟨subject, payload, projected⟩ := by
  unfold checkClosed
  split
  · rename_i code failed
    rw [admitted] at failed
    cases failed
  · rename_i checked accepted
    rw [admitted] at accepted
    cases accepted
    split
    · rename_i code failed
      rw [projected] at failed
      cases failed
    · rename_i result same
      rw [projected] at same
      cases same
      rfl

/-- Split an ordered `mapM` over a literal list into its element equations. -/
theorem mapM_cons_ok {α β : Type} {f : α → Except String β} {head : α} {tail : List α}
    {first : β} {rest : List β} (headEq : f head = .ok first) (tailEq : tail.mapM f = .ok rest) :
    (head :: tail).mapM f = .ok (first :: rest) := by
  simp only [List.mapM_cons, headEq, tailEq, bind, Except.bind, pure, Except.pure]

theorem mapM_nil_ok {α β : Type} (f : α → Except String β) : ([] : List α).mapM f = .ok [] := rfl

namespace UnitViews

/-- A list of naturals below `2 ^ 20` as one natural. The generator asks the
kernel for this number, so a whole computed list is evaluated in one reduction
that shares its intermediate results. -/
def encodeDigits : List Nat → Nat
  | [] => 0
  | digit :: rest => digit + 1048576 * encodeDigits rest

/-- A checker result as one natural: `0` for a refusal, otherwise one plus the
encoded projection of the accepted value. -/
def encodeResult {α : Type} (project : α → List Nat) : Except String α → Nat
  | .ok value => 1 + encodeDigits (project value)
  | .error _ => 0

open Lean Meta Elab Command Term

/-- The first `count` digits of `encodeDigits`. -/
meta def decodeDigits (count value : Nat) : List Nat :=
  (List.range count).map fun index => value / 1048576 ^ index % 1048576

/-- Kernel weak-head reduction, then recursive normalization of constructor
arguments. Proof arguments are kept unchanged. -/
meta partial def normalize (expression : Expr) : MetaM Expr := do
  let environment ← getEnv
  let reduced ← match Kernel.whnf environment (← getLCtx) expression with
    | .ok reduced => pure reduced
    | .error error => throwError "kernel reduction failed: {error.toMessageData {}}"
  let .const name _ := reduced.getAppFn | return reduced
  let some (.ctorInfo _) := environment.find? name | return reduced
  let mut arguments := reduced.getAppArgs
  for index in [0:arguments.size] do
    let argument := arguments[index]!
    if (← isProof argument) || (← isType argument) then continue
    arguments := arguments.set! index (← normalize argument)
  return mkAppN reduced.getAppFn arguments

/-- Explicit application syntax that elaborates back to a normalized literal. -/
meta partial def literalSyntax (expression : Expr) : MetaM Term := do
  match expression with
  | .lit (.natVal value) => return Syntax.mkNumLit (toString value)
  | .lit (.strVal value) => return Syntax.mkStrLit value
  | .const name _ => `(@$(mkCIdent name))
  | .app .. =>
    let .const name _ := expression.getAppFn
      | throwError "unexpected literal head{indentExpr expression}"
    let arguments ← expression.getAppArgs.mapM literalSyntax
    `(@$(mkCIdent name) $arguments*)
  | _ => throwError "unexpected literal{indentExpr expression}"

meta def normalizeTerm (term : Term) : TermElabM Expr := do
  let expression ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  normalize (← instantiateMVars expression)

meta def stringValue (expression : Expr) : MetaM String := do
  let .lit (.strVal value) := expression
    | throwError "expected a string literal{indentExpr expression}"
  return value

meta partial def listValues (expression : Expr) : MetaM (List Expr) := do
  match expression.getAppFn.constName?, expression.getAppArgs with
  | some ``List.nil, _ => return []
  | some ``List.cons, #[_, head, tail] => return head :: (← listValues tail)
  | _, _ => throwError "expected a literal list{indentExpr expression}"

/-- The value of a normalized checker result, or the checker's refusal. -/
meta def exceptValue (expression : Expr) (phase : String) : MetaM Expr := do
  match expression.getAppFn.constName?, expression.getAppArgs with
  | some ``Except.ok, #[_, _, value] => return value
  | some ``Except.error, #[_, _, .lit (.strVal code)] => throwError "{phase} refused the unit: {code}"
  | some ``Except.error, #[_, _, error] => throwError "{phase} refused the unit:{indentExpr error}"
  | _, _ => throwError "expected a literal checker result{indentExpr expression}"

meta def natValue (expression : Expr) : MetaM Nat := do
  let .lit (.natVal value) := expression
    | throwError "expected a natural literal{indentExpr expression}"
  return value

/-- An authored declaration: its local name and the terms giving its full
signature and typed body. -/
structure Entry where
  name : Name
  signature : Term
  body : Term

/-- Names of the unit-level declarations; a closed subject keeps the plain names
for its closed projection. -/
structure Naming where
  program : Name := `program
  imported : Name := `imported
  admission : Name := `kernel_admission
  helperRaw : String := "_raw"
  helperBody : String := "_body"
  closed : Bool := false
  command : String := "structured_views"

meta def suffixed (base : Name) (suffix : String) : Name :=
  match base with
  | .str parent last => .str parent (last ++ suffix)
  | _ => base

meta def entryIdent (base : Name) (suffix : String) : Ident :=
  mkIdent (suffixed base suffix)

end UnitViews

/-- `local`, or `local := Source.prefix` (uses `prefixHelper`/`prefixBody`, or
`prefixSignature`/`prefixBody` for protocols), or `local := (signature, body)`. -/
syntax structuredViewEntry := ident (" := " (ident <|> ("(" term ", " term ")")))?

/-- Emit a literal checked unit and its named admission phases. -/
syntax (name := structuredViews) "structured_views " term:max
  &" helpers" " [" structuredViewEntry,* "]" &" protocols" " [" structuredViewEntry,* "]" : command

/-- Emit a literal checked unit of the closed single-role profile. The unit is
named `subject`; `program` is its closed projection with root body `root`. -/
syntax (name := structuredClosedViews) "structured_closed_views " term:max
  &" helpers" " [" structuredViewEntry,* "]" &" protocols" " [" structuredViewEntry,* "]"
  &" root" term:max : command

/-- Emit membership, full signature, raw tree and association for each body of a
unit emitted by `structured_views` in the given namespace. -/
syntax (name := structuredAssociations) "structured_associations " ident
  " [" structuredViewEntry,* "]" : command

namespace UnitViews
open Lean Meta Elab Command Term

meta def parseEntry (signatureSuffix : String) (entry : Syntax) : CommandElabM Entry := do
  let name := entry[0].getId
  let source := entry[1]
  if source.getNumArgs == 0 then
    return ⟨name, entryIdent name signatureSuffix, entryIdent name "Body"⟩
  let target := source[1]
  if target.isIdent then
    return ⟨name, entryIdent target.getId signatureSuffix, entryIdent target.getId "Body"⟩
  return ⟨name, ⟨target[1]⟩, ⟨target[3]⟩⟩

meta def definitionIdent (entry : Entry) : Ident := entryIdent entry.name "Definition"

meta def theoremIdent (entry : Entry) (suffix : String) : Ident :=
  mkIdent (Name.mkSimple ((match entry.name with | .str _ last => last | name => name.toString) ++ suffix))

/-- For each retained name, the index of the authored entry carrying it. Names
are compared by the kernel, so computed names need not reduce to literals. -/
meta def matchEntries (retained : List String) (entries : Array Entry) (kind : String) :
    TermElabM (List Entry) := do
  let names ← entries.mapM fun entry => `(($(entry.signature)).name)
  let retainedTerm ← `([$((retained.map Syntax.mkStrLit).toArray),*])
  let encoded ← natValue (← normalizeTerm
    (← `(encodeDigits (List.map (fun (name : String) => List.idxOf name ([$names,*] : List String))
      ($retainedTerm : List String)))))
  let mut used : Array Bool := entries.map fun _ => false
  let mut result := #[]
  for (name, index) in retained.zip (decodeDigits retained.length encoded) do
    let some entry := entries[index]?
      | throwError "no authored {kind} body for retained declaration {name}"
    used := used.set! index true
    result := result.push entry
  for h : index in [0:entries.size] do
    unless used[index]?.getD false do
      throwError "authored {kind} {entries[index].name} is not retained by the snapshot"
  return result.toList

/-- Every declaration name a views command emits. A local name that would make
two generated names equal is refused before any reduction. In the closed
profile the entry-protocol names are reserved for every protocol. -/
meta def generatedNames (helperEntries protocolEntries : Array Entry) (naming : Naming) : Array Name :=
  Id.run do
    let simple (entry : Entry) (suffix : String) : Name :=
      Name.mkSimple ((match entry.name with | .str _ last => last | name => name.toString) ++ suffix)
    let mut names : Array Name := #[`definitions, `ordered, `headers, `domains, `summaries, `unit,
      naming.program, `headers_checked, `helpers_checked, `protocols_checked, `native_metadata_checked,
      `effective_sites_checked, `metadata_checked, `payload_linked, naming.admission, naming.imported,
      `exact_subject, `complete_protocol_source, `complete_helper_source, `complete_original_protocol]
    names := names ++ (if naming.closed then
        #[`root, `payload, `program, `kernel_admission, `imported, `entry_exact, `entry_body_exact]
      else #[`entry_selection, `entry_signature, `entry_raw])
    for entry in helperEntries do
      names := names ++ #[suffixed entry.name "Definition", simple entry naming.helperRaw,
        simple entry naming.helperBody]
      if naming.closed then
        names := names.push (simple entry "_member")
    for entry in protocolEntries do
      names := names.push (suffixed entry.name "Definition")
      for suffix in ["_signature", "_raw", "_body", "_checked", "_member"] do
        names := names.push (simple entry suffix)
      if naming.closed then
        for suffix in ["_selected", "_exact", "_body_exact"] do
          names := names.push (simple entry suffix)
    return names

/-- Elaborate one generated declaration and stop at the first one that Lean or
the kernel refuses, naming it; later declarations would otherwise be
elaborated on top of a failed one. Phase equations are named as such. -/
meta def emit (naming : Naming) (command : Syntax) : CommandElabM Unit := do
  elabCommand command
  if (← get).messages.hasErrors then
    let name := ((command.find? (·.isOfKind ``Parser.Command.declId)).map (·[0].getId)).getD .anonymous
    if name.toString.endsWith "_checked" || name == `payload_linked then
      throwError "{naming.command}: the authored bodies do not satisfy the admission phase {name}"
    throwError "{naming.command}: generated declaration {name} was not accepted for the authored bodies"

/-- Generated declarations: literal payload, admission phases and source facts. -/
meta def emitViews (snapshot : Term) (helperEntries protocolEntries : Array Entry)
    (naming : Naming := {}) : CommandElabM Entry := do
  let mut seen : NameSet := {}
  for name in generatedNames helperEntries protocolEntries naming do
    if seen.contains name then
      throwError "{naming.command}: two generated declarations would be named {name}; rename an authored entry"
    seen := seen.insert name
  let (helperOrder, protocolOrder, snapshotProtocols, entryIndex, domains, summaries) ←
      tryCatch (liftTermElabM do
    let retainedTerm ← `(List.map Definition.name (List.filter
      (fun definition => definition.kind != .protocol) (Snapshot.definitions $snapshot)))
    let retained ← (← listValues (← normalizeTerm retainedTerm)).mapM fun value => stringValue value
    let helpers ← matchEntries retained helperEntries "helper"
    let retainedNames ← `(([$((retained.map Syntax.mkStrLit).toArray),*] : List String))
    let pendingItems ← helpers.toArray.mapM fun entry =>
      `(CheckedDefinition.ofBody $(entry.signature) $(entry.body))
    let pending ← `(([$pendingItems,*] : List CheckedDefinition))
    let orderTerm ← `(orderDefinitions (List.length $pending) $pending [])
    let order ← natValue (← normalizeTerm (← `(encodeResult
      (fun (ordered : List OrderedDefinition) => List.flatMap (fun item =>
        [List.idxOf (OrderedDefinition.definition item).name $retainedNames, OrderedDefinition.depth item]) ordered)
      $orderTerm)))
    if order == 0 then
      discard <| exceptValue (← normalizeTerm orderTerm) "helper ordering"
      throwError "helper ordering refused the unit"
    let digits := decodeDigits (2 * helpers.length) (order - 1)
    let helperOrder ← (List.range helpers.length).mapM fun position => do
      let some entry := helpers[digits[2 * position]!]? | throwError "unexpected helper order"
      return (entry, digits[2 * position + 1]!)
    let protocolTerm ← `(List.map Function.name (Snapshot.protocolFunctions $snapshot))
    let protocolNames ← (← listValues (← normalizeTerm protocolTerm)).mapM fun value => stringValue value
    let protocols ← matchEntries protocolNames protocolEntries "protocol"
    let protocolRetained ← `(([$((protocolNames.map Syntax.mkStrLit).toArray),*] : List String))
    let orderedHelpers ← helperOrder.toArray.mapM fun (entry, depth) =>
      `(OrderedDefinition.mk (CheckedDefinition.ofBody $(entry.signature) $(entry.body))
        $(Syntax.mkNumLit (toString depth)))
    let protocolItems ← protocols.toArray.mapM fun entry =>
      `(CheckedProtocol.ofBody $(entry.signature) $(entry.body))
    let pendingProtocols ← `(([$protocolItems,*] : List CheckedProtocol))
    let protocolOrderTerm ←
      `(orderProtocols [$orderedHelpers,*] (List.length $pendingProtocols) $pendingProtocols [])
    let protocolOrder ← natValue (← normalizeTerm (← `(encodeResult
      (fun (ordered : List OrderedProtocol) => List.map (fun item =>
        List.idxOf (OrderedProtocol.definition item).name $protocolRetained) ordered)
      $protocolOrderTerm)))
    if protocolOrder == 0 then
      discard <| exceptValue (← normalizeTerm protocolOrderTerm) "protocol ordering"
      throwError "protocol ordering refused the unit"
    let protocolOrder ← (decodeDigits protocols.length (protocolOrder - 1)).mapM fun index => do
      let some entry := protocols[index]? | throwError "unexpected protocol order"
      return (index, entry)
    let entryName ← stringValue (← normalizeTerm (← `(Snapshot.entry $snapshot)))
    let some retainedEntry := protocolNames.idxOf? entryName
      | throwError "the snapshot entry {entryName} is not a retained protocol"
    let some entryIndex := protocolOrder.findIdx? (·.1 == retainedEntry)
      | throwError "the snapshot entry {entryName} was not ordered"
    let domainsTerm ← `(List.mapM Domain.resolve (Snapshot.domains $snapshot))
    let domains ← exceptValue (← normalizeTerm domainsTerm) "domain resolution"
    let summaries ← exceptValue (← normalizeTerm (← `(Snapshot.identitySummaries $snapshot))) "identity summaries"
    return (helperOrder, protocolOrder.map (·.2), protocols, entryIndex,
      ← literalSyntax domains, ← literalSyntax summaries))
    fun error => throwError "{naming.command}: {error.toMessageData}"
  -- Literal declarations.
  for entry in helperEntries do
    let definition := definitionIdent entry
    emit naming (← `(def $definition : CheckedDefinition := CheckedDefinition.ofBody $(entry.signature) $(entry.body)))
    emit naming (← `(theorem $(theoremIdent entry naming.helperRaw) :
        ($definition).raw = ($(entry.body)).erase := rfl))
    emit naming (← `(theorem $(theoremIdent entry naming.helperBody) : ($definition).body = $(entry.body) := rfl))
  for entry in protocolEntries do
    let definition := definitionIdent entry
    emit naming (← `(def $definition : CheckedProtocol := CheckedProtocol.ofBody $(entry.signature) $(entry.body)))
    emit naming (← `(theorem $(theoremIdent entry "_signature") : ($definition).signature = $(entry.signature) := rfl))
    emit naming (← `(theorem $(theoremIdent entry "_raw") : ($definition).raw = ($(entry.body)).erase := rfl))
    emit naming (← `(theorem $(theoremIdent entry "_body") : ($definition).body = $(entry.body) := rfl))
  let definitionsList ← helperOrder.toArray.mapM fun (entry, _) => `($(definitionIdent entry))
  let orderedList ← helperOrder.toArray.mapM fun (entry, depth) =>
    `(⟨$(definitionIdent entry), $(Syntax.mkNumLit (toString depth))⟩)
  let headersList ← snapshotProtocols.toArray.mapM fun entry => `($(entry.signature))
  let protocolsList ← protocolOrder.toArray.mapM fun entry => `($(definitionIdent entry))
  let definitionsId := mkIdent `definitions
  let orderedId := mkIdent `ordered
  let headersId := mkIdent `headers
  let domainsId := mkIdent `domains
  let summariesId := mkIdent `summaries
  let unitId := mkIdent `unit
  let programId := mkIdent naming.program
  emit naming (← `(def $definitionsId : List CheckedDefinition := [$definitionsList,*]))
  emit naming (← `(def $orderedId : List OrderedDefinition := [$orderedList,*]))
  emit naming (← `(def $headersId : List ProtocolSignature := [$headersList,*]))
  emit naming (← `(def $domainsId : List DomainSpec := $domains))
  emit naming (← `(def $summariesId : IdentitySummaries := $summaries))
  emit naming (← `(def $unitId : UnitPayload where
    definitions := $definitionsId
    protocols := [$protocolsList,*]
    entryIndex := ⟨$(Syntax.mkNumLit (toString entryIndex)), by decide +kernel⟩
    linked := by decide +kernel
    protocolsLinked := by decide +kernel
    available := checkUnitAvailability_ok_of_isOk (by decide +kernel)
    realizationClosed := by decide +kernel
    mapClosed := by decide +kernel))
  emit naming (← `(def $programId : Program := ⟨$snapshot, $unitId⟩))
  -- Admission phases, each checked by the kernel.
  emit naming (← `(theorem $(mkIdent `headers_checked) : checkUnitHeaders $snapshot =
      .ok ($domainsId, $headersId, $summariesId) := by kernel_rfl))
  emit naming (← `(theorem $(mkIdent `helpers_checked) :
      checkUnitHelpers $snapshot $domainsId $summariesId = .ok $orderedId := by kernel_rfl))
  let mut sourceEquations : Array Ident := #[]
  for h : index in [0:snapshotProtocols.length] do
    let entry := snapshotProtocols[index]
    let name := theoremIdent entry "_checked"
    sourceEquations := sourceEquations.push name
    emit naming (← `(theorem $name : checkProtocol $snapshot $domainsId $summariesId
        ((Snapshot.protocolFunctions $snapshot)[$(Syntax.mkNumLit (toString index))]'(by decide +kernel))
        $headersId = .ok $(definitionIdent entry) := by kernel_rfl))
  let mut sources ← `(mapM_nil_ok _)
  for name in sourceEquations.reverse do
    sources ← `(mapM_cons_ok $name $sources)
  let checkedList ← snapshotProtocols.toArray.mapM fun entry => `($(definitionIdent entry))
  let sourceList ← (List.range snapshotProtocols.length).toArray.mapM fun index =>
    `((Snapshot.protocolFunctions $snapshot)[$(Syntax.mkNumLit (toString index))]'(by decide +kernel))
  emit naming (← `(theorem $(mkIdent `protocols_checked) :
      checkUnitProtocols $snapshot $domainsId $summariesId $headersId $orderedId =
        .ok ($unitId).protocols :=
      checkUnitProtocols_of_checked [$checkedList,*]
        (by rw [show Snapshot.protocolFunctions $snapshot = [$sourceList,*] from rfl]
            exact $sources)
        (by kernel_rfl)))
  emit naming (← `(theorem $(mkIdent `native_metadata_checked) :
      (checkNativeApplicationBudgets $snapshot).isOk = true := by decide +kernel))
  emit naming (← `(theorem $(mkIdent `effective_sites_checked) :
      checkEffectiveProtocolSites $snapshot = .ok () := by kernel_rfl))
  emit naming (← `(theorem $(mkIdent `metadata_checked) : checkApplicationMetadata $snapshot = .ok () :=
      checkApplicationMetadata_of_checks $(mkIdent `native_metadata_checked) $(mkIdent `effective_sites_checked)))
  emit naming (← `(theorem $(mkIdent `payload_linked) :
      linkUnitPayload $snapshot $orderedId ($unitId).protocols = .ok $unitId :=
      linkUnitPayload_of_payload _ _ _ rfl rfl))
  emit naming (← `(/-- All declarations, callback trees and metadata phases of the original unit. -/
    theorem $(mkIdent naming.admission) : check $snapshot = .ok $programId :=
      check_parts _ $unitId (check_payload_of_phases $(mkIdent `headers_checked) $(mkIdent `helpers_checked)
        $(mkIdent `protocols_checked) $(mkIdent `metadata_checked) $(mkIdent `payload_linked))))
  let importedId := mkIdent naming.imported
  emit naming (← `(def $importedId : Imported $snapshot := ⟨$programId, $(mkIdent naming.admission)⟩))
  unless naming.closed do
    emit naming (← `(theorem $(mkIdent `exact_subject) : ($programId).snapshot = $snapshot :=
        ($importedId).exactSubject))
  for entry in protocolOrder do
    emit naming (← `(theorem $(theoremIdent entry "_member") : $(definitionIdent entry) ∈ ($unitId).protocols :=
      by structured_mem))
  let some entry := protocolOrder[entryIndex]? | throwError "{naming.command}: missing entry protocol"
  unless naming.closed do
    emit naming (← `(theorem $(mkIdent `entry_selection) : ($unitId).entry = $(definitionIdent entry) := rfl))
    emit naming (← `(theorem $(mkIdent `entry_signature) :
        ($programId).payload.entry.signature = $(entry.signature) := rfl))
    emit naming (← `(theorem $(mkIdent `entry_raw) :
        ($programId).payload.entry.raw = ($(entry.body)).erase := rfl))
  emit naming (← `(/-- Complete original-to-checked association includes every nested callback. -/
    theorem $(mkIdent `complete_protocol_source) (definition : CheckedProtocol)
      (member : definition ∈ ($unitId).protocols) :
      ∃ function domains signatures summaries,
        .function function ∈ ($snapshot).definitions ∧
        function.kind = .protocol ∧
        checkUnitHeaders $snapshot = .ok (domains, signatures, summaries) ∧
        checkProtocol $snapshot domains summaries function signatures = .ok definition ∧
        resolveProtocolSignature function = .ok definition.signature ∧
        lowerProtocol $snapshot domains summaries signatures function
          definition.signature = .ok definition.raw :=
      ($importedId).protocolSource member))
  emit naming (← `(/-- Every checked helper is the exact checked form of a retained declaration. -/
    theorem $(mkIdent `complete_helper_source) (definition : CheckedDefinition)
      (member : definition ∈ ($unitId).definitions) :
      ∃ original domains headers summaries,
        original ∈ ($snapshot).definitions ∧ original.kind ≠ .protocol ∧
        checkUnitHeaders $snapshot = .ok (domains, headers, summaries) ∧
        checkDefinition $snapshot domains summaries original = .ok definition :=
      ($importedId).helperSource member))
  emit naming (← `(/-- Every original protocol is admitted to one exact checked tree. -/
    theorem $(mkIdent `complete_original_protocol) (function : Zkc.Source.Structured.Function)
      (member : .function function ∈ ($snapshot).definitions)
      (kind : function.kind = .protocol) :
      ∃ domains headers summaries,
        checkUnitHeaders $snapshot = .ok (domains, headers, summaries) ∧
        ∃ definition, definition ∈ ($unitId).protocols ∧
          checkProtocol $snapshot domains summaries function headers = .ok definition ∧
          ∀ other, other ∈ ($unitId).protocols →
            checkProtocol $snapshot domains summaries function headers = .ok other →
              other = definition :=
      ($importedId).protocolChecked member kind))
  return entry

/-- Generated declarations are elaborated synchronously, so a refused one is
seen before the next is emitted. A refused command restores the environment it
started from: no partial unit is left behind. -/
meta def synchronously (action : CommandElabM Unit) : CommandElabM Unit := do
  let environment ← getEnv
  try
    withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) action
  catch error =>
    setEnv environment
    throw error

@[command_elab structuredViews] meta def elabStructuredViews : CommandElab := fun stx => synchronously do
  let helperEntries ← stx[4].getSepArgs.mapM (parseEntry "Helper")
  let protocolEntries ← stx[8].getSepArgs.mapM (parseEntry "Signature")
  discard <| emitViews ⟨stx[1]⟩ helperEntries protocolEntries

@[command_elab structuredClosedViews] meta def elabStructuredClosedViews : CommandElab :=
    fun stx => synchronously do
  let snapshot : Term := ⟨stx[1]⟩
  let rootBody : Term := ⟨stx[11]⟩
  let helperEntries ← stx[4].getSepArgs.mapM (parseEntry "Helper")
  let protocolEntries ← stx[8].getSepArgs.mapM (parseEntry "Signature")
  let naming : Naming :=
    { program := `subject, imported := `subjectImported, admission := `subject_admission,
      helperRaw := "_exact", helperBody := "_body_exact", closed := true,
      command := "structured_closed_views" }
  let entry ← emitViews snapshot helperEntries protocolEntries naming
  let signature := entry.signature
  let program := mkIdent `program
  let imported := mkIdent `imported
  emit naming (← `(def $(mkIdent `root) : ClosedRoot :=
      ⟨($signature).name, ($signature).inputs, ($signature).outputs, ($rootBody).erase, $rootBody,
        ($rootBody).elaborate_erase⟩))
  emit naming (← `(def $(mkIdent `payload) : Payload where
      definitions := $(mkIdent `definitions)
      entry := $(mkIdent `root)
      linked := ($(mkIdent `unit)).linked
      entryLinked := by decide +kernel))
  emit naming (← `(def $program : ClosedProgram :=
      ⟨$(mkIdent `subject), $(mkIdent `payload), by kernel_rfl⟩))
  emit naming (← `(/-- Complete actual-source admission, including the closed projection. -/
    theorem $(mkIdent `kernel_admission) : checkClosed $snapshot = .ok $program :=
      checkClosed_of_check $(mkIdent `subject_admission) ($program).projected))
  emit naming (← `(def $imported : ClosedImported $snapshot := ⟨$program, $(mkIdent `kernel_admission)⟩))
  emit naming (← `(theorem $(mkIdent `exact_subject) : ($program).snapshot = $snapshot :=
      ($imported).exactSubject))
  emit naming (← `(theorem $(theoremIdent entry "_selected") :
      ($program).subject.payload.entry = $(definitionIdent entry) := rfl))
  emit naming (← `(theorem $(theoremIdent entry "_exact") :
      ($program).subject.payload.entry.raw = ($(entry.body)).erase := rfl))
  emit naming (← `(theorem $(theoremIdent entry "_body_exact") :
      ($program).subject.payload.entry.body = $(entry.body) := rfl))
  emit naming (← `(theorem $(mkIdent `entry_exact) : ($program).payload.entry.raw = ($rootBody).erase := rfl))
  emit naming (← `(theorem $(mkIdent `entry_body_exact) : ($program).payload.entry.body = $rootBody := rfl))
  for helper in helperEntries do
    emit naming (← `(theorem $(theoremIdent helper "_member") :
        $(definitionIdent helper) ∈ ($program).payload.definitions := by structured_mem))

@[command_elab structuredAssociations] meta def elabStructuredAssociations : CommandElab := fun stx => do
  let views := stx[1].getId
  let unit := mkIdent (views ++ `unit)
  for entry in ← stx[3].getSepArgs.mapM (parseEntry "Helper") do
    let definition := mkIdent (views ++ suffixed entry.name "Definition")
    let member := theoremIdent entry "_member"
    let signature := theoremIdent entry "_signature"
    let raw := theoremIdent entry "_shared_raw"
    elabCommand (← `(theorem $member : $definition ∈ ($unit).definitions := by structured_mem))
    elabCommand (← `(theorem $signature : ($definition).helper = $(entry.signature) := rfl))
    elabCommand (← `(theorem $raw : ($definition).raw = ($(entry.body)).erase := rfl))
    elabCommand (← `(theorem $(theoremIdent entry "_association") :
        BodyIn ($unit).definitions $(entry.signature) $(entry.body) := BodyIn.of_mem $member $signature $raw))

end UnitViews

end Zkc.Source.Structured
