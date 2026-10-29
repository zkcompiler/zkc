module

public import ZkcSecurity.Tools.SubjectABI
public import ZkcTools.StructuredSource.Constructed

@[expose] public section

/-! Untrusted syntax production, separate from the elaborators used by checked
subject modules. Configuration selects an admitted subject and output module. -/
set_option autoImplicit false
namespace ZkcSecurity.Generation.SubjectABI
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair
open ZkcSecurity.Tools.SubjectABI
open ZkcTools.StructuredSource.Constructed (literal)

/-- An optional presentation of the fixed retained input clauses. The emitted
law is checked at `∀ values, (∀ index isInput, subject.inputClause values index
isInput) ↔ condition values`; it cannot replace the subject's input contract. -/
structure ClauseInterpretation where
  condition : String
  law : String

structure Output where
  moduleName : String
  subjectModule : String
  /-- Optional installation modules; the fixed subject need not import proofs. -/
  imports : List String := []
  clauseInterpretation : Option ClauseInterpretation := none

def inputName (index : Nat) : String := "input" ++ toString index
def call (name : String) (arguments : List String) : String :=
  "(" ++ " ".intercalate (name :: arguments) ++ ")"
def values (arguments : List String) : String :=
  arguments.foldr (fun argument rest => "(.cons " ++ argument ++ " " ++ rest ++ ")") ".nil"
def binder (index : Nat) (ty : Ty) (optional : Bool) : String :=
  " (" ++ inputName index ++ " : " ++ (if optional then "Option " else "") ++
    "(model.Value " ++ literal ty ++ "))"
def binders (types : List Ty) (optional : Ty → Bool) : String :=
  String.join ((types.zipIdx).map fun (ty, index) => binder index ty (optional ty))
def existentialBinders (declarations : String) : String :=
  if declarations.isEmpty then "" else "∃" ++ declarations ++ ", "
def existential (types : List Ty) (optional : Ty → Bool) : String :=
  existentialBinders (binders types optional)
def names (types : List Ty) : List String := (List.range types.length).map inputName
def isService (ty : Ty) : Bool := ty.isService

/-- Emit the existing nominal data constructor; no second carrier enumeration
or recursive data encoding is owned by the generator. The kernel checks the
closed capability-exclusion proof in the generated module. -/
def encoded (ty : Ty) (name : String) : Except String String :=
  if ty.isService then .error "subject-abi-service-projection"
  else if ty.isHandle then .error "subject-abi-handle-projection"
  else .ok (".data ⟨" ++ literal ty ++ ", by decide, " ++ name ++ "⟩")

def atPositions (types : List Ty) (positions : List Nat) : Except String (List Ty) :=
  positions.mapM fun position => match types[position]? with
    | some ty => pure ty
    | none => throw "subject-abi-input-position"

def environment (types : List Ty) (positions : List Nat) (history : String)
    (suite : String) (profile : Profile) : Except String String := do
  let entries ← positions.mapM fun index => do
    let some ty := types[index]? | throw "subject-abi-input-position"
    encoded ty (inputName index)
  let entries := match profile with
    | .plain => entries
    | .fiatShamir _ => entries ++ [".transcript " ++ literal suite ++ " " ++ history]
  pure ("[" ++ ", ".intercalate entries ++ "]")

def rawEnvironment (types : List Ty) (positions : List Nat) : Except String String := do
  let entries ← positions.mapM fun index => do
    let some ty := types[index]? | throw "subject-abi-input-position"
    encoded ty (inputName index)
  pure ("[" ++ ", ".intercalate entries ++ "]")

/-- ABI bounds are derived only from source sorts; shape and round limits
belong to retained input clauses and their separately checked interpretation. -/
def representationProposition (types : List Ty) : String :=
  let bounds := types.zipIdx.filterMap fun (ty, index) => match ty with
    | .index => some (inputName index ++ " < indexLimit")
    | .vector _ => some (inputName index ++ ".length < indexLimit")
    | .sequence _ | .product .. => some ("inputRepresentable (carriers := model.toCarriers) " ++
        literal ty ++ " (some " ++ inputName index ++ ")")
    | _ => none
  if bounds.isEmpty then "True" else " ∧ ".intercalate bounds

/-- Print the explicit constructor rather than inherited record `Repr` syntax. -/
def contextLiteral (context : Context) : String :=
  let identity := literal context.entry ++ " " ++ literal context.roles ++ " " ++
    toString context.producer ++ " " ++ toString context.validator
  match context.profile with
  | .plain => "(Context.plain " ++ identity ++ ")"
  | .fiatShamir replacement =>
    "(Context.fiatShamir " ++ identity ++ " " ++ toString replacement.service ++ " " ++
      literal replacement.contract ++ " " ++ literal replacement.request ++ " " ++
      literal replacement.suite ++ " " ++ literal replacement.draws ++ ")"

structure Metadata where
  types : List Ty
  producerPositions : Option (List Nat)
  publicPositions : List Nat
  targetPositions : Except String (List Nat)
  targetPurposes : List String
  clausesEmpty : Bool
  suite : String
  context : Context
  originalExport : String
  producerExport : String
  validatorExport : String
  producerIdentity : String × String × String
  validatorIdentity : String × String × String

def metadata {model : DomainModel} {original : Snapshot} {imported : Imported original}
    {selected : AuthoredPair.Selection original}
    (subject : Subject model original imported selected) : Metadata where
  types := subject.target.owner.protocol.inputs
  producerPositions := (entryInterface original).map fun (types, interface) =>
    dataInputs types interface.inputScopes selected.policy.producer
  publicPositions := selected.policy.publicInputs
  targetPositions := selectorPositions subject.target.application.selectors
  targetPurposes := subject.target.application.relation.declaration.purposes
  clausesEmpty := subject.target.owner.contract.clauses.all (fun clause => clause.kind != .input)
  suite := selected.policy.suite
  context := subject.selection.context
  originalExport := subject.originalExport
  producerExport := subject.producerExport
  validatorExport := subject.validatorExport
  producerIdentity := (selected.artifacts.producer.source, selected.artifacts.producer.candidate,
    selected.artifacts.producer.symbol)
  validatorIdentity := (selected.artifacts.validator.source, selected.artifacts.validator.candidate,
    selected.artifacts.validator.symbol)

def source (metadata : Metadata) (output : Output) : Except String String := do
  let types := metadata.types
  let some producerPositions := metadata.producerPositions | throw "subject-abi-source-interface"
  let publicPositions := metadata.publicPositions
  -- This presentation stores every data coordinate as present. Refuse profiles
  -- whose actual preparation may leave such a coordinate absent; the fixed
  -- subject semantics must never be strengthened to fit a generated ABI.
  for (type, index) in types.zipIdx do
    if Domain.dataType type && !producerPositions.contains index && !publicPositions.contains index then
      throw ("subject-abi-uncovered-data-input:" ++ toString index)
  let publicTypes ← atPositions types publicPositions
  let targetPositions ← metadata.targetPositions
  let hasPrivate := targetPositions.any (fun position => !publicPositions.contains position)
  let validatorComponents ← (targetPositions.zipIdx).mapM fun (position, argument) => do
    if publicPositions.contains position then pure ("(some " ++ inputName position ++ ")")
    else
      if metadata.targetPurposes[argument]? != some "witness" then
        throw "subject-abi-private-nonwitness"
      let ref := (List.range argument).foldl (fun ref _ => "(.there " ++ ref ++ ")") ".here"
      pure ("(witness _ (validatorSubject.target.application.selectors.get " ++ ref ++ "))")
  let n := names types
  let all := call "sourceInputs" n
  let present := call "inputs" n
  let presentSource := call "sourceInputs" ((types.zip n).map fun (ty, name) =>
    if isService ty then name else "(some " ++ name ++ ")")
  let rawBinders := binders types (fun _ => true)
  let dataBinders := binders types isService
  let publicBinders := String.join ((publicTypes.zip publicPositions).map fun (ty, index) => binder index ty false)
  let publicNames := publicPositions.map inputName
  let targetPublicPositions := publicPositions.filter targetPositions.contains
  let targetPublicNames := targetPublicPositions.map inputName
  let targetPublicBinders := String.join (targetPublicPositions.map fun index => binder index types[index]! false)
  let producerArgumentPositions := (List.range types.length).filter fun index =>
    producerPositions.contains index ||
      (match metadata.context.profile with
       | .plain => false
       | .fiatShamir _ => publicPositions.contains index)
  let producerNames := producerArgumentPositions.map inputName
  let producerBinders := String.join (producerArgumentPositions.map fun index => binder index types[index]! false)
  let targetNames := targetPositions.map inputName
  -- Declaration/call binders are distinct and in source order. The payload
  -- above remains in selector order, including every repeated selector.
  let targetBinderPositions := (List.range types.length).filter targetPositions.contains
  let targetBinderNames := targetBinderPositions.map inputName
  let targetBinders := String.join (targetBinderPositions.map fun index => binder index types[index]! false)
  let history := call "initialHistory" publicNames
  let producer ← environment types producerPositions history metadata.suite metadata.context.profile
  let validator ← environment types publicPositions history metadata.suite metadata.context.profile
  let producerData ← rawEnvironment types producerPositions
  let validatorData ← rawEnvironment types publicPositions
  let pair := "(" ++ call "producerInputs" producerNames ++ ", " ++ call "validatorInputs" publicNames ++ ")"
  let representable := representationProposition types
  let automaticClauses := metadata.clausesEmpty && output.clauseInterpretation.isNone
  let clauseDeclarations := if automaticClauses then
    "theorem source_clauses (values : subject.Inputs) :\n" ++
    "    ∀ index isInput, subject.inputClause values index isInput :=\n" ++
    "  Subject.no_input_clauses subject (by decide +kernel) values\n\n"
    else
      let condition := match output.clauseInterpretation with
        | some interpretation => "(" ++ interpretation.condition ++ ") values"
        | none => "source_input_condition subject on values"
      let proof := match output.clauseInterpretation with
        | some interpretation => "(" ++ interpretation.law ++ ") values"
        | none => "by source_input_clauses"
      "def inputCondition (values : subject.Inputs) : Prop :=\n  " ++ condition ++ "\n\n" ++
      "theorem source_clauses (values : subject.Inputs) :\n" ++
      "    (∀ index isInput, subject.inputClause values index isInput) ↔ inputCondition values :=\n  " ++
      proof ++ "\n\n"
  let honestCondition := if automaticClauses then representable
    else "(" ++ representable ++ ") ∧ " ++
      (if output.clauseInterpretation.isNone then "(source_input_condition subject on " ++ present ++ ")"
       else "inputCondition " ++ present)
  let unpacked := (List.range types.length).map fun index =>
    "(TypedABI.unpack data)" ++ String.join (List.replicate index ".2") ++ ".1"
  let dataPair := "(" ++ call "producerInputs" (producerArgumentPositions.map (fun index => unpacked[index]!)) ++ ", " ++
    call "validatorInputs" (publicPositions.map (fun index => unpacked[index]!)) ++ ")"
  let producerDataName := if producerArgumentPositions.isEmpty then "_data" else "data"
  let validatorDataName := if publicPositions.isEmpty then "_data" else "data"
  let pairDataName := if producerArgumentPositions.isEmpty && publicPositions.isEmpty then "_data" else "data"
  let imports := ([output.subjectModule, "ZkcSecurity.Tools.SubjectABI", "ZkcSecurity.Tools.SourceInputClauses"] ++ output.imports).eraseDups
  let mut text := "module\n\n" ++ String.join (imports.map ("public import " ++ · ++ "\n")) ++
    "\n@[expose] public section\nnoncomputable section\n\n" ++
    "/-! Generated from the actual admitted subject, source ABI, input clauses\n" ++
    "and retained selectors. Regenerate; do not hand edit. Input formula semantics\n" ++
    "are reduced in Lean. Target mathematics requires its own checked laws. -/\n" ++
    "set_option autoImplicit false\nset_option maxRecDepth 50000\nset_option maxHeartbeats 8000000\n" ++
    "namespace " ++ output.moduleName ++ "\n" ++
    "open Zkc.Source Zkc.Source.Structured Zkc.Construction\n" ++
    "open ZkcSecurity.Claims.HonestPair ZkcSecurity.Tools.SubjectABI\n" ++
    "open " ++ output.subjectModule ++ "\n\n" ++
    "abbrev model := subject.domainModel\n" ++
    "abbrev Data := Values (TypedABI.Slot Domain.dataType model.Value) subject.target.owner.protocol.inputs\n\n" ++
    "theorem source_types : subject.target.owner.protocol.inputs = " ++ literal types ++ " := rfl\n" ++
    "theorem public_positions : selected.policy.publicInputs = " ++ literal publicPositions ++ " := rfl\n" ++
    "theorem public_types : validatorArtifacts.publics = " ++ literal publicTypes ++ " := rfl\n" ++
    "theorem target_positions : selectorPositions subject.target.application.selectors = .ok " ++ literal targetPositions ++ " := rfl\n" ++
    "theorem artifact_identities :\n" ++
    "    (artifacts.producer.source, artifacts.producer.candidate, artifacts.producer.symbol) = " ++ literal metadata.producerIdentity ++ " ∧\n" ++
    "    (artifacts.validator.source, artifacts.validator.candidate, artifacts.validator.symbol) = " ++ literal metadata.validatorIdentity ++ " := by decide +kernel\n\n" ++
    "def sourceInputs" ++ rawBinders ++ " : subject.Inputs :=\n  " ++ values n ++ "\n\n" ++
    "def data" ++ dataBinders ++ " : Data :=\n  " ++ values n ++ "\n\n" ++
    "def inputs" ++ dataBinders ++ " : subject.Inputs :=\n  TypedABI.optional Domain.dataType " ++ call "data" n ++ "\n\n" ++
    "theorem sourceInputs_surjective (values : subject.Inputs) :\n    " ++ existential types (fun _ => true) ++
      "values = " ++ all ++ " := by subject_abi_surjective\n\n" ++
    "theorem data_surjective (values : Data) :\n    " ++ existential types isService ++
      "values = " ++ call "data" n ++ " := by subject_abi_surjective\n\n" ++
    "def statement" ++ publicBinders ++ " : validatorArtifacts.Statement model :=\n  " ++ values publicNames ++ "\n\n" ++
    "theorem statement_surjective (values : validatorArtifacts.Statement model) :\n    " ++
      existentialBinders publicBinders ++ "values = " ++ call "statement" publicNames ++ " := by subject_abi_surjective\n\n" ++
    "abbrev StatementData := TypedABI.Fields model.Value validatorArtifacts.publics\n\n" ++
    "def statementData (values : validatorArtifacts.Statement model) : StatementData := TypedABI.unpack values\n" ++
    "def statementOfData (fields : StatementData) : validatorArtifacts.Statement model := TypedABI.pack fields\n\n" ++
    "theorem statementOfData_statementData (values : validatorArtifacts.Statement model) :\n" ++
    "    statementOfData (statementData values) = values := TypedABI.pack_unpack values\n\n" ++
    "theorem statementData_statementOfData (fields : StatementData) :\n" ++
    "    statementData (statementOfData fields) = fields := TypedABI.unpack_pack fields\n\n" ++
    "def initialHistory" ++ publicBinders ++ " : Domain.History model.toCarriers :=\n" ++
    "  Domain.PublicBinding.history subject.originalExport selected.policy.publicInputs\n" ++
    "    " ++ call "statement" publicNames ++ " subject.publicBindingArity subject.publicBindingData\n\n" ++
    "def producerInputs" ++ producerBinders ++ " : Domain.Environment model.toCarriers :=\n  " ++ producer ++ "\n\n" ++
    "def validatorInputs" ++ publicBinders ++ " : Domain.Environment model.toCarriers :=\n  " ++ validator ++ "\n\n" ++
    "theorem producer_sorts" ++ producerBinders ++ " :\n" ++
    "    Domain.sortsMatch selected.artifacts.producer.inputs " ++ call "producerInputs" producerNames ++ " = true := rfl\n\n" ++
    "theorem validator_sorts" ++ publicBinders ++ " :\n" ++
    "    Domain.sortsMatch selected.artifacts.validator.inputs " ++ call "validatorInputs" publicNames ++ " = true := rfl\n\n" ++
    "theorem runtimeInputs_eq" ++ dataBinders ++ " :\n" ++
    "    subject.runtimeInputs " ++ present ++ " = some " ++ pair ++ " := by\n" ++
    "  exact Subject.runtime_of_projections subject " ++ present ++ " (by rfl)\n" ++
    "    " ++ producerData ++ " " ++ validatorData ++ " " ++ call "statement" publicNames ++ "\n" ++
    "    (by rfl) (by rfl) (by rfl)\n\n"
  -- The preparation proof is emitted below as an application of shared
  -- extensional elimination; it never duplicates a per-root case script.
  text := text ++ "theorem preparation (values : subject.Inputs) :\n" ++
    "    subject.runtimeInputs values = (TypedABI.complete Domain.dataType values).map\n" ++
    "      (fun (" ++ pairDataName ++ " : Data) => " ++ dataPair ++ ") := by\n" ++
    "  rw [Subject.runtime_layout subject values " ++ literal producerPositions ++ " (by rfl)]\n" ++
    "  subject_abi_options\n\n" ++
    "def abi : Subject.ABI subject where\n" ++
    "  Data := Data\n  pack := TypedABI.optional Domain.dataType\n" ++
    "  complete := TypedABI.complete Domain.dataType\n" ++
    "  complete_iff := TypedABI.complete_eq_some_iff Domain.dataType\n" ++
    "  producer := fun " ++ producerDataName ++ " => " ++ call "producerInputs" (producerArgumentPositions.map (fun index => unpacked[index]!)) ++ "\n" ++
    "  validator := fun " ++ validatorDataName ++ " => " ++ call "validatorInputs" (publicPositions.map (fun index => unpacked[index]!)) ++ "\n" ++
    "  preparation := preparation\n" ++
    "  producerSorts := fun " ++ producerDataName ++ " => producer_sorts" ++ String.join (producerArgumentPositions.map (fun index => " " ++ unpacked[index]!)) ++ "\n" ++
    "  validatorSorts := fun " ++ validatorDataName ++ " => validator_sorts" ++ String.join (publicPositions.map (fun index => " " ++ unpacked[index]!)) ++ "\n\n" ++
    clauseDeclarations ++
    "set_option backward.isDefEq.respectTransparency false in\n" ++
    "theorem representable_iff" ++ dataBinders ++ " :\n" ++
    "    inputsRepresentable " ++ present ++ " ↔ (" ++ representable ++ ") := by\n" ++
    "  change inputsRepresentable " ++ presentSource ++ " ↔ _\n" ++
    "  simp [inputsRepresentable, inputRepresentable, sourceInputs]\n\n" ++
    "theorem honestInput_iff" ++ dataBinders ++ " :\n" ++
    "    subject.HonestInput " ++ present ++ " ↔ (" ++ honestCondition ++ ") := by\n" ++
    "  exact (abi.honest_pack_iff " ++ call "data" n ++ ").trans\n" ++
    (if automaticClauses then
      "    ((and_iff_left (source_clauses _)).trans " ++ call "representable_iff" n ++ ")\n\n"
    else
      "    (and_congr " ++ call "representable_iff" n ++
        (if output.clauseInterpretation.isNone then " (by source_input_clauses))\n\n"
         else " (source_clauses _))\n\n")) ++
    "theorem honestInput_exists (values : subject.Inputs) (honest : subject.HonestInput values) :\n" ++
    "    " ++ existential types isService ++ "values = " ++ present ++ " := by\n" ++
    "  obtain ⟨data, rfl⟩ := abi.honest_exists values honest\n" ++
    "  subject_abi_surjective\n\n" ++
    "def arguments" ++ targetBinders ++ " : Values model.Value subject.target.application.relation.declaration.inputs :=\n  " ++
    values targetNames ++ "\n\n" ++
    "theorem application_read" ++ dataBinders ++ " :\n" ++
    "    subject.target.application.read {} (subject.boundary " ++ present ++ ")\n" ++
    "      (subject.assignments " ++ present ++ ") = some " ++ call "arguments" targetBinderNames ++ " := rfl\n\n" ++
    "def validatorArguments" ++ targetPublicBinders ++ " (" ++ (if hasPrivate then "witness" else "_witness") ++ " : validatorSubject.Witness) :\n" ++
    "    Option (Values model.Value validatorSubject.target.application.relation.declaration.inputs) :=\n" ++
    "  RoleFamily.sequence " ++ values validatorComponents ++ "\n\n" ++
    "theorem validator_application_read" ++ publicBinders ++ " (witness : validatorSubject.Witness) :\n" ++
    "    validatorSubject.target.application.read {} (validatorSubject.boundary " ++ call "statement" publicNames ++ ")\n" ++
    "      (validatorSubject.assignments " ++ call "statement" publicNames ++ " witness) =\n" ++
    "      " ++ (if hasPrivate then call "validatorArguments" (targetPublicNames ++ ["witness"])
      else "some " ++ values targetNames) ++ " := by\n  rfl\n\n" ++
    "theorem context_eq : subject.selection.context = " ++ contextLiteral metadata.context ++ " := rfl\n\n" ++
    "theorem pair_eq : selected.artifacts = artifacts := rfl\n\n" ++
    "theorem original_export : subject.originalExport = " ++ literal metadata.originalExport ++ " := rfl\n" ++
    "theorem producer_export : subject.producerExport = " ++ literal metadata.producerExport ++ " := rfl\n" ++
    "theorem validator_export : subject.validatorExport = " ++ literal metadata.validatorExport ++ " := rfl\n\n" ++
    "end " ++ output.moduleName ++ "\n"
  return text

end ZkcSecurity.Generation.SubjectABI
