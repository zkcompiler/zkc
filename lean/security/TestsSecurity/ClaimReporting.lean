import ZkcSecurity.Claims.Canonical
import ZkcSecurity.Claims.Endpoint
import ZkcSecurity.Examples.Subjects.Schnorr.Registration
import ZkcSecurity.Examples.Subjects.ChaumPedersen.Contract
import ZkcSecurity.Registry
import Zkc.Claims.Receipt

/-! Actual request/receipt controls for interpreted-stage assurance reporting.
The source-shaped forking request uses admitted Schnorr artifacts and the
registered model; stage links are supplied independently of its family proof. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
-- Some negative coverage controls intentionally retain an unused String binder.
set_option linter.unusedVariables false
namespace TestsSecurity.ClaimReporting
open Zkc.Claims Zkc.Construction ZkcSecurity.Claims ZkcSecurity.Endpoint

def artifacts := ZkcSecurity.Examples.Subjects.Schnorr.artifacts

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F] [Fintype F] [Inhabited F] [SampleableType G]

def subject (endpoint : Semantics) : Subject F G artifacts endpoint where
  reference := ZkcSecurity.Examples.Subjects.Schnorr.sourceReference (stage endpoint)
  stageMatched := rfl
  compiled := ZkcSecurity.Examples.Subjects.Schnorr.compiled
  target := .retained ZkcSecurity.Examples.Subjects.Schnorr.Contract.retained
  importedRegistered := by intro declaration impossible; cases impossible
  sites := []
  sitesUnique := .nil
  sitesNativeUnique := .nil
  lowering := match endpoint with
    | .idealMeaning => PUnit.unit
    | .executableBytes => ZkcSecurity.Examples.Subjects.Schnorr.lowering
  extractors := ZkcSecurity.Examples.Subjects.Schnorr.Registration.extractionProfile.registry
    (.retained ZkcSecurity.Examples.Subjects.Schnorr.Contract.retained) rfl

def model : Model := ⟨.fixed, .symbolic "Q", "Q", "", .constant 0, none⟩

def knowledge (endpoint : Semantics) : KnowledgeRequest (subject (F := F) (G := G) endpoint) where
  registered := rfl
  model := model
  fixed := rfl

def replay (endpoint : Semantics) :
    SigmaJustification (subject (F := F) (G := G) endpoint)
      (ZkcSecurity.Examples.Subjects.Schnorr.Registration.extractionProfile (F := F) (G := G)) where
  Stmt := G
  PrvState := F
  handle := 0
  family := ZkcSecurity.Examples.Subjects.Schnorr.family
  model := ZkcSecurity.Examples.Subjects.Schnorr.model
  relation := (ZkcSecurity.Examples.Subjects.Schnorr.Registration.justification endpoint).relation
  shape := rfl
  recovery := (ZkcSecurity.Examples.Subjects.Schnorr.Registration.justification endpoint).recovery

example : (knowledge (F := F) (G := G) .idealMeaning).meaning :=
  knowledgeEndpoint _ (replay .idealMeaning)
example : (knowledge (F := F) (G := G) .executableBytes).meaning :=
  knowledgeEndpoint _ (replay .executableBytes)

def wire (endpoint : Semantics) : Wire.Request where
  subject := (subject (F := F) (G := G) endpoint).reference
  property := ⟨"knowledge", 0⟩
  model := ⟨exactUniform, [(some "level", .reference
    (match endpoint with | .idealMeaning => "levels.ideal" | .executableBytes => "levels.bytes")),
    (some "statement", .reference "statements.fixed"),
    (some "oracle", .application "oracles.random" (some 0) [(none, .reference "construction.provider")]),
    (some "queries", .reference "Q"), (some "budget_symbol", .reference "Q")]⟩
  target := (subject (F := F) (G := G) endpoint).targetReference
  accept := (subject (F := F) (G := G) endpoint).acceptance
  quantity := .guarantee ⟨forking, [
    (some "challenges", .application "cardinality" none [(none, .reference "bls12-381.fr")]),
    (some "cost", .application "prover_runs" none [(none, .natural 2)])]⟩

def modelRegistry (endpoint : Semantics) : ModelRegistry :=
  models .empty endpoint
noncomputable def registry (endpoint : Semantics) :=
  properties (F := F) (G := G) (art := artifacts) (endpoint := endpoint) (modelRegistry endpoint)

noncomputable def resolved (endpoint : Semantics) : Resolved (registry (F := F) (G := G) endpoint)
    Subject.reference (subject (F := F) (G := G) endpoint) (wire (F := F) (G := G) endpoint) where
  subjectMatched := rfl
  entry := ⟨⟨"knowledge", 0⟩, "zkc.property.knowledge/0",
    some (knowledgeProperty (modelRegistry endpoint))⟩
  registered := rfl
  property := knowledgeProperty (modelRegistry endpoint)
  defined := rfl
  arguments := .ok (knowledge endpoint)
  elaborated := by
    cases endpoint <;>
      simp [knowledgeProperty, knowledgeArguments, wire, subject, artifacts, modelRegistry, resolveModel,
        models, modelSchema, modelSchemaWith, responseDifference, ExtractionProfile.registry, named, checkArguments, reference, Numeric.natural, Numeric.naturalWith, Numeric.cardinality,
        Registry.lookup, Subject.check, Subject.targetReference, Subject.acceptance,
        Wire.TargetRef.matches, model, knowledge, checkCapabilities,
        show ZkcSecurity.Examples.Subjects.Schnorr.artifacts.original.catalogue.identitySort "bls12-381.fr" = some .field from rfl] <;> rfl

def meaning (endpoint : Semantics) : Evaluated (resolved (F := F) (G := G) endpoint) :=
  ⟨(knowledge endpoint).meaning, rfl⟩

def provenance : Provenance :=
  ⟨.endpoint, "ZkcSecurity.Claims.knowledgeEndpoint", ⟨"fs.forking", 0⟩,
    ["ZkcSecurity.Examples.Subjects.Schnorr.model", "ZkcSecurity.Endpoint.knowledge_soundness"],
    [⟨⟨"source.correspondence", 0⟩, .sourceCorrespondence, .infrastructure⟩]⟩

noncomputable def endpointReceipt (endpoint : Semantics) : Receipt (meaning (F := F) (G := G) endpoint) :=
  Receipt.ofEndpoint (knowledgeEndpoint (knowledge endpoint) (replay endpoint)) provenance (subject endpoint).stageLinkProofs
noncomputable def directReceipt (endpoint : Semantics) : Receipt (meaning (F := F) (G := G) endpoint) :=
  Receipt.ofTheorem (knowledgeEndpoint (knowledge endpoint) (replay endpoint)) provenance (subject endpoint).stageLinkProofs



def idealData : Wire.Request := wire (F := F) (G := G) .idealMeaning
def bytesData : Wire.Request := wire (F := F) (G := G) .executableBytes

noncomputable def idealReceipt : Receipt (meaning (F := F) (G := G) .idealMeaning) :=
  endpointReceipt .idealMeaning
noncomputable def bytesReceipt : Receipt (meaning (F := F) (G := G) .executableBytes) :=
  endpointReceipt .executableBytes
noncomputable def omittedReceipt : Receipt (meaning (F := F) (G := G) .idealMeaning) :=
  Receipt.ofEndpoint (knowledgeEndpoint (knowledge .idealMeaning) (replay .idealMeaning)) provenance
noncomputable def bytesOmittedReceipt : Receipt (meaning (F := F) (G := G) .executableBytes) :=
  Receipt.ofEndpoint (knowledgeEndpoint (knowledge .executableBytes) (replay .executableBytes)) provenance

noncomputable def explicitFalse (_hypothesis : False) : Receipt (meaning (F := F) (G := G) .idealMeaning) :=
  idealReceipt
noncomputable def implicitFalse {_hypothesis : False} : Receipt (meaning (F := F) (G := G) .idealMeaning) :=
  idealReceipt
noncomputable def factFalse [Fact False] : Receipt (meaning (F := F) (G := G) .idealMeaning) := idealReceipt
noncomputable def inhabitedFalse [Inhabited False] : Receipt (meaning (F := F) (G := G) .idealMeaning) := idealReceipt
noncomputable def liftedFalse (_hypothesis : PLift False) : Receipt (meaning (F := F) (G := G) .idealMeaning) := idealReceipt

/-- A distinct subject reference, even though these test subjects share their
interpreted compiled artifact. Goal normalization must not erase this index. -/
def foreignSubject (endpoint : Semantics) : Subject F G artifacts endpoint :=
  { subject (F := F) (G := G) endpoint with
    reference := { (subject (F := F) (G := G) endpoint).reference with unitDigest := "foreign-unit" } }

def trueLinks (_subject : Subject F G artifacts .idealMeaning) : List Obligation :=
  [⟨"construction.checked", "false attribution", True, .infrastructure⟩]
def foreignLinks (_subject : Subject F G artifacts .idealMeaning) : List Obligation :=
  [(foreignSubject (F := F) (G := G) .idealMeaning).constructionLink]
def otherArtifactsSubject : Subject F G ZkcSecurity.Examples.Subjects.ChaumPedersen.artifacts .idealMeaning where
  reference := ZkcSecurity.Examples.Subjects.ChaumPedersen.sourceReference .compiledIdeal
  stageMatched := rfl
  compiled := ZkcSecurity.Examples.Subjects.ChaumPedersen.compiled
  target := .retained ZkcSecurity.Examples.Subjects.ChaumPedersen.Contract.retained
  importedRegistered := by intro declaration impossible; cases impossible
  sites := []
  sitesUnique := .nil
  sitesNativeUnique := .nil
  lowering := PUnit.unit
def otherArtifactsLinks (_subject : Subject F G artifacts .idealMeaning) : List Obligation :=
  [(otherArtifactsSubject (F := F) (G := G)).constructionLink]
def nativeSchemaLinks (_subject : Subject F G artifacts .idealMeaning) : List Obligation :=
  [⟨"construction.checked", "abstract export equality", ZkcSecurity.Registry.ExportDenotes
    artifacts artifacts, .infrastructure⟩]
def constructionLinks (subject : Subject F G artifacts .executableBytes) : List Obligation :=
  [subject.constructionLink]

noncomputable def extensionProperty {endpoint : Semantics}
    (links : Subject F G artifacts endpoint → List Obligation) :
    PropertyExport (Subject F G artifacts endpoint) :=
  { knowledgeProperty (modelRegistry endpoint) with requiredLinks := fun subject _ => links subject }

def extensionData (endpoint : Semantics) : Wire.Request :=
  { wire (F := F) (G := G) endpoint with property := ⟨"user.stage_reporting", 0⟩ }
noncomputable def extensionRegistry {endpoint : Semantics}
    (links : Subject F G artifacts endpoint → List Obligation) :=
  (⟨[⟨⟨"user.stage_reporting", 0⟩, "zkc.property.stage-reporting/0", some (extensionProperty links)⟩]⟩ :
    Registry (PropertyExport (Subject F G artifacts endpoint)))
noncomputable def extensionResolved {endpoint : Semantics}
    (links : Subject F G artifacts endpoint → List Obligation) :
    Resolved (extensionRegistry links) Subject.reference (subject endpoint)
      (extensionData (F := F) (G := G) endpoint) where
  subjectMatched := rfl
  entry := ⟨⟨"user.stage_reporting", 0⟩, "zkc.property.stage-reporting/0", some (extensionProperty links)⟩
  registered := rfl
  property := extensionProperty links
  defined := rfl
  arguments := .ok (knowledge endpoint)
  elaborated := (resolved (F := F) (G := G) endpoint).elaborated
noncomputable def extensionMeaning {endpoint : Semantics}
    (links : Subject F G artifacts endpoint → List Obligation) : Evaluated (extensionResolved links) :=
  ⟨(knowledge endpoint).meaning, rfl⟩

def extensionIdealData : Wire.Request := extensionData (F := F) (G := G) .idealMeaning
def extensionBytesData : Wire.Request := extensionData (F := F) (G := G) .executableBytes

noncomputable def trueReceipt : Receipt (extensionMeaning (F := F) (G := G) trueLinks) :=
  Receipt.ofEndpoint (knowledgeEndpoint (knowledge .idealMeaning) (replay .idealMeaning)) provenance
    (fun ⟨index, bounded⟩ => by
      have equal : index = 0 := Nat.lt_one_iff.mp bounded
      subst index
      exact some ⟨True.intro⟩)
noncomputable def foreignReceipt : Receipt (extensionMeaning (F := F) (G := G) foreignLinks) :=
  Receipt.ofEndpoint (knowledgeEndpoint (knowledge .idealMeaning) (replay .idealMeaning)) provenance
    (fun ⟨index, bounded⟩ => by
      have equal : index = 0 := Nat.lt_one_iff.mp bounded
      subst index
      exact some ⟨(foreignSubject .idealMeaning).constructionChecked⟩)
noncomputable def constructionOnlyReceipt : Receipt (extensionMeaning (F := F) (G := G) constructionLinks) :=
  Receipt.ofEndpoint (knowledgeEndpoint (knowledge .executableBytes) (replay .executableBytes)) provenance
    (fun ⟨index, bounded⟩ => by
      have equal : index = 0 := Nat.lt_one_iff.mp bounded
      subst index
      exact some ⟨(subject .executableBytes).constructionChecked⟩)
noncomputable def otherArtifactsReceipt : Receipt (extensionMeaning (F := F) (G := G) otherArtifactsLinks) :=
  Receipt.ofEndpoint (knowledgeEndpoint (knowledge .idealMeaning) (replay .idealMeaning)) provenance
    (fun ⟨index, bounded⟩ => by
      have equal : index = 0 := Nat.lt_one_iff.mp bounded
      subst index
      exact some ⟨otherArtifactsSubject.constructionChecked⟩)
noncomputable def nativeSchemaReceipt : Receipt (extensionMeaning (F := F) (G := G) nativeSchemaLinks) :=
  Receipt.ofEndpoint (knowledgeEndpoint (knowledge .idealMeaning) (replay .idealMeaning)) provenance
    (fun ⟨index, bounded⟩ => by
      have equal : index = 0 := Nat.lt_one_iff.mp bounded
      subst index
      exact some ⟨Eq.refl _⟩)
noncomputable def conditionalReceipt
    (assumed : (subject (F := F) (G := G) .idealMeaning).ConstructionChecked) :
    Receipt (meaning (F := F) (G := G) .idealMeaning) :=
  Receipt.ofEndpoint (knowledgeEndpoint (knowledge .idealMeaning) (replay .idealMeaning)) provenance
    (fun ⟨index, bounded⟩ => by
      have equal : index = 0 := Nat.lt_one_iff.mp bounded
      subst index
      exact some ⟨assumed⟩)

/- Selected built-ins remain canonical when unrelated exports are appended. -/
noncomputable def extendedRegistry : Registry (PropertyExport (Subject F G artifacts .idealMeaning)) :=
  { exports :=
      (registry (F := F) (G := G) .idealMeaning).exports ++
      [⟨⟨"user.unrelated", 0⟩, "zkc.property.unrelated/0", none⟩] }
noncomputable def extendedResolved : Resolved (extendedRegistry (F := F) (G := G))
    Subject.reference (subject .idealMeaning) (idealData (F := F) (G := G)) where
  subjectMatched := rfl
  entry := (resolved (F := F) (G := G) .idealMeaning).entry
  registered := rfl
  property := (resolved (F := F) (G := G) .idealMeaning).property
  defined := rfl
  arguments := (resolved (F := F) (G := G) .idealMeaning).arguments
  elaborated := (resolved (F := F) (G := G) .idealMeaning).elaborated
noncomputable def extendedMeaning : Evaluated (extendedResolved (F := F) (G := G)) :=
  ⟨(knowledge .idealMeaning).meaning, rfl⟩
noncomputable def extendedReceipt : Receipt (extendedMeaning (F := F) (G := G)) :=
  Receipt.ofEndpoint (knowledgeEndpoint (knowledge .idealMeaning) (replay .idealMeaning)) provenance
    (subject .idealMeaning).stageLinkProofs

/-- Duplicate exports are a checked lookup conflict, so no Resolved receipt can
be constructed from this registry without an additional false premise. -/
noncomputable def duplicateRegistry :=
  { extendedRegistry (F := F) (G := G) with exports :=
      (extendedRegistry (F := F) (G := G)).exports ++ [(resolved .idealMeaning).entry] }
example : (duplicateRegistry (F := F) (G := G)).lookup ⟨"knowledge", 0⟩ =
    .error (.conflict ⟨"knowledge", 0⟩) := rfl

/-- An actual charged argument does not confer capability meaning on a custom
property whose interpretation is True. All stage proofs are nevertheless real. -/
def actualSite : Site (subject (F := F) (G := G) .idealMeaning).compiled.context where
  label := "challenge"
  native := (ZkcSecurity.Examples.Subjects.Schnorr.compiled.context.draws.head (by decide +kernel)).1
  delivery := (ZkcSecurity.Examples.Subjects.Schnorr.compiled.context.draws.head (by decide +kernel)).2
  selected := by
    change (_, _) ∈ ZkcSecurity.Examples.Subjects.Schnorr.compiled.context.draws
    decide +kernel
  request := ZkcSecurity.Examples.Subjects.Schnorr.compiled.context.request.get (by decide +kernel)
  requestSelected := by
    change ZkcSecurity.Examples.Subjects.Schnorr.compiled.context.request = some _
    decide +kernel

def trivialCharged : SoundnessRequest (subject (F := F) (G := G) .idealMeaning) :=
  ⟨model, .charged ⟨[(actualSite, .constant 1)], by simp, by simp, by simp⟩⟩
noncomputable def trivialChargedProperty : PropertyExport (Subject F G artifacts .idealMeaning) where
  Arguments _ := Except Incomplete (SoundnessRequest (subject (F := F) (G := G) .idealMeaning))
  elaborate _ _ := .ok (.ok trivialCharged)
  meaning _ _ := .ok True
  requiredLinks admitted _ := admitted.stageLinks
def chargedExtensionData : Wire.Request :=
  { idealData (F := F) (G := G) with
    property := ⟨"user.trivial_charged", 0⟩
    quantity := .charged [("challenge", .natural 1)]
    capabilities := [⟨chargedReduction, []⟩] }
noncomputable def chargedExtensionRegistry : Registry (PropertyExport (Subject F G artifacts .idealMeaning)) :=
  ⟨[⟨⟨"user.trivial_charged", 0⟩, "zkc.property.trivial-charged/0", some trivialChargedProperty⟩]⟩
noncomputable def chargedExtensionResolved : Resolved (chargedExtensionRegistry (F := F) (G := G))
    Subject.reference (subject .idealMeaning) (chargedExtensionData (F := F) (G := G)) where
  subjectMatched := rfl
  entry := ⟨⟨"user.trivial_charged", 0⟩, "zkc.property.trivial-charged/0", some trivialChargedProperty⟩
  registered := rfl
  property := trivialChargedProperty
  defined := rfl
  arguments := .ok trivialCharged
  elaborated := rfl
noncomputable def chargedExtensionMeaning : Evaluated (chargedExtensionResolved (F := F) (G := G)) := ⟨True, rfl⟩
theorem trivialProof : True := True.intro
def trivialProvenance : Provenance :=
  ⟨.theorem, "TestsSecurity.ClaimReporting.trivialProof", ⟨"methods.trivial", 0⟩, [], []⟩
noncomputable def chargedExtensionReceipt : Receipt (chargedExtensionMeaning (F := F) (G := G)) :=
  Receipt.ofTheorem trivialProof trivialProvenance (subject .idealMeaning).stageLinkProofs

/-- Actual model coverage controls: the probability bound is universally valid,
so refusals isolate coverage rather than a missing family proof. -/
def adaptiveWire : Wire.Request :=
  { idealData (F := F) (G := G) with
    property := ⟨"soundness", 0⟩
    model := ⟨exactUniform, [(some "statement", .reference "statements.adaptive"),
      (some "queries", .reference "Q"), (some "budget_symbol", .reference "Q"),
      (some "application", .reference "application")]⟩
    quantity := .scalar (.natural 1) }
def adaptiveModel (binding : ApplicationBinding) : Model :=
  ⟨.adaptive, .symbolic "Q", "Q", binding.value, .constant 0, some binding⟩
def adaptiveRequest (binding : ApplicationBinding) : SoundnessRequest (subject (F := F) (G := G) .idealMeaning) :=
  ⟨adaptiveModel binding, .scalar (.constant 1)⟩
noncomputable def adaptiveRegistry (binding : ApplicationBinding) :=
  properties (F := F) (G := G) (art := artifacts) (endpoint := .idealMeaning)
    (models ⟨some binding⟩ .idealMeaning)
noncomputable def adaptiveResolved (binding : ApplicationBinding) (symbol : binding.symbol = "application") :
    Resolved (adaptiveRegistry (F := F) (G := G) binding) Subject.reference (subject .idealMeaning)
      (adaptiveWire (F := F) (G := G)) where
  subjectMatched := rfl
  entry := ⟨⟨"soundness", 0⟩, "zkc.property.soundness/0", some (soundnessProperty (models ⟨some binding⟩ .idealMeaning))⟩
  registered := rfl
  property := soundnessProperty (models ⟨some binding⟩ .idealMeaning)
  defined := rfl
  arguments := .ok (adaptiveRequest binding)
  elaborated := by
    have relationChecked : checkDefaultRelation
        ZkcSecurity.Examples.Subjects.Schnorr.compiled.imported.program.payload.definitions
        ZkcSecurity.Examples.Subjects.Schnorr.Contract.retained.formula.definition.helper =
          .ok () := by decide +kernel
    simp [soundnessProperty, soundnessArguments, adaptiveWire, idealData, wire, Subject.check,
      subject, Subject.targetReference, Subject.acceptance, Wire.TargetRef.matches, checkCapabilities,
      soundnessParameters, decodeSoundnessParameters, requireExactSoundness, relationChecked,
      resolveModel, models, Registry.lookup, modelSchema, modelSchemaWith, named, checkArguments, reference,
      ModelContext.resolveApplication, symbol, adaptiveRequest, adaptiveModel,
      soundnessParameters, decodeSoundnessParameters, requireExactSoundness]
    rfl
noncomputable def adaptiveMeaning (binding : ApplicationBinding) (symbol : binding.symbol = "application") :
    Evaluated (adaptiveResolved (F := F) (G := G) binding symbol) := ⟨(adaptiveRequest binding).meaning, rfl⟩
theorem adaptiveBound (binding : ApplicationBinding) : (adaptiveRequest (F := F) (G := G) binding).meaning := by
  intro prover queries _ _
  simp [Bound.value]
noncomputable def adaptiveReceipt (binding : ApplicationBinding) (symbol : binding.symbol = "application") :
    Receipt (adaptiveMeaning (F := F) (G := G) binding symbol) :=
  Receipt.ofTheorem (adaptiveBound binding)
    ⟨.theorem, "TestsSecurity.ClaimReporting.adaptiveBound", ⟨"methods.probability_one", 0⟩, [], []⟩
    (subject .idealMeaning).stageLinkProofs

def applicationData : Wire.Request := adaptiveWire (F := F) (G := G)
noncomputable def parameterReceipt (application : String) :=
  adaptiveReceipt (F := F) (G := G) ⟨"application", application, .parameter⟩ rfl
noncomputable def prefixReceipt (application : String) :=
  adaptiveReceipt (F := F) (G := G) ⟨"application", "prefix/" ++ application, .parameter⟩ rfl
noncomputable def constantReceipt (application : String) :=
  adaptiveReceipt (F := F) (G := G) ⟨"application", "constant", .parameter⟩ rfl
noncomputable def unrelatedReceipt (unrelated : String) :=
  adaptiveReceipt (F := F) (G := G) ⟨"application", unrelated, .parameter⟩ rfl
noncomputable def fixedReceipt :=
  adaptiveReceipt (F := F) (G := G) ⟨"application", "deployment-a", .fixed⟩ rfl
noncomputable def falselyFixedReceipt (application : String) :=
  adaptiveReceipt (F := F) (G := G) ⟨"application", "deployment-a", .fixed⟩ rfl

/- A replacement under the canonical key is not the canonical property. -/
noncomputable def replacedProperty : PropertyExport (Subject F G artifacts .idealMeaning) :=
  { knowledgeProperty (modelRegistry .idealMeaning) with meaning := fun _ _ => .ok True }
noncomputable def replacedRegistry : Registry (PropertyExport (Subject F G artifacts .idealMeaning)) :=
  ⟨[⟨⟨"knowledge", 0⟩, "zkc.property.knowledge/0", some replacedProperty⟩]⟩
noncomputable def replacedResolved : Resolved (replacedRegistry (F := F) (G := G))
    Subject.reference (subject .idealMeaning) (idealData (F := F) (G := G)) where
  subjectMatched := rfl
  entry := ⟨⟨"knowledge", 0⟩, "zkc.property.knowledge/0", some replacedProperty⟩
  registered := rfl
  property := replacedProperty
  defined := rfl
  arguments := .ok (knowledge .idealMeaning)
  elaborated := (resolved (F := F) (G := G) .idealMeaning).elaborated
noncomputable def replacedMeaning : Evaluated (replacedResolved (F := F) (G := G)) := ⟨True, rfl⟩
noncomputable def replacedReceipt : Receipt (replacedMeaning (F := F) (G := G)) :=
  Receipt.ofTheorem trivialProof trivialProvenance (subject .idealMeaning).stageLinkProofs

/-- Same interpretation at this input, but no registered-stage guard. Merely
containing the canonical modelSchema is insufficient. -/
def replacedModels : ModelRegistry :=
  ⟨[⟨exactUniform, "zkc.model.fiat-shamir/0", some (fun F finite snapshot actual application =>
    @modelSchema F finite snapshot .empty actual application)⟩]⟩
noncomputable def replacedModelRegistry :=
  properties (F := F) (G := G) (art := artifacts) (endpoint := .idealMeaning) replacedModels
noncomputable def replacedModelResolved : Resolved (replacedModelRegistry (F := F) (G := G))
    Subject.reference (subject .idealMeaning) (idealData (F := F) (G := G)) where
  subjectMatched := rfl
  entry := ⟨⟨"knowledge", 0⟩, "zkc.property.knowledge/0", some (knowledgeProperty replacedModels)⟩
  registered := rfl
  property := knowledgeProperty replacedModels
  defined := rfl
  arguments := .ok (knowledge .idealMeaning)
  elaborated := by
    simp [knowledgeProperty, knowledgeArguments, idealData, wire, subject, artifacts, resolveModel,
      replacedModels, modelSchema, modelSchemaWith, responseDifference, ExtractionProfile.registry, named, checkArguments, reference, Numeric.natural, Numeric.naturalWith, Numeric.cardinality,
      Registry.lookup, Subject.check, Subject.targetReference, Subject.acceptance,
      Wire.TargetRef.matches, model, knowledge, checkCapabilities,
      show ZkcSecurity.Examples.Subjects.Schnorr.artifacts.original.catalogue.identitySort "bls12-381.fr" = some .field from rfl]
    rfl
noncomputable def replacedModelMeaning : Evaluated (replacedModelResolved (F := F) (G := G)) :=
  ⟨(knowledge .idealMeaning).meaning, rfl⟩
noncomputable def replacedModelReceipt : Receipt (replacedModelMeaning (F := F) (G := G)) :=
  Receipt.ofEndpoint (knowledgeEndpoint (knowledge .idealMeaning) (replay .idealMeaning)) provenance
    (subject .idealMeaning).stageLinkProofs

/- Both registries may carry unrelated extensions. -/
def extendedModels : ModelRegistry :=
  ⟨(models .empty .idealMeaning).exports ++ [⟨⟨"models.unrelated", 0⟩, "zkc.model.unrelated/0", none⟩]⟩
noncomputable def bothExtendedRegistry : Registry (PropertyExport (Subject F G artifacts .idealMeaning)) :=
  ⟨(properties extendedModels).exports ++ [⟨⟨"user.unrelated", 0⟩, "zkc.property.unrelated/0", none⟩]⟩
noncomputable def bothExtendedResolved : Resolved (bothExtendedRegistry (F := F) (G := G))
    Subject.reference (subject .idealMeaning) (idealData (F := F) (G := G)) where
  subjectMatched := rfl
  entry := ⟨⟨"knowledge", 0⟩, "zkc.property.knowledge/0", some (knowledgeProperty extendedModels)⟩
  registered := rfl
  property := knowledgeProperty extendedModels
  defined := rfl
  arguments := .ok (knowledge .idealMeaning)
  elaborated := by
    have same : resolveModel extendedModels F artifacts.original .idealMeaning
        (idealData (F := F) (G := G)).model =
        resolveModel (modelRegistry .idealMeaning) F artifacts.original .idealMeaning
          (idealData (F := F) (G := G)).model := rfl
    have original : (knowledgeProperty (modelRegistry .idealMeaning)).elaborate
        (idealData (F := F) (G := G)) (subject .idealMeaning) = .ok (.ok (knowledge .idealMeaning)) :=
      (resolved (F := F) (G := G) .idealMeaning).elaborated
    simpa only [knowledgeProperty, knowledgeArguments, same] using original
noncomputable def bothExtendedMeaning : Evaluated (bothExtendedResolved (F := F) (G := G)) :=
  ⟨(knowledge .idealMeaning).meaning, rfl⟩
noncomputable def bothExtendedReceipt : Receipt (bothExtendedMeaning (F := F) (G := G)) :=
  Receipt.ofEndpoint (knowledgeEndpoint (knowledge .idealMeaning) (replay .idealMeaning)) provenance
    (subject .idealMeaning).stageLinkProofs


/- Manual extensions need no generator names. Their model registry is bound by
an admission certificate, independently of an elaborator returning True. -/
noncomputable def manualProperty : PropertyExport (Subject F G artifacts .idealMeaning) where
  Arguments _ := Unit
  elaborate _ _ := .ok ()
  meaning _ _ := .ok True
  requiredLinks admitted _ := admitted.stageLinks
noncomputable def manualRegistry : Registry (PropertyExport (Subject F G artifacts .idealMeaning)) :=
  ⟨[⟨⟨"user.manual", 0⟩, "zkc.property.manual/0", some manualProperty⟩]⟩
def manualData : Wire.Request :=
  { idealData (F := F) (G := G) with property := ⟨"user.manual", 0⟩ }
def wrongTargetData : Wire.Request :=
  { manualData (F := F) (G := G) with target := .retained "wrong" 9 "wrong" }
def wrongAcceptanceData : Wire.Request :=
  { manualData (F := F) (G := G) with accept := ⟨false, 9, 9, []⟩ }
def undefinedModelData : Wire.Request := manualData (F := F) (G := G)
def malformedModelData : Wire.Request :=
  { manualData (F := F) (G := G) with model := ⟨exactUniform, [(some "unexpected", .natural 0)]⟩ }
def wrongModelVersionData : Wire.Request :=
  { manualData (F := F) (G := G) with model := ⟨⟨exactUniform.name, 99⟩, []⟩ }
def undefinedModels : ModelRegistry := ⟨[⟨exactUniform, "zkc.model.fiat-shamir/0", none⟩]⟩
noncomputable def manualResolved (data : Wire.Request)
    (same : data.subject = (subject (F := F) (G := G) .idealMeaning).reference)
    (selected : data.property = ⟨"user.manual", 0⟩) :
    Resolved (manualRegistry (F := F) (G := G)) Subject.reference (subject .idealMeaning) data where
  subjectMatched := same
  entry := ⟨⟨"user.manual", 0⟩, "zkc.property.manual/0", some manualProperty⟩
  registered := by rw [selected]; rfl
  property := manualProperty
  defined := rfl
  arguments := ()
  elaborated := rfl
noncomputable def manualMeaning (data : Wire.Request)
    (same : data.subject = (subject (F := F) (G := G) .idealMeaning).reference)
    (selected : data.property = ⟨"user.manual", 0⟩) :
    Evaluated (manualResolved data same selected) := ⟨True, rfl⟩
noncomputable def manualCore (data : Wire.Request)
    (same : data.subject = (subject (F := F) (G := G) .idealMeaning).reference)
    (selected : data.property = ⟨"user.manual", 0⟩) :
    Receipt (manualMeaning data same selected) :=
  Receipt.ofTheorem trivialProof trivialProvenance (subject .idealMeaning).stageLinkProofs
noncomputable def manualBareReceipt := manualCore (F := F) (G := G) (manualData (F := F) (G := G)) rfl rfl
noncomputable def manualReceipt : AdmittedReceipt (modelRegistry .idealMeaning)
    (manualMeaning (F := F) (G := G) (manualData (F := F) (G := G)) rfl rfl) where
  receipt := manualBareReceipt (F := F) (G := G)
  checked := rfl
  modelAdmitted := ⟨model, rfl⟩
noncomputable def wrongTargetReceipt := manualCore (F := F) (G := G) (wrongTargetData (F := F) (G := G)) rfl rfl
noncomputable def wrongAcceptanceReceipt := manualCore (F := F) (G := G) (wrongAcceptanceData (F := F) (G := G)) rfl rfl

/-- False certificates are conditional controls, not admitted model results.
Their actual typed registry and resolveModel call must still be inspected. -/
noncomputable def undefinedModelReceipt (impossible : False) : AdmittedReceipt undefinedModels
    (manualMeaning (F := F) (G := G) (undefinedModelData (F := F) (G := G)) rfl rfl) where
  receipt := manualCore (F := F) (G := G) _ rfl rfl
  checked := rfl
  modelAdmitted := impossible.elim
noncomputable def malformedModelReceipt (impossible : False) : AdmittedReceipt (modelRegistry .idealMeaning)
    (manualMeaning (F := F) (G := G) (malformedModelData (F := F) (G := G)) rfl rfl) where
  receipt := manualCore (F := F) (G := G) _ rfl rfl
  checked := rfl
  modelAdmitted := impossible.elim
noncomputable def wrongModelVersionReceipt (impossible : False) : AdmittedReceipt (modelRegistry .idealMeaning)
    (manualMeaning (F := F) (G := G) (wrongModelVersionData (F := F) (G := G)) rfl rfl) where
  receipt := manualCore (F := F) (G := G) _ rfl rfl
  checked := rfl
  modelAdmitted := impossible.elim

/-- A generic endpoint Evidence constructor applied at the concrete endpoint
is positive. Its Semantics/LoweringRequirement telescope is not free here. -/
noncomputable def appliedEvidenceReceipt : AdmittedReceipt (modelRegistry .idealMeaning)
    (meaning (F := F) (G := G) .idealMeaning) where
  receipt := idealReceipt
  checked := rfl
  modelAdmitted := ⟨model, rfl⟩

namespace HigherOrder

/-- The callback's Evidence ancestry is absent from this generic definition. -/
def invoke {A : Type} {B : Sort _} (function : A → B) (argument : A) : B :=
  function argument

noncomputable def labeledEvidence (label : String) :=
  { ZkcSecurity.Examples.Subjects.Schnorr.knowledge (F := F) (G := G) .idealMeaning
      (subject (F := F) (G := G) .idealMeaning).lowering with
    hypotheses := [⟨label, .model, True, .proved True.intro⟩] }

noncomputable def labeledMethod (label : String) : SigmaJustification (subject (F := F) (G := G) .idealMeaning)
    (ZkcSecurity.Examples.Subjects.Schnorr.Registration.extractionProfile (F := F) (G := G)) :=
  { replay .idealMeaning with
    family := (labeledEvidence (F := F) (G := G) label).family
    model := (labeledEvidence (F := F) (G := G) label).model }

theorem directProof : (meaning (F := F) (G := G) .idealMeaning).proposition :=
  knowledgeEndpoint (knowledge .idealMeaning) (labeledMethod "unregistered.higherorder.control")

theorem wrappedProof : (meaning (F := F) (G := G) .idealMeaning).proposition :=
  invoke (fun label : String => knowledgeEndpoint (knowledge .idealMeaning) (labeledMethod label))
    "unregistered.higherorder.control"

theorem positiveProof : (meaning (F := F) (G := G) .idealMeaning).proposition :=
  invoke (fun _ : String => knowledgeEndpoint (knowledge .idealMeaning) (replay .idealMeaning)) ""

noncomputable def directReceipt : Receipt (meaning (F := F) (G := G) .idealMeaning) :=
  Receipt.ofTheorem (directProof (F := F) (G := G))
    { provenance with discharger := "TestsSecurity.ClaimReporting.HigherOrder.directProof", dependencies := [] }
    (subject .idealMeaning).stageLinkProofs

noncomputable def wrappedReceipt : Receipt (meaning (F := F) (G := G) .idealMeaning) :=
  Receipt.ofTheorem (wrappedProof (F := F) (G := G))
    { provenance with discharger := "TestsSecurity.ClaimReporting.HigherOrder.wrappedProof", dependencies := [] }
    (subject .idealMeaning).stageLinkProofs

noncomputable def positiveReceipt : Receipt (meaning (F := F) (G := G) .idealMeaning) :=
  Receipt.ofTheorem (positiveProof (F := F) (G := G))
    { provenance with discharger := "TestsSecurity.ClaimReporting.HigherOrder.positiveProof", dependencies := [] }
    (subject .idealMeaning).stageLinkProofs

/-- A generic proof wrapper establishes the exact same requested proposition.
No claimed author method is needed for receipt certification. -/
noncomputable def unattributedReceipt : Receipt (meaning (F := F) (G := G) .idealMeaning) :=
  Receipt.ofTheorem
    (invoke (fun _ : Unit => positiveProof (F := F) (G := G)) ())
    { provenance with discharger := "unattributed", dependencies := [] }
    (subject .idealMeaning).stageLinkProofs

noncomputable def extraPremiseReceipt (_unregistered : True) :
    Receipt (meaning (F := F) (G := G) .idealMeaning) := unattributedReceipt

/-- An unresolved optional provenance string is diagnostic only. -/
noncomputable def symbolicProvenanceReceipt (application : String) :
    Receipt (meaning (F := F) (G := G) .idealMeaning) :=
  Receipt.ofTheorem (positiveProof (F := F) (G := G))
    { provenance with discharger := application, dependencies := [] }
    (subject .idealMeaning).stageLinkProofs

/-- The adapter accepts proved notes regardless of spelling. A note with no
proof cannot satisfy HypothesesProved, even when the legacy registry cites it. -/
example : HypothesesProved (labeledEvidence (F := F) (G := G) "unregistered.note").hypotheses := by
  trivial

example (hypothesis : Hypothesis) (unproved : ¬ hypothesis.status.Discharged) :
    ¬ HypothesesProved [hypothesis] := fun proved => unproved proved.1

def assumedNote : Hypothesis :=
  ⟨"binding.collision-bounded-identity", .binding .collisionBoundedIdentity, False,
    ZkcSecurity.FiatShamir.ObligationStatus.cite "binding.collision-bounded-identity" _ rfl rfl⟩

example : ¬ HypothesesProved [assumedNote] := fun proved => proved.1

noncomputable def notedEvidence :=
  { ZkcSecurity.Examples.Subjects.Schnorr.knowledge (F := F) (G := G) .idealMeaning
      (subject (F := F) (G := G) .idealMeaning).lowering with
    hypotheses := [assumedNote] }

/-- Generic notes need not be readable before the helper is applied. -/
noncomputable def withNotes (notes : List Hypothesis) :=
  { notedEvidence (F := F) (G := G) with hypotheses := notes }

include F G

/-- An applied empty note list cannot prevent extraction of a valid receipt. -/
theorem optionalNotesProof : (meaning (F := F) (G := G) .idealMeaning).proposition :=
  Nat.rec (positiveProof (F := F) (G := G)) (fun _ proof => proof)
    (withNotes (F := F) (G := G) []).handle

noncomputable def optionalNotesReceipt : Receipt (meaning (F := F) (G := G) .idealMeaning) :=
  Receipt.ofTheorem (optionalNotesProof (F := F) (G := G))
    { provenance with discharger := "TestsSecurity.ClaimReporting.HigherOrder.optionalNotesProof" }
    (subject .idealMeaning).stageLinkProofs

/-- Reading a legacy note is not assuming its False claim. The actual theorem
still has a kernel proof and no extra premise in its remaining telescope. -/
theorem notedProof : True :=
  Nat.rec True.intro (fun _ proof => proof) (notedEvidence (F := F) (G := G)).handle

noncomputable def unprovedNoteReceipt : AdmittedReceipt (modelRegistry .idealMeaning)
    (manualMeaning (F := F) (G := G) (manualData (F := F) (G := G)) rfl rfl) where
  receipt := Receipt.ofTheorem (notedProof (F := F) (G := G))
    { trivialProvenance with discharger := "TestsSecurity.ClaimReporting.HigherOrder.notedProof" }
    (subject .idealMeaning).stageLinkProofs
  checked := rfl
  modelAdmitted := ⟨model, rfl⟩

end HigherOrder


namespace ProjectedCarrier

/-- The callback is carried in data rather than a function-typed argument. -/
structure Box where
  callback : String → Nat
  argument : String

structure Runner where
  run : Box → Nat

def runner : Runner := ⟨fun box => box.callback box.argument⟩
opaque hiddenRunner : Runner := runner
noncomputable def blockedRunner : Runner := Classical.choice ⟨runner⟩

-- Retain a kernel projection as the applied head rather than its named wrapper.
elab "raw_carrier_runner% " term:term : term => do
  let value ← Lean.Elab.Term.elabTerm term none
  pure (.proj ``Runner 0 value)

noncomputable def callback (label : String) : Nat :=
  (HigherOrder.labeledEvidence (F := F) (G := G) label).handle

noncomputable def validCallback (_ : String) : Nat :=
  (ZkcSecurity.Examples.Subjects.Schnorr.knowledge (F := F) (G := G) .idealMeaning
    (subject (F := F) (G := G) .idealMeaning).lowering).handle

include F G

theorem directProof : True :=
  Nat.rec True.intro (fun _ proof => proof)
    (callback (F := F) (G := G) "unregistered.projected.carrier")

theorem carrierProof : True :=
  Nat.rec True.intro (fun _ proof => proof)
    ((raw_carrier_runner% runner)
      ⟨callback (F := F) (G := G), "unregistered.projected.carrier"⟩)

theorem opaqueProof : True :=
  Nat.rec True.intro (fun _ proof => proof)
    ((raw_carrier_runner% hiddenRunner)
      ⟨callback (F := F) (G := G), "unregistered.projected.carrier"⟩)

theorem blockedProof : True :=
  Nat.rec True.intro (fun _ proof => proof)
    ((raw_carrier_runner% blockedRunner)
      ⟨callback (F := F) (G := G), "unregistered.projected.carrier"⟩)

theorem positiveProof : True :=
  Nat.rec True.intro (fun _ proof => proof)
    ((raw_carrier_runner% runner) ⟨validCallback (F := F) (G := G), ""⟩)

noncomputable def directReceipt : AdmittedReceipt (modelRegistry .idealMeaning)
    (manualMeaning (F := F) (G := G) (manualData (F := F) (G := G)) rfl rfl) where
  receipt := Receipt.ofTheorem (directProof (F := F) (G := G))
    { trivialProvenance with discharger := "TestsSecurity.ClaimReporting.ProjectedCarrier.directProof", dependencies := [] }
    (subject .idealMeaning).stageLinkProofs
  checked := rfl
  modelAdmitted := ⟨model, rfl⟩

noncomputable def carrierReceipt : AdmittedReceipt (modelRegistry .idealMeaning)
    (manualMeaning (F := F) (G := G) (manualData (F := F) (G := G)) rfl rfl) where
  receipt := Receipt.ofTheorem (carrierProof (F := F) (G := G))
    { trivialProvenance with discharger := "TestsSecurity.ClaimReporting.ProjectedCarrier.carrierProof", dependencies := [] }
    (subject .idealMeaning).stageLinkProofs
  checked := rfl
  modelAdmitted := ⟨model, rfl⟩

noncomputable def opaqueReceipt : AdmittedReceipt (modelRegistry .idealMeaning)
    (manualMeaning (F := F) (G := G) (manualData (F := F) (G := G)) rfl rfl) where
  receipt := Receipt.ofTheorem (opaqueProof (F := F) (G := G))
    { trivialProvenance with discharger := "TestsSecurity.ClaimReporting.ProjectedCarrier.opaqueProof", dependencies := [] }
    (subject .idealMeaning).stageLinkProofs
  checked := rfl
  modelAdmitted := ⟨model, rfl⟩

noncomputable def blockedReceipt : AdmittedReceipt (modelRegistry .idealMeaning)
    (manualMeaning (F := F) (G := G) (manualData (F := F) (G := G)) rfl rfl) where
  receipt := Receipt.ofTheorem (blockedProof (F := F) (G := G))
    { trivialProvenance with discharger := "TestsSecurity.ClaimReporting.ProjectedCarrier.blockedProof", dependencies := [] }
    (subject .idealMeaning).stageLinkProofs
  checked := rfl
  modelAdmitted := ⟨model, rfl⟩

noncomputable def positiveReceipt : AdmittedReceipt (modelRegistry .idealMeaning)
    (manualMeaning (F := F) (G := G) (manualData (F := F) (G := G)) rfl rfl) where
  receipt := Receipt.ofTheorem (positiveProof (F := F) (G := G))
    { trivialProvenance with discharger := "TestsSecurity.ClaimReporting.ProjectedCarrier.positiveProof", dependencies := [] }
    (subject .idealMeaning).stageLinkProofs
  checked := rfl
  modelAdmitted := ⟨model, rfl⟩

end ProjectedCarrier

namespace Canonical
open ZkcSecurity.Tools.ClaimConstruction

/-- Switching to a generic subject cannot give a reserved security name the
meaning True. Core receipts remain available independently of admission. -/
def genericReservedData : Wire.Request where
  subject := ⟨"test-unit", "test::Entry", .interactive, []⟩
  property := ⟨"knowledge", 0⟩
  model := ⟨exactUniform, []⟩
  target := .retained "test" 0 "control"
  accept := ⟨true, 0, 0, []⟩
  quantity := .scalar (.natural 0)
def genericProperty : PropertyExport Unit where
  Arguments _ := Unit
  elaborate _ _ := .ok ()
  meaning _ _ := .ok True
def genericRegistry : Registry (PropertyExport Unit) :=
  ⟨[⟨⟨"knowledge", 0⟩, "zkc.property.knowledge/0", some genericProperty⟩]⟩
def genericResolved : Resolved genericRegistry (fun _ => genericReservedData.subject) () genericReservedData :=
  ⟨rfl, _, rfl, genericProperty, rfl, (), rfl⟩
def genericMeaning : Evaluated genericResolved := ⟨True, rfl⟩
def genericReservedReceipt : Receipt genericMeaning :=
  Receipt.ofTheorem True.intro ⟨.theorem, "True.intro", ⟨"methods.reporting_control", 0⟩, [], []⟩

/-- Explicit checked associations on the existing generic receipt. -/
noncomputable def checkedReceipt : CanonicalReceipt (.uniform (F := F) (G := G) artifacts .idealMeaning) (modelRegistry .idealMeaning) .empty .knowledge
    (meaning (F := F) (G := G) .idealMeaning) where
  receipt := idealReceipt
  modelAdmission := ⟨rfl, model, rfl⟩
  association := ⟨rfl, rfl⟩

/-- The undefined completeness name is still reserved to canonical meanings. -/
def reservedData : Wire.Request :=
  { manualData (F := F) (G := G) with property := ⟨"completeness", 0⟩ }
noncomputable def reservedRegistry : Registry (PropertyExport (Subject F G artifacts .idealMeaning)) :=
  ⟨[⟨⟨"completeness", 0⟩, "zkc.property.manual/0", some manualProperty⟩]⟩
noncomputable def reservedResolved : Resolved (reservedRegistry (F := F) (G := G)) Subject.reference
    (subject .idealMeaning) (reservedData (F := F) (G := G)) :=
  ⟨rfl, _, rfl, manualProperty, rfl, (), rfl⟩
noncomputable def reservedMeaning : Evaluated (reservedResolved (F := F) (G := G)) := ⟨True, rfl⟩
noncomputable def reservedReceipt : AdmittedReceipt (modelRegistry .idealMeaning)
    (reservedMeaning (F := F) (G := G)) :=
  ⟨Receipt.ofTheorem trivialProof trivialProvenance (subject .idealMeaning).stageLinkProofs,
    rfl, model, rfl⟩

example : ¬ AuthorExtensionAdmission (.uniform (F := F) (G := G) artifacts .idealMeaning) (reservedResolved (F := F) (G := G)) := by
  intro admission
  have impossible : reservedIdentifier (reservedData (F := F) (G := G)).property = true := rfl
  rw [admission.unreserved] at impossible
  contradiction

example : ¬ CanonicalAdmission (.uniform (F := F) (G := G) artifacts .idealMeaning) (modelRegistry .idealMeaning) .completeness
    (reservedResolved (F := F) (G := G)) := by
  intro admission
  have impossible := congrArg Export.definition admission.selected
  cases impossible

/-- A semantic counterexample refutes the complete forged property export;
this is stronger than refusing one proposed reflexivity proof. -/
example : ¬ CanonicalAdmission (.uniform (F := F) (G := G) artifacts .idealMeaning) (modelRegistry .idealMeaning) .knowledge
    (replacedResolved (F := F) (G := G)) := by
  intro admission
  have definition := congrArg Export.definition admission.selected
  have same := Option.some.inj definition
  have always : ∀ admitted arguments,
      (replacedProperty (F := F) (G := G)).meaning admitted arguments = .ok True := fun _ _ => rfl
  rw [same] at always
  have impossible := always (subject .idealMeaning) (.error ⟨[]⟩)
  cases impossible

/-- A closed authorization chooses a fixed schema. The limit is selected by
model elaboration, so a theorem with a different limit remains unresolved. -/
def authorizedData : Wire.Request :=
  { idealData (F := F) (G := G) with model := ⟨exactUniform,
    [(some "queries", .natural 0), (some "budget_symbol", .reference "Q"),
      (some "assumptions", .list [.application "assumptions.dlog_search" (some 0) []])]⟩ }
noncomputable def authorizedResolved : Resolved (registry (F := F) (G := G) .idealMeaning)
    Subject.reference (subject .idealMeaning) (authorizedData (F := F) (G := G)) := by
  claim_resolve (modelRegistry .idealMeaning) normalizing
    [registry, modelRegistry, authorizedData, idealData, wire, subject, artifacts,
      premiseKeys]
noncomputable def authorizedMeaning : Evaluated (authorizedResolved (F := F) (G := G)) := by
  claim_evaluate

noncomputable def conditionalCore : Receipt (authorizedMeaning (F := F) (G := G)) :=
  Receipt.ofTheorem
    (knowledgeEndpoint ⟨rfl, { model with queries := .fixed 0 }, rfl⟩ (replay .idealMeaning))
    provenance (subject .idealMeaning).stageLinkProofs

/-- Conditional kernel theorem for the exact canonical meaning. This limited
search-game condition does not strengthen the extraction guarantee. -/
noncomputable def authorizedReceipt (_hardness : DLogSearchHard (F := F) (G := G) 0) :
    CanonicalReceipt (.uniform (F := F) (G := G) artifacts .idealMeaning) (modelRegistry .idealMeaning) .empty .knowledge
      (authorizedMeaning (F := F) (G := G)) where
  receipt := conditionalCore
  modelAdmission := ⟨rfl, { model with queries := .fixed 0 }, rfl⟩
  association := ⟨rfl, rfl⟩

noncomputable def substitutedArguments (_hardness : DLogSearchHard (F := F) (G := G) 1) :
    Receipt (authorizedMeaning (F := F) (G := G)) := conditionalCore
noncomputable def unauthorizedReceipt (_hardness : DLogSearchHard (F := F) (G := G) 0) :
    Receipt (meaning (F := F) (G := G) .idealMeaning) := idealReceipt
noncomputable def unauthorizedModel (_law : FaithfulScalarAction F G) :
    Receipt (meaning (F := F) (G := G) .idealMeaning) := idealReceipt

/-- Extra carrier dependencies cannot smuggle a proof-producing instance into
an otherwise accepted telescope, including dependencies on an earlier premise. -/
noncomputable def dependentInstance {P : Prop} [Inhabited (PLift P)] :
    Receipt (meaning (F := F) (G := G) .idealMeaning) := idealReceipt

/-- A direct opaque proof establishes exactly the same fixed meaning. -/
opaque retainProof {P : Prop} (proof : P) : P := proof
noncomputable def opaqueReceipt : Receipt (meaning (F := F) (G := G) .idealMeaning) :=
  Receipt.ofTheorem (retainProof (knowledgeEndpoint (knowledge .idealMeaning) (replay .idealMeaning)))
    trivialProvenance (subject .idealMeaning).stageLinkProofs

/-- Compare a complete selected model export, not entire registry containers. -/
example : ¬ CanonicalModelAdmission (.uniform (F := F) (G := G) artifacts .idealMeaning) replacedModels .empty (subject (F := F) (G := G) .idealMeaning)
    (idealData (F := F) (G := G)).model := by
  intro admission
  have same : replacedModels.exports.head (by simp [replacedModels]) =
      canonicalModelEntry .empty .idealMeaning := Except.ok.inj admission.selected
  have observation := congrArg (fun entry => (entry.definition.map fun elaborate =>
    (elaborate Unit inferInstance artifacts.original .executableBytes
      ⟨exactUniform, [(some "level", .reference "levels.bytes")]⟩).toBool).getD false) same
  change true = false at observation
  cases observation

end Canonical
end TestsSecurity.ClaimReporting
