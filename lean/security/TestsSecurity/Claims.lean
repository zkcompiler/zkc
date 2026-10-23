import ZkcSecurity.Claims.Resolution
import ZkcSecurity.Claims.Endpoint
import ZkcSecurity.Examples.Subjects.Schnorr.Registration
import Zkc.Claims.Receipt

/-! Real compiled Schnorr artifacts instantiate the request-fixed replay model.
Wrong structural references fail before evidence is chosen. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace TestsSecurity.Claims
open Zkc.Claims Zkc.Construction ZkcSecurity.Claims ZkcSecurity.Endpoint

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F] [Fintype F] [Inhabited F] [SampleableType G]

private def subject (endpoint : Semantics) : Subject F G ZkcSecurity.Examples.Subjects.Schnorr.artifacts endpoint where
  reference := ⟨"admitted-schnorr-unit", "example::Proof", stage endpoint, [⟨"validator", "schnorr-program"⟩]⟩
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

private def model : Model := ⟨.fixed, .symbolic "Q", "Q", "", .constant 0, none⟩

private def knowledge (endpoint : Semantics) : KnowledgeRequest (subject (F := F) (G := G) endpoint) where
  registered := rfl
  model := model
  fixed := rfl

private def replay (endpoint : Semantics) :
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

private def wire (endpoint : Semantics) : Wire.Request where
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

private def modelRegistry (endpoint : Semantics) : ModelRegistry :=
  models .empty endpoint
private noncomputable def registry (endpoint : Semantics) :=
  properties (F := F) (G := G) (art := ZkcSecurity.Examples.Subjects.Schnorr.artifacts) (endpoint := endpoint) (modelRegistry endpoint)

private noncomputable def resolved (endpoint : Semantics) : Resolved (registry (F := F) (G := G) endpoint)
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
      simp [knowledgeProperty, knowledgeArguments, wire, subject, modelRegistry, resolveModel,
        models, modelSchema, modelSchemaWith, responseDifference, ExtractionProfile.registry, named, checkArguments, reference, Numeric.natural, Numeric.naturalWith, Numeric.cardinality,
        Registry.lookup, Subject.check, Subject.targetReference, Subject.acceptance,
        Wire.TargetRef.matches, model, knowledge, checkCapabilities,
        show ZkcSecurity.Examples.Subjects.Schnorr.artifacts.original.catalogue.identitySort "bls12-381.fr" = some .field from rfl] <;> rfl

private def meaning (endpoint : Semantics) : Evaluated (resolved (F := F) (G := G) endpoint) :=
  ⟨(knowledge endpoint).meaning, rfl⟩

example (endpoint : Semantics) :
    resolveRequest (registry (F := F) (G := G) endpoint) (modelRegistry endpoint)
      (subject (F := F) (G := G) endpoint) (wire (F := F) (G := G) endpoint) =
      .ok (.ok (resolved endpoint)) := by
  cases endpoint <;> exact resolveRequest_eq rfl rfl _

private def provenance : Provenance :=
  ⟨.endpoint, "ZkcSecurity.Claims.knowledgeEndpoint", ⟨"fs.forking", 0⟩,
    ["ZkcSecurity.Examples.Subjects.Schnorr.model", "ZkcSecurity.Endpoint.knowledge_soundness"],
    [⟨⟨"source.correspondence", 0⟩, .sourceCorrespondence, .infrastructure⟩]⟩

private noncomputable def endpointReceipt (endpoint : Semantics) : Receipt (meaning (F := F) (G := G) endpoint) :=
  Receipt.ofEndpoint (knowledgeEndpoint (knowledge endpoint) (replay endpoint)) provenance (subject endpoint).stageLinkProofs
private noncomputable def directReceipt (endpoint : Semantics) : Receipt (meaning (F := F) (G := G) endpoint) :=
  Receipt.ofTheorem (knowledgeEndpoint (knowledge endpoint) (replay endpoint)) provenance (subject endpoint).stageLinkProofs

example : (endpointReceipt (F := F) (G := G) .idealMeaning).proof =
    (directReceipt (F := F) (G := G) .idealMeaning).proof := rfl

example : (registry (F := F) (G := G) .idealMeaning).lookup ⟨"knowledge", 1⟩ =
    .error (.unknownIdentifier ⟨"knowledge", 1⟩) := rfl
example : (modelRegistry .idealMeaning).lookup ⟨"models.fiat_shamir", 1⟩ =
    .error (.unknownIdentifier ⟨"models.fiat_shamir", 1⟩) := rfl

example : (subject (F := F) (G := G) .idealMeaning).check
    { wire (F := F) (G := G) .idealMeaning with target := .retained "wrong" 0 "knowledge" } =
    .error .targetMismatch := rfl
example : (subject (F := F) (G := G) .idealMeaning).check
    { wire (F := F) (G := G) .idealMeaning with target := .retained "wrong" 99 "missing" } =
    .error .targetMismatch := rfl
example : (subject (F := F) (G := G) .idealMeaning).check
    { wire (F := F) (G := G) .idealMeaning with accept := ⟨true, 99, 1, []⟩ } =
    .error .acceptanceMismatch := rfl

example : (subject (F := F) (G := G) .idealMeaning).check
    { wire (F := F) (G := G) .idealMeaning with
      subject := { (wire (F := F) (G := G) .idealMeaning).subject with unitDigest := "stale-unit" } } =
      .error .subjectMismatch := rfl
example : (subject (F := F) (G := G) .idealMeaning).check
    { wire (F := F) (G := G) .idealMeaning with
      subject := { (wire (F := F) (G := G) .idealMeaning).subject with artifacts := [⟨"validator", "stale-program"⟩] } } =
      .error .subjectMismatch := rfl
example : (subject (F := F) (G := G) .idealMeaning).check
    { wire (F := F) (G := G) .idealMeaning with
      target := .retained ZkcSecurity.Examples.Subjects.Schnorr.Contract.retained.owner.contract.owner 1 "knowledge" } =
      .error .targetMismatch := rfl
example : (subject (F := F) (G := G) .idealMeaning).check
    { wire (F := F) (G := G) .idealMeaning with
      target := .retained ZkcSecurity.Examples.Subjects.Schnorr.Contract.retained.owner.contract.owner 0 "missing" } =
      .error .targetMismatch := rfl

example : soundnessArguments (modelRegistry .idealMeaning)
    { wire (F := F) (G := G) .idealMeaning with property := ⟨"soundness", 0⟩, quantity := .charged [("missing", .natural 1)] }
    (subject (F := F) (G := G) .idealMeaning) = .error (.siteMismatch "missing") := rfl

/-- A scalar meaning does not carry or require a charged certificate. -/
example (error : Bound) :
    (SoundnessRequest.mk model (.scalar error) : SoundnessRequest (subject (F := F) (G := G) .idealMeaning)).meaning =
      Ordinary (subject (F := F) (G := G) .idealMeaning) model error.value := rfl

example : checkCapabilities { wire (F := F) (G := G) .idealMeaning with
    capabilities := [⟨⟨"capabilities.unknown", 0⟩, []⟩] } =
    .error (.unknownIdentifier ⟨"capabilities.unknown", 0⟩) := rfl

example : modelSchema F ZkcSecurity.Examples.Subjects.Schnorr.artifacts.original .empty .idealMeaning
    ⟨exactUniform, [(some "statement", .reference "statements.adaptive")]⟩ =
    .error (.schema "adaptive model requires application") := rfl
example : modelSchema F ZkcSecurity.Examples.Subjects.Schnorr.artifacts.original .empty .idealMeaning
    ⟨exactUniform, [(some "level", .reference "levels.bytes")]⟩ =
    .error .stageMismatch := rfl

example : soundnessArguments (modelRegistry .idealMeaning)
    { wire (F := F) (G := G) .idealMeaning with quantity := .scalar (.natural 1) }
    (subject (F := F) (G := G) .idealMeaning) =
    .ok (.ok ⟨model, .scalar (.constant 1)⟩) := rfl

example : soundnessArguments (modelRegistry .idealMeaning)
    { wire (F := F) (G := G) .idealMeaning with
      quantity := .scalar (.natural 1)
      capabilities := [⟨chargedReduction, []⟩] }
    (subject (F := F) (G := G) .idealMeaning) =
    .ok (.error ⟨["charged capability requires a charge schedule"]⟩) := rfl

example : resolveRequest (registry (F := F) (G := G) .idealMeaning) (modelRegistry .idealMeaning)
    (subject (F := F) (G := G) .idealMeaning)
    { wire (F := F) (G := G) .idealMeaning with
      subject := { (wire (F := F) (G := G) .idealMeaning).subject with stage := .executableBytes } } =
    .error .subjectMismatch := rfl

example : knowledgeArguments (modelRegistry .idealMeaning)
    { wire (F := F) (G := G) .idealMeaning with quantity := .guarantee ⟨⟨"guarantees.forking", 1⟩, []⟩ }
    (subject (F := F) (G := G) .idealMeaning) =
    .error (.unknownIdentifier ⟨"guarantees.forking", 1⟩) := rfl

example : knowledgeArguments (modelRegistry .idealMeaning)
    { wire (F := F) (G := G) .idealMeaning with quantity := .guarantee ⟨forking, [(some "cost", .application "prover_runs" none [(none, .natural 3)])]⟩ }
    (subject (F := F) (G := G) .idealMeaning) =
    .ok (.error ⟨["two-run replay extraction cost"]⟩) := rfl

example : soundnessArguments ⟨[⟨exactUniform, "zkc.model.fiat-shamir/0", none⟩]⟩
    { wire (F := F) (G := G) .idealMeaning with quantity := .scalar (.natural 1) }
    (subject (F := F) (G := G) .idealMeaning) =
    .ok (.error ⟨["model definition: models.fiat_shamir"]⟩) := rfl

example : (endpointReceipt (F := F) (G := G) .idealMeaning).status = .certified := rfl
example : (endpointReceipt (F := F) (G := G) .executableBytes).status = .certified := rfl
example : (Receipt.ofEndpoint (meaning := meaning (F := F) (G := G) .idealMeaning)
    (knowledgeEndpoint (knowledge .idealMeaning) (replay .idealMeaning)) provenance).status = .open := rfl

example : knowledgeArguments (modelRegistry .idealMeaning)
    { wire (F := F) (G := G) .idealMeaning with
      model := ⟨exactUniform, [(some "validator_cost", .natural 0)]⟩ }
    (subject (F := F) (G := G) .idealMeaning) =
      .error (.schema "knowledge model has no validator cost") := rfl
example : knowledgeArguments (modelRegistry .idealMeaning)
    { wire (F := F) (G := G) .idealMeaning with
      model := ⟨exactUniform, [(some "application", .reference "application")]⟩ }
    (subject (F := F) (G := G) .idealMeaning) =
      .error (.schema "knowledge model has no application context") := rfl
example : knowledgeArguments (modelRegistry .idealMeaning)
    { wire (F := F) (G := G) .idealMeaning with quantity := .guarantee ⟨forking,
      [(some "challenges", .application "cardinality" none [(none, .reference "unrelated.fr")])]⟩ }
    (subject (F := F) (G := G) .idealMeaning) =
      .ok (.error ⟨["unadmitted nominal domain: unrelated.fr"]⟩) := rfl

example : knowledgeArguments (modelRegistry .idealMeaning)
    { wire (F := F) (G := G) .idealMeaning with quantity := .guarantee ⟨forking,
      [(some "challenges", .natural (Fintype.card F + 1))]⟩ }
    (subject (F := F) (G := G) .idealMeaning) =
      .ok (.error ⟨["exact field challenge cardinality"]⟩) := by
  simp [knowledgeArguments, wire, subject, Subject.check, checkCapabilities,
    Subject.targetReference, Subject.acceptance, Wire.TargetRef.matches, checkArguments, named, Numeric.natural, Numeric.naturalWith]

-- A witness of one request cannot fill a receipt for a different meaning.
#check_failure (show False from (endpointReceipt (F := F) (G := G) .idealMeaning).proof)

end TestsSecurity.Claims
