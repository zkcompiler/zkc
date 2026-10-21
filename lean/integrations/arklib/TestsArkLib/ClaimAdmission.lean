import ZkcSecurity.Claims.Resolution
import ZkcSecurity.Claims.Arithmetic
import Zkc.Claims.Receipt
import ZkcArkLib.Examples.Subjects.Sumcheck.Evidence

/-! The actual Sumcheck source-shaped scalar requests, at both interpreted
stages, retain symbolic Q and a universally bound application context. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
namespace TestsArkLib.ClaimAdmission
open Zkc.Claims Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims ZkcSecurity.Endpoint
open ZkcSecurity.Examples.Subjects.Sumcheck

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F] [Inhabited F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

private def subject (endpoint : Semantics) : Subject F G artifacts endpoint where
  reference := ⟨"admitted-sumcheck-unit", "example::Proof", stage endpoint, []⟩
  stageMatched := rfl
  compiled := compiled
  target := .retained Contract.retained
  importedRegistered := by intro declaration impossible; cases impossible
  sites := []
  sitesUnique := .nil
  sitesNativeUnique := .nil
  lowering := match endpoint with
    | .idealMeaning => PUnit.unit
    | .executableBytes => lowering

private def cardinality : Wire.Expr := .application "cardinality" none [(none, .reference "bls12-381.fr")]

private def wire (endpoint : Semantics) : Wire.Request where
  subject := (subject (F := F) (G := G) endpoint).reference
  property := ⟨"soundness", 0⟩
  model := ⟨exactUniform, [
    (some "level", .reference (match endpoint with | .idealMeaning => "levels.ideal" | .executableBytes => "levels.bytes")),
    (some "statement", .reference "statements.adaptive"),
    (some "oracle", .application "oracles.random" (some 0) [(none, .reference "construction.provider")]),
    (some "queries", .reference "Q"), (some "budget_symbol", .reference "Q"),
    (some "validator_cost", .binary .div (.natural 2) cardinality),
    (some "application", .reference "application")]⟩
  target := (subject (F := F) (G := G) endpoint).targetReference
  accept := (subject (F := F) (G := G) endpoint).acceptance
  quantity := .scalar (.binary .div (.binary .add (.reference "Q") (.natural 2)) cardinality)

private def model (application : String) : Model :=
  ⟨.adaptive, .symbolic "Q", "Q", application, .div (.constant 2) (Fintype.card F : ℚ≥0),
    some ⟨"application", application, .parameter⟩⟩

private def request (endpoint : Semantics) (application : String) : SoundnessRequest (subject (F := F) (G := G) endpoint) :=
  ⟨model (F := F) application, .scalar (.div (.add .queryBudget (.constant 2)) (Fintype.card F : ℚ≥0))⟩

private def modelRegistry (endpoint : Semantics) (application : String) : ModelRegistry :=
  models (.parameter "application" application) endpoint

omit [SampleableType F] in
private theorem elaborated (endpoint : Semantics) (application : String) :
    soundnessArguments (modelRegistry endpoint application) (wire (F := F) (G := G) endpoint)
      (subject (F := F) (G := G) endpoint) = .ok (.ok (request endpoint application)) := by
  cases endpoint <;>
    simp [soundnessArguments, wire, subject, modelRegistry, resolveModel, models, modelSchema,
      named, checkArguments, reference, Subject.check, Subject.targetReference, Subject.acceptance,
      Wire.TargetRef.matches, cardinality, request, model, checkCapabilities,
      show artifacts.original.catalogue.identitySort "bls12-381.fr" = some .field from rfl,
      Registry.lookup, ModelContext.parameter, ModelContext.resolveApplication]

private noncomputable def registry (endpoint : Semantics) (application : String) :=
  properties (F := F) (G := G) (art := artifacts) (endpoint := endpoint) (modelRegistry endpoint application)

private noncomputable def resolved (endpoint : Semantics) (application : String) :
    Resolved (registry (F := F) (G := G) endpoint application) Subject.reference
      (subject (F := F) (G := G) endpoint) (wire (F := F) (G := G) endpoint) where
  subjectMatched := rfl
  entry := ⟨⟨"soundness", 0⟩, "zkc.property.soundness/0", some (soundnessProperty (modelRegistry endpoint application))⟩
  registered := rfl
  property := soundnessProperty (modelRegistry endpoint application)
  defined := rfl
  arguments := .ok (request endpoint application)
  elaborated := elaborated endpoint application

private def evaluated (endpoint : Semantics) (application : String) :
    Evaluated (resolved (F := F) (G := G) endpoint application) :=
  ⟨(request endpoint application).meaning, rfl⟩

example (endpoint : Semantics) (application : String) :
    resolveRequest (registry (F := F) (G := G) endpoint application) (modelRegistry endpoint application)
      (subject (F := F) (G := G) endpoint) (wire (F := F) (G := G) endpoint) =
      .ok (.ok (resolved endpoint application)) := by
  cases endpoint <;> exact resolveRequest_eq rfl rfl _

private noncomputable def evidence (endpoint : Semantics) (application : String) :=
  soundness (F := F) (G := G) endpoint .adaptive ⟨application⟩ (subject endpoint).lowering

private noncomputable def implication (endpoint : Semantics) (application : String) :
    BoundImplication (evidence (F := F) (G := G) endpoint application) (model (F := F) application)
      (.div (.add .queryBudget (.constant 2)) (Fintype.card F : ℚ≥0) : ZkcSecurity.Claims.Bound).value := by
  refine BoundImplication.ofConstantRate _ _ _ (1 / (Fintype.card F : ENNReal))
    (2 / (Fintype.card F : ENNReal)) ?_ ?_ ?_ ?_
  · intro history event
    simp [evidence, soundness, family]
  · intro statement
    change (2 : ENNReal) * (1 / (Fintype.card F : ENNReal) + 0) ≤ 2 / (Fintype.card F : ENNReal)
    simp [div_eq_mul_inv]
  · intro queries
    simp [model]
  · intro queries _
    simp only [model, Bound.value_div, Bound.value_add, Bound.value_query, Bound.value_constant, ennreal_nnrat_natural]
    simpa using (query_rate_add_cost queries 2 (Fintype.card F : ENNReal)).le

omit [Inhabited F] in
private theorem sourceSoundness (endpoint : Semantics) (application : String) :
    (request (F := F) (G := G) endpoint application).meaning := by
  cases endpoint with
  | idealMeaning =>
    exact adaptiveIdealEndpoint _ _ _ (evidence .idealMeaning application) rfl
      (fun statement => Contract.falseStatement_pinned statement) rfl (implication .idealMeaning application)
  | executableBytes =>
    exact adaptiveBytesEndpoint _ _ _ (evidence .executableBytes application) rfl
      (fun statement => Contract.falseStatement_pinned statement) rfl
      (fun _ _ _ _ _ _ => rfl) (implication .executableBytes application)

/-- The application is a theorem binder, not the literal spelling in source. -/
private noncomputable def receipt (endpoint : Semantics) (application : String) :
    Receipt (evaluated (F := F) (G := G) endpoint application) :=
  Receipt.ofEndpoint (sourceSoundness endpoint application)
    ⟨.endpoint, (match endpoint with
      | .idealMeaning => "ZkcSecurity.Claims.adaptiveIdealEndpoint"
      | .executableBytes => "ZkcSecurity.Claims.adaptiveBytesEndpoint"),
      ⟨"fs.keyed_soundness", 0⟩, [], []⟩
    (subject endpoint).stageLinkProofs

example : ∀ application : String, (request (F := F) (G := G) .idealMeaning application).meaning :=
  sourceSoundness .idealMeaning
example : ∀ application : String, (request (F := F) (G := G) .executableBytes application).meaning :=
  sourceSoundness .executableBytes
example (application : String) : (model (F := F) application).application = application := rfl
example (application : String) : (model (F := F) application).applicationBinding =
    some ⟨"application", application, .parameter⟩ := rfl
example (application : String) : (receipt (F := F) (G := G) .idealMeaning application).status = .certified := rfl
example (application : String) : (receipt (F := F) (G := G) .executableBytes application).status = .certified := rfl

#print axioms sourceSoundness
#print axioms receipt

end TestsArkLib.ClaimAdmission
