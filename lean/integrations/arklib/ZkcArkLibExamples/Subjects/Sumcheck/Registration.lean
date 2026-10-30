module

public import ZkcArkLibExamples.Subjects.Sumcheck.Endpoints
public import ZkcSecurityTools.ClaimConstruction
public import ZkcSecurity.Claims.Arithmetic

@[expose] public section

/-! Typed exports for the actual admitted subject. Source requests select their
quantity; these author-library adapters prove only the exact shapes below.
Application contexts remain universal and the query budget is never fixed. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Examples.Subjects.Sumcheck.Registration
open Zkc.Construction Zkc.Claims ZkcSecurity.Claims ZkcSecurity.Endpoint ZkcSecurity.FiatShamir
open ZkcSecurity.Tools.ClaimConstruction

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
  [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G]

def subject (endpoint : Semantics) : Subject F G artifacts endpoint where
  reference := sourceReference (stage endpoint)
  stageMatched := rfl
  compiled := compiled
  connection := sourceConnection
  target := .retained Contract.retained ZkcExamples.Structured.SumcheckContractBindings.publicFormula
  importedRegistered := by intro declaration impossible; cases impossible
  sites := sourceSites
  sitesUnique := by decide +kernel
  sitesNativeUnique := by decide +kernel
  lowering := match endpoint with
    | .idealMeaning => PUnit.unit
    | .executableBytes => lowering

def subjectIdeal := subject (F := F) (G := G) .idealMeaning

def subjectBytes := subject (F := F) (G := G) .executableBytes

def modelRegistry (endpoint : Semantics) (application : String) :=
  models (.parameter "application" application) endpoint

noncomputable def propertyRegistry (endpoint : Semantics) (application : String) :=
  properties (F := F) (G := G) (art := artifacts) (endpoint := endpoint)
    (modelRegistry endpoint application)

def requestedModel (application : String) : Model :=
  ⟨.adaptive, .symbolic "Q", "Q", application, .div (.constant 2) (Fintype.card F : ℚ≥0),
    some ⟨"application", application, .parameter⟩⟩

def requestedError : Bound :=
  .div (.add .queryBudget (.constant 2)) (Fintype.card F : ℚ≥0)

def scalarRequest (endpoint : Semantics) (application : String) :
    SoundnessRequest (subject (F := F) (G := G) endpoint) :=
  ⟨requestedModel (F := F) application, .scalar (requestedError (F := F))⟩

noncomputable def endpointEvidence (endpoint : Semantics) (application : String) :=
  soundness (F := F) (G := G) endpoint .adaptive ⟨application⟩ (subject endpoint).lowering

noncomputable def implication (endpoint : Semantics) (application : String) :
    BoundImplication (endpointEvidence (F := F) (G := G) endpoint application)
      (requestedModel (F := F) application) (requestedError (F := F)).value := by
  refine BoundImplication.ofConstantRate _ _ _ (1 / (Fintype.card F : ENNReal))
    (2 / (Fintype.card F : ENNReal)) ?_ ?_ ?_ ?_
  · intro history event
    simp [endpointEvidence, soundness, family]
  · intro statement
    change (2 : ENNReal) * (1 / (Fintype.card F : ENNReal) + 0) ≤ 2 / (Fintype.card F : ENNReal)
    simp [div_eq_mul_inv]
  · intro queries
    simp [requestedModel]
  · intro queries _
    simp only [requestedModel, requestedError, Bound.value_div, Bound.value_add,
      Bound.value_query, Bound.value_constant, ennreal_nnrat_natural]
    simp [div_eq_mul_inv, add_mul]

omit [Inhabited F] in
theorem proveScalar {endpoint : Semantics} (application : String) :
    (scalarRequest (F := F) (G := G) endpoint application).meaning := by
  cases endpoint with
  | idealMeaning =>
    exact adaptiveIdealEndpoint _ _ _ (endpointEvidence .idealMeaning application) (by trivial) rfl
      (fun statement => Contract.falseStatement_pinned statement) rfl (implication .idealMeaning application)
  | executableBytes =>
    exact adaptiveBytesEndpoint _ _ _ (endpointEvidence .executableBytes application) (by trivial) rfl
      (fun statement => Contract.falseStatement_pinned statement) rfl
      (fun _ _ _ _ _ _ => rfl) (implication .executableBytes application)

/-- The occurrence is generated from full native source-site paths and checked
against this participant. No protocol position or first matching label is used. -/
def requestedSchedule : ChargeSchedule (subjectIdeal (F := F) (G := G)) where
  entries := [(sourceSites.head (by decide +kernel),
    .div (.constant 1) (Fintype.card F : ℚ≥0))]
  nonempty := by simp
  unique := by simp
  nativeUnique := by simp

omit [Inhabited F] [SampleableType F] in
theorem requestedCharge (queries : Nat) (history : History F G) (event : Zkc.Construction.Event F G) :
    (requestedSchedule (F := F) (G := G)).charge queries history event =
      1 / (Fintype.card F : ENNReal) := by
  by_cases matched : (sourceSites.head (by decide +kernel)).event (F := F) (G := G) = event
  · simp [ChargeSchedule.charge, requestedSchedule, matched]
  · simp [ChargeSchedule.charge, requestedSchedule, matched, ChargeSchedule.maximum]

def chargedRequest (application : String) : SoundnessRequest (subjectIdeal (F := F) (G := G)) :=
  ⟨requestedModel (F := F) application, .charged requestedSchedule⟩

omit [Inhabited F] in
theorem proveCharged (application : String) :
    (chargedRequest (F := F) (G := G) application).meaning := by
  have same : ∀ queries, (requestedSchedule (F := F) (G := G)).charge queries =
      (endpointEvidence (F := F) (G := G) .idealMeaning application).family.charge := by
    intro queries
    funext history event
    rw [requestedCharge]
    simp [endpointEvidence, soundness, family]
  have cost : ∀ queries statement,
      (endpointEvidence (F := F) (G := G) .idealMeaning application).cost statement ≤
        (requestedModel (F := F) application).validatorCost.value queries := by
    intro queries statement
    exact (implication .idealMeaning application).cost queries statement
  constructor
  · apply weightedAdaptiveIdealEndpoint (subjectIdeal (F := F) (G := G)) (requestedModel (F := F) application) requestedSchedule (endpointEvidence .idealMeaning application) (by trivial) rfl
      (fun statement => Contract.falseStatement_pinned statement) rfl
    · intro queries history event
      rw [same]
    · exact cost
  · intro queries _
    refine ⟨chargedExport _ _ queries _ (endpointEvidence .idealMeaning application) (by trivial) rfl
      (fun statement falseStatement => (Contract.falseStatement_pinned statement).mpr falseStatement)
      (fun history event => by rw [same]) ?_⟩
    exact requestedCost_of_equal_charge _ _ queries _ _ (same queries) (cost queries)

@[simp] theorem admittedField : artifacts.original.catalogue.identitySort "bls12-381.fr" = some .field := rfl

omit [Field F] [DecidableEq F] [SampleableType F] in
/-- The nominal field is admitted by this actual snapshot, not an alias table. -/
@[simp] theorem elaborateFieldDivision (budgetSymbol : String) (numerator : Wire.Expr) :
    Bound.elaborate F artifacts.original budgetSymbol
      (.binary .div numerator (.application "cardinality" none [(none, .reference "bls12-381.fr")])) =
      (do return .div (← Bound.elaborate F artifacts.original budgetSymbol numerator) (Fintype.card F : ℚ≥0)) :=
  Bound.elaborate_div_cardinality F artifacts.original budgetSymbol "bls12-381.fr" numerator rfl

def library : Library where
  subject := ``subjectIdeal
  bytesSubject := some ``subjectBytes
  properties := ``propertyRegistry
  models := ``modelRegistry
  normalization := [``propertyRegistry, ``modelRegistry, ``subject, ``subjectIdeal,
    ``admittedField, ``elaborateFieldDivision, ``sourceReference, ``ZkcSecurity.Claims.stage, ``subjectBytes]
  methods := [(⟨"fs.keyed_soundness", 0⟩, ``proveScalar),
    (⟨"fs.keyed_charged", 0⟩, ``proveCharged)]

end ZkcSecurity.Examples.Subjects.Sumcheck.Registration
