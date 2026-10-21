import ZkcSecurity.Claims.Resolution
import ZkcSecurity.Claims.Endpoint
import ZkcSecurity.Claims.Arithmetic
import Zkc.Claims.Receipt
import ZkcArkLib.Examples.Subjects.Guess.Evidence

/-! The actual guessing artifacts instantiate scalar and exactly charged
requests through the same endpoint implications. Imported language is fixed by
a typed registry before any family evidence is selected. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
namespace TestsArkLib.ClaimSoundness
open Zkc.Claims Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims ZkcSecurity.Endpoint ZkcSecurity.FiatShamir
open ZkcSecurity.Examples.Subjects.Guess

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

private def site : Site compiled.context where
  label := "challenge"
  native := "label_6368616c6c656e6765"
  delivery := "label_64656c6976657279_0"
  selected := by change _ ∈ ZkcExamples.Construction.GuessProof.context.draws; rw [ZkcExamples.Construction.GuessProof.context_eq]; simp
  request := .draw "bls12-381.fr"
  requestSelected := by change ZkcExamples.Construction.GuessProof.context.request = _; rw [ZkcExamples.Construction.GuessProof.context_eq]

private def subject : Subject F G artifacts .idealMeaning where
  reference := ⟨"admitted-guess-unit", "example::Proof", .compiledIdeal, []⟩
  stageMatched := rfl
  compiled := compiled
  target := .importedLanguage Contract.importedLanguage
  importedRegistry := ⟨[⟨⟨"languages.guess", 0⟩, "arklib.guess.language/0", some Contract.importedLanguage⟩]⟩
  importedRegistered := by
    intro declaration same
    cases same
    exact ⟨_, rfl, rfl⟩
  sites := [site]
  sitesUnique := by simp
  sitesNativeUnique := by simp
  lowering := PUnit.unit

private def rate : ℚ≥0 := 1 / (Fintype.card F : ℚ≥0)

omit [Field F] [DecidableEq F] [SampleableType F] in
private theorem rate_eq : ((rate (F := F)) : ENNReal) = error (F := F) := by
  rw [← ENNReal.coe_nnratCast]
  congr 1
  simp [rate, one_div]

private def model : Model :=
  ⟨.fixed, .symbolic "budgets.queries", "budgets.queries", "", .constant (rate (F := F)), none⟩

private noncomputable def evidence := soundness (F := F) (G := G) .idealMeaning .fixed PUnit.unit PUnit.unit

private def schedule : ChargeSchedule (subject (F := F) (G := G)) where
  entries := [(site, .constant (rate (F := F)))]
  nonempty := by simp
  unique := by simp
  nativeUnique := by simp

private def wire : Wire.Request where
  subject := (subject (F := F) (G := G)).reference
  property := ⟨"soundness", 0⟩
  model := ⟨exactUniform, []⟩
  target := (subject (F := F) (G := G)).targetReference
  accept := (subject (F := F) (G := G)).acceptance
  quantity := .scalar (.natural 1)

example : (subject (F := F) (G := G)).check
    { wire (F := F) (G := G) with target := (.importedLanguage artifacts.original.entry
        ⟨⟨"languages.guess", 1⟩, []⟩) } = .error .targetMismatch := rfl
example : (subject (F := F) (G := G)).check
    { wire (F := F) (G := G) with target := (.importedLanguage "wrong-protocol"
        ⟨⟨"languages.guess", 0⟩, []⟩) } = .error .targetMismatch := rfl
example : (subject (F := F) (G := G)).check
    { wire (F := F) (G := G) with target := (.importedLanguage artifacts.original.entry
        ⟨⟨"languages.guess", 0⟩, [(none, .natural 1)]⟩) } = .error .targetMismatch := rfl

omit [SampleableType F] in
private theorem charge_eq (queries : Nat) (history : History F G) (event : Event F G) :
    (schedule (F := F) (G := G)).charge queries history event = error (F := F) := by
  by_cases matched : site.event (F := F) (G := G) = event
  · simp [ChargeSchedule.charge, schedule, matched, Bound.value, rate_eq]
  · simp [ChargeSchedule.charge, schedule, matched, ChargeSchedule.maximum, Bound.value, rate_eq]

/-- Ordinary scalar soundness has no charged export in its hypotheses. -/
private theorem scalarSoundness : (SoundnessRequest.mk (model (F := F))
    (.scalar (.add (.mul .queryBudget (.constant (rate (F := F)))) (.constant (rate (F := F))))) :
      SoundnessRequest (subject (F := F) (G := G))).meaning := by
  change FixedIdeal (subject (F := F) (G := G)) (model (F := F))
    (fun queries => queries * (rate (F := F) : ENNReal) + (rate (F := F) : ENNReal))
  apply fixedIdealEndpoint (subject (F := F) (G := G)) (model (F := F)) _ (evidence (F := F) (G := G)) rfl
    (fun statement falseStatement => (Contract.falseStatement_pinned statement).mpr falseStatement)
  exact {
    rate := fun _ => error (F := F)
    charge := fun _ _ _ => le_rfl
    cost := fun _ _ => by simp only [model, Bound.value, evidence, rate_eq]; exact le_rfl
    conclusion := fun (queries : Nat) _ => by
      simp only [model, Bound.value, rate_eq]
      exact le_rfl }

/-- The charged bundle has its ordinary weighted theorem and its certificate
at precisely the requested prices; its cost proof is checked at those prices. -/
private theorem chargedSoundness : (SoundnessRequest.mk (model (F := F)) (.charged (schedule (F := F) (G := G))) :
    SoundnessRequest (subject (F := F) (G := G))).meaning := by
  constructor
  · apply weightedFixedIdealEndpoint (subject (F := F) (G := G)) (model (F := F)) (schedule (F := F) (G := G)) (evidence (F := F) (G := G)) rfl
      (fun statement falseStatement => (Contract.falseStatement_pinned statement).mpr falseStatement)
    · intro queries history event
      rw [charge_eq]
      exact le_rfl
    · intro queries statement
      simp only [model, Bound.value, evidence, rate_eq]
      exact le_rfl
  · intro queries _
    refine ⟨chargedExport _ _ queries _ (evidence (F := F) (G := G)) rfl
      (fun statement falseStatement => (Contract.falseStatement_pinned statement).mpr falseStatement)
      (fun history event => by rw [charge_eq]; exact le_rfl) ?_⟩
    intro statement initial
    have sameCharge : (schedule (F := F) (G := G)).charge queries = (family (F := F) (G := G)).charge :=
      funext fun history => funext fun event => charge_eq queries history event
    rw [sameCharge]
    simpa only [model, Bound.value, rate_eq, evidence,
      ZkcSecurity.Examples.Subjects.Guess.soundness, Regime.exact] using
      (evidence (F := F) (G := G)).costBound statement initial

-- An ordinary numerical theorem cannot supply a charged capability bundle.
#check_failure (show
  (SoundnessRequest.mk (model (F := F)) (.charged (schedule (F := F) (G := G))) :
    SoundnessRequest (subject (F := F) (G := G))).meaning from
  scalarSoundness (F := F) (G := G))

#print axioms scalarSoundness
#print axioms chargedSoundness

private def sourceCardinality : Wire.Expr :=
  .application "cardinality" none [(none, .reference "bls12-381.fr")]

private def sourceModel (application : String) : Model :=
  ⟨.adaptive, .symbolic "Q", "Q", application, .div (.constant 1) (Fintype.card F : ℚ≥0),
    some ⟨"application", application, .parameter⟩⟩

private def sourceSchedule : ChargeSchedule (subject (F := F) (G := G)) where
  entries := [(site, .div (.constant 1) (Fintype.card F : ℚ≥0))]
  nonempty := by simp
  unique := by simp
  nativeUnique := by simp

private def sourceRequest (application : String) (charged : Bool) : SoundnessRequest (subject (F := F) (G := G)) :=
  ⟨sourceModel (F := F) application, if charged then .charged sourceSchedule else
    .scalar (.div (.add .queryBudget (.constant 1)) (Fintype.card F : ℚ≥0))⟩

private def sourceWire (charged : Bool) : Wire.Request where
  subject := (subject (F := F) (G := G)).reference
  property := ⟨"soundness", 0⟩
  model := ⟨exactUniform, [(some "level", .reference "levels.ideal"),
    (some "statement", .reference "statements.adaptive"),
    (some "oracle", .application "oracles.random" (some 0) [(none, .reference "construction.provider")]),
    (some "queries", .reference "Q"), (some "budget_symbol", .reference "Q"),
    (some "validator_cost", .binary .div (.natural 1) sourceCardinality),
    (some "application", .reference "application")]⟩
  target := .importedLanguage artifacts.original.entry ⟨⟨"languages.guess", 0⟩, []⟩
  accept := (subject (F := F) (G := G)).acceptance
  quantity := if charged then .charged [("challenge", .binary .div (.natural 1) sourceCardinality)] else
    .scalar (.binary .div (.binary .add (.reference "Q") (.natural 1)) sourceCardinality)

omit [SampleableType F] in
private theorem sourceElaborated (application : String) (charged : Bool) :
    soundnessArguments (models (.parameter "application" application) .idealMeaning)
      (sourceWire (F := F) (G := G) charged) (subject (F := F) (G := G)) =
      .ok (.ok (sourceRequest application charged)) := by
  cases charged <;>
    simp [soundnessArguments, sourceWire, subject, resolveModel, models, modelSchema, named,
      checkArguments, reference, Subject.check, Subject.targetReference, Subject.acceptance,
      Wire.TargetRef.matches, sourceCardinality, sourceRequest, sourceModel, checkCapabilities,
      show artifacts.original.catalogue.identitySort "bls12-381.fr" = some .field from rfl,
      Registry.lookup, ModelContext.parameter, ModelContext.resolveApplication, sourceSchedule,
      ZkcSecurity.Claims.schedule, site, Contract.importedLanguage]; rfl

private noncomputable def sourceRegistry (application : String) :=
  properties (F := F) (G := G) (art := artifacts) (endpoint := .idealMeaning)
    (models (.parameter "application" application) .idealMeaning)

private noncomputable def sourceResolved (application : String) (charged : Bool) :
    Resolved (sourceRegistry (F := F) (G := G) application) Subject.reference
      (subject (F := F) (G := G)) (sourceWire (F := F) (G := G) charged) where
  subjectMatched := rfl
  entry := ⟨⟨"soundness", 0⟩, "zkc.property.soundness/0",
    some (soundnessProperty (models (.parameter "application" application) .idealMeaning))⟩
  registered := rfl
  property := soundnessProperty (models (.parameter "application" application) .idealMeaning)
  defined := rfl
  arguments := .ok (sourceRequest application charged)
  elaborated := sourceElaborated application charged

private def sourceEvaluated (application : String) (charged : Bool) :
    Evaluated (sourceResolved (F := F) (G := G) application charged) :=
  ⟨(sourceRequest application charged).meaning, rfl⟩

example (application : String) (charged : Bool) :
    resolveRequest (sourceRegistry (F := F) (G := G) application)
      (models (.parameter "application" application) .idealMeaning)
      (subject (F := F) (G := G)) (sourceWire (F := F) (G := G) charged) =
      .ok (.ok (sourceResolved application charged)) := resolveRequest_eq rfl rfl _

private noncomputable def adaptiveEvidence (application : String) :=
  soundness (F := F) (G := G) .idealMeaning .adaptive ⟨application⟩ PUnit.unit

omit [DecidableEq F] [SampleableType F] in
private theorem sourceError : error (F := F) = 1 / (Fintype.card F : ENNReal) :=
  (rate_eq (F := F)).symm.trans (nnrat_inv_card_value F)

omit [SampleableType F] in
private theorem sourceCharge (queries : Nat) (history : History F G) (event : Event F G) :
    (sourceSchedule (F := F) (G := G)).charge queries history event = error (F := F) := by
  by_cases matched : site.event (F := F) (G := G) = event
  · simp [ChargeSchedule.charge, sourceSchedule, matched, sourceError]
  · simp [ChargeSchedule.charge, sourceSchedule, matched, ChargeSchedule.maximum, sourceError]

private theorem sourceScalar (application : String) :
    (sourceRequest (F := F) (G := G) application false).meaning := by
  apply adaptiveIdealEndpoint _ _ _ (adaptiveEvidence application) rfl Contract.falseStatement_pinned rfl
  refine BoundImplication.ofConstantRate _ _ _ (error (F := F)) (error (F := F))
    (fun _ _ => le_rfl) (fun _ => le_rfl) ?_ ?_
  · intro queries
    simp [sourceRequest, sourceModel, sourceError]
  · intro queries _
    simpa [sourceRequest, sourceModel, sourceError] using (query_rate_add_cost queries 1 (Fintype.card F : ENNReal)).le

private theorem sourceCharged (application : String) :
    (sourceRequest (F := F) (G := G) application true).meaning := by
  constructor
  · apply weightedAdaptiveIdealEndpoint _ _ _ (adaptiveEvidence application) rfl Contract.falseStatement_pinned rfl
    · intro queries history event
      rw [sourceCharge]
      exact le_rfl
    · intro queries statement
      simp [adaptiveEvidence, ZkcSecurity.Examples.Subjects.Guess.soundness, sourceRequest, sourceModel, sourceError]
  · intro queries _
    refine ⟨chargedExport _ _ queries _ (adaptiveEvidence application) rfl
      (fun statement => (Contract.falseStatement_pinned statement).mpr)
      (fun history event => by rw [sourceCharge]; exact le_rfl) ?_⟩
    apply requestedCost_of_equal_charge
    · exact funext fun history => funext fun event => sourceCharge queries history event
    · intro statement
      simp [adaptiveEvidence, ZkcSecurity.Examples.Subjects.Guess.soundness, sourceRequest, sourceModel, sourceError]

private noncomputable def sourceReceipt (application : String) (charged : Bool) :
    Receipt (sourceEvaluated (F := F) (G := G) application charged) :=
  Receipt.ofEndpoint
    (by cases charged; exact sourceScalar application; exact sourceCharged application)
    ⟨.endpoint, (if charged then "ZkcSecurity.Claims.weightedAdaptiveIdealEndpoint"
      else "ZkcSecurity.Claims.adaptiveIdealEndpoint"), ⟨"fs.keyed_soundness", 0⟩, [], []⟩
    (subject (F := F) (G := G)).stageLinkProofs

#check_failure (fun application : String => show
  (sourceRequest (F := F) (G := G) application true).meaning from sourceScalar application)

example (application : String) : (sourceReceipt (F := F) (G := G) application false).status = .certified := rfl
example (application : String) : (sourceReceipt (F := F) (G := G) application true).status = .certified := rfl

#print axioms sourceScalar
#print axioms sourceCharged
#print axioms sourceReceipt

end TestsArkLib.ClaimSoundness
