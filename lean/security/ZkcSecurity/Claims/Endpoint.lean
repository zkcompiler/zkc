module

public import ZkcSecurity.Claims.Soundness
public import ZkcSecurity.Claims.EndpointHypotheses
public import ZkcSecurity.Claims.ChargeMonotonicity

@[expose] public section

/-! Checked implications from the preserved endpoints to request-fixed ordinary
bounds. Prices and validator costs occur only in implication premises. They can
never change the requested error or adversary class. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option smartUnfolding false
namespace ZkcSecurity.Claims
open OracleComp OracleSpec
open Zkc.Claims Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Endpoint ZkcSecurity.FiatShamir

section
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F] {art : Artifacts} {endpoint : Semantics} {form : Form}
  {claim : art.Statement F G → Prop}

/-- Family charges must be bounded on every history, including adversarially
queried malformed ones. Site schedules fix those prices before this proof. -/
structure BoundImplication (evidence : SoundnessEvidence art endpoint form claim (Regime.exact F))
    (model : Model) (error : Nat → ENNReal) where
  rate : Nat → ENNReal
  charge : ∀ queries history event, evidence.family.charge history event ≤ rate queries
  cost : ∀ queries statement, evidence.cost statement ≤ model.validatorCost.value queries
  conclusion : ∀ queries, model.queries.allows queries →
    queries * rate queries + model.validatorCost.value queries ≤ error queries

private theorem proverBound {α : Type}
    (evidence : SoundnessEvidence art endpoint form claim (Regime.exact F))
    {model : Model} {error : Nat → ENNReal} (implication : BoundImplication evidence model error)
    (prover : OracleComp (Oracle F G (Regime.exact F).Answer) α) (queries : Nat) (bounded : IsTotalQueryBound prover queries) :
    WorstCaseCostBound prover ⟨Typed.keyCharge evidence.family.charge⟩ (queries * implication.rate queries) :=
  Typed.worstCaseCostBound_of_isTotalQueryBound _
    (fun key => Typed.keyCharge_le (implication.charge queries) key) prover queries bounded

theorem fixedIdealEndpoint (subject : Subject F G art .idealMeaning) (model : Model) (error : Nat → ENNReal)
    (evidence : SoundnessEvidence art .idealMeaning .fixed claim (Regime.exact F))
    (_hypotheses : HypothesesProved evidence.hypotheses)
    (compiled : evidence.compiled = subject.compiled)
    (covers : ∀ statement, subject.falseStatement statement → claim statement)
    (implication : BoundImplication evidence model error) : FixedIdeal subject model error := by
  intro statement falseStatement initial prover queries allowed bounded
  have bound := fixed_soundness evidence statement (covers statement falseStatement) initial prover
    (queries * implication.rate queries) (proverBound evidence implication prover queries bounded)
  have cost := (add_le_add le_rfl (implication.cost queries statement)).trans (implication.conclusion queries allowed)
  have result := bound.trans cost
  simpa [SoundnessEvidence.verify, Subject.verify, compiled, Regime.exact] using result

theorem adaptiveIdealEndpoint (subject : Subject F G art .idealMeaning) (model : Model) (error : Nat → ENNReal)
    (evidence : SoundnessEvidence art .idealMeaning .adaptive claim (Regime.exact F))
    (_hypotheses : HypothesesProved evidence.hypotheses)
    (compiled : evidence.compiled = subject.compiled)
    (falseSet : ∀ statement, claim statement ↔ subject.falseStatement statement)
    (application : evidence.bound.application = model.application)
    (implication : BoundImplication evidence model error) : AdaptiveIdeal subject model error := by
  intro prover queries allowed bounded
  have bound := adaptive_soundness evidence prover (queries * implication.rate queries)
    (proverBound evidence implication prover queries bounded)
  have cost : (⨆ statement, evidence.cost statement) ≤ model.validatorCost.value queries :=
    iSup_le (implication.cost queries)
  have result := bound.trans ((add_le_add le_rfl cost).trans (implication.conclusion queries allowed))
  simpa [ApplicationFalse, falseSet, SoundnessEvidence.verify, Subject.verify, compiled,
    SoundnessEvidence.codec, application, Regime.exact] using result

theorem fixedBytesEndpoint (subject : Subject F G art .executableBytes) (model : Model) (error : Nat → ENNReal)
    (evidence : SoundnessEvidence art .executableBytes .fixed claim (Regime.exact F))
    (_hypotheses : HypothesesProved evidence.hypotheses)
    (_compiled : evidence.compiled = subject.compiled)
    (covers : ∀ statement, subject.falseStatement statement → claim statement)
    (validation : ∀ codec budget binding statement initial bytes,
      evidence.lowered.validate (Regime.exact F).challenge codec budget binding statement initial bytes =
        subject.validate codec budget binding statement initial bytes)
    (implication : BoundImplication evidence model error) : FixedBytes subject model error := by
  intro codec budget binding statement falseStatement initial prover queries allowed bounded
  have bound := fixed_soundness_bytes evidence codec budget binding statement (covers statement falseStatement)
    initial prover (queries * implication.rate queries) (proverBound evidence implication prover queries bounded)
  have result := bound.trans
    ((add_le_add le_rfl (implication.cost queries statement)).trans (implication.conclusion queries allowed))
  rw [show (evidence.lowered.validate (Regime.exact F).challenge codec budget binding statement initial) =
    subject.validate codec budget binding statement initial from funext (validation codec budget binding statement initial)] at result
  exact result

theorem adaptiveBytesEndpoint (subject : Subject F G art .executableBytes) (model : Model) (error : Nat → ENNReal)
    (evidence : SoundnessEvidence art .executableBytes .adaptive claim (Regime.exact F))
    (_hypotheses : HypothesesProved evidence.hypotheses)
    (_compiled : evidence.compiled = subject.compiled)
    (falseSet : ∀ statement, claim statement ↔ subject.falseStatement statement)
    (application : evidence.bound.application = model.application)
    (validation : ∀ codec budget binding statement initial bytes,
      evidence.lowered.validate (Regime.exact F).challenge codec budget binding statement initial bytes =
        subject.validate codec budget binding statement initial bytes)
    (implication : BoundImplication evidence model error) : AdaptiveBytes subject model error := by
  intro codec budget binding prover queries allowed bounded
  have bound := adaptive_soundness_bytes evidence codec budget binding prover (queries * implication.rate queries)
    (proverBound evidence implication prover queries bounded)
  have cost : (⨆ statement, evidence.cost statement) ≤ model.validatorCost.value queries :=
    iSup_le (implication.cost queries)
  have result := bound.trans ((add_le_add le_rfl cost).trans (implication.conclusion queries allowed))
  simp_rw [validation] at result
  simpa [ApplicationFalse, falseSet, SoundnessEvidence.codec, application, Regime.exact] using result

/-- The requested weighted budget dominates the family's budget in the
correct direction: a prover affordable at larger requested prices is also
affordable at smaller family prices, at the same numerical cost. -/
private theorem weightedProverBound {α : Type} (subject : Subject F G art endpoint)
    (schedule : ChargeSchedule subject)
    (evidence : SoundnessEvidence art endpoint form claim (Regime.exact F)) (queries : Nat)
    (charges : ∀ history event, evidence.family.charge history event ≤ schedule.charge queries history event)
    (prover : OracleComp (Oracle F G (Regime.exact F).Answer) α) (cost : ENNReal)
    (bounded : WorstCaseCostBound prover ⟨Typed.keyCharge (schedule.charge queries)⟩ cost) :
    WorstCaseCostBound prover ⟨Typed.keyCharge evidence.family.charge⟩ cost :=
  worstCaseCostBound_mono_charge _ _ (keyCharge_mono charges) prover cost bounded

theorem weightedFixedIdealEndpoint (subject : Subject F G art .idealMeaning) (model : Model)
    (schedule : ChargeSchedule subject)
    (evidence : SoundnessEvidence art .idealMeaning .fixed claim (Regime.exact F))
    (_hypotheses : HypothesesProved evidence.hypotheses)
    (compiled : evidence.compiled = subject.compiled)
    (covers : ∀ statement, subject.falseStatement statement → claim statement)
    (charges : ∀ queries history event, evidence.family.charge history event ≤ schedule.charge queries history event)
    (cost : ∀ queries statement, evidence.cost statement ≤ model.validatorCost.value queries) :
    WeightedFixedIdeal subject model schedule := by
  intro queries _ statement falseStatement initial prover proverCost bounded
  have bound := fixed_soundness evidence statement (covers statement falseStatement) initial prover proverCost
    (weightedProverBound subject schedule evidence queries (charges queries) prover proverCost bounded)
  have result := bound.trans (add_le_add le_rfl (cost queries statement))
  simpa [SoundnessEvidence.verify, Subject.verify, compiled, Regime.exact] using result

theorem weightedAdaptiveIdealEndpoint (subject : Subject F G art .idealMeaning) (model : Model)
    (schedule : ChargeSchedule subject)
    (evidence : SoundnessEvidence art .idealMeaning .adaptive claim (Regime.exact F))
    (_hypotheses : HypothesesProved evidence.hypotheses)
    (compiled : evidence.compiled = subject.compiled)
    (falseSet : ∀ statement, claim statement ↔ subject.falseStatement statement)
    (application : evidence.bound.application = model.application)
    (charges : ∀ queries history event, evidence.family.charge history event ≤ schedule.charge queries history event)
    (cost : ∀ queries statement, evidence.cost statement ≤ model.validatorCost.value queries) :
    WeightedAdaptiveIdeal subject model schedule := by
  intro queries _ prover proverCost bounded
  have bound := adaptive_soundness evidence prover proverCost
    (weightedProverBound subject schedule evidence queries (charges queries) prover proverCost bounded)
  have result := bound.trans (add_le_add le_rfl (iSup_le (cost queries)))
  simpa [ApplicationFalse, falseSet, SoundnessEvidence.verify, Subject.verify, compiled,
    SoundnessEvidence.codec, application, Regime.exact] using result

theorem weightedFixedBytesEndpoint (subject : Subject F G art .executableBytes) (model : Model)
    (schedule : ChargeSchedule subject)
    (evidence : SoundnessEvidence art .executableBytes .fixed claim (Regime.exact F))
    (_hypotheses : HypothesesProved evidence.hypotheses)
    (_compiled : evidence.compiled = subject.compiled)
    (covers : ∀ statement, subject.falseStatement statement → claim statement)
    (validation : ∀ codec budget binding statement initial bytes,
      evidence.lowered.validate (Regime.exact F).challenge codec budget binding statement initial bytes =
        subject.validate codec budget binding statement initial bytes)
    (charges : ∀ queries history event, evidence.family.charge history event ≤ schedule.charge queries history event)
    (cost : ∀ queries statement, evidence.cost statement ≤ model.validatorCost.value queries) :
    WeightedFixedBytes subject model schedule := by
  intro queries _ codec budget binding statement falseStatement initial prover proverCost bounded
  have bound := fixed_soundness_bytes evidence codec budget binding statement (covers statement falseStatement)
    initial prover proverCost
    (weightedProverBound subject schedule evidence queries (charges queries) prover proverCost bounded)
  have result := bound.trans (add_le_add le_rfl (cost queries statement))
  rw [show (evidence.lowered.validate (Regime.exact F).challenge codec budget binding statement initial) =
    subject.validate codec budget binding statement initial from funext (validation codec budget binding statement initial)] at result
  exact result

theorem weightedAdaptiveBytesEndpoint (subject : Subject F G art .executableBytes) (model : Model)
    (schedule : ChargeSchedule subject)
    (evidence : SoundnessEvidence art .executableBytes .adaptive claim (Regime.exact F))
    (_hypotheses : HypothesesProved evidence.hypotheses)
    (_compiled : evidence.compiled = subject.compiled)
    (falseSet : ∀ statement, claim statement ↔ subject.falseStatement statement)
    (application : evidence.bound.application = model.application)
    (validation : ∀ codec budget binding statement initial bytes,
      evidence.lowered.validate (Regime.exact F).challenge codec budget binding statement initial bytes =
        subject.validate codec budget binding statement initial bytes)
    (charges : ∀ queries history event, evidence.family.charge history event ≤ schedule.charge queries history event)
    (cost : ∀ queries statement, evidence.cost statement ≤ model.validatorCost.value queries) :
    WeightedAdaptiveBytes subject model schedule := by
  intro queries _ codec budget binding prover proverCost bounded
  have bound := adaptive_soundness_bytes evidence codec budget binding prover proverCost
    (weightedProverBound subject schedule evidence queries (charges queries) prover proverCost bounded)
  have result := bound.trans (add_le_add le_rfl (iSup_le (cost queries)))
  simp_rw [validation] at result
  simpa [ApplicationFalse, falseSet, SoundnessEvidence.codec, application, Regime.exact] using result

/-- A schedule checks domination at each occurrence and every other oracle key.
This constructor exposes the same ordinary rate used by the charged bundle. -/
noncomputable def chargedBoundImplication (subject : Subject F G art endpoint) (model : Model)
    (schedule : ChargeSchedule subject)
    (evidence : SoundnessEvidence art endpoint form claim (Regime.exact F))
    (charges : ∀ queries history event, evidence.family.charge history event ≤ schedule.charge queries history event)
    (cost : ∀ queries statement, evidence.cost statement ≤ model.validatorCost.value queries) :
    BoundImplication evidence model (fun queries => queries * schedule.maximum queries + model.validatorCost.value queries) where
  rate := schedule.maximum
  charge queries history event := (charges queries history event).trans (schedule.charge_le_maximum queries history event)
  cost := cost
  conclusion _ _ := le_rfl

/-- Enlarging certificate prices is sound; validator costs must separately be
proved at the requested prices. This is the obligation monotonicity cannot fill. -/
noncomputable def chargedExport (subject : Subject F G art endpoint) (schedule : ChargeSchedule subject)
    (queries : Nat) (cost : ENNReal)
    (evidence : SoundnessEvidence art endpoint form claim (Regime.exact F))
    (_hypotheses : HypothesesProved evidence.hypotheses)
    (compiled : evidence.compiled = subject.compiled)
    (covers : ∀ statement, subject.falseStatement statement → claim statement)
    (charges : ∀ history event, evidence.family.charge history event ≤ schedule.charge queries history event)
    (requestedCost : ∀ statement initial, Typed.ChargedCostBound
      (interface (G := G) evidence.compiled.context id) (schedule.charge queries)
      (evidence.compiled.original statement evidence.handle) initial cost) :
    ChargedExport subject schedule queries cost := by
  rcases subject with ⟨reference, stageMatched, subjectCompiled, target, version, registry,
    registered, sites, unique, nativeUnique, lowering⟩
  dsimp only at compiled
  cases compiled
  exact {
    certificate := Typed.ChargedCertificate.weaken _ evidence.family.certificate charges
    handle := evidence.handle
    doomed := fun statement falseStatement initial =>
      evidence.original_doomed (covers statement falseStatement) initial
    costBound := requestedCost }

end
end ZkcSecurity.Claims
