import TestsSecurity.DomainCharges
import ZkcSecurity.Examples.RootProperties.TwoSums.Soundness
import ZkcSecurity.Claims.ChargeMonotonicity
import ZkcSecurity.FiatShamir.DomainViewReading
import ZkcSecurity.FiatShamir.CostComposition

/-! Controls at the charge assembly boundary. The nonuniform client uses the
whole installed TwoSums binding with deliberately loose prices, not new
probability mathematics. The no-query client is a small constructed participant
fixture, not a compiled export, plain-profile admission or native receipt. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace TestsSecurity.MethodNeutralChargeAssembly
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open OracleComp OracleSpec ZkcSecurity.Claims ZkcSecurity.FiatShamir ZkcSecurity.Obligations
open ZkcSecurity
open ZkcSecurity.Examples.Generated

abbrev model := ZkcSecurity.Domains.PrimeField.blsScalarModel
abbrev carriers := model.toCarriers
abbrev Scalar := ZMod blsModulus
abbrev Group := ZMod blsModulus
abbrev Statement := TwoSums.validatorArtifacts.Statement model
local instance : DecidableEq (Domain.Event carriers) := Classical.decEq _
local instance : ∀ event : Domain.Event carriers, SampleableType (Domain.Raw event) :=
  ZkcSecurity.Domains.PrimeField.rawSampleable blsModulus

/-- Decreasing the prices preserves the existing pathwise cost semantics. -/
private theorem smallerPrices {I : PIR.Signature} {E P A : Type} {Raw : E → Type}
    (absorb : Typed.Interface I E P Raw) (small large : List E → E → ENNReal)
    (prices : ∀ history event, small history event ≤ large history event) :
    ∀ (process : PIR.Process I A) (history : List E) (budget : ENNReal),
      Typed.ChargedCostBound absorb large process history budget →
      Typed.ChargedCostBound absorb small process history budget
  | .done _, _, _, _ => trivial
  | .halt _, _, _, _ => trivial
  | .call operation next, history, budget, bounded => by
    rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ | ⟨event, decode⟩ | _
    · simp only [Typed.ChargedCostBound, absorbed] at bounded ⊢
      exact fun packet value recovered => smallerPrices absorb small large prices (next value) _ budget
        (bounded packet value recovered)
    · simp only [Typed.ChargedCostBound, absorbed] at bounded ⊢
      exact smallerPrices absorb small large prices (next value) _ budget bounded
    · simp only [Typed.ChargedCostBound, absorbed] at bounded ⊢
      obtain ⟨remaining, charged, rest⟩ := bounded
      exact ⟨remaining, (add_le_add (prices history event) le_rfl).trans charged,
        fun value => smallerPrices absorb small large prices (next value) _ remaining (rest value)⟩
    · simp only [Typed.ChargedCostBound, absorbed]

attribute [local irreducible] ZkcExamples.Structured.Generated.Connections.TwoSums.validator
  Occurrence.participant RootConnection.publicPresentation

namespace Heterogeneous
open ZkcSecurity.Examples.RootProperties.TwoSums.Soundness (installation)
abbrev schedule := TestsSecurity.DomainCharges.schedule

theorem maximum (queries : Nat) : schedule.maximum queries = 2 := by
  norm_num [schedule, TestsSecurity.DomainCharges.schedule, Claims.Domain.ChargeSchedule.maximum, Bound.value]

theorem minimum (queries : Nat) (history : Domain.History carriers) (event : Domain.Event carriers) :
    1 ≤ schedule.charge queries history event := by
  cases event <;> try { change 1 ≤ schedule.maximum queries; rw [maximum]; norm_num }
  rename_i origin
  simp only [Claims.Domain.ChargeSchedule.charge]
  cases found : schedule.entries.find? (fun entry => entry.1.matches origin) with
  | none => rw [maximum]; norm_num
  | some entry =>
    have member := List.mem_of_find?_eq_some found
    rcases List.mem_cons.mp member with same | member
    · subst entry; norm_num [Bound.value]
    · have same := List.mem_singleton.mp member
      subst entry; norm_num [Bound.value]

/-- Query-dependent validator cost is a checked upper bound, not a formula
chosen by the common printer. Both actual component executions are retained. -/
def validatorCost (queries : Nat) : ENNReal := 16 + queries

def rejected (queries : Nat) (statement : Statement)
    (falseStatement : TwoSums.validatorSubject.FalseStatement statement) (initial : Domain.History carriers) :
    Zkc.Obligations.Derivation installation.absorb (boundedEscape (schedule.charge queries))
      (fun _ result => installation.acceptance result ≠ some true) initial
      (installation.presented statement initial) :=
  (ZkcSecurity.Examples.RootProperties.TwoSums.Soundness.rejected statement falseStatement initial).mapEscape
    (fun history event _ _ => (prEvent_le_one _).trans (minimum queries history event))

/-- Lift the installed all-input source cost to the loose nonuniform prices.
The generic monotonicity rule checks every reached operation. -/
theorem costs (queries : Nat) (statement : Statement) (initial : Domain.History carriers) :
    Typed.ChargedCostBound installation.absorb (schedule.charge queries)
      (installation.presented statement initial) initial (validatorCost queries) := by
  -- Uniform price 2 bounds both entries of this independently selected schedule.
  have : Fact (IsField (model.Field ZkcExamples.Structured.SumcheckReferenceInstallation.field)) := ⟨Field.toIsField Scalar⟩
  have uniform := ZkcSecurity.Realizations.Sumcheck.SourcePublicInstallations.two_cost model 2
  have installed (left right : List Scalar) (a b : Scalar) (count : Nat) :=
    ZkcSecurity.Source.RootPublic.cost_inputFrame
      ZkcExamples.Structured.Generated.Connections.TwoSums.validator rfl model
      (ZkcSecurity.Realizations.Sumcheck.SourceRootReference.rootInputs model .twoSums
        (.cons (some left) (.cons (some right) (.cons (some a) (.cons (some b)
          (.cons (some count) (.cons (some ZkcSecurity.Examples.RootProperties.TwoSums.serviceHandle) .nil))))))) 2
      ((Domain.encodeValues (ZkcSecurity.Examples.Generated.Components.TwoSumsABI.statement left right a b count)).getD []) initial _ rfl
      (ZkcSecurity.Examples.RootProperties.TwoSums.Soundness.source_inputs left right a b count initial) [] _
      (uniform left right a b count ZkcSecurity.Examples.RootProperties.TwoSums.serviceHandle [])
  have budget : ZkcExamples.Structured.SumcheckSourceSelections.maximum .twoSums • (2 : ENNReal) +
      ZkcExamples.Structured.SumcheckSourceSelections.maximum .twoSums • (2 : ENNReal) = 16 := by
    norm_num [ZkcExamples.Structured.SumcheckSourceSelections.maximum]
  simp only [budget] at installed
  have uniformCosts (statement : Statement) :
      Typed.ChargedCostBound installation.absorb (fun _ _ => 2)
        (installation.presented statement initial) initial 16 := by
    bind_subject_abi using installed
  apply chargedCostBound_mono_bound _ _ _ _ 16 _ ?_ (le_add_right le_rfl)
  exact smallerPrices _ _ _
    (fun history event => by simpa only [maximum] using schedule.charge_le_maximum queries history event)
    _ _ _ (uniformCosts statement)

def reductionExport (queries : Nat) :
    Claims.Domain.ChargedExport TwoSums.validatorSubject schedule queries (validatorCost queries) :=
  RootConnection.losslessChargedExport TwoSums.validatorSubject
    ZkcExamples.Structured.Generated.Connections.TwoSums.validatorRouting rfl
    ZkcExamples.Structured.Generated.Connections.TwoSums.validator
    ZkcSecurity.Examples.RootProperties.TwoSums.Soundness.supported _ rfl
    ZkcSecurity.Examples.RootProperties.TwoSums.noLocal
    schedule queries (validatorCost queries) (rejected queries) (costs queries)

def capabilities := ZkcSecurity.Examples.RootProperties.TwoSums.Soundness.claimCapabilities
def scalarBound (queries : Nat) : ENNReal := (queries : ENNReal) * 2 + validatorCost queries

theorem scalar_bound (queries : Nat) :
    (queries : ENNReal) * schedule.maximum queries + validatorCost queries ≤ scalarBound queries := by
  rw [maximum]
  exact le_rfl

def selected : Model := ⟨.adaptive, .symbolic "Q", "Q", "heterogeneous", .add (.constant 16) .queryBudget, none⟩
theorem costLaw (queries : Nat) : selected.validatorCost.value queries = validatorCost queries := by
  norm_num [selected, validatorCost, Bound.value]

example : Claims.Domain.SoundnessArguments.meaning capabilities
    (⟨selected, .charged schedule⟩ : Claims.Domain.SoundnessArguments TwoSums.validatorSubject) :=
  Claims.CompiledSoundness.charged_meaning (model := model) (art := TwoSums.validatorArtifacts)
    (subject := TwoSums.validatorSubject) capabilities schedule validatorCost reductionExport selected rfl costLaw

example : Claims.Domain.Soundness capabilities TwoSums.validatorSubject selected scalarBound :=
  Claims.CompiledSoundness.scalar_meaning (model := model) (art := TwoSums.validatorArtifacts)
    (subject := TwoSums.validatorSubject) capabilities schedule validatorCost scalarBound reductionExport scalar_bound selected rfl

-- A declaration name cannot authorize another subject, schedule or cost.
#check_failure (show Claims.Domain.ChargedExport SmallSumcheck.validatorSubject
  (Claims.Domain.ChargeSchedule.empty SmallSumcheck.validatorSubject) 0 0 from reductionExport 0)
#check_failure (show Claims.Domain.ChargedExport TwoSums.validatorSubject
  (Claims.Domain.ChargeSchedule.empty TwoSums.validatorSubject) 0 (validatorCost 0) from reductionExport 0)
#check_failure (show Claims.Domain.ChargedExport TwoSums.validatorSubject schedule 0 0 from reductionExport 0)
#check_failure (show ∀ queries, selected.validatorCost.value queries = 0 from costLaw)
#check_failure (show ∀ (queries : Nat),
  (queries : ENNReal) * schedule.maximum queries + validatorCost queries ≤ 0 from scalar_bound)

end Heterogeneous

namespace Empty

def schedule : Claims.Domain.ChargeSchedule TwoSums.validatorSubject := .empty _

example : (Claims.Domain.chargeSchedule TestsSecurity.DomainCharges.capabilities TwoSums.validatorSubject
    TestsSecurity.DomainCharges.selected []).map (fun result => result.toOption.isSome) = .ok true := rfl
example (queries : Nat) : schedule.charge queries = fun _ _ => 0 :=
  Claims.Domain.ChargeSchedule.empty_charge _ queries

/-- A constructed validator fixture with an actual Boolean return instruction.
No construction certificate, source target or stage identity is fabricated. -/
def artifact (decision : Bool) : Participant :=
  { TwoSums.validatorArtifacts.participant with
    inputs := [], outputs := [.data .boolean], returned := [0]
    instructions := [⟨.calculate (.booleanConstant decision), [], [.data .boolean], []⟩] }

def result (decision : Bool) : Domain.Result carriers :=
  ⟨[.data (.boolean decision)], [.data (.boolean decision)]⟩

def actual (decision : Bool) : PIR.Process (Domain.effects carriers) (Domain.Result carriers) :=
  Domain.participant model TwoSums.validatorCompiled.imported.program
    TwoSums.validatorCompiled.selection.context (artifact decision) []

def presented (decision : Bool) : PIR.Process (Domain.effects carriers) (Domain.Result carriers) :=
  .done (result decision)

def accepts (value : Domain.Result carriers) : Prop := value.values = [.data (.boolean true)]

theorem bridge (decision : Bool) (initial : Domain.History carriers) :
    DomainReduction.Bridge DomainReduction.queryInterface (fun _ _ => True) initial
      (actual decision) (presented decision) := by
  change DomainReduction.Bridge _ _ initial
    (.call (.checkpoint []) fun _ => .call (.checkpoint []) fun _ =>
      .call (.checkpoint [.data (.boolean decision)]) fun _ => .done (result decision)) _
  apply DomainReduction.Bridge.checkpoint
  apply DomainReduction.Bridge.checkpoint
  apply DomainReduction.Bridge.checkpoint
  exact .done _ _ trivial

def rejection (queries : Nat) (initial : Domain.History carriers) :
    Zkc.Obligations.Derivation DomainReduction.queryInterface (boundedEscape (schedule.charge queries))
      (fun _ value => ¬ accepts value) initial (presented false) :=
  .done (by simp [accepts, result])

theorem cost (decision : Bool) (queries : Nat) (initial : Domain.History carriers) :
    Typed.ChargedCostBound DomainReduction.queryInterface (schedule.charge queries)
      (presented decision) initial 0 := trivial

/-- Zero error uses an actual rejection derivation and the existing property
of the actual Domain handler; the empty schedule alone is insufficient. -/
theorem soundness (queries : Nat) (initial : Domain.History carriers)
    (prover : OracleComp (TranscriptOracle.DomainSpec carriers) (Domain.Proof carriers))
    (bounded : WorstCaseCostBound prover ⟨Typed.keyCharge (schedule.charge queries)⟩ 0) :
    Pr{let value ← (simulateQ randomOracle
      (prover >>= fun proof => (fun execution => (execution.outcome, execution.state.proof)) <$>
        Domain.run .validator (ZkcSecurity.Endpoint.Domain.Compiled.oracle (Typed.ask (R := Typed.ByLast Domain.Raw)))
          (actual false) ⟨[], proof, ()⟩)).run' ∅}[Zkc.Transcript.Accepted accepts value.1] ≤ 0 := by
  simpa only [add_zero] using (bridge false initial).soundness_charged
    (reduction DomainReduction.queryInterface (fun _ value => ¬ accepts value) (schedule.charge queries))
    (fun _ _ rejected => rejected) (derived_doomed (rejection queries initial))
    0 (cost false queries initial) [] prover 0 bounded

/-- A false Boolean claim and an always-accepting result are a concrete bad
case. Cost is zero for both fixture variants; rejection is independent. -/
def target (claim : Bool) : Prop := claim = true
example : ¬ target false ∧ accepts (result true) := by
  constructor
  · intro impossible
    cases impossible
  · rfl
example (queries : Nat) (initial : Domain.History carriers) :
    ¬ Nonempty (Zkc.Obligations.Derivation DomainReduction.queryInterface (boundedEscape (schedule.charge queries))
      (fun _ value => ¬ accepts value) initial (presented true)) := by
  rintro ⟨derivation⟩
  cases derivation with
  | done impossible => exact impossible rfl

#check_failure (show Zkc.Obligations.Derivation DomainReduction.queryInterface (boundedEscape (schedule.charge 0))
  (fun _ value => ¬ accepts value) [] (presented true) from rejection 0 [])

end Empty

#print axioms Heterogeneous.reductionExport
#print axioms Empty.soundness

end TestsSecurity.MethodNeutralChargeAssembly
