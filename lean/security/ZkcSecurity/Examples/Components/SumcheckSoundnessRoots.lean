module

public import ZkcSecurity.Examples.Components.SmallSumcheckSoundness
public import ZkcSecurity.Examples.Components.TwoSumsSoundness
public import ZkcSecurity.Examples.Components.SmallSumcheckDomainTarget
public import ZkcSecurity.Examples.Components.TwoSumsDomainTarget
public import ZkcSecurity.Claims.CompiledSoundness
public import ZkcSecurity.FiatShamir.DomainAdaptive
public import ZkcSecurity.FiatShamir.DomainBinding

@[expose] public section
noncomputable section

/-! Canonical domain exports for the actual full compiled validators. The
retained source target, same checked pair, full public binding, actual ROM
cache, complete acceptance and charged certificate all meet in these roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace ZkcSecurity.Examples.Components.SumcheckSoundnessRoots
open OracleComp OracleSpec
open Zkc.Claims Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims ZkcSecurity.FiatShamir ZkcSecurity.Obligations
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Families.Sumcheck.TableComponent
open ZkcSecurity.Domains.PrimeField

abbrev Scalar := ZMod blsModulus
abbrev carriers := blsScalarModel.toCarriers
local instance : DecidableEq (Domain.Event carriers) := Classical.decEq _
local instance : ∀ event : Domain.Event carriers, SampleableType (Domain.Raw event) :=
  rawSampleable blsModulus

noncomputable def price : ENNReal := 1 / (Fintype.card Scalar : ENNReal)
def priceBound : Claims.Bound := .div (.constant 1) (Fintype.card Scalar : ℚ≥0)

theorem priceBound_value (queries : Nat) : priceBound.value queries = price := by
  simp only [priceBound, Bound.value, ennreal_nnrat_one, ennreal_nnrat_natural, price]

namespace Small
open ZkcSecurity.Examples.Generated.SmallSumcheck
abbrev Statement := validatorArtifacts.Statement blsScalarModel

def presented (statement : Statement) : Domain.History carriers →
    PIR.Process (Nominal.signature Scalar SmallSumcheck.Validator.field) (Domain.Result carriers) :=
  TypedABI.apply (Value := blsScalarModel.Value) (types := validatorArtifacts.publics)
    (SmallSumcheck.Validator.presented (F := Scalar) (G := Scalar)) statement

theorem bridge (statement : Statement) (initial : Domain.History carriers) :
    DomainReduction.Bridge (Nominal.interface (G := Scalar) SmallSumcheck.Validator.field) (fun _ _ => True) initial
      (Domain.participant blsScalarModel validatorCompiled.imported.program validatorCompiled.selection.context
        validatorArtifacts.participant ((Domain.encodeValues statement).getD [] ++ [.transcript validatorCompiled.selection.context.suite initial]))
      (presented statement initial) := by
  bind_subject_abi using SmallSumcheck.Validator.bridge

/-- The source formula supplies the mathematical false-input condition. Shape
and the source round guard are internal cases, not adversary restrictions. -/
noncomputable def false_input (raw : List Scalar) (claim : Scalar) (count : Nat)
    (falseStatement : validatorSubject.FalseStatement
      (ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI.statement raw claim count))
    (initial : Domain.History carriers) :
    Zkc.Obligations.Derivation (Nominal.interface (G := Scalar) SmallSumcheck.Validator.field)
      (boundedEscape (fun _ _ => price)) (fun _ result => SmallSumcheck.Soundness.Rejected result)
      initial (SmallSumcheck.Validator.presented raw claim count initial) := by
  by_cases allowed : count ≤ 2
  · exact SmallSumcheck.Soundness.derivation (fun _ _ => price)
      (TableComponent.PrimeField.conditionalWithFrame blsModulus SmallSumcheck.Validator.field
        (CompiledValidator.frameUpdate (F := Scalar) (G := Scalar) SmallSumcheck.Validator.field))
      raw claim count initial (fun shape => by
        have bounded : raw.length < indexLimit := by
          rw [shape]
          exact lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) allowed) (by decide +kernel)
        exact fun correct => ((SmallSumcheck.DomainTarget.false_iff raw claim count bounded).mp falseStatement) correct.symm)
  · change Zkc.Obligations.Derivation _ _ _ _ (SmallSumcheck.Validator.presented raw claim count initial)
    simp only [SmallSumcheck.Validator.presented, allowed, ite_false]
    exact .halt .refused

noncomputable def rejected (statement : Statement)
    (falseStatement : validatorSubject.FalseStatement statement) (initial : Domain.History carriers) :
    Zkc.Obligations.Derivation (Nominal.interface (G := Scalar) SmallSumcheck.Validator.field)
      (boundedEscape (fun _ _ => price)) (fun _ result => SmallSumcheck.Soundness.Rejected result)
      initial (presented statement initial) := by
  bind_subject_abi using false_input

noncomputable def installation : Claims.CompiledSoundness.Installation validatorSubject :=
  Claims.CompiledSoundness.Installation.typed
    (Nominal.signature Scalar SmallSumcheck.Validator.field)
    (Nominal.interface (G := Scalar) SmallSumcheck.Validator.field) (by rfl) presented bridge

theorem costs (statement : Statement) (initial : Domain.History carriers) :
    Typed.ChargedCostBound installation.absorb (fun _ _ => price)
      (presented statement initial) initial (2 • price) := by
  bind_subject_abi using (SmallSumcheck.Soundness.cost (fun _ _ => price) price (fun _ _ => le_rfl))

noncomputable def chargedExport (schedule : Claims.Domain.ChargeSchedule validatorSubject) (queries : Nat)
    (prices : ∀ entry ∈ schedule.entries, entry.2.value queries = price) :
    Claims.Domain.ChargedExport validatorSubject schedule queries (2 • price) :=
  Claims.CompiledSoundness.assembled installation price (2 • price) rejected costs schedule queries prices

def capabilities := blsCapabilities original (by decide +kernel)

def schedule : Claims.Domain.ChargeSchedule validatorSubject :=
  Claims.CompiledSoundness.uniformSchedule validatorSubject priceBound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem schedule_prices (queries : Nat) : ∀ entry ∈ schedule.entries, entry.2.value queries = price := by
  intro entry member
  exact (Claims.CompiledSoundness.uniformSchedule_prices priceBound _ _ _ queries entry member).trans
    (priceBound_value queries)

noncomputable def reductionExport (queries : Nat) :
    Claims.Domain.ChargedExport validatorSubject schedule queries (2 • price) :=
  chargedExport schedule queries (schedule_prices queries)

/-- The actual compiled experiment, after arbitrary oracle queries and adaptive
statement choice, with the same cache and full public binding. -/
theorem adaptive_charged (application : String) (queries : Nat)
    (prover : OracleComp (HonestCompiled.Spec carriers) (Statement × Domain.Proof carriers))
    (cost : ENNReal)
    (bounded : WorstCaseCostBound prover ⟨Typed.keyCharge (schedule.charge queries)⟩ cost) :
    Pr{let result ← (simulateQ randomOracle
      (prover >>= fun claimed => (fun result => (claimed.1, result)) <$>
        validatorCompiled.verifier blsScalarModel (Typed.ask (R := Typed.ByLast Domain.Raw)) claimed.1
          ((DomainReduction.policyCodec validatorArtifacts.publics validatorArtifacts.participant.policy.publicInputs
            (DomainReduction.policyArity validatorCompiled) application).encode claimed.1) claimed.2)).run' ∅}[
      validatorSubject.FalseStatement result.1 ∧ ZkcSecurity.Endpoint.Domain.CompleteAccepted result.2] ≤
        cost + 2 • price := by
  exact Claims.CompiledSoundness.adaptive_charged (reductionExport queries) application prover cost bounded

/-- The scalar specialization charges every adversary query visit, including
cache hits before statement choice. -/
theorem adaptive (application : String) (queries : Nat)
    (prover : OracleComp (HonestCompiled.Spec carriers) (Statement × Domain.Proof carriers))
    (bounded : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle
      (prover >>= fun claimed => (fun result => (claimed.1, result)) <$>
        validatorCompiled.verifier blsScalarModel (Typed.ask (R := Typed.ByLast Domain.Raw)) claimed.1
          ((DomainReduction.policyCodec validatorArtifacts.publics validatorArtifacts.participant.policy.publicInputs
            (DomainReduction.policyArity validatorCompiled) application).encode claimed.1) claimed.2)).run' ∅}[
      validatorSubject.FalseStatement result.1 ∧ ZkcSecurity.Endpoint.Domain.CompleteAccepted result.2] ≤
        ((queries : ENNReal) + 2) / (Fintype.card Scalar : ENNReal) := by
  exact Claims.CompiledSoundness.adaptive_fraction (Fintype.card Scalar) 2
    (reductionExport queries) (schedule_prices queries) application prover bounded

/-- Canonical scalar meaning for every admitted adaptive model context. -/
theorem scalar_meaning (selected : Model) (adaptiveForm : selected.form = .adaptive) :
    Claims.Domain.Soundness capabilities validatorSubject selected
      (fun queries => ((queries : ENNReal) + 2) / (Fintype.card Scalar : ENNReal)) := by
  exact Claims.CompiledSoundness.scalar_meaning (model := blsScalarModel)
    (art := validatorArtifacts) (subject := validatorSubject) capabilities schedule (Fintype.card Scalar) 2
    reductionExport schedule_prices selected adaptiveForm

/-- Canonical charged meaning includes the same reduction export at the exact
requested site prices, as well as the compiled adaptive probability theorem. -/
theorem charged_meaning (selected : Model) (adaptiveForm : selected.form = .adaptive)
    (validatorCost : ∀ queries, selected.validatorCost.value queries = 2 • price) :
    Claims.Domain.SoundnessArguments.meaning capabilities
      (⟨selected, .charged schedule⟩ : Claims.Domain.SoundnessArguments validatorSubject) := by
  exact Claims.CompiledSoundness.charged_meaning (model := blsScalarModel)
    (art := validatorArtifacts) (subject := validatorSubject) capabilities schedule (2 • price)
    reductionExport selected adaptiveForm validatorCost

#print axioms reductionExport
#print axioms adaptive
#print axioms charged_meaning

end Small

namespace Two
open ZkcSecurity.Examples.Generated.TwoSums
abbrev Statement := validatorArtifacts.Statement blsScalarModel

def presented (statement : Statement) : Domain.History carriers →
    PIR.Process (Nominal.signature Scalar TwoSums.Validator.field) (Domain.Result carriers) :=
  TypedABI.apply (Value := blsScalarModel.Value) (types := validatorArtifacts.publics)
    (TwoSums.Validator.presented (F := Scalar) (G := Scalar)) statement

theorem bridge (statement : Statement) (initial : Domain.History carriers) :
    DomainReduction.Bridge (Nominal.interface (G := Scalar) TwoSums.Validator.field) (fun _ _ => True) initial
      (Domain.participant blsScalarModel validatorCompiled.imported.program validatorCompiled.selection.context
        validatorArtifacts.participant ((Domain.encodeValues statement).getD [] ++ [.transcript validatorCompiled.selection.context.suite initial]))
      (presented statement initial) := by
  bind_subject_abi using TwoSums.Validator.bridge

/-- The source formula supplies the mathematical false-input condition. Shape
and the source round guard are internal cases, not adversary restrictions. -/
noncomputable def false_input (left right : List Scalar) (leftClaim rightClaim : Scalar) (count : Nat)
    (falseStatement : validatorSubject.FalseStatement
      (ZkcSecurity.Examples.Generated.Components.TwoSumsABI.statement left right leftClaim rightClaim count))
    (initial : Domain.History carriers) :
    Zkc.Obligations.Derivation (Nominal.interface (G := Scalar) TwoSums.Validator.field)
      (boundedEscape (fun _ _ => price)) (fun _ result => TwoSums.Soundness.Rejected result)
      initial (TwoSums.Validator.presented left right leftClaim rightClaim count initial) := by
  by_cases allowed : count ≤ 4
  · exact TwoSums.Soundness.derivation (fun _ _ => price)
      (TableComponent.PrimeField.conditionalWithFrame blsModulus TwoSums.Validator.field
        (CompiledValidator.frameUpdate (F := Scalar) (G := Scalar) TwoSums.Validator.field))
      left right leftClaim rightClaim count initial (fun leftShape rightShape => by
        have leftBounded : left.length < indexLimit := by
          rw [leftShape]
          exact lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) allowed) (by decide +kernel)
        have rightBounded : right.length < indexLimit := by
          rw [rightShape]
          exact lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) allowed) (by decide +kernel)
        have wrong := (TwoSums.DomainTarget.false_iff left right leftClaim rightClaim count leftBounded rightBounded).mp falseStatement
        simpa only [ne_eq, eq_comm] using wrong)
  · change Zkc.Obligations.Derivation _ _ _ _ (TwoSums.Validator.presented left right leftClaim rightClaim count initial)
    simp only [TwoSums.Validator.presented, allowed, ite_false]
    exact .halt .refused

noncomputable def rejected (statement : Statement)
    (falseStatement : validatorSubject.FalseStatement statement) (initial : Domain.History carriers) :
    Zkc.Obligations.Derivation (Nominal.interface (G := Scalar) TwoSums.Validator.field)
      (boundedEscape (fun _ _ => price)) (fun _ result => TwoSums.Soundness.Rejected result)
      initial (presented statement initial) := by
  bind_subject_abi using false_input

noncomputable def installation : Claims.CompiledSoundness.Installation validatorSubject :=
  Claims.CompiledSoundness.Installation.typed
    (Nominal.signature Scalar TwoSums.Validator.field)
    (Nominal.interface (G := Scalar) TwoSums.Validator.field) (by rfl) presented bridge

theorem costs (statement : Statement) (initial : Domain.History carriers) :
    Typed.ChargedCostBound installation.absorb (fun _ _ => price)
      (presented statement initial) initial (8 • price) := by
  bind_subject_abi using (TwoSums.Soundness.cost (fun _ _ => price) price (fun _ _ => le_rfl))

noncomputable def chargedExport (schedule : Claims.Domain.ChargeSchedule validatorSubject) (queries : Nat)
    (prices : ∀ entry ∈ schedule.entries, entry.2.value queries = price) :
    Claims.Domain.ChargedExport validatorSubject schedule queries (8 • price) :=
  Claims.CompiledSoundness.assembled installation price (8 • price) rejected costs schedule queries prices

def capabilities := blsCapabilities original (by decide +kernel)

def schedule : Claims.Domain.ChargeSchedule validatorSubject :=
  Claims.CompiledSoundness.uniformSchedule validatorSubject priceBound
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem schedule_prices (queries : Nat) : ∀ entry ∈ schedule.entries, entry.2.value queries = price := by
  intro entry member
  exact (Claims.CompiledSoundness.uniformSchedule_prices priceBound _ _ _ queries entry member).trans
    (priceBound_value queries)

noncomputable def reductionExport (queries : Nat) :
    Claims.Domain.ChargedExport validatorSubject schedule queries (8 • price) :=
  chargedExport schedule queries (schedule_prices queries)

/-- The actual compiled experiment, after arbitrary oracle queries and adaptive
statement choice, with the same cache and full public binding. -/
theorem adaptive_charged (application : String) (queries : Nat)
    (prover : OracleComp (HonestCompiled.Spec carriers) (Statement × Domain.Proof carriers))
    (cost : ENNReal)
    (bounded : WorstCaseCostBound prover ⟨Typed.keyCharge (schedule.charge queries)⟩ cost) :
    Pr{let result ← (simulateQ randomOracle
      (prover >>= fun claimed => (fun result => (claimed.1, result)) <$>
        validatorCompiled.verifier blsScalarModel (Typed.ask (R := Typed.ByLast Domain.Raw)) claimed.1
          ((DomainReduction.policyCodec validatorArtifacts.publics validatorArtifacts.participant.policy.publicInputs
            (DomainReduction.policyArity validatorCompiled) application).encode claimed.1) claimed.2)).run' ∅}[
      validatorSubject.FalseStatement result.1 ∧ ZkcSecurity.Endpoint.Domain.CompleteAccepted result.2] ≤
        cost + 8 • price := by
  exact Claims.CompiledSoundness.adaptive_charged (reductionExport queries) application prover cost bounded

/-- The scalar specialization charges every adversary query visit, including
cache hits before statement choice. -/
theorem adaptive (application : String) (queries : Nat)
    (prover : OracleComp (HonestCompiled.Spec carriers) (Statement × Domain.Proof carriers))
    (bounded : IsTotalQueryBound prover queries) :
    Pr{let result ← (simulateQ randomOracle
      (prover >>= fun claimed => (fun result => (claimed.1, result)) <$>
        validatorCompiled.verifier blsScalarModel (Typed.ask (R := Typed.ByLast Domain.Raw)) claimed.1
          ((DomainReduction.policyCodec validatorArtifacts.publics validatorArtifacts.participant.policy.publicInputs
            (DomainReduction.policyArity validatorCompiled) application).encode claimed.1) claimed.2)).run' ∅}[
      validatorSubject.FalseStatement result.1 ∧ ZkcSecurity.Endpoint.Domain.CompleteAccepted result.2] ≤
        ((queries : ENNReal) + 8) / (Fintype.card Scalar : ENNReal) := by
  exact Claims.CompiledSoundness.adaptive_fraction (Fintype.card Scalar) 8
    (reductionExport queries) (schedule_prices queries) application prover bounded

/-- Canonical scalar meaning for every admitted adaptive model context. -/
theorem scalar_meaning (selected : Model) (adaptiveForm : selected.form = .adaptive) :
    Claims.Domain.Soundness capabilities validatorSubject selected
      (fun queries => ((queries : ENNReal) + 8) / (Fintype.card Scalar : ENNReal)) := by
  exact Claims.CompiledSoundness.scalar_meaning (model := blsScalarModel)
    (art := validatorArtifacts) (subject := validatorSubject) capabilities schedule (Fintype.card Scalar) 8
    reductionExport schedule_prices selected adaptiveForm

/-- Canonical charged meaning includes the same reduction export at the exact
requested site prices, as well as the compiled adaptive probability theorem. -/
theorem charged_meaning (selected : Model) (adaptiveForm : selected.form = .adaptive)
    (validatorCost : ∀ queries, selected.validatorCost.value queries = 8 • price) :
    Claims.Domain.SoundnessArguments.meaning capabilities
      (⟨selected, .charged schedule⟩ : Claims.Domain.SoundnessArguments validatorSubject) := by
  exact Claims.CompiledSoundness.charged_meaning (model := blsScalarModel)
    (art := validatorArtifacts) (subject := validatorSubject) capabilities schedule (8 • price)
    reductionExport selected adaptiveForm validatorCost

#print axioms reductionExport
#print axioms adaptive
#print axioms charged_meaning

end Two
end ZkcSecurity.Examples.Components.SumcheckSoundnessRoots
