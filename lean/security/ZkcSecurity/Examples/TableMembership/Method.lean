module

public import ZkcSecurity.Examples.TableMembership.ABI
public import ZkcSecurity.Claims.Completeness
public import ZkcSecurity.Claims.CompiledSoundness
public import ZkcSecurity.Endpoint.DomainSafety

@[expose] public section

/-! Perfect honest completion and zero-error adversarial soundness consume the
same actual whole-validator binding and the existing table-helper mathematics.
Only honest inputs carry representation bounds. Every raw typed statement and
every proof remains in the soundness game, including exhausted computations. -/
set_option autoImplicit false
set_option smartUnfolding false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace ZkcSecurity.Examples.TableMembership.Method
open ZkcSecurity.Examples.TableMembership.Subject
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity ZkcSecurity.Claims ZkcSecurity.FiatShamir
open OracleComp OracleSpec
open ZkcExamples.Structured
open TableMembershipLaws

abbrev Query := QueryValue Scalar
abbrev Statement := validatorArtifacts.Statement model
abbrev carriers := model.toCarriers
local instance : DecidableEq (Domain.Event carriers) := Classical.decEq _

/-- The exact retained source helper, selected independently of property evidence. -/
def formula : FormulaBinding imported subject.target.application.relation := by bind_contract

/-- The retained source formula is characterized by the existing helper law.
Successful bounded execution is part of retained truth, rather than an
adversarial admission premise. -/
theorem formula_truth (table : List Scalar) (queries : List Query) :
    formula.invokeRelationOn model (ABI.arguments table queries) =
      .done (subject.target.booleanOutput.symm ▸ Values.cons true .nil) ↔
    Admissible table queries ∧ PIR.Relation.Table.membership table (queries.map decodeQuery) = true := by
  let witness : ZkcExamples.Construction.TableMembership.target.Witness Scalar Scalar := fun _ _ => none
  exact (ZkcExamples.Construction.TableMembership.target.holds_iff_of_arguments
      ZkcExamples.Structured.TableContractBindings.membershipFormula
    (ZkcExamples.Construction.TableMembership.statement table queries) witness
    (.cons table (.cons queries .nil))
    (ZkcExamples.Construction.TableMembership.target_arguments table queries witness)).symm.trans
      (ZkcExamples.Construction.TableMembership.target_holds_iff table queries witness)

theorem relation_iff (table : List Scalar) (queries : List Query) :
    subject.Relation (ABI.inputs table queries) ↔
      Admissible table queries ∧ PIR.Relation.Table.membership table (queries.map decodeQuery) = true :=
  (subject.relation_iff_of_read _ _ (ABI.application_read table queries)).trans (formula_truth table queries)

theorem holds_iff (table : List Scalar) (queries : List Query) (witness : validatorSubject.Witness) :
    validatorSubject.Holds (ABI.statement table queries) witness ↔
      Admissible table queries ∧ PIR.Relation.Table.membership table (queries.map decodeQuery) = true :=
  (validatorSubject.holds_iff_of_read _ witness _
    (ABI.validator_application_read table queries witness)).trans (formula_truth table queries)

theorem false_iff (table : List Scalar) (queries : List Query) :
    validatorSubject.FalseStatement (ABI.statement table queries) ↔
      ¬ (Admissible table queries ∧ PIR.Relation.Table.membership table (queries.map decodeQuery) = true) :=
  validatorSubject.falseStatement_iff_of_holds _ _ (holds_iff table queries)

set_option smartUnfolding true in
theorem nonvacuous : HonestPair.Nonvacuous subject := by
  refine ⟨ABI.inputs [] [], (relation_iff [] []).mpr ?_, (ABI.honestInput_iff [] []).mpr ?_⟩
  · exact ⟨⟨by decide, Or.inl rfl⟩, rfl⟩
  · simp [inputRepresentable, indexLimit]

/-- Exact producer and validator executions, before probability. The native
root equation uses the same validator_binding as adversarial rejection. -/
theorem honest_runtime (table : List Scalar) (queries : List Query)
    (related : subject.Relation (ABI.inputs table queries))
    (answers : QueryImpl (TranscriptOracle.DomainSpec carriers) Id) :
    Domain.PairExecution.Success subject.selection.position
      (Domain.executePair (m := Id) model imported.program subject.selection.context
        artifacts.producer artifacts.validator ABI.producerInputs
        (ABI.validatorInputs table queries) (HonestCompiled.tableOracle answers) ()) := by
  let witness : ZkcExamples.Construction.TableMembership.target.Witness Scalar Scalar := fun _ _ => none
  exact ZkcExamples.Construction.TableMembership.completeness table queries witness
    ((ZkcExamples.Construction.TableMembership.target_holds_iff table queries witness).mpr
      ((relation_iff table queries).mp related)) (HonestCompiled.tableOracle answers) ()

theorem compiled_ideal_complete : HonestPair.CanonicalCompleteness subject 0 := by
  apply HonestPair.perfect_of_pointwise_wp subject nonvacuous (by rfl) (by rfl)
  intro values related honest producer validator prepared answers
  obtain ⟨table, queries, rfl⟩ := ABI.honestInput_exists values honest
  rw [ABI.runtimeInputs_eq] at prepared
  cases Option.some.inj prepared
  exact (HonestCompiled.pair_success_iff_wp ..).mp (honest_runtime table queries related answers)

/-- A zero-query reference keeps the complete returned frame and exhausted
outcome of the actual helper. Its bridge below preserves the whole execution. -/
def presented (statement : Statement) (_initial : Domain.History carriers) :
    PIR.Process (Domain.Actions carriers) (Domain.Result carriers) :=
  let fields := ABI.statementData statement
  if Admissible fields.1 fields.2.1 then
    .done (ZkcExamples.Construction.TableMembership.result fields.1 fields.2.1)
  else .halt .exhausted

def absorb := Domain.interface (carriers := carriers) subject.selection.context

/-- Whole-process equality supplies all checkpoints and terminal frames; the
existing bridge erases only silent checkpoints in its oracle presentation. -/
theorem bridge (statement : Statement) (initial : Domain.History carriers) :
    DomainReduction.Bridge absorb (fun _ _ => True) initial
      (Domain.participant model imported.program subject.selection.context artifacts.validator
        (Domain.inputFrame subject.selection.context
          ((Domain.encodeValues statement).getD []) initial))
      (presented statement initial) := by
  obtain ⟨table, queries, rfl⟩ := ABI.statement_surjective statement
  change DomainReduction.Bridge _ _ _
    (Domain.participant (ringModel Scalar Scalar)
      ZkcExamples.Construction.TableMembership.program ZkcExamples.Construction.TableMembership.context
      ZkcExamples.Construction.TableMembership.validator
      (ZkcExamples.Construction.TableMembership.inputs (G := Scalar) table queries)) _
  rw [ZkcExamples.Construction.TableMembership.validator_equation (F := Scalar) (G := Scalar)]
  change DomainReduction.Bridge _ _ _ _
    (if Admissible table queries then
      .done (ZkcExamples.Construction.TableMembership.result (G := Scalar) table queries)
     else .halt .exhausted)
  by_cases bounded : Admissible table queries
  · rw [ite_eq_left bounded, ite_eq_left bounded]
    exact .checkpoint _ (.checkpoint _ (.checkpoint _ (.done initial _ trivial)))
  · rw [ite_eq_right bounded, ite_eq_right bounded]
    exact .checkpoint _ (.checkpoint _ (.halt initial .exhausted))

/-- False inputs reject under all replies, including those outside every
honest bound. This certificate is independent of the empty schedule. -/
theorem rejects (statement : Statement) (falseStatement : validatorSubject.FalseStatement statement)
    (initial : Domain.History carriers) :
    PIR.Yields (fun result => validatorCompiled.acceptance result ≠ some true) (presented statement initial) := by
  obtain ⟨table, queries, rfl⟩ := ABI.statement_surjective statement
  have falseTarget : ZkcExamples.Construction.TableMembership.target.FalseStatement
      ZkcExamples.Structured.TableContractBindings.membershipFormula
      (ZkcExamples.Construction.TableMembership.statement table queries) (G := Scalar) := by
    rintro ⟨witness, truth⟩
    apply (false_iff table queries).mp falseStatement
    exact (ZkcExamples.Construction.TableMembership.target_holds_iff table queries witness).mp truth
  have safe := ZkcExamples.Construction.TableMembership.false_input_rejected table queries falseTarget
  rw [ZkcExamples.Construction.TableMembership.validator_equation] at safe
  change PIR.Yields _ (if Admissible table queries then .done _ else .halt .exhausted)
  by_cases bounded : Admissible table queries
  · rw [ite_eq_left bounded] at safe ⊢
    exact safe () () ()
  · rw [ite_eq_right bounded]
    trivial

def schedule : Claims.Domain.ChargeSchedule validatorSubject := .empty validatorSubject

def validatorCost (_queries : Nat) : ENNReal := 0

def scalarBound (_queries : Nat) : ENNReal := 0

/-- The installed generic certificate sees the actual rejection theorem.
An empty schedule alone is insufficient to construct this export. -/
def reductionExport (queries : Nat) :
    Claims.Domain.ChargedExport validatorSubject schedule queries (validatorCost queries) where
  signature := Domain.Actions carriers
  absorb := absorb
  inputs statement := (Domain.encodeValues statement).getD []
  encoded statement := Domain.encodeValues_getD statement subject.publicBindingData
  presented := presented
  bridge := bridge
  certificate :=
    ((Endpoint.Domain.safetyReduction absorb
      (fun result => validatorCompiled.acceptance result ≠ some true)).mono absorb
        (fun _ _ post => post) (fun _ _ => bot_le)).toCertificate _ (fun _ _ post => post)
  doomed statement falseStatement initial := by
    exact rejects statement falseStatement initial
  costBound statement initial := by
    rw [show schedule = Claims.Domain.ChargeSchedule.empty validatorSubject from rfl,
      Claims.Domain.ChargeSchedule.empty_charge]
    exact Endpoint.Domain.zero_validator_cost absorb _ initial

theorem scalar_bound (queries : Nat) :
    (queries : ENNReal) * schedule.maximum queries + validatorCost queries ≤ scalarBound queries := by
  simp [schedule, Claims.Domain.ChargeSchedule.empty, Claims.Domain.ChargeSchedule.maximum,
    validatorCost, scalarBound]

/-- Zero error also holds without a query-count premise. The adversary may
choose any raw typed statement and proof after any terminating oracle work. -/
theorem adaptive_zero (application : String)
    (prover : OracleComp (TranscriptOracle.DomainSpec carriers) (Statement × Domain.Proof carriers)) :
    Claims.CompiledSoundness.probability validatorSubject application prover = 0 := by
  have bounded : WorstCaseCostBound prover ⟨Typed.keyCharge (schedule.charge 0)⟩ 0 := by
    rw [show schedule = Claims.Domain.ChargeSchedule.empty validatorSubject from rfl,
      Claims.Domain.ChargeSchedule.empty_charge]
    have zeroKeys : Typed.keyCharge (fun (_ : Domain.History carriers) (_ : Domain.Event carriers) =>
        (0 : ENNReal)) = fun _ => 0 := by
      funext key
      unfold Typed.keyCharge
      split <;> rfl
    rw [zeroKeys]
    exact Endpoint.Domain.zero_prover_cost prover
  have bound := Claims.CompiledSoundness.adaptive_charged (reductionExport 0) application prover 0 bounded
  have nonpositive : Claims.CompiledSoundness.probability validatorSubject application prover ≤ 0 := by
    simpa only [validatorCost, add_zero] using bound
  exact nonpos_iff_eq_zero.mp nonpositive

end ZkcSecurity.Examples.TableMembership.Method
