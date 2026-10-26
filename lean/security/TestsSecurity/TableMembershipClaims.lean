import ZkcSecurity.Examples.TableMembership.Claims

/-! Actual aggregate ABI, fixed canonical meanings and refusal controls.
Generic nominal decoding and source/export admission controls remain with their
owning modules; these tests exercise the selected CheckMembership subject. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace TestsSecurity.TableMembershipClaims
open Zkc.Claims Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity ZkcSecurity.Claims ZkcSecurity.FiatShamir
open OracleComp OracleSpec
open ZkcSecurity.Examples.TableMembership
open ZkcSecurity.Examples.TableMembership.Subject
open ZkcExamples.Structured.TableMembershipLaws
local instance : DecidableEq (Domain.Event model.toCarriers) := Classical.decEq _

example : Completeness.completeEvaluated.proposition :=
  Completeness.completeReceipt.receipt.proof
example (application : String) : (Soundness.soundEvaluated application).proposition :=
  (Soundness.soundReceipt application).receipt.proof
example (application : String) : (Soundness.chargedEvaluated application).proposition :=
  (Soundness.chargedReceipt application).receipt.proof

example : Completeness.completeEvaluated.proposition = HonestPair.CanonicalCompleteness subject 0 := by
  change HonestPair.CanonicalCompleteness subject ((0 : ℚ≥0) : ENNReal) = _
  rw [ennreal_nnrat_zero]
example : Completeness.completeReceipt.receipt.status = .certified := rfl
example (application : String) : (Soundness.soundReceipt application).receipt.status = .certified := rfl
example (application : String) : (Soundness.chargedReceipt application).receipt.status = .certified := rfl
example : Completeness.subject.down.validatorSubject = Soundness.subject := rfl
example : Completeness.completeResolved.requiredLinks = subject.stageLinks :=
  Completeness.completeReceipt.association.requiredLinks
example (application : String) : (Soundness.soundResolved application).requiredLinks = validatorSubject.stageLinks :=
  (Soundness.soundReceipt application).association.requiredLinks

-- A proof of the same proposition without its required links stays open.
def missingLinks : Receipt Completeness.completeEvaluated :=
  Receipt.ofTheorem Completeness.completeReceipt.receipt.proof
    Completeness.completeReceipt.receipt.provenance
example : missingLinks.status = .open := rfl

example : ABI.producerInputs = [] := rfl
example (table : List Scalar) (queries : List Method.Query) :
    ABI.validatorInputs table queries = ZkcExamples.Construction.TableMembership.inputs table queries := rfl
example (table : List Scalar) (queries : List Method.Query) :
    (DomainReduction.policyCodec validatorCompiled subject.originalExport).encode (ABI.statement table queries) =
      ABI.initialHistory table queries := subject.validatorCodec_eq _ _
example : ABI.sourceInputs none none ≠ ABI.inputs [] [] := by
  intro same
  have wrong := congrArg (fun values => values.get .here) same
  cases wrong
example : subject.runtimeInputs (ABI.sourceInputs none none) = none := rfl

example : subject.Relation (ABI.inputs [] []) :=
  (Method.relation_iff [] []).mpr ⟨⟨by decide, Or.inl rfl⟩, rfl⟩
example : subject.HonestInput (ABI.inputs [] []) := by
  rw [ABI.honestInput_iff]
  simp [inputRepresentable, indexLimit]
example : subject.Relation (ABI.inputs [7] [(true, (7, ())), (false, (8, ()))]) := by
  apply (Method.relation_iff _ _).mpr
  decide +kernel
example : validatorSubject.FalseStatement (ABI.statement [7] [(true, (8, ()))]) := by
  apply (Method.false_iff _ _).mpr
  decide +kernel

private def refusingOracle : Domain.Oracle Id model.toCarriers Nat :=
  fun _ _ state => (.stopped .refused, state + 1)
private def execution (table : List Scalar) (queries : List Method.Query) :=
  Domain.executePair (m := Id) model imported.program subject.selection.context
    artifacts.producer artifacts.validator ABI.producerInputs
    (ABI.validatorInputs table queries) refusingOracle 0

example : Domain.PairExecution.succeeds subject.selection.position
    (execution [7] [(true, (7, ())), (false, (8, ()))]) = true := by decide +kernel
example : Domain.PairExecution.succeeds subject.selection.position
    (execution [7] [(true, (8, ()))]) = false := by decide +kernel
example : Domain.PairExecution.succeeds subject.selection.position (execution [] []) = true := by decide +kernel
example : ((execution [] []).validator.map (·.state.oracle)) = some 0 := by kernel_rfl

-- Equal mathematical decisions do not erase inactive values from the binding.
example : ABI.initialHistory [] [(false, (7, ()))] ≠ ABI.initialHistory [] [(false, (8, ()))] := by
  intro same
  have row := (Domain.PublicBinding.history_eq_iff subject.originalExport subject.originalExport
    selected.policy.publicInputs subject.publicBindingArity subject.publicBindingData
    (ABI.statement [] [(false, (7, ()))]) (ABI.statement [] [(false, (8, ()))])).mp same
  have values := congrArg (fun statement => statement.get (.there .here)) row.2
  have wrong := congrArg (fun queries => (queries.headD (false, (0, ()))).2.1) values
  exact (by decide +kernel : (7 : Scalar) ≠ 8) wrong

example (template : Template) : check subject.selection.context
    { artifacts.validator with instructions := [⟨.challenge "" "koala-bear" template, [0, 1],
      [.data (.field "koala-bear")], []⟩] } = .error "construction-plain-challenge" :=
  ZkcExamples.Construction.TableMembership.forged_challenge_refused template

-- This is the actual unbounded raw-statement theorem, with no HonestInput premise.
example (statement : Method.Statement) (falseStatement : validatorSubject.FalseStatement statement)
    (initial : Domain.History model.toCarriers) :
    PIR.Yields (fun result => validatorCompiled.acceptance result ≠ some true)
      (Method.presented statement initial) := Method.rejects statement falseStatement initial
example (application : String)
    (prover : OracleComp (TranscriptOracle.DomainSpec model.toCarriers)
      (Method.Statement × Domain.Proof model.toCarriers)) :
    Claims.CompiledSoundness.probability validatorSubject application prover = 0 :=
  Method.adaptive_zero application prover

-- Overbound values remain encoded; execution stops with their entire frame,
-- proof suffix and oracle state retained. Empty queries keep their special case.
example (table : List Scalar) (queries : List Method.Query) :
    Domain.encodeValues (ABI.statement table queries) = some (ABI.validatorInputs table queries) := rfl
example (table : List Scalar) (queries : List Method.Query) (proof : Domain.Proof model.toCarriers)
    (oracle : Domain.Oracle Id model.toCarriers Nat) (state : Nat)
    (overbound : ¬ Admissible table queries) :
    Domain.validate model imported.program subject.selection.context artifacts.validator
      (ABI.validatorInputs table queries) proof oracle state =
      ⟨.stopped .exhausted, ⟨ABI.validatorInputs table queries, proof, state⟩, []⟩ := by
  change Domain.validate (ringModel Scalar Scalar)
    ZkcExamples.Construction.TableMembership.program ZkcExamples.Construction.TableMembership.context
    ZkcExamples.Construction.TableMembership.validator
    (ZkcExamples.Construction.TableMembership.inputs (G := Scalar) table queries) proof oracle state = _
  rw [ZkcExamples.Construction.TableMembership.validate_equation (F := Scalar) (G := Scalar),
    ite_eq_right overbound]
  rfl
example (table : List Scalar) : Admissible table [] := ⟨by decide, Or.inl rfl⟩

namespace WrongTarget
def completeData : Wire.Request := { Completeness.completeData with
  target := .retained "wrong-owner" 0 "selected_rows" }
claim_request completeData using Completeness.library method
  (some (⟨⟨"fs.honest_completeness", 0⟩, []⟩ : Wire.Application))
run_cmd do
  if (← Lean.getEnv).contains `TestsSecurity.TableMembershipClaims.WrongTarget.completeReceipt then
    throwError "a wrong retained target produced a receipt"
end WrongTarget

namespace WrongStage
def completeData : Wire.Request := { Completeness.completeData with
  subject := { Completeness.completeData.subject with stage := .executableBytes } }
claim_request completeData using Completeness.library method
  (some (⟨⟨"fs.honest_completeness", 0⟩, []⟩ : Wire.Application))
run_cmd do
  if (← Lean.getEnv).contains `TestsSecurity.TableMembershipClaims.WrongStage.completeReceipt then
    throwError "an unproved native stage produced a receipt"
end WrongStage

#print axioms Completeness.completeReceipt
#print axioms Soundness.soundReceipt
#print axioms Soundness.chargedReceipt
end TestsSecurity.TableMembershipClaims
