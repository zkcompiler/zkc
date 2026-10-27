module

public import ZkcExamples.Construction.BatchOpeningData
public import ZkcExamples.Construction.BatchOpeningArtifacts
public import ZkcExamples.Construction.BatchOpeningBodies
public import Zkc.Source.Structured.UnitViews
public import Zkc.Construction.DomainBinding
public import Zkc.Construction.DomainViewLaws
public import Zkc.Construction.AuthoredPairExecution

@[expose] public section

/-! Actual plain construction of a record-valued batch response. The source
validates the point/value fields by its retained finite helper. The full open
bindings quantify arbitrary environments and receive replies. This client is
transport evidence and makes no commitment or KZG security assertion. -/
set_option autoImplicit false
set_option smartUnfolding false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
noncomputable section
namespace ZkcExamples.Construction.BatchOpening
open Zkc.Source Zkc.Source.Structured Zkc.Construction BatchOpeningBodies

abbrev snapshot := BatchOpeningData.snapshot
abbrev artifacts := BatchOpeningArtifacts.artifacts
abbrev producer := artifacts.producer
abbrev validator := artifacts.validator

structured_views snapshot
  helpers [checkOpening, batchStep, batchValues, formula, mathematicalAdmission, checkBatch]
  protocols [run]

def context : Context := Context.plain snapshot.entry ["role00000000", "role00000001"] 0 1

def selected : AuthoredPair.Selection snapshot :=
  (AuthoredPair.select snapshot artifacts "values").toOption.get (by decide +kernel)

theorem admitted : AuthoredPair.Admitted imported selected artifacts := ⟨by decide +kernel⟩
theorem actual_context : exportContext snapshot validator = some context := by kernel_rfl

abbrev batchTy : Ty := runSignature.inputs[2]
abbrev openingTy : Ty := batchStepHelper.inputs[1]

/-- The batch is a real returned data output, following the Boolean decision. -/
theorem actual_outputs : validator.outputs = [.data .boolean, .data batchTy] ∧
    validator.returned = [3, 2] := ⟨rfl, rfl⟩

variable (model : DomainModel)

def producerView : Domain.Binding.Meaning model.toCarriers :=
  Domain.View.participant producer.inputs producer.outputs producer.returned
    (Domain.View.sequence (Domain.View.send "label_6261746368_0" "label_6261746368_0" "role00000001" 0 [])
      Domain.View.empty)

def validatorView : Domain.Binding.Meaning model.toCarriers :=
  Domain.View.participant validator.inputs validator.outputs validator.returned
    (Domain.View.sequence
      (Domain.View.receive "label_6261746368_0" "label_6261746368_0" "role00000000" batchTy [.data batchTy])
      (Domain.View.sequence
        (Domain.View.helper model program checkBatchHelper.name [0, 1, 2] [.data .boolean])
        Domain.View.empty))

theorem producer_binding (env : Domain.Environment model.toCarriers) :
    Domain.participant model program context producer env = producerView model env := by
  apply Domain.Correspondence.participant
  exact Domain.Correspondence.sequence (Domain.Correspondence.send _ _ _ _ _)
    Domain.Correspondence.empty

theorem validator_binding (env : Domain.Environment model.toCarriers) :
    Domain.participant model program context validator env = validatorView model env := by
  apply Domain.Correspondence.participant
  exact Domain.Correspondence.sequence (Domain.Correspondence.receive _ _ _ _ _)
    (Domain.Correspondence.sequence (Domain.Correspondence.helper _ _ _) Domain.Correspondence.empty)

def payload (batch : model.Value batchTy) : Domain.Payload model.toCarriers :=
  ⟨batchTy, by decide, batch⟩

theorem roundtrip (batch : model.Value batchTy) : (payload model batch).value batchTy = some batch := by
  simp only [payload, Domain.Payload.value, ↓reduceDIte]

theorem payload_injective : Function.Injective (payload model) := by
  intro first second same
  have decoded := congrArg (Domain.Payload.value batchTy) same
  simpa only [roundtrip, Option.some.injEq] using decoded

/-- The actual producer sends the complete nominal record sequence, with no
observation or transcript capability inserted before or after the send. -/
theorem producer_process (batch : model.Value batchTy) :
    Domain.participant model program context producer [.data (payload model batch)] =
      .call (.checkpoint [.data (payload model batch)]) (fun _ =>
        .call (.checkpoint [.data (payload model batch)]) (fun _ =>
          .call (.send "label_6261746368_0" "label_6261746368_0" "role00000001" (payload model batch)) (fun _ =>
            .call (.checkpoint [.data (payload model batch)]) (fun _ =>
              .done ⟨[], [.data (payload model batch)]⟩)))) := by
  rw [producer_binding]
  kernel_rfl

/-- Both layouts come from the same actual source tuple. Plain preparation
keeps the complete aggregate and adds no transcript capability. -/
theorem preparation (point value : model.Field "koala-bear") (batch : model.Value batchTy)
    (history : Domain.History model.toCarriers) :
    AuthoredPair.prepare imported selected model (.cons point (.cons value (.cons batch .nil))) history =
      some ([.data (payload model batch)],
        [.data (.field "koala-bear" point), .data (.field "koala-bear" value)]) := by kernel_rfl

/-- The public admitted runner executes these exact source-derived layouts. -/
theorem admitted_execution {m : Type → Type} [Monad m] {S : Type}
    (point value : model.Field "koala-bear") (batch : model.Value batchTy)
    (history : Domain.History model.toCarriers) (oracle : Domain.Oracle m model.toCarriers S) (state : S) :
    AuthoredPair.execute imported selected model (.cons point (.cons value (.cons batch .nil))) history oracle state =
      Domain.executePair model program context producer validator [.data (payload model batch)]
        [.data (.field "koala-bear" point), .data (.field "koala-bear" value)] oracle state := by kernel_rfl

/-- Typed receive admission is recursive data eligibility, with no scalar gate. -/
theorem receive_reply (env : Domain.Environment model.toCarriers) :
    Domain.View.receive "label_6261746368_0" "label_6261746368_0" "role00000000" batchTy [.data batchTy] env =
      .call (.receive batchTy "label_6261746368_0" "label_6261746368_0" "role00000000") (fun reply =>
        .done (env ++ [.data (payload model reply)])) := by
  rw [Domain.View.receive_eq _ _ _ _ (by decide)]
  kernel_rfl

end ZkcExamples.Construction.BatchOpening
