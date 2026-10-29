import ZkcExamples.Construction.TableMembership
import ZkcExamples.Construction.BatchOpening
import Mathlib.Data.ZMod.Basic
import ZkcTools.ConstructionBindings.Admission
import Tests.ConnectionRefusal

/-! Kernel controls through the actual admitted plain construction path.
The batch checks concern transport and the source's finite validation helper;
they are not commitment-security or native byte-codec receipts. -/
set_option autoImplicit false
set_option smartUnfolding false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
noncomputable section
set_option linter.unusedTactic false
namespace Tests.PlainConstruction
open Zkc.Source Zkc.Source.Structured Zkc.Construction
namespace Batch
open ZkcExamples.Construction.BatchOpening

private abbrev F := ZMod 2130706433
private abbrev selectedModel := ringModel F F
private def batch : selectedModel.Value batchTy := [(3, (5, ())), (3, (5, ()))]
private def swapped : selectedModel.Value batchTy := [(5, (3, ()))]
private def publicInputs : Domain.Environment selectedModel.toCarriers :=
  [.data (.field "koala-bear" 3), .data (.field "koala-bear" 5)]
private def oracle : Domain.Oracle Id selectedModel.toCarriers Nat :=
  fun _ _ state => (.stopped .refused, state + 1)
private def execution (messages : selectedModel.Value batchTy) :=
  AuthoredPair.execute (m := Id) imported selected selectedModel
    (.cons 3 (.cons 5 (.cons messages .nil))) [] oracle 0

example : AuthoredPair.check imported selected artifacts = .ok () := admitted.checked
example : Domain.PairExecution.succeeds 0 (execution batch) = true := by decide +kernel
example : Domain.PairExecution.succeeds 0 (execution swapped) = false := by decide +kernel

-- The real aggregate output is kept after the decision, with its field order.
example : ((execution batch).validator.map fun checked =>
    match checked.outcome with
    | .returned result => result.values[1]?
    | .stopped _ => none) = some (some (.data (payload selectedModel batch))) := by kernel_rfl
example : (execution batch).producer.state.proof = [payload selectedModel batch] := by kernel_rfl
example : ((execution batch).validator.map (·.state.proof)) = some [] := by kernel_rfl
example : ((execution batch).validator.map (·.state.oracle)) = some 0 := by kernel_rfl
example : AuthoredPair.observations (execution batch) = [] := by kernel_rfl

private def wrongNominal : Ty := .sequence (.product "other.Opening" "case00000000"
  (.cons (.field "koala-bear") (.cons (.field "koala-bear") .nil)))
private def wrongMessage : Domain.Payload selectedModel.toCarriers :=
  ⟨wrongNominal, by decide, [(3, (5, ()))]⟩

example : (Domain.validate (m := Id) selectedModel program context validator publicInputs
    [wrongMessage] oracle 0).outcome = .stopped .refused := by kernel_rfl
example : (Domain.validate (m := Id) selectedModel program context validator publicInputs
    [wrongMessage] oracle 0).state.proof = [wrongMessage] := by kernel_rfl

-- Empty sequences retain their element sort despite sharing an empty host list.
private def emptyWrong : Domain.Payload selectedModel.toCarriers :=
  ⟨.sequence (.field "koala-bear"), by decide, []⟩
example : (Domain.validate (m := Id) selectedModel program context validator publicInputs
    [emptyWrong] oracle 0).outcome = .stopped .refused := by kernel_rfl

private def wrongNominalParticipant : Participant := { validator with instructions :=
    (⟨.receive "label_6261746368_0" "label_6261746368_0" "role00000000" wrongNominal,
      [], [.data wrongNominal], []⟩ :: validator.instructions.drop 1) }
example : True := by
  expect_connection_refusal "plain nominal message" because "alignment-"
    have refused : ConnectionAdmission.Required program context .validator wrongNominalParticipant := by
      derive_source_connection
  trivial

example (template : Template) : Domain.queryOrigin context "" "koala-bear" template [] = none := by
  kernel_rfl
example : Domain.interface (carriers := selectedModel.toCarriers) context
    (.query "forged" "koala-bear" (.cons 0 .nil)) = .refuse := by kernel_rfl
end Batch

namespace Table
open ZkcExamples.Construction.TableMembership
private abbrev F := ZMod 2130706433
private abbrev selectedModel := ringModel F F
private def oracle : Domain.Oracle Id selectedModel.toCarriers Nat :=
  fun _ _ state => (.stopped .refused, state + 1)

example : AuthoredPair.selectedSucceeds selected
    (AuthoredPair.execute (m := Id) imported selected selectedModel
      (.cons [7] (.cons [(true, (7, ())), (false, (8, ()))] .nil)) [] oracle 0) = true := by decide +kernel
example : AuthoredPair.selectedSucceeds selected
    (AuthoredPair.execute (m := Id) imported selected selectedModel
      (.cons [7] (.cons [(true, (8, ()))] .nil)) [] oracle 0) = false := by decide +kernel

-- Inactive rows can have the same mathematical decision and different bound data.
example : PIR.Relation.Table.membership ([] : List F) [⟨false, 7⟩] =
    PIR.Relation.Table.membership ([] : List F) [⟨false, 8⟩] := by kernel_rfl
example : Domain.Payload.ofValue (carriers := selectedModel.toCarriers)
      (.sequence ZkcExamples.Structured.TableMembershipLaws.query) [(false, (7, ()))] ≠
    Domain.Payload.ofValue (carriers := selectedModel.toCarriers)
      (.sequence ZkcExamples.Structured.TableMembershipLaws.query) [(false, (8, ()))] := by
  intro same
  have values := Domain.Payload.ofValue_injective (by decide) same
  have wrong := congrArg (fun values => (values.headD (false, (0, ()))).2.1) values
  exact (by decide +kernel : (7 : F) ≠ 8) wrong

example : exportAcceptance snapshot { validator with outputs := [] } = none := by kernel_rfl
example : exportContext snapshot { validator with inputs := validator.inputs ++ [.transcript ""] } = none := by
  kernel_rfl

example (template : Template) : check context
    { validator with instructions := [⟨.challenge "" "koala-bear" template, [0, 1],
      [.data (.field "koala-bear")], []⟩] } = .error "construction-plain-challenge" :=
  forged_challenge_refused template
end Table
namespace RuleControls
open ZkcExamples.Construction.TableMembership
private def state : PlainState := ⟨[.data .index, .data .boolean], []⟩
private def step := checkPlainStep context context.validator context.producer state
private def template : Template := ⟨snapshot.entry, [], []⟩
private def port : ServicePort := ⟨"private", "role00000001", 2, 2, "random.koala-bear/0"⟩

example : step ⟨.receive "site" "other" "role00000000" .boolean, [], [.data .boolean], []⟩ =
    .error "construction-plain-receive" := by kernel_rfl
example : step ⟨.send "site" "site" "role00000000", [99], [], []⟩ =
    .error "construction-plain-send" := by kernel_rfl
example : step ⟨.calculate .booleanAnd, [0, 1], [.data .boolean], []⟩ =
    .error "construction-plain-calculation" := by kernel_rfl
example : step ⟨.call "helper", [99], [.data .boolean], []⟩ =
    .error "construction-plain-call" := by kernel_rfl
example : step ⟨.guard "site", [0], [], []⟩ = .error "construction-plain-guard" := by kernel_rfl
example : step ⟨.localService { port with owner := "role00000000" } (.draw "koala-bear") template [],
    [], [.data (.field "koala-bear")], []⟩ = .error "construction-plain-local-service" := by kernel_rfl
example : step ⟨.localService port ⟨"read", [], .boolean⟩ template [], [], [.data .boolean], []⟩ =
    .error "construction-plain-local-service-request" := by kernel_rfl
example : step ⟨.loop "site" 4 [0], [1, 0], [.data .index], []⟩ =
    .error "construction-plain-loop" := by kernel_rfl
example : step ⟨.loop "site" 4 [99], [0, 1], [.data .boolean], []⟩ =
    .error "construction-plain-loop-yield" := by kernel_rfl
example : step ⟨.observe "" template, [], [], []⟩ = .error "construction-plain-transcript" := by kernel_rfl
example : step ⟨.indicesEmpty, [], [.indices], []⟩ = .error "construction-plain-shape" := by kernel_rfl
example : check context { validator with inputs := [.transcript ""] } =
    .error "construction-plain-inputs" := by kernel_rfl
example : check context { validator with returned := [99] } =
    .error "construction-plain-final" := by kernel_rfl

-- Private services retain their owner and do not require a replacement service.
example : step ⟨.localService port (.draw "koala-bear") template [],
    [], [.data (.field "koala-bear")], []⟩ =
    .ok { state with sorts := state.sorts ++ [.data (.field "koala-bear")] } := by kernel_rfl
end RuleControls
end Tests.PlainConstruction
