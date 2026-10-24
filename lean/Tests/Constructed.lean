import ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer
import ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator
import ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer
import ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator
import ZkcTools.StructuredSource.Constructed
import Zkc.Construction.DomainViewLaws

/-! Exact actual-artifact bindings and controls for the compositional seam.
No mathematical author module or uniform source presentation is imported. -/
set_option autoImplicit false
set_option smartUnfolding false
namespace Tests.Constructed
open Zkc.Source Zkc.Construction Zkc.Construction.Domain
open ZkcExamples.Structured.Generated.Constructed

-- The same admitted-program certificate applies to each actual role.
example {original : Structured.Snapshot} (imported : Structured.Imported original)
    (model : Structured.DomainModel) (context : Context) :
    Zkc.Verification.Certificate imported
      (fun program => Domain.participant model program context SmallSumcheckProducer.artifact)
      (fun actual => ∀ inputs,
        actual inputs = SmallSumcheckProducer.view model imported.program context inputs) :=
  Binding.certificate imported model context _ _
    (SmallSumcheckProducer.participant_eq model imported.program context)

example {original : Structured.Snapshot} (imported : Structured.Imported original)
    (model : Structured.DomainModel) (context : Context) :
    Zkc.Verification.Certificate imported
      (fun program => Domain.participant model program context SmallSumcheckValidator.artifact)
      (fun actual => ∀ inputs,
        actual inputs = SmallSumcheckValidator.view model imported.program context inputs) :=
  Binding.certificate imported model context _ _
    (SmallSumcheckValidator.participant_eq model imported.program context)

example {original : Structured.Snapshot} (imported : Structured.Imported original)
    (model : Structured.DomainModel) (context : Context) :
    Zkc.Verification.Certificate imported
      (fun program => Domain.participant model program context TwoSumsProducer.artifact)
      (fun actual => ∀ inputs,
        actual inputs = TwoSumsProducer.view model imported.program context inputs) :=
  Binding.certificate imported model context _ _
    (TwoSumsProducer.participant_eq model imported.program context)

example {original : Structured.Snapshot} (imported : Structured.Imported original)
    (model : Structured.DomainModel) (context : Context) :
    Zkc.Verification.Certificate imported
      (fun program => Domain.participant model program context TwoSumsValidator.artifact)
      (fun actual => ∀ inputs,
        actual inputs = TwoSumsValidator.view model imported.program context inputs) :=
  Binding.certificate imported model context _ _
    (TwoSumsValidator.participant_eq model imported.program context)

private abbrev carriers := Structured.uniformCarriers Int Unit
private def input : Environment carriers := [.data (.boolean false)]
private def oracle : Oracle Id carriers Nat := fun _ _ state => (.stopped .abort, state + 1)
private def state (proof : Proof carriers := []) : RuntimeState carriers Nat := ⟨[], proof, 0⟩

-- Failure keeps the exact pre-guard checkpoint and already emitted payload.
private def stopped : PIR.Process (effects carriers) (Environment carriers) :=
  View.sequence (View.send "m" "m" "V" 0 []) (View.sequence (View.guard 0 []) View.empty) input
example : (run .producer oracle stopped (state [])).outcome = .stopped .reject := by kernel_rfl
example : (run .producer oracle stopped (state [])).state.proof = [.boolean false] := by kernel_rfl
example : (run .producer oracle stopped (state [])).state.environment = input := by kernel_rfl

-- The open equation cannot erase a checkpoint, even when it changes no return.
example : View.sequence (carriers := carriers) View.empty View.empty [] ≠ View.empty [] := by
  intro equal
  cases equal

-- Every Boolean reply is retained; a constant honest reply is insufficient.
private def receive : PIR.Process (effects carriers) (Environment carriers) :=
  View.receive "m" "m" "P" .boolean [.data .boolean] []
example : receive = .call (.receive .boolean "m" "m" "P")
    (fun value => .done [.data (.boolean value)]) := by kernel_rfl
example : receive ≠ .call (.receive .boolean "m" "m" "P")
    (fun _ => .done [.data (.boolean true)]) := by
  intro equal
  have reply := PIR.Process.call.inj equal
  have wrong := congrFun (eq_of_heq reply.2) false
  cases wrong

example : (run .validator oracle receive (state [.index 0, .boolean true])).state.proof =
    [.index 0, .boolean true] := by kernel_rfl
example : (run .validator oracle receive (state [.boolean false, .index 0])).state.proof =
    [.index 0] := by kernel_rfl

-- Zero loops retain their carried values without executing the failing body.
private def failedBody : View.Block carriers := fun _ => .halt .abort
example : View.loop 4 [0] 0 [1] [.data .boolean] failedBody
    [.data (.index 0), .data (.boolean true)] =
      .done [.data (.index 0), .data (.boolean true), .data (.boolean true)] := by kernel_rfl
example : View.loop 4 [0] 0 [1] [.data .boolean] failedBody
    [.data (.index 5), .data (.boolean true)] = .halt .refused := by kernel_rfl

-- The whole returned frame and private output order remain observable.
example : View.participant [.data .boolean] [.data .boolean] [0] View.empty input =
    .call (.checkpoint input) (fun _ => .done ⟨input, input⟩) := by kernel_rfl
example : View.participant [.data .boolean] [] [] View.empty input =
    .call (.checkpoint input) (fun _ => .done ⟨[], input⟩) := by kernel_rfl
example : View.participant [.data .boolean] [.data .boolean] [1] View.empty input =
    .call (.checkpoint input) (fun _ => .halt .refused) := by kernel_rfl

-- Unsupported static shapes cause printing refusal, never evaluator fallback.
-- Match the stable code; ConstructedDiagnostics checks the full added context.
#guard match ZkcTools.StructuredSource.Constructed.action
    ⟨.send "m" "m" "V", [], [], []⟩ "unused" with
  | .error reason => reason.startsWith "constructed-view-unsupported-shape:"
  | .ok _ => false
#guard match ZkcTools.StructuredSource.Constructed.action
    ⟨.unsupported "private-coins", [], [], []⟩ "unused" with
  | .error reason => reason.startsWith "constructed-view-unsupported-shape:"
  | .ok _ => false
#guard match ZkcTools.StructuredSource.Constructed.block 0 [] "body" "artifact.instructions" with
  | .error reason => reason == "constructed-view-depth: path=artifact.instructions"
  | .ok _ => false

#print axioms ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.participant_eq
#print axioms ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.participant_eq
#print axioms ZkcExamples.Structured.Generated.Constructed.TwoSumsProducer.participant_eq
#print axioms ZkcExamples.Structured.Generated.Constructed.TwoSumsValidator.participant_eq
#print axioms Zkc.Construction.Domain.Binding.executePair_eq
#print axioms Zkc.Construction.Domain.Binding.callHelper_of_invoke_return
end Tests.Constructed
