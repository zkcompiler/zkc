module

public import ZkcExamples.Structured.Generated.Original.SmallSumcheck
public import ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckValidatorRoot
public import ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckProducerRoot
public import ZkcSecurity.Realizations.Sumcheck.OriginalRoot

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Sources
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.FiatShamir ZkcSecurity.Families.Sumcheck TableComponent
open ZkcSecurity.Realizations.Sumcheck
open ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open ZkcSecurity.Realizations.Sumcheck.OriginalRoot
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev program := ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.program
abbrev payload := program.payload
abbrev routing := ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.routing
abbrev context := ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.context
theorem terminal_bodies : OriginalSumcheckLibrary.TerminalBodies payload.definitions := by bind_structured_bodies

theorem source_root_association : ZkcExamples.Structured.Generated.Original.SmallSumcheck.root.signature = ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.program.payload.entry.signature := by kernel_rfl

theorem nominal_order : [ZkcExamples.Structured.Generated.Original.SmallSumcheck.callContext0] = [ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0.protocol] := by kernel_rfl

theorem check0_helper : ZkcExamples.Structured.Generated.Original.SmallSumcheck.sourceHelper27.helper = SumcheckHelperBodies.checkHelper := by kernel_rfl

def schedule0 := schedule ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0 context
 theorem routes0 (handle : Nat) : OriginalSecurity.Routes (routing handle)
    ⟨ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0.protocol, handle⟩ schedule0 [] :=
  routes (routing handle) ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0 handle (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0_routes handle)

theorem call0_raw (scalar : F) (count handle : Nat) :
    ZkcExamples.Structured.Generated.Original.SmallSumcheck.step0Realized (G := G) (some scalar) (some count) (some handle) =
      if count ≤ 2 then
        (run (G := G) ⟨ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0.protocol, handle⟩ (List.range count) ⟨[], scalar⟩).bind
          (fun result => .done (output result))
      else .halt .refused := by
  change verifierCall payload 2 ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0.protocol ZkcExamples.Structured.Generated.Original.SmallSumcheck.reduceDefinition.outputScopes scalar count handle = _
  rw [call_raw payload ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.verifier_bodies 2 ⟨ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0.protocol, handle⟩ (by change 0 ≠ 1; decide)]
  split
  · apply congrArg (PIR.Process.bind _)
    funext result
    exact congrArg PIR.Process.done (by kernel_rfl)
  · rfl

theorem check0_raw (raw : List F) (state : State F) :
    ZkcExamples.Structured.Generated.Original.SmallSumcheck.step1 (OriginalSumcheckLibrary.helpers payload) (some raw) (output (G := G) state) =
      terminal raw state.point state.scalar := by
  change Participant.owned 1 1 (invoke (OriginalSumcheckLibrary.helpers payload).closed SumcheckHelperBodies.checkHelper)
    (.cons (some raw) (.cons (some state.point) (.cons (some state.scalar) .nil))) = _
  exact source_terminal payload terminal_bodies 1 raw state.point state.scalar

theorem checked0 (raw : List F) (scalar : F) (count handle : Nat) :
    (ZkcExamples.Structured.Generated.Original.SmallSumcheck.step0Realized (G := G) (some scalar) (some count) (some handle)).bind
      (ZkcExamples.Structured.Generated.Original.SmallSumcheck.step1 (OriginalSumcheckLibrary.helpers payload) (some raw)) =
      sourceRoot 2 ⟨ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0.protocol, handle⟩ raw scalar count := by
  rw [call0_raw]
  unfold sourceRoot
  split
  · simp only [PIR.Process.bind_assoc, PIR.Process.bind]
    apply congrArg (PIR.Process.bind _)
    funext state
    exact check0_raw raw state
  · rfl

theorem call0_binding (scalar : F) (count handle : Nat) :
    ZkcExamples.Structured.Generated.Original.SmallSumcheck.step0Realized (G := G) (some scalar) (some count) (some handle) =
      verifierCall payload 2 ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0.protocol ZkcExamples.Structured.Generated.Original.SmallSumcheck.reduceDefinition.outputScopes scalar count handle := by rfl

theorem check0_honest (state : OriginalHonest.MathState F 0)
    (bounded : state.original.length < indexLimit) (pointBound : state.point.length < 64) :
    ZkcExamples.Structured.Generated.Original.SmallSumcheck.step1 (OriginalSumcheckLibrary.helpers payload) (some state.original)
      (maskValues (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0.protocol.roles 1)
        (ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0.protocol.mapScopes ZkcExamples.Structured.Generated.Original.SmallSumcheck.reduceDefinition.outputScopes)
        (SumcheckVerifierBodies.reduceReturnValues (OriginalHonest.verifierValues (G := G) state))) =
      .done (.cons (some (decide (state.entries.sum = state.scalar))) .nil) := by
  change Participant.owned 1 1 (invoke (OriginalSumcheckLibrary.helpers payload).closed SumcheckHelperBodies.checkHelper)
    (.cons (some state.original) (.cons (some state.point) (.cons (some state.scalar) .nil))) = _
  exact honest_check payload terminal_bodies state bounded pointBound

theorem source_root (input0 : List F) (input1 : F) (input2 : Nat) (handle : Nat) :
    Occurrence.participant (ringModel F G) program 1 (.cons (some input0) (.cons (some input1) (.cons (some input2) (.cons (some handle) .nil)))) =
      sourceRoot 2 ⟨ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0.protocol, handle⟩ input0 input1 input2 := by
  rw [ZkcExamples.Structured.Generated.Original.SmallSumcheck.participant_binding]
  exact checked0 input0 input1 input2 handle

def presented (input0 : List F) (input1 : F) (input2 : Nat) (history : Domain.History (uniformCarriers F G)) :=
  root 2 schedule0 input0 input1 input2 ⟨[], history⟩

theorem bridge (input0 : List F) (input1 : F) (input2 : Nat) (handle : Nat) (history : Domain.History (uniformCarriers F G)) :
    DomainReduction.Bridge (Nominal.interface (G := G) "bls12-381.fr") closedPost history
      (Original.participant (ringModel F G) program (routing handle) 1 (.cons (some input0) (.cons (some input1) (.cons (some input2) (.cons (some handle) .nil)))) ⟨[], history⟩)
      (presented input0 input1 input2 history) := by
  unfold Original.participant
  rw [source_root]
  exact root_bridge (routing handle) ⟨ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheck.occurrence0.protocol, handle⟩ schedule0 2 input0 input1 input2 ⟨[], history⟩ (routes0 handle)

end ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Sources
