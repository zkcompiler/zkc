module

public import ZkcExamples.Structured.Generated.Original.TwoSums
public import ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSumsValidatorRoot
public import ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSumsProducerRoot
public import ZkcSecurity.Realizations.Sumcheck.OriginalRoot

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Sources
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.FiatShamir ZkcSecurity.Families.Sumcheck TableComponent
open ZkcSecurity.Realizations.Sumcheck
open ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open ZkcSecurity.Realizations.Sumcheck.OriginalRoot
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev program := ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.program
abbrev payload := program.payload
abbrev routing := ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.routing
abbrev context := ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.context
theorem terminal_bodies : OriginalSumcheckLibrary.TerminalBodies payload.definitions := by bind_structured_bodies

theorem source_root_association : ZkcExamples.Structured.Generated.Original.TwoSums.root.signature = ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.program.payload.entry.signature := by kernel_rfl

theorem nominal_order : [ZkcExamples.Structured.Generated.Original.TwoSums.callContext0, ZkcExamples.Structured.Generated.Original.TwoSums.callContext2] = [ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence0.protocol, ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence1.protocol] := by kernel_rfl

theorem check0_helper : ZkcExamples.Structured.Generated.Original.TwoSums.sourceHelper30.helper = SumcheckHelperBodies.checkHelper := by kernel_rfl

theorem check1_helper : ZkcExamples.Structured.Generated.Original.TwoSums.sourceHelper30.helper = SumcheckHelperBodies.checkHelper := by kernel_rfl

def schedule0 := schedule ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence0 context
 theorem routes0 (handle : Nat) : OriginalSecurity.Routes (routing handle)
    ⟨ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence0.protocol, handle⟩ schedule0 [] :=
  routes (routing handle) ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence0 handle (ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence0_routes handle)

theorem call0_raw (scalar : F) (count handle : Nat) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step0Realized (G := G) (some scalar) (some count) (some handle) =
      if count ≤ 4 then
        (run (G := G) ⟨ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence0.protocol, handle⟩ (List.range count) ⟨[], scalar⟩).bind
          (fun result => .done (output result))
      else .halt .refused := by
  change verifierCall payload 4 ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence0.protocol ZkcExamples.Structured.Generated.Original.TwoSums.reduceDefinition.outputScopes scalar count handle = _
  rw [call_raw payload ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.verifier_bodies 4 ⟨ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence0.protocol, handle⟩ (by change 0 ≠ 1; decide)]
  split
  · apply congrArg (PIR.Process.bind _)
    funext result
    exact congrArg PIR.Process.done (by kernel_rfl)
  · rfl

theorem check0_raw (raw : List F) (state : State F) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step1 (OriginalSumcheckLibrary.helpers payload) (some raw) (output (G := G) state) =
      terminal raw state.point state.scalar := by
  change Participant.owned 1 1 (invoke (OriginalSumcheckLibrary.helpers payload).closed SumcheckHelperBodies.checkHelper)
    (.cons (some raw) (.cons (some state.point) (.cons (some state.scalar) .nil))) = _
  exact source_terminal payload terminal_bodies 1 raw state.point state.scalar

theorem checked0 (raw : List F) (scalar : F) (count handle : Nat) :
    (ZkcExamples.Structured.Generated.Original.TwoSums.step0Realized (G := G) (some scalar) (some count) (some handle)).bind
      (ZkcExamples.Structured.Generated.Original.TwoSums.step1 (OriginalSumcheckLibrary.helpers payload) (some raw)) =
      sourceRoot 4 ⟨ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence0.protocol, handle⟩ raw scalar count := by
  rw [call0_raw]
  unfold sourceRoot
  split
  · simp only [PIR.Process.bind_assoc, PIR.Process.bind]
    apply congrArg (PIR.Process.bind _)
    funext state
    exact check0_raw raw state
  · rfl

def schedule1 := schedule ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence1 context
 theorem routes1 (handle : Nat) : OriginalSecurity.Routes (routing handle)
    ⟨ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence1.protocol, handle⟩ schedule1 [] :=
  routes (routing handle) ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence1 handle (ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence1_routes handle)

theorem call1_raw (scalar : F) (count handle : Nat) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step2Realized (G := G) (some scalar) (some count) (some handle) =
      if count ≤ 4 then
        (run (G := G) ⟨ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence1.protocol, handle⟩ (List.range count) ⟨[], scalar⟩).bind
          (fun result => .done (output result))
      else .halt .refused := by
  change verifierCall payload 4 ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence1.protocol ZkcExamples.Structured.Generated.Original.TwoSums.reduceDefinition.outputScopes scalar count handle = _
  rw [call_raw payload ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.verifier_bodies 4 ⟨ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence1.protocol, handle⟩ (by change 0 ≠ 1; decide)]
  split
  · apply congrArg (PIR.Process.bind _)
    funext result
    exact congrArg PIR.Process.done (by kernel_rfl)
  · rfl

theorem check1_raw (raw : List F) (state : State F) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step3 (OriginalSumcheckLibrary.helpers payload) (some raw) (output (G := G) state) =
      terminal raw state.point state.scalar := by
  change Participant.owned 1 1 (invoke (OriginalSumcheckLibrary.helpers payload).closed SumcheckHelperBodies.checkHelper)
    (.cons (some raw) (.cons (some state.point) (.cons (some state.scalar) .nil))) = _
  exact source_terminal payload terminal_bodies 1 raw state.point state.scalar

theorem checked1 (raw : List F) (scalar : F) (count handle : Nat) :
    (ZkcExamples.Structured.Generated.Original.TwoSums.step2Realized (G := G) (some scalar) (some count) (some handle)).bind
      (ZkcExamples.Structured.Generated.Original.TwoSums.step3 (OriginalSumcheckLibrary.helpers payload) (some raw)) =
      sourceRoot 4 ⟨ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence1.protocol, handle⟩ raw scalar count := by
  rw [call1_raw]
  unfold sourceRoot
  split
  · simp only [PIR.Process.bind_assoc, PIR.Process.bind]
    apply congrArg (PIR.Process.bind _)
    funext state
    exact check1_raw raw state
  · rfl

theorem call0_binding (scalar : F) (count handle : Nat) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step0Realized (G := G) (some scalar) (some count) (some handle) =
      verifierCall payload 4 ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence0.protocol ZkcExamples.Structured.Generated.Original.TwoSums.reduceDefinition.outputScopes scalar count handle := by rfl

theorem check0_honest (state : OriginalHonest.MathState F 0)
    (bounded : state.original.length < indexLimit) (pointBound : state.point.length < 64) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step1 (OriginalSumcheckLibrary.helpers payload) (some state.original)
      (maskValues (ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence0.protocol.roles 1)
        (ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence0.protocol.mapScopes ZkcExamples.Structured.Generated.Original.TwoSums.reduceDefinition.outputScopes)
        (SumcheckVerifierBodies.reduceReturnValues (OriginalHonest.verifierValues (G := G) state))) =
      .done (.cons (some (decide (state.entries.sum = state.scalar))) .nil) := by
  change Participant.owned 1 1 (invoke (OriginalSumcheckLibrary.helpers payload).closed SumcheckHelperBodies.checkHelper)
    (.cons (some state.original) (.cons (some state.point) (.cons (some state.scalar) .nil))) = _
  exact honest_check payload terminal_bodies state bounded pointBound

theorem call1_binding (scalar : F) (count handle : Nat) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step2Realized (G := G) (some scalar) (some count) (some handle) =
      verifierCall payload 4 ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence1.protocol ZkcExamples.Structured.Generated.Original.TwoSums.reduceDefinition.outputScopes scalar count handle := by rfl

theorem check1_honest (state : OriginalHonest.MathState F 0)
    (bounded : state.original.length < indexLimit) (pointBound : state.point.length < 64) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step3 (OriginalSumcheckLibrary.helpers payload) (some state.original)
      (maskValues (ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence1.protocol.roles 1)
        (ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence1.protocol.mapScopes ZkcExamples.Structured.Generated.Original.TwoSums.reduceDefinition.outputScopes)
        (SumcheckVerifierBodies.reduceReturnValues (OriginalHonest.verifierValues (G := G) state))) =
      .done (.cons (some (decide (state.entries.sum = state.scalar))) .nil) := by
  change Participant.owned 1 1 (invoke (OriginalSumcheckLibrary.helpers payload).closed SumcheckHelperBodies.checkHelper)
    (.cons (some state.original) (.cons (some state.point) (.cons (some state.scalar) .nil))) = _
  exact honest_check payload terminal_bodies state bounded pointBound

theorem combine (left right : Values (Component (assignment F G)) [.boolean]) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step4 (OriginalSumcheckLibrary.helpers payload) left right = both left right := by
  cases left with
  | cons a left =>
    cases left
    cases right with
    | cons b right =>
      cases right
      change invoke (OriginalSumcheckLibrary.helpers payload).components ZkcExamples.Structured.Generated.Original.TwoSums.terminalHelper
        (.cons a (.cons b .nil)) = _
      exact ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSumsValidatorRoot.mathHelper31 a b

theorem source_root (input0 : List F) (input1 : List F) (input2 : F) (input3 : F) (input4 : Nat) (handle : Nat) :
    Occurrence.participant (ringModel F G) program 1 (.cons (some input0) (.cons (some input1) (.cons (some input2) (.cons (some input3) (.cons (some input4) (.cons (some handle) .nil)))))) =
      sourceTwoRoots 4 ⟨ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence0.protocol, handle⟩ ⟨ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence1.protocol, handle⟩ input0 input1 input2 input3 input4 := by
  rw [ZkcExamples.Structured.Generated.Original.TwoSums.participant_binding]
  unfold ZkcExamples.Structured.Generated.Original.TwoSums.realized sourceTwoRoots
  rw [← checked0 input0 input2 input4 handle, ← checked1 input1 input3 input4 handle]
  simp only [PIR.Process.bind_assoc, combine]

def presented (input0 : List F) (input1 : List F) (input2 : F) (input3 : F) (input4 : Nat) (history : Domain.History (uniformCarriers F G)) :=
  twoRoots 4 schedule0 schedule1 input0 input1 input2 input3 input4 ⟨[], history⟩

theorem bridge (input0 : List F) (input1 : List F) (input2 : F) (input3 : F) (input4 : Nat) (handle : Nat) (history : Domain.History (uniformCarriers F G)) :
    DomainReduction.Bridge (Nominal.interface (G := G) "bls12-381.fr") closedPost history
      (Original.participant (ringModel F G) program (routing handle) 1 (.cons (some input0) (.cons (some input1) (.cons (some input2) (.cons (some input3) (.cons (some input4) (.cons (some handle) .nil)))))) ⟨[], history⟩)
      (presented input0 input1 input2 input3 input4 history) := by
  unfold Original.participant
  rw [source_root]
  exact twoRoots_bridge (routing handle) ⟨ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence0.protocol, handle⟩ ⟨ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSums.occurrence1.protocol, handle⟩ schedule0 schedule1 4 input0 input1 input2 input3 input4 ⟨[], history⟩ (routes0 handle) (routes1 handle)

end ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Sources
