module

public import ZkcExamples.Structured.Generated.Original.TwoSums
public import ZkcExamples.Structured.OriginalArtifacts.TwoSumsValidatorRoot
public import ZkcExamples.Structured.OriginalArtifacts.TwoSumsProducerRoot
public import ZkcSecurity.Realizations.Sumcheck.OriginalRoot

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Sources
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.FiatShamir ZkcSecurity.Families.Sumcheck TableComponent
open ZkcSecurity.Realizations.Sumcheck
open ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open ZkcSecurity.Realizations.Sumcheck.OriginalRoot
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev program := ZkcExamples.Structured.OriginalArtifacts.TwoSums.program
abbrev payload := program.payload
abbrev routing := ZkcExamples.Structured.OriginalArtifacts.TwoSums.routing
abbrev context := ZkcExamples.Structured.OriginalArtifacts.TwoSums.context
theorem terminal_bodies : OriginalSumcheckLibrary.TerminalBodies payload.definitions :=
  ZkcExamples.Structured.OriginalArtifacts.TwoSums.helper_bodies.terminal

theorem source_root_association : ZkcExamples.Structured.Generated.Original.TwoSums.root.signature = ZkcExamples.Structured.OriginalArtifacts.TwoSums.program.payload.entry.signature := by kernel_rfl

theorem nominal_order : [ZkcExamples.Structured.Generated.Original.TwoSums.callContext1, ZkcExamples.Structured.Generated.Original.TwoSums.callContext4] = [ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0.protocol, ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1.protocol] := by kernel_rfl

theorem check0_helper : ZkcExamples.Structured.Generated.Original.TwoSums.sourceHelper37.helper = SumcheckHelperBodies.checkHelper := by kernel_rfl

theorem check1_helper : ZkcExamples.Structured.Generated.Original.TwoSums.sourceHelper37.helper = SumcheckHelperBodies.checkHelper := by kernel_rfl

theorem pending0_raw (scalar : F) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step0 (OriginalSumcheckLibrary.helpers (F := F) (G := G) payload) (some scalar) =
      .done (.cons (some []) (.cons (some scalar) .nil)) := by
  change Participant.owned 1 1 (invoke (OriginalSumcheckLibrary.helpers payload).closed SumcheckPendingBodies.pendingHelper) (.cons (some scalar) .nil) = _
  exact SumcheckPendingLaws.pending_owned payload ZkcExamples.Structured.OriginalArtifacts.TwoSums.claim_bodies 1 scalar

theorem pending1_raw (scalar : F) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step3 (OriginalSumcheckLibrary.helpers (F := F) (G := G) payload) (some scalar) =
      .done (.cons (some []) (.cons (some scalar) .nil)) := by
  change Participant.owned 1 1 (invoke (OriginalSumcheckLibrary.helpers payload).closed SumcheckPendingBodies.pendingHelper) (.cons (some scalar) .nil) = _
  exact SumcheckPendingLaws.pending_owned payload ZkcExamples.Structured.OriginalArtifacts.TwoSums.claim_bodies 1 scalar

def schedule0 := schedule ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0 context
 theorem routes0 (handle : Nat) : OriginalSecurity.Routes (routing handle)
    ⟨ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0.protocol, handle⟩ schedule0 [] :=
  routes (routing handle) ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0 handle (ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0_routes handle)

theorem call0_raw (scalar : F) (count handle : Nat) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step1Realized (G := G) (some count) (some handle) (.cons (some []) (.cons (some scalar) .nil)) =
      if count ≤ 4 then
        (run (G := G) ⟨ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0.protocol, handle⟩ (List.range count) ⟨[], scalar⟩).bind
          (fun result => .done (output result))
      else .halt .refused := by
  change verifierCall payload 4 ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0.protocol ZkcExamples.Structured.Generated.Original.TwoSums.reduceDefinition.outputScopes [] scalar count handle = _
  rw [call_raw payload ZkcExamples.Structured.OriginalArtifacts.TwoSums.verifier_bodies ZkcExamples.Structured.OriginalArtifacts.TwoSums.claim_bodies 4 ⟨ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0.protocol, handle⟩ (by change 0 ≠ 1; decide)]
  split
  · apply congrArg (PIR.Process.bind _)
    funext result
    exact congrArg PIR.Process.done (by kernel_rfl)
  · rfl

theorem check0_raw (raw : List F) (state : State F) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step2 (OriginalSumcheckLibrary.helpers payload) (some raw) (output (G := G) state) =
      terminal raw state.point state.scalar := by
  change Participant.owned 1 1 (invoke (OriginalSumcheckLibrary.helpers payload).closed SumcheckHelperBodies.checkHelper)
    (.cons (some raw) (.cons (some state.point) (.cons (some state.scalar) .nil))) = _
  exact source_terminal payload terminal_bodies 1 raw state.point state.scalar

theorem checked0 (raw : List F) (scalar : F) (count handle : Nat) :
    (ZkcExamples.Structured.Generated.Original.TwoSums.step1Realized (G := G) (some count) (some handle) (.cons (some []) (.cons (some scalar) .nil))).bind
      (ZkcExamples.Structured.Generated.Original.TwoSums.step2 (OriginalSumcheckLibrary.helpers payload) (some raw)) =
      sourceRoot 4 ⟨ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0.protocol, handle⟩ raw scalar count := by
  rw [call0_raw]
  unfold sourceRoot
  split
  · simp only [PIR.Process.bind_assoc, PIR.Process.bind]
    apply congrArg (PIR.Process.bind _)
    funext state
    exact check0_raw raw state
  · rfl

def schedule1 := schedule ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1 context
 theorem routes1 (handle : Nat) : OriginalSecurity.Routes (routing handle)
    ⟨ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1.protocol, handle⟩ schedule1 [] :=
  routes (routing handle) ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1 handle (ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1_routes handle)

theorem call1_raw (scalar : F) (count handle : Nat) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step4Realized (G := G) (some count) (some handle) (.cons (some []) (.cons (some scalar) .nil)) =
      if count ≤ 4 then
        (run (G := G) ⟨ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1.protocol, handle⟩ (List.range count) ⟨[], scalar⟩).bind
          (fun result => .done (output result))
      else .halt .refused := by
  change verifierCall payload 4 ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1.protocol ZkcExamples.Structured.Generated.Original.TwoSums.reduceDefinition.outputScopes [] scalar count handle = _
  rw [call_raw payload ZkcExamples.Structured.OriginalArtifacts.TwoSums.verifier_bodies ZkcExamples.Structured.OriginalArtifacts.TwoSums.claim_bodies 4 ⟨ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1.protocol, handle⟩ (by change 0 ≠ 1; decide)]
  split
  · apply congrArg (PIR.Process.bind _)
    funext result
    exact congrArg PIR.Process.done (by kernel_rfl)
  · rfl

theorem check1_raw (raw : List F) (state : State F) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step5 (OriginalSumcheckLibrary.helpers payload) (some raw) (output (G := G) state) =
      terminal raw state.point state.scalar := by
  change Participant.owned 1 1 (invoke (OriginalSumcheckLibrary.helpers payload).closed SumcheckHelperBodies.checkHelper)
    (.cons (some raw) (.cons (some state.point) (.cons (some state.scalar) .nil))) = _
  exact source_terminal payload terminal_bodies 1 raw state.point state.scalar

theorem checked1 (raw : List F) (scalar : F) (count handle : Nat) :
    (ZkcExamples.Structured.Generated.Original.TwoSums.step4Realized (G := G) (some count) (some handle) (.cons (some []) (.cons (some scalar) .nil))).bind
      (ZkcExamples.Structured.Generated.Original.TwoSums.step5 (OriginalSumcheckLibrary.helpers payload) (some raw)) =
      sourceRoot 4 ⟨ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1.protocol, handle⟩ raw scalar count := by
  rw [call1_raw]
  unfold sourceRoot
  split
  · simp only [PIR.Process.bind_assoc, PIR.Process.bind]
    apply congrArg (PIR.Process.bind _)
    funext state
    exact check1_raw raw state
  · rfl

theorem call0_binding (scalar : F) (count handle : Nat) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step1Realized (G := G) (some count) (some handle) (.cons (some []) (.cons (some scalar) .nil)) =
      verifierCall payload 4 ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0.protocol ZkcExamples.Structured.Generated.Original.TwoSums.reduceDefinition.outputScopes [] scalar count handle := by rfl

theorem check0_honest (state : OriginalHonest.MathState F 0)
    (bounded : state.original.length < indexLimit) (pointBound : state.point.length < 64) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step2 (OriginalSumcheckLibrary.helpers payload) (some state.original)
      (maskValues (ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0.protocol.roles 1)
        (ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0.protocol.mapScopes ZkcExamples.Structured.Generated.Original.TwoSums.reduceDefinition.outputScopes)
        (SumcheckVerifierBodies.reduceReturnValues (OriginalHonest.verifierValues (G := G) state))) =
      .done (.cons (some (decide (state.entries.sum = state.scalar))) .nil) := by
  change Participant.owned 1 1 (invoke (OriginalSumcheckLibrary.helpers payload).closed SumcheckHelperBodies.checkHelper)
    (.cons (some state.original) (.cons (some state.point) (.cons (some state.scalar) .nil))) = _
  exact honest_check payload terminal_bodies state bounded pointBound

theorem call1_binding (scalar : F) (count handle : Nat) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step4Realized (G := G) (some count) (some handle) (.cons (some []) (.cons (some scalar) .nil)) =
      verifierCall payload 4 ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1.protocol ZkcExamples.Structured.Generated.Original.TwoSums.reduceDefinition.outputScopes [] scalar count handle := by rfl

theorem check1_honest (state : OriginalHonest.MathState F 0)
    (bounded : state.original.length < indexLimit) (pointBound : state.point.length < 64) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step5 (OriginalSumcheckLibrary.helpers payload) (some state.original)
      (maskValues (ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1.protocol.roles 1)
        (ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1.protocol.mapScopes ZkcExamples.Structured.Generated.Original.TwoSums.reduceDefinition.outputScopes)
        (SumcheckVerifierBodies.reduceReturnValues (OriginalHonest.verifierValues (G := G) state))) =
      .done (.cons (some (decide (state.entries.sum = state.scalar))) .nil) := by
  change Participant.owned 1 1 (invoke (OriginalSumcheckLibrary.helpers payload).closed SumcheckHelperBodies.checkHelper)
    (.cons (some state.original) (.cons (some state.point) (.cons (some state.scalar) .nil))) = _
  exact honest_check payload terminal_bodies state bounded pointBound

theorem combine_step6 (left right : Values (Component (assignment F G)) [.boolean]) :
    ZkcExamples.Structured.Generated.Original.TwoSums.step6 (OriginalSumcheckLibrary.helpers payload) left right = both left right := by
  cases left with
  | cons a left =>
    cases left
    cases right with
    | cons b right =>
      cases right
      change invoke (OriginalSumcheckLibrary.helpers payload).components ZkcExamples.Structured.Generated.Original.TwoSums.sourceHelper25.helper
        (.cons a (.cons b .nil)) = _
      exact ZkcExamples.Structured.OriginalArtifacts.TwoSumsValidatorRoot.mathHelper25 a b

def calls (input0 : List F) (input1 : List F) (input2 : F) (input3 : F) (input4 : Nat) (handle : Nat) : List (Call F) :=
  [⟨⟨input0, input2, input4⟩, ⟨ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0.protocol, handle⟩, schedule0⟩, ⟨⟨input1, input3, input4⟩, ⟨ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1.protocol, handle⟩, schedule1⟩]

def terminalTree : Conjunction := (.and (.leaf 0) (.leaf 1))

omit [Field F] [DecidableEq F] in
set_option linter.unusedSimpArgs false in
theorem terminal_coverage (input0 : List F) (input1 : List F) (input2 : F) (input3 : F) (input4 : Nat) (handle : Nat) :
    ∀ index < (calls input0 input1 input2 input3 input4 handle).length, index ∈ terminalTree.leaves := by
  simp only [calls, List.length_cons, List.length_nil, terminalTree, Conjunction.leaves, List.mem_append, List.mem_singleton]
  omega

set_option linter.unusedSimpArgs false in
theorem source_root (input0 : List F) (input1 : List F) (input2 : F) (input3 : F) (input4 : Nat) (handle : Nat) :
    Occurrence.participant (ringModel F G) program 1 (.cons (some input0) (.cons (some input1) (.cons (some input2) (.cons (some input3) (.cons (some input4) (.cons (some handle) .nil)))))) =
      sourceComposition (G := G) 4 (calls input0 input1 input2 input3 input4 handle) terminalTree := by
  rw [ZkcExamples.Structured.Generated.Original.TwoSums.participant_binding]
  unfold ZkcExamples.Structured.Generated.Original.TwoSums.realized sourceComposition calls
  simp only [sourceSequence]
  simp only [pending0_raw, pending1_raw, PIR.Process.bind]
  rw [← checked0 input0 input2 input4 handle]
  rw [← checked1 input1 input3 input4 handle]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind, combine_step6, id_eq, both, terminalTree, Conjunction.evaluate, Values.get, PIR.Process.bind_done, Option.bind_some, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.join, ZkcExamples.Structured.OriginalSumcheckCalls.singleton_eta]

def presented (input0 : List F) (input1 : List F) (input2 : F) (input3 : F) (input4 : Nat) (history : Domain.History (uniformCarriers F G)) :=
  composition (G := G) 4 (calls input0 input1 input2 input3 input4 0) terminalTree ⟨[], history⟩

theorem bridge (input0 : List F) (input1 : List F) (input2 : F) (input3 : F) (input4 : Nat) (handle : Nat) (history : Domain.History (uniformCarriers F G)) :
    DomainReduction.Bridge (NominalField.interface (G := G) "bls12-381.fr") closedPost history
      (Original.participant (ringModel F G) program (routing handle) 1 (.cons (some input0) (.cons (some input1) (.cons (some input2) (.cons (some input3) (.cons (some input4) (.cons (some handle) .nil)))))) ⟨[], history⟩)
      (presented input0 input1 input2 input3 input4 history) := by
  unfold Original.participant
  rw [source_root]
  exact composition_bridge (routing handle) 4 (calls input0 input1 input2 input3 input4 handle) terminalTree ⟨[], history⟩ (by
    intro call member
    simp only [calls, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact routes0 handle
    · exact routes1 handle
  )

end ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Sources
