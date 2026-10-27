module

public import ZkcExamples.Structured.Generated.Original.SmallSumcheck
public import ZkcExamples.Structured.OriginalArtifacts.SmallSumcheckValidatorRoot
public import ZkcExamples.Structured.OriginalArtifacts.SmallSumcheckProducerRoot
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

abbrev program := ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.program
abbrev payload := program.payload
abbrev routing := ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.routing
abbrev context := ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.context
theorem terminal_bodies : OriginalSumcheckLibrary.TerminalBodies payload.definitions :=
  ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.helper_bodies.terminal

theorem source_root_association : ZkcExamples.Structured.Generated.Original.SmallSumcheck.root.signature = ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.program.payload.entry.signature := by kernel_rfl

theorem nominal_order : [ZkcExamples.Structured.Generated.Original.SmallSumcheck.callContext1] = [ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.occurrence0.protocol] := by kernel_rfl

theorem check0_helper : ZkcExamples.Structured.Generated.Original.SmallSumcheck.sourceHelper33.helper = SumcheckHelperBodies.checkHelper := by kernel_rfl

theorem pending0_raw (scalar : F) :
    ZkcExamples.Structured.Generated.Original.SmallSumcheck.step0 (OriginalSumcheckLibrary.helpers (F := F) (G := G) payload) (some scalar) =
      .done (.cons (some []) (.cons (some scalar) .nil)) := by
  change Participant.owned 1 1 (invoke (OriginalSumcheckLibrary.helpers payload).closed SumcheckPendingBodies.pendingHelper) (.cons (some scalar) .nil) = _
  exact SumcheckPendingLaws.pending_owned payload ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.claim_bodies 1 scalar

def schedule0 := schedule ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.occurrence0 context
 theorem routes0 (handle : Nat) : OriginalSecurity.Routes (routing handle)
    ⟨ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.occurrence0.protocol, handle⟩ schedule0 [] :=
  routes (routing handle) ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.occurrence0 handle (ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.occurrence0_routes handle)

theorem call0_raw (scalar : F) (count handle : Nat) :
    ZkcExamples.Structured.Generated.Original.SmallSumcheck.step1Realized (G := G) (some count) (some handle) (.cons (some []) (.cons (some scalar) .nil)) =
      if count ≤ 2 then
        (run (G := G) ⟨ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.occurrence0.protocol, handle⟩ (List.range count) ⟨[], scalar⟩).bind
          (fun result => .done (output result))
      else .halt .refused := by
  change verifierCall payload 2 ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.occurrence0.protocol ZkcExamples.Structured.Generated.Original.SmallSumcheck.reduceDefinition.outputScopes [] scalar count handle = _
  rw [call_raw payload ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.verifier_bodies ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.claim_bodies 2 ⟨ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.occurrence0.protocol, handle⟩ (by change 0 ≠ 1; decide)]
  split
  · apply congrArg (PIR.Process.bind _)
    funext result
    exact congrArg PIR.Process.done (by kernel_rfl)
  · rfl

theorem check0_raw (raw : List F) (state : State F) :
    ZkcExamples.Structured.Generated.Original.SmallSumcheck.step2 (OriginalSumcheckLibrary.helpers payload) (some raw) (output (G := G) state) =
      terminal raw state.point state.scalar := by
  change Participant.owned 1 1 (invoke (OriginalSumcheckLibrary.helpers payload).closed SumcheckHelperBodies.checkHelper)
    (.cons (some raw) (.cons (some state.point) (.cons (some state.scalar) .nil))) = _
  exact source_terminal payload terminal_bodies 1 raw state.point state.scalar

theorem checked0 (raw : List F) (scalar : F) (count handle : Nat) :
    (ZkcExamples.Structured.Generated.Original.SmallSumcheck.step1Realized (G := G) (some count) (some handle) (.cons (some []) (.cons (some scalar) .nil))).bind
      (ZkcExamples.Structured.Generated.Original.SmallSumcheck.step2 (OriginalSumcheckLibrary.helpers payload) (some raw)) =
      sourceRoot 2 ⟨ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.occurrence0.protocol, handle⟩ raw scalar count := by
  rw [call0_raw]
  unfold sourceRoot
  split
  · simp only [PIR.Process.bind_assoc, PIR.Process.bind]
    apply congrArg (PIR.Process.bind _)
    funext state
    exact check0_raw raw state
  · rfl

theorem call0_binding (scalar : F) (count handle : Nat) :
    ZkcExamples.Structured.Generated.Original.SmallSumcheck.step1Realized (G := G) (some count) (some handle) (.cons (some []) (.cons (some scalar) .nil)) =
      verifierCall payload 2 ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.occurrence0.protocol ZkcExamples.Structured.Generated.Original.SmallSumcheck.reduceDefinition.outputScopes [] scalar count handle := by rfl

theorem check0_honest (state : OriginalHonest.MathState F 0)
    (bounded : state.original.length < indexLimit) (pointBound : state.point.length < 64) :
    ZkcExamples.Structured.Generated.Original.SmallSumcheck.step2 (OriginalSumcheckLibrary.helpers payload) (some state.original)
      (maskValues (ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.occurrence0.protocol.roles 1)
        (ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.occurrence0.protocol.mapScopes ZkcExamples.Structured.Generated.Original.SmallSumcheck.reduceDefinition.outputScopes)
        (SumcheckVerifierBodies.reduceReturnValues (OriginalHonest.verifierValues (G := G) state))) =
      .done (.cons (some (decide (state.entries.sum = state.scalar))) .nil) := by
  change Participant.owned 1 1 (invoke (OriginalSumcheckLibrary.helpers payload).closed SumcheckHelperBodies.checkHelper)
    (.cons (some state.original) (.cons (some state.point) (.cons (some state.scalar) .nil))) = _
  exact honest_check payload terminal_bodies state bounded pointBound

def calls (input0 : List F) (input1 : F) (input2 : Nat) (handle : Nat) : List (Call F) :=
  [⟨⟨input0, input1, input2⟩, ⟨ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.occurrence0.protocol, handle⟩, schedule0⟩]

def terminalTree : Conjunction := (.leaf 0)

omit [Field F] [DecidableEq F] in
set_option linter.unusedSimpArgs false in
theorem terminal_coverage (input0 : List F) (input1 : F) (input2 : Nat) (handle : Nat) :
    ∀ index < (calls input0 input1 input2 handle).length, index ∈ terminalTree.leaves := by
  simp only [calls, List.length_cons, List.length_nil, terminalTree, Conjunction.leaves, List.mem_append, List.mem_singleton]
  omega

set_option linter.unusedSimpArgs false in
theorem source_root (input0 : List F) (input1 : F) (input2 : Nat) (handle : Nat) :
    Occurrence.participant (ringModel F G) program 1 (.cons (some input0) (.cons (some input1) (.cons (some input2) (.cons (some handle) .nil)))) =
      sourceComposition (G := G) 2 (calls input0 input1 input2 handle) terminalTree := by
  rw [ZkcExamples.Structured.Generated.Original.SmallSumcheck.participant_binding]
  unfold ZkcExamples.Structured.Generated.Original.SmallSumcheck.realized sourceComposition calls
  simp only [sourceSequence]
  simp only [pending0_raw, PIR.Process.bind]
  rw [← checked0 input0 input1 input2 handle]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind, id_eq, both, terminalTree, Conjunction.evaluate, Values.get, PIR.Process.bind_done, Option.bind_some, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.join, ZkcExamples.Structured.OriginalSumcheckCalls.singleton_eta]

def presented (input0 : List F) (input1 : F) (input2 : Nat) (history : Domain.History (uniformCarriers F G)) :=
  composition (G := G) 2 (calls input0 input1 input2 0) terminalTree ⟨[], history⟩

theorem bridge (input0 : List F) (input1 : F) (input2 : Nat) (handle : Nat) (history : Domain.History (uniformCarriers F G)) :
    DomainReduction.Bridge (NominalField.interface (G := G) "bls12-381.fr") closedPost history
      (Original.participant (ringModel F G) program (routing handle) 1 (.cons (some input0) (.cons (some input1) (.cons (some input2) (.cons (some handle) .nil)))) ⟨[], history⟩)
      (presented input0 input1 input2 history) := by
  unfold Original.participant
  rw [source_root]
  exact composition_bridge (routing handle) 2 (calls input0 input1 input2 handle) terminalTree ⟨[], history⟩ (by
    intro call member
    simp only [calls, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    · exact routes0 handle
  )

end ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Sources
