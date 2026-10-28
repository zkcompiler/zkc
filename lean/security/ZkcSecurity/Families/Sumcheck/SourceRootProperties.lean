module

public import ZkcSecurity.Families.Sumcheck.SourceTerminal

@[expose] public section

/-! Property consumers for actual source roots. The shared symbolic reduction
supplies shape, honest return and No; the nominal terminal helper supplies the
Boolean comparison. The two-table caller composes the same component twice. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Families.Sumcheck.SourceRootProperties
open Zkc.Source Zkc.Source.Structured ReferenceLibrary Zkc.Transcript Zkc.Obligations
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent SourceIteration
open SumcheckSourceSelections hiding field

variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {Frame E P : Type} {Raw : E → Type}

def context (site : String) : ProtocolContext := ProtocolContext.enter {} site [0,1]

theorem context_distinct (site : String) : NormalForm.RosterDistinct (context site) 1 2 :=
  .ofSeparate (by change (0 : Nat) ≠ 1; decide) (by decide)

variable (selection : Selection) (site : String)
  (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
  (callerFrame : Frame) (shape : original.length = 2^count)
  (bounded : count ≤ maximum selection) (small : count < 64) (finite : original.length < indexLimit)

include callerFrame shape bounded small finite

/-- Shape preservation is independent of the truth of this scalar claim. -/
theorem one_present :
    PIR.Yields (fun out => ∃ accepted : Bool, out = some accepted)
      (SourceRootReference.one model selection {} site (some original) (some scalar) (some count) (some handle)) := by
  rw [one_reduction model selection site original count handle scalar callerFrame shape]
  exact (reduction_frame model _ (source selection).payload.linked (roundBodies selection)
    (Occurrence.table model (source selection).payload) (context site) (context_distinct site) handle
    (SumcheckReductionReference.actual_bodies model selection) (maximum selection) count bounded
    (PrefixState.initial original count scalar callerFrame shape)).bind (by
      intro out valid
      obtain ⟨next,same,_,returned⟩ := valid
      change next.original = original at same
      rw [returned]
      have nextShape : next.original.length = 2^count := (congrArg List.length same).trans shape
      have nextFinite : next.original.length < indexLimit := by simpa only [same] using finite
      change PIR.Yields _ (terminalCheck model selection original _)
      have checked := terminal_check model selection next count nextShape small nextFinite
      rw [same] at checked
      rw [checked]
      exact ⟨_,rfl⟩)

/-- At every reached history a false represented claim returns false, stops,
or escapes only through the supplied reached-history collision law. -/
def one_no (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (escape : EscapeJudgment E Raw)
    (steps : RepeatedComponent.NoContract
      (component model (source selection).payload.definitions (Occurrence.table model (source selection).payload)
        (context site) handle) absorb escape (no model original callerFrame))
    (wrong : scalar ≠ original.sum) (history : List E) :
    Derivation absorb escape (fun _ out => out = some false) history
      (SourceRootReference.one model selection {} site (some original) (some scalar) (some count) (some handle)) := by
  rw [one_reduction model selection site original count handle scalar callerFrame shape]
  exact (reduction_no model _ (source selection).payload.linked (roundBodies selection)
    (Occurrence.table model (source selection).payload) (context site) (context_distinct site) handle
    (SumcheckReductionReference.actual_bodies model selection) absorb escape original callerFrame steps
    (maximum selection) count bounded (PrefixState.initial original count scalar callerFrame shape)
    rfl rfl (initial_no model original count scalar callerFrame shape wrong) history).bind _ (by
      intro reached out valid
      let next := Classical.choose valid
      have result : next.original = original ∧ next.frame = callerFrame ∧
          out = (SumcheckVerifierBodies.reduceReturnValues (encode model 0 next).slots, callerFrame) ∧
          (layout model).representation.No next := Classical.choose_spec valid
      have same : next.original = original := result.1
      have returned := result.2.2.1
      have wrongNext := result.2.2.2
      rw [returned]
      have nextShape : next.original.length = 2^count := (congrArg List.length same).trans shape
      have nextFinite : next.original.length < indexLimit := by simpa only [same] using finite
      change Derivation _ _ _ _ (terminalCheck model selection original _)
      have checked := terminal_check model selection next count nextShape small nextFinite
      rw [same] at checked
      rw [checked]
      apply Derivation.done
      have unequal := ((layout model).no_iff next).mp wrongNext
      change next.scalar ≠ next.entries.sum at unequal
      simp [unequal])

/-- This is successful completeness: the exception postcondition is False.
The handler state and complete accumulated history remain the WP arguments. -/
theorem one_honest {H : Type}
    (handler : PIR.Handler (Occurrence.signature model.toCarriers) H E)
    (good : List E → Runtime model Frame → H → Prop)
    (steps : RepeatedComponent.HonestContract
      (component model (source selection).payload.definitions (Occurrence.table model (source selection).payload)
        (context site) handle) handler (honest model good original callerFrame))
    (history : List E) (h : H)
    (initial : honest model good original callerFrame history count
      (encode model 0 (PrefixState.initial original count scalar callerFrame shape)) h) :
    PIR.WeakestPrecondition.satisfies
      ((SourceRootReference.one model selection {} site (some original) (some scalar)
        (some count) (some handle)).run handler h)
      (fun out _ _ => out = some true) (fun _ _ _ => False) history := by
  rw [one_reduction model selection site original count handle scalar callerFrame shape]
  have successful := reduction_honest model _ (source selection).payload.linked (roundBodies selection)
    (Occurrence.table model (source selection).payload) (context site) (context_distinct site) handle
    (SumcheckReductionReference.actual_bodies model selection) original callerFrame handler good steps
    (maximum selection) count bounded (PrefixState.initial original count scalar callerFrame shape) history h initial
  apply PIR.WeakestPrecondition.successful_bind _ _ _ _ _ _ _ successful
  intro out final reached valid
  obtain ⟨next,same,_,returned,yes⟩ := valid
  rw [returned]
  have nextShape : next.original.length = 2^count := (congrArg List.length same).trans shape
  have nextFinite : next.original.length < indexLimit := by simpa only [same] using finite
  change PIR.WeakestPrecondition.satisfies (PIR.Process.run _ (terminalCheck model selection original _) _)
    _ _ reached
  have checked := terminal_check model selection next count nextShape small nextFinite
  rw [same] at checked
  rw [checked]
  have equal := ((layout model).yes_iff next).mp yes
  change next.scalar = next.entries.sum at equal
  change some (decide (next.scalar = next.entries.sum)) = some true
  simp [equal]


/-- A sequential caller supplies an ordinary synchronization invariant for its
next component. Successful source execution preserves it with the reached history. -/
theorem one_honest_preserving {H : Type}
    (handler : PIR.Handler (Occurrence.signature model.toCarriers) H E)
    (good : List E → Runtime model Frame → H → Prop)
    (steps : RepeatedComponent.HonestContract
      (component model (source selection).payload.definitions (Occurrence.table model (source selection).payload)
        (context site) handle) handler (honest model good original callerFrame))
    (history : List E) (h : H)
    (initial : honest model good original callerFrame history count
      (encode model 0 (PrefixState.initial original count scalar callerFrame shape)) h)
    (after : H → List E → Prop)
    (finish : ∀ reached runtime final, honest model good original callerFrame reached 0 runtime final → after final reached) :
    PIR.WeakestPrecondition.satisfies
      ((SourceRootReference.one model selection {} site (some original) (some scalar)
        (some count) (some handle)).run handler h)
      (fun out final reached => out = some true ∧ after final reached) (fun _ _ _ => False) history := by
  rw [one_reduction model selection site original count handle scalar callerFrame shape]
  let post := fun (out : Values (Component model.Value) SumcheckVerifierBodies.reduceOutputs × Frame)
    (final : H) (reached : List E) => reductionYes model original callerFrame out ∧ after final reached
  have successful := reduction_honest_preserving model _ (source selection).payload.linked (roundBodies selection)
    (Occurrence.table model (source selection).payload) (context site) (context_distinct site) handle
    (SumcheckReductionReference.actual_bodies model selection) original callerFrame handler good steps
    (maximum selection) count bounded (PrefixState.initial original count scalar callerFrame shape) history h initial
    post (by
      intro reached runtime final valid
      have afterNow := finish reached runtime final valid
      obtain ⟨next,same,retained,encoded,yes,_⟩ := valid
      refine ⟨⟨next,same,retained,?_,yes⟩,afterNow⟩
      rw [encoded]
      rfl)
  apply PIR.WeakestPrecondition.successful_bind _ _ _ _ _ _ _ successful
  intro out final reached valid
  obtain ⟨⟨next,same,_,returned,yes⟩,afterNow⟩ := valid
  rw [returned]
  have nextShape : next.original.length = 2^count := (congrArg List.length same).trans shape
  have nextFinite : next.original.length < indexLimit := by simpa only [same] using finite
  have checked := terminal_check model selection next count nextShape small nextFinite
  rw [same] at checked
  change PIR.WeakestPrecondition.satisfies (PIR.Process.run _ (terminalCheck model selection original _) _) _ _ reached
  rw [checked]
  have equal : next.scalar = next.entries.sum := ((layout model).yes_iff next).mp yes
  change some (decide (next.scalar = next.entries.sum)) = some true ∧ after final (reached ++ [])
  constructor
  · simp only [equal, decide_true]
  · simpa only [List.append_nil] using afterNow

end ZkcSecurity.Families.Sumcheck.SourceRootProperties
