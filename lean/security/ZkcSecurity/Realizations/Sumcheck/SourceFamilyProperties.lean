module

public import ZkcSecurity.Realizations.Sumcheck.SourceFamily
public import ZkcSecurity.Realizations.Sumcheck.SourceReduction
public import ZkcSecurity.Families.Sumcheck.SourceAdmission
public import ZkcSecurity.Obligations.SourcePure

@[expose] public section

/-! Source component mathematics for any checked family installation. The same
Pair, No and cost contracts range over arbitrary admitted round bounds below
64. No root layout or source enumeration occurs in these laws. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourceFamily
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured ReferenceLibrary Zkc.Transcript Zkc.Obligations
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent SourceIteration
open Zkc.Polynomial.Multilinear ZkcSecurity.FiatShamir
variable {program : Zkc.Source.Structured.Program}
variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {Frame E P : Type} {Raw : E → Type}

theorem initial_no (original : List (model.Field field)) (count : Nat) (scalar : model.Field field)
    (callerFrame : Frame) (shape : original.length = 2^count) (wrong : scalar ≠ original.sum) :
    (layout model).representation.No (PrefixState.initial original count scalar callerFrame shape) :=
  ((layout model).no_iff _).mpr wrong

theorem initial_yes (original : List (model.Field field)) (count : Nat) (scalar : model.Field field)
    (callerFrame : Frame) (shape : original.length = 2^count) (right : scalar = original.sum) :
    (layout model).representation.Yes (PrefixState.initial original count scalar callerFrame shape) :=
  ((layout model).yes_iff _).mpr right

theorem terminal_point_length (reference : PrefixState (model.Field field) Frame 0)
    (count : Nat) (shape : reference.original.length = 2^count) : reference.point.length = count := by
  apply Nat.pow_right_injective (a := 2) (by decide)
  exact (by simpa using reference.shape.symm : 2^reference.point.length = reference.original.length).trans shape

theorem terminal_shape (reference : PrefixState (model.Field field) Frame 0)
    (count : Nat) (shape : reference.original.length = 2^count) (small : count < 64) :
    Multilinear.Admission.HasShape reference.original reference.point.length 1 := by
  apply Multilinear.Admission.hasShape_of_length _ _ _ (by decide)
  · rw [terminal_point_length model reference count shape]
    exact small
  · simpa using reference.shape

def terminalCheck (_installation : Installation program) (original : List (model.Field field))
    (returned : Values (Component model.Value) SumcheckVerifierBodies.reduceOutputs) :=
  (Participant.owned 1 1
    (invoke (tables model program.payload.definitions).closed
      SumcheckHelperBodies.checkHelper)
    (.cons (some original) (.cons (returned.get (.there (.there (.there (.there .here)))))
      (.cons (returned.get (.there (.there (.there (.there (.there .here)))))) .nil)))).bind fun checked =>
    PIR.Process.done (checked.get .here)

theorem terminal_check (installation : Installation program) (reference : PrefixState (model.Field field) Frame 0)
    (count : Nat) (shape : reference.original.length = 2^count) (small : count < 64)
    (finite : reference.original.length < indexLimit) :
    terminalCheck model installation reference.original
      (SumcheckVerifierBodies.reduceReturnValues (encode model 0 reference).slots) =
      .done (some (decide (reference.scalar = reference.entries.sum))) := by
  have pointBound : reference.point.length < indexLimit := by
    rw [terminal_point_length model reference count shape]
    exact lt_trans small (by decide +kernel)
  have checker := Multilinear.Admission.check_eq model program.payload.linked
    installation.admissionBodies reference.original reference.point reference.scalar finite pointBound
  unfold terminalCheck
  change ((invoke (tables model program.payload.definitions).closed
    SumcheckHelperBodies.checkHelper
    (Multilinear.Admission.checkInputs model field reference.original reference.point reference.scalar)).bind _).bind _ = _
  rw [Evaluation.closed_invoke_componentTablesOn, checker]
  have valid := terminal_shape model reference count shape small
  simp only [valid, true_and, PIR.Process.interpret, PIR.Process.bind]
  apply congrArg PIR.Process.done
  change some (decide (reference.entries.sum = reference.scalar)) =
    some (decide (reference.scalar = reference.entries.sum))
  simp only [eq_comm]

/-- The reduction invariant may use an independent mathematical table. The
terminal checker still consumes the actual original source input, which may
have invalid shape or exceed the nominal index range. -/
theorem one_reduction_with_original (installation : Installation program) (site : String)
    (original referenceOriginal : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (callerFrame : Frame) (shape : referenceOriginal.length = 2^count) :
    one installation model {} site (some original) (some scalar) (some count) (some handle) =
      (reduction model program.payload.definitions
        (Occurrence.table model program.payload) (ProtocolContext.enter {} site [0,1]) handle
        installation.maximum count (PrefixState.initial referenceOriginal count scalar callerFrame shape)).bind
        (fun returned => terminalCheck model installation original returned.1) := by
  have distinct : NormalForm.RosterDistinct (ProtocolContext.enter {} site [0,1]) 1 2 := by
    exact .ofSeparate (by change (0 : Nat) ≠ 1; decide) (by decide)
  unfold reduction
  rw [SumcheckReductionReference.body_reference model _ program.payload.linked
    (installation.validatorBodies model) _ _ _ distinct]
  unfold one
  have initial := (Sum.initial model field "s0").invokeOn (model := model)
    (I := Occurrence.signature model.toCarriers)
    (helper := initialHelper)
    _ program.payload.linked (installation.initial model) (.cons scalar .nil) trivial
  change invoke (tables model program.payload.definitions).closed
    initialHelper (.cons scalar .nil) =
    PIR.Process.done (.cons [] (.cons scalar .nil)) at initial
  change ((invoke (tables model program.payload.definitions).closed
    initialHelper (.cons scalar .nil)).bind _).bind _ = _
  rw [initial]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  rfl


/-- One source use equals the actual complete reduction followed by its actual
checker. The arbitrary caller frame remains available until the source result. -/
theorem one_reduction (installation : Installation program) (site : String)
    (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (callerFrame : Frame) (shape : original.length = 2^count) :
    one installation model {} site (some original) (some scalar) (some count) (some handle) =
      (reduction model program.payload.definitions
        (Occurrence.table model program.payload) (ProtocolContext.enter {} site [0,1]) handle
        installation.maximum count (PrefixState.initial original count scalar callerFrame shape)).bind
        (fun returned => terminalCheck model installation original returned.1) :=
  one_reduction_with_original model installation site original original count handle scalar callerFrame shape

def context (site : String) : ProtocolContext := ProtocolContext.enter {} site [0,1]

theorem context_distinct (site : String) : NormalForm.RosterDistinct (context site) 1 2 :=
  .ofSeparate (by change (0 : Nat) ≠ 1; decide) (by decide)

section Bounded
variable (installation : Installation program) (site : String)
  (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
  (callerFrame : Frame) (shape : original.length = 2^count)
  (bounded : count ≤ installation.maximum) (small : count < 64) (finite : original.length < indexLimit)

include callerFrame shape bounded small finite

/-- Shape preservation is independent of the truth of this scalar claim. -/
theorem one_present_bounded :
    PIR.Yields (fun out => ∃ accepted : Bool, out = some accepted)
      (one installation model {} site (some original) (some scalar) (some count) (some handle)) := by
  rw [one_reduction model installation site original count handle scalar callerFrame shape]
  exact (reduction_frame model _ program.payload.linked installation.roundBodies
    (Occurrence.table model program.payload) (context site) (context_distinct site) handle
    (installation.validatorBodies model) installation.maximum count bounded
    (PrefixState.initial original count scalar callerFrame shape)).bind (by
      intro out valid
      obtain ⟨next,same,_,returned⟩ := valid
      change next.original = original at same
      rw [returned]
      have nextShape : next.original.length = 2^count := (congrArg List.length same).trans shape
      have nextFinite : next.original.length < indexLimit := by simpa only [same] using finite
      change PIR.Yields _ (terminalCheck model installation original _)
      have checked := terminal_check model installation next count nextShape small nextFinite
      rw [same] at checked
      rw [checked]
      exact ⟨_,rfl⟩)

/-- At every reached history a false represented claim returns false, stops,
or escapes only through the supplied reached-history collision law. -/
def one_no_bounded (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (escape : EscapeJudgment E Raw)
    (steps : RepeatedComponent.NoContract
      (component model program.payload.definitions (Occurrence.table model program.payload)
        (context site) handle) absorb escape (no model original callerFrame))
    (wrong : scalar ≠ original.sum) (history : List E) :
    Derivation absorb escape (fun _ out => out = some false) history
      (one installation model {} site (some original) (some scalar) (some count) (some handle)) := by
  rw [one_reduction model installation site original count handle scalar callerFrame shape]
  exact (reduction_no model _ program.payload.linked installation.roundBodies
    (Occurrence.table model program.payload) (context site) (context_distinct site) handle
    (installation.validatorBodies model) absorb escape original callerFrame steps
    installation.maximum count bounded (PrefixState.initial original count scalar callerFrame shape)
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
      change Derivation _ _ _ _ (terminalCheck model installation original _)
      have checked := terminal_check model installation next count nextShape small nextFinite
      rw [same] at checked
      rw [checked]
      apply Derivation.done
      have unequal := ((layout model).no_iff next).mp wrongNext
      change next.scalar ≠ next.entries.sum at unequal
      simp [unequal])

/-- Conditional successful validator execution: the exception postcondition is
False. This does not construct honest-pair readback. The handler state and
complete accumulated history remain the WP arguments. -/
theorem one_honest {H : Type}
    (handler : PIR.Handler (Occurrence.signature model.toCarriers) H E)
    (good : List E → Runtime model Frame → H → Prop)
    (steps : RepeatedComponent.HonestContract
      (component model program.payload.definitions (Occurrence.table model program.payload)
        (context site) handle) handler (honest model good original callerFrame))
    (history : List E) (h : H)
    (initial : honest model good original callerFrame history count
      (encode model 0 (PrefixState.initial original count scalar callerFrame shape)) h) :
    PIR.WeakestPrecondition.satisfies
      ((one installation model {} site (some original) (some scalar)
        (some count) (some handle)).run handler h)
      (fun out _ _ => out = some true) (fun _ _ _ => False) history := by
  rw [one_reduction model installation site original count handle scalar callerFrame shape]
  have successful := reduction_honest model _ program.payload.linked installation.roundBodies
    (Occurrence.table model program.payload) (context site) (context_distinct site) handle
    (installation.validatorBodies model) original callerFrame handler good steps
    installation.maximum count bounded (PrefixState.initial original count scalar callerFrame shape) history h initial
  apply PIR.WeakestPrecondition.successful_bind _ _ _ _ _ _ _ successful
  intro out final reached valid
  obtain ⟨next,same,_,returned,yes⟩ := valid
  rw [returned]
  have nextShape : next.original.length = 2^count := (congrArg List.length same).trans shape
  have nextFinite : next.original.length < indexLimit := by simpa only [same] using finite
  change PIR.WeakestPrecondition.satisfies (PIR.Process.run _ (terminalCheck model installation original _) _)
    _ _ reached
  have checked := terminal_check model installation next count nextShape small nextFinite
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
      (component model program.payload.definitions (Occurrence.table model program.payload)
        (context site) handle) handler (honest model good original callerFrame))
    (history : List E) (h : H)
    (initial : honest model good original callerFrame history count
      (encode model 0 (PrefixState.initial original count scalar callerFrame shape)) h)
    (after : H → List E → Prop)
    (finish : ∀ reached runtime final, honest model good original callerFrame reached 0 runtime final → after final reached) :
    PIR.WeakestPrecondition.satisfies
      ((one installation model {} site (some original) (some scalar)
        (some count) (some handle)).run handler h)
      (fun out final reached => out = some true ∧ after final reached) (fun _ _ _ => False) history := by
  rw [one_reduction model installation site original count handle scalar callerFrame shape]
  let post := fun (out : Values (Component model.Value) SumcheckVerifierBodies.reduceOutputs × Frame)
    (final : H) (reached : List E) => reductionYes model original callerFrame out ∧ after final reached
  have successful := reduction_honest_preserving model _ program.payload.linked installation.roundBodies
    (Occurrence.table model program.payload) (context site) (context_distinct site) handle
    (installation.validatorBodies model) original callerFrame handler good steps
    installation.maximum count bounded (PrefixState.initial original count scalar callerFrame shape) history h initial
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
  have checked := terminal_check model installation next count nextShape small nextFinite
  rw [same] at checked
  change PIR.WeakestPrecondition.satisfies (PIR.Process.run _ (terminalCheck model installation original _) _) _ _ reached
  rw [checked]
  have equal : next.scalar = next.entries.sum := ((layout model).yes_iff next).mp yes
  change some (decide (next.scalar = next.entries.sum)) = some true ∧ after final (reached ++ [])
  constructor
  · simp only [equal, decide_true]
  · simpa only [List.append_nil] using afterNow

end Bounded

variable (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
  (charge : List E → E → ENNReal)
omit fieldLaw in
theorem terminal_cost (installation : Installation program) (original : List (model.Field field))
    (out : Values (Component model.Value) SumcheckVerifierBodies.reduceOutputs) (history : List E) :
    Typed.ChargedCostBound absorb charge (terminalCheck model installation original out) history 0 := by
  apply (CostComposition.map_iff _ _ _).mpr
  exact ZkcSecurity.Obligations.SourcePure.owned_cost absorb charge model _ _ 1 1 _ history

theorem one_cost_bounded (installation : Installation program) (site : String)
    (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (callerFrame : Frame) (shape : original.length = 2^count) (bounded : count ≤ installation.maximum)
    (cuts : SourceRound.Cuts model absorb (context site) handle)
    (boundaries : Boundaries model absorb (context site)) (error : ENNReal)
    (price : ∀ reached, charge reached cuts.query ≤ error) (history : List E) :
    Typed.ChargedCostBound absorb charge
      (one installation model {} site (some original) (some scalar) (some count) (some handle))
      history (count • error) := by
  rw [one_reduction model installation site original count handle scalar callerFrame shape]
  have head := reduction_cost model _ program.payload.linked installation.roundBodies
    (Occurrence.table model program.payload) (context site) (context_distinct site) handle
    (installation.validatorBodies model) absorb charge cuts boundaries error price
    installation.maximum count bounded (PrefixState.initial original count scalar callerFrame shape) history
  simpa only [add_zero, context] using CostComposition.bind _ _ (count • error) 0 head
    (fun out reached => terminal_cost model absorb charge installation original out.1 reached)

def controlTable (count : Nat) : List (model.Field field) := List.replicate (2^count) 0

theorem control_shape (count : Nat) : (controlTable model count).length = 2^count := List.length_replicate



theorem terminal_equation (installation : Installation program) (original : List (model.Field field))
    (reference : PrefixState (model.Field field) Frame 0) (small : reference.point.length < 64) :
    terminalCheck model installation original
      (SumcheckVerifierBodies.reduceReturnValues (encode model 0 reference).slots) =
      if original.length < indexLimit then .done (some (decide
        (Multilinear.Admission.HasShape original reference.point.length 1 ∧
          (Zkc.Polynomial.Multilinear.restrictPrefixValues original reference.point).sum = reference.scalar)))
      else .halt .exhausted := by
  unfold terminalCheck
  change (((invoke (tables model program.payload.definitions).closed
    SumcheckHelperBodies.checkHelper
    (Multilinear.Admission.checkInputs model field original reference.point reference.scalar)).bind _).bind _) = _
  rw [Evaluation.closed_invoke_componentTablesOn]
  by_cases finite : original.length < indexLimit
  · rw [Multilinear.Admission.check_eq model program.payload.linked
      installation.admissionBodies original reference.point reference.scalar finite (lt_trans small (by decide +kernel))]
    simp only [finite, ↓reduceIte, PIR.Process.interpret, PIR.Process.bind]
    rfl
  · rw [SourceAdmission.check_overflow model field _ program.payload.linked
      installation.admissionBodies original reference.point reference.scalar finite small]
    simp only [finite, ↓reduceIte, PIR.Process.interpret, PIR.Process.bind]

theorem terminal_invalid (installation : Installation program) (original : List (model.Field field))
    (reference : PrefixState (model.Field field) Frame 0) (count : Nat)
    (referenceShape : reference.original.length = 2^count) (small : count < 64)
    (invalid : original.length ≠ 2^count) :
    PIR.Yields (fun out => out = some false) (terminalCheck model installation original
      (SumcheckVerifierBodies.reduceReturnValues (encode model 0 reference).slots)) := by
  have length := terminal_point_length model reference count referenceShape
  have pointSmall : reference.point.length < 64 := by simpa only [length] using small
  rw [terminal_equation model installation original reference pointSmall]
  split
  · have malformed : ¬ Multilinear.Admission.HasShape original reference.point.length 1 := by
      intro valid
      apply invalid
      simpa only [length, Nat.mul_one] using valid.length
    simp only [malformed, false_and, decide_false]
    rfl
  · trivial

theorem one_unbounded (installation : Installation program) (site : String)
    (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (unbounded : ¬ count ≤ installation.maximum) :
    one installation model {} site (some original) (some scalar) (some count) (some handle) =
      .halt .refused := by
  rw [one_reduction_with_original model installation site original (controlTable model count) count handle scalar ()
    (control_shape model count)]
  unfold SourceIteration.reduction
  dsimp only [PrefixState.initial]
  rw [SumcheckReductionReference.body_reference model _ program.payload.linked
    (installation.validatorBodies model)
    (Occurrence.table model program.payload) installation.maximum
    (ProtocolContext.enter {} site [0,1]) (context_distinct site)
    (some []) (some scalar) (some count) (some handle)]
  simp [SumcheckReductionReference.reference, denoteRepeatOn, unbounded, PIR.Process.bind]

theorem one_invalid_shape (installation : Installation program) (site : String)
    (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (bounded : count ≤ installation.maximum) (invalid : original.length ≠ 2^count) :
    PIR.Yields (fun out => out = some false)
      (one installation model {} site (some original) (some scalar) (some count) (some handle)) := by
  rw [one_reduction_with_original model installation site original (controlTable model count) count handle scalar ()
    (control_shape model count)]
  exact (reduction_frame model _ program.payload.linked installation.roundBodies
    (Occurrence.table model program.payload) (context site) (context_distinct site) handle
    (installation.validatorBodies model) installation.maximum count bounded
    (PrefixState.initial (controlTable model count) count scalar () (control_shape model count))).bind (by
      intro out valid
      obtain ⟨next, same, _, returned⟩ := valid
      rw [returned]
      exact terminal_invalid model installation original next count
        (by rw [same]; exact control_shape model count)
        (lt_of_le_of_lt bounded (installation.maximum_small)) invalid)

/-- Every successful call returns a present Boolean, including false checks
on malformed raw data. Oversized counts and overflowing lengths may stop. -/
theorem one_present (installation : Installation program) (site : String)
    (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field) :
    PIR.Yields (fun out => ∃ accepted : Bool, out = some accepted)
      (one installation model {} site (some original) (some scalar) (some count) (some handle)) := by
  by_cases bounded : count ≤ installation.maximum
  · rw [one_reduction_with_original model installation site original (controlTable model count) count handle scalar ()
      (control_shape model count)]
    exact (reduction_frame model _ program.payload.linked installation.roundBodies
      (Occurrence.table model program.payload) (context site) (context_distinct site) handle
      (installation.validatorBodies model) installation.maximum count bounded
      (PrefixState.initial (controlTable model count) count scalar () (control_shape model count))).bind (by
        intro out valid
        obtain ⟨next, same, _, returned⟩ := valid
        rw [returned]
        have length := terminal_point_length model next count (by rw [same]; exact control_shape model count)
        have small : next.point.length < 64 := by rw [length]; exact lt_of_le_of_lt bounded (installation.maximum_small)
        rw [terminal_equation model installation original next small]
        split
        · exact ⟨_, rfl⟩
        · trivial)
  · rw [one_unbounded model installation site original count handle scalar bounded]
    trivial

/-- All false represented calls, including invalid source admission, reject or
stop outside the explicit collision escape set. No shape premise is discarded. -/
def one_no (installation : Installation program) (site : String)
    (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (escape : EscapeJudgment E Raw) (empty : ∀ reached event, escape reached event (fun _ => False))
    (steps : RepeatedComponent.NoContract
      (component model program.payload.definitions (Occurrence.table model program.payload)
        (context site) handle) absorb escape (no model original ()))
    (wrong : ¬ (count ≤ installation.maximum ∧ original.length = 2^count ∧ scalar = original.sum))
    (history : List E) :
    Derivation absorb escape (fun _ out => out = some false) history
      (one installation model {} site (some original) (some scalar) (some count) (some handle)) := by
  by_cases bounded : count ≤ installation.maximum
  · by_cases shape : original.length = 2^count
    · have small := lt_of_le_of_lt bounded (installation.maximum_small)
      have finite : original.length < indexLimit := by rw [shape]; exact Multilinear.Admission.power_bound count small
      exact (one_no_bounded model installation site original count handle scalar () shape bounded small finite
        absorb escape steps (fun right => wrong ⟨bounded, shape, right⟩) history)
    · exact Derivation.ofYields empty (one_invalid_shape model installation site original count handle scalar bounded shape) history
  · rw [one_unbounded model installation site original count handle scalar bounded]
    exact .halt .refused

/-- Query cost holds for every nominal raw table and every source count. -/
theorem one_cost (installation : Installation program) (site : String)
    (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (charge : List E → E → ENNReal) (cuts : SourceRound.Cuts model absorb (context site) handle)
    (boundaries : Boundaries model absorb (context site)) (error : ENNReal)
    (price : ∀ reached, charge reached cuts.query ≤ error) (history : List E) :
    Typed.ChargedCostBound absorb charge
      (one installation model {} site (some original) (some scalar) (some count) (some handle))
      history (installation.maximum • error) := by
  by_cases bounded : count ≤ installation.maximum
  · rw [one_reduction_with_original model installation site original (controlTable model count) count handle scalar ()
      (control_shape model count)]
    have head := reduction_cost model _ program.payload.linked installation.roundBodies
      (Occurrence.table model program.payload) (context site) (context_distinct site) handle
      (installation.validatorBodies model) absorb charge cuts boundaries error price
      installation.maximum count bounded
      (PrefixState.initial (controlTable model count) count scalar () (control_shape model count)) history
    have total := CostComposition.bind _ _ (count • error) 0 head
      (fun out reached => terminal_cost model absorb charge installation original out.1 reached)
    apply CostComposition.mono (by simpa only [add_zero, context] using total)
    exact nsmul_le_nsmul_left (by positivity) bounded
  · rw [one_unbounded model installation site original count handle scalar bounded]
    trivial

#print axioms one_no
#print axioms one_cost
end ZkcSecurity.Realizations.Sumcheck.SourceFamily
