module

public import ZkcSecurity.Families.Sumcheck.SourceReduction
public import ZkcSecurity.Families.Sumcheck.SourceRootReference

@[expose] public section

/-! Terminal and initial mathematics for the same nominal source library.
Shape is independent of scalar truth. A terminal No produces a returned false;
a terminal Yes produces a returned true. Bounds remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Families.Sumcheck.SourceIteration
open Zkc.Source Zkc.Source.Structured ReferenceLibrary Zkc.Transcript Zkc.Obligations
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent
open SumcheckSourceSelections hiding field
open Zkc.Polynomial.Multilinear

variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {Frame : Type}

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

def terminalCheck (selection : Selection) (original : List (model.Field field))
    (returned : Values (Component model.Value) SumcheckVerifierBodies.reduceOutputs) :=
  (Participant.owned 1 1
    (invoke (tables model (source selection).payload.definitions).closed
      Generated.Bindings.SmallSumcheckInputs.helper33Helper)
    (.cons (some original) (.cons (returned.get (.there (.there (.there (.there .here)))))
      (.cons (returned.get (.there (.there (.there (.there (.there .here)))))) .nil)))).bind fun checked =>
    PIR.Process.done (checked.get .here)

theorem terminal_check (selection : Selection) (reference : PrefixState (model.Field field) Frame 0)
    (count : Nat) (shape : reference.original.length = 2^count) (small : count < 64)
    (finite : reference.original.length < indexLimit) :
    terminalCheck model selection reference.original
      (SumcheckVerifierBodies.reduceReturnValues (encode model 0 reference).slots) =
      .done (some (decide (reference.scalar = reference.entries.sum))) := by
  have pointBound : reference.point.length < indexLimit := by
    rw [terminal_point_length model reference count shape]
    exact lt_trans small (by decide +kernel)
  have checker := Multilinear.Admission.check_eq model (source selection).payload.linked
    (admissionBodies selection) reference.original reference.point reference.scalar finite pointBound
  unfold terminalCheck
  change ((invoke (tables model (source selection).payload.definitions).closed
    Generated.Bindings.SmallSumcheckInputs.helper33Helper
    (Multilinear.Admission.checkInputs model field reference.original reference.point reference.scalar)).bind _).bind _ = _
  rw [Evaluation.closed_invoke_componentTablesOn, checker]
  have valid := terminal_shape model reference count shape small
  simp only [valid, true_and, PIR.Process.interpret, PIR.Process.bind]
  apply congrArg PIR.Process.done
  change some (decide (reference.entries.sum = reference.scalar)) =
    some (decide (reference.scalar = reference.entries.sum))
  simp only [eq_comm]

/-- One source use equals the actual complete reduction followed by its actual
checker. The arbitrary caller frame remains available until the source result. -/
theorem one_reduction (selection : Selection) (site : String)
    (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (callerFrame : Frame) (shape : original.length = 2^count) :
    SourceRootReference.one model selection {} site (some original) (some scalar) (some count) (some handle) =
      (reduction model (source selection).payload.definitions
        (Occurrence.table model (source selection).payload) (ProtocolContext.enter {} site [0,1]) handle
        (maximum selection) count (PrefixState.initial original count scalar callerFrame shape)).bind
        (fun returned => terminalCheck model selection original returned.1) := by
  have distinct : NormalForm.RosterDistinct (ProtocolContext.enter {} site [0,1]) 1 2 := by
    exact .ofSeparate (by change (0 : Nat) ≠ 1; decide) (by decide)
  unfold reduction
  rw [SumcheckReductionReference.body_reference model _ (source selection).payload.linked
    (SumcheckReductionReference.actual_bodies model selection) _ _ _ distinct]
  unfold SourceRootReference.one
  have initial := (Sum.initial model field "s0").invokeOn (model := model)
    (I := Occurrence.signature model.toCarriers)
    (helper := Generated.Bindings.SmallSumcheckInputs.helper9Helper)
    _ (source selection).payload.linked (wrappers model selection).initial (.cons scalar .nil) trivial
  change invoke (tables model (source selection).payload.definitions).closed
    Generated.Bindings.SmallSumcheckInputs.helper9Helper (.cons scalar .nil) =
    PIR.Process.done (.cons [] (.cons scalar .nil)) at initial
  change ((invoke (tables model (source selection).payload.definitions).closed
    Generated.Bindings.SmallSumcheckInputs.helper9Helper (.cons scalar .nil)).bind _).bind _ = _
  rw [initial]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]
  rfl

end ZkcSecurity.Families.Sumcheck.SourceIteration
