module

public import ZkcSecurity.Bindings.Sumcheck.SourceFamilyProperties
public import ZkcSecurity.Bindings.Sumcheck.SourceReduction
public import ZkcSecurityExamples.Sumcheck.SourceRootReference

@[expose] public section

/-! Terminal and initial mathematics for the same nominal source library.
Shape is independent of scalar truth. A terminal No produces a returned false;
a terminal Yes produces a returned true. Bounds remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourceIteration
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured ReferenceLibrary Zkc.Transcript Zkc.Obligations
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent
open SumcheckSourceSelections hiding field
open Zkc.Polynomial.Multilinear

variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {Frame : Type}

theorem initial_no (original : List (model.Field field)) (count : Nat) (scalar : model.Field field)
    (callerFrame : Frame) (shape : original.length = 2^count) (wrong : scalar ≠ original.sum) :
    (layout model).representation.No (PrefixState.initial original count scalar callerFrame shape) := by
  exact SourceFamily.initial_no model original count scalar callerFrame shape wrong

theorem initial_yes (original : List (model.Field field)) (count : Nat) (scalar : model.Field field)
    (callerFrame : Frame) (shape : original.length = 2^count) (right : scalar = original.sum) :
    (layout model).representation.Yes (PrefixState.initial original count scalar callerFrame shape) := by
  exact SourceFamily.initial_yes model original count scalar callerFrame shape right

theorem terminal_point_length (reference : PrefixState (model.Field field) Frame 0)
    (count : Nat) (shape : reference.original.length = 2^count) : reference.point.length = count := by
  exact SourceFamily.terminal_point_length model reference count shape

theorem terminal_shape (reference : PrefixState (model.Field field) Frame 0)
    (count : Nat) (shape : reference.original.length = 2^count) (small : count < 64) :
    Multilinear.Admission.HasShape reference.original reference.point.length 1 := by
  exact SourceFamily.terminal_shape model reference count shape small

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
  exact SourceFamily.terminal_check model (SourceFamilySelections.installed selection) reference count shape small finite

/-- The reduction invariant may use an independent mathematical table. The
terminal checker still consumes the actual original source input, which may
have invalid shape or exceed the nominal index range. -/
theorem one_reduction_with_original (selection : Selection) (site : String)
    (original referenceOriginal : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (callerFrame : Frame) (shape : referenceOriginal.length = 2^count) :
    SourceRootReference.one model selection {} site (some original) (some scalar) (some count) (some handle) =
      (reduction model (source selection).payload.definitions
        (Occurrence.table model (source selection).payload) (ProtocolContext.enter {} site [0,1]) handle
        (maximum selection) count (PrefixState.initial referenceOriginal count scalar callerFrame shape)).bind
        (fun returned => terminalCheck model selection original returned.1) := by
  exact SourceFamily.one_reduction_with_original model (SourceFamilySelections.installed selection) site original referenceOriginal count handle scalar callerFrame shape

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
  exact SourceFamily.one_reduction model (SourceFamilySelections.installed selection) site original count handle scalar callerFrame shape

end ZkcSecurity.Realizations.Sumcheck.SourceIteration
