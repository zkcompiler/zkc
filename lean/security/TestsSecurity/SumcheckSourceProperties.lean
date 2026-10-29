import Tests.SumcheckSourceProperties
import ZkcSecurity.Realizations.Sumcheck.SourceLossless

set_option autoImplicit false
noncomputable section
namespace TestsSecurity.SumcheckSourceProperties
open Zkc.Source Zkc.Source.Structured ReferenceLibrary Zkc.Transcript Zkc.Obligations
open ZkcExamples.Structured SumcheckReferenceInstallation
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck TableComponent SourceIteration
open SumcheckSourceSelections hiding field
open OracleComp OracleSpec

variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {Frame E P : Type} {Raw : E → Type}

/-- These selections install all symbolic contracts in both actual libraries.
The function still requires actual cuts, successful handler laws, conditional
sampling and an incoming history; none is inferred from a selected name. -/
def actual_sampled (selection : Selection) :=
  SourceInstallations.selected_sampled model (Frame := Frame) (E := E) (P := P) (Raw := Raw) selection

abbrev actual_honest {H : Type} (selection : Selection) :=
  SourceInstallations.selected_honest model (Frame := Frame) (E := E) (H := H) selection

/-- A false scalar has a valid, complete representation, including the frame. -/
theorem false_initial (xs : List (model.Field field)) (scalar : model.Field field) (frame : Frame)
    (count : Nat) (shape : xs.length = 2^count) (wrong : scalar ≠ xs.sum) :
    (layout model).representation.No (PrefixState.initial xs count scalar frame shape) :=
  initial_no model xs count scalar frame shape wrong

/-- Bad initial shape cannot be repaired by scalar truth. -/
theorem bad_initial_shape (xs : List (model.Field field)) (count : Nat) (bad : xs.length ≠ 2^count) :
    ¬ ∃ reference : PrefixState (model.Field field) Frame count,
      reference.original = xs ∧ reference.point = [] := by
  rintro ⟨reference,same,empty⟩
  apply bad
  simpa only [same,empty,List.length_nil,Nat.add_zero] using reference.shape

/-- Losing any arbitrary private suffix invalidates both complete residual predicates. -/
theorem lost_private_no (xs : List (model.Field field)) (original changed : Frame)
    (different : changed ≠ original) (history : List E)
    (values : Values (Component model.Value) SumcheckVerifierBodies.reduceOutputs) :
    ¬ reductionNo model xs original history (values,changed) := by
  rintro ⟨_,_,_,same,_⟩
  exact different (congrArg Prod.snd same)

theorem lost_private_yes (xs : List (model.Field field)) (original changed : Frame)
    (different : changed ≠ original)
    (values : Values (Component model.Value) SumcheckVerifierBodies.reduceOutputs) :
    ¬ reductionYes model xs original (values,changed) := by
  rintro ⟨_,_,_,same,_⟩
  exact different (congrArg Prod.snd same)

/-- False terminal claims return false under the exact same source checker. -/
theorem terminal_false (selection : Selection) (reference : PrefixState (model.Field field) Frame 0)
    (count : Nat) (shape : reference.original.length = 2^count) (small : count < 64)
    (finite : reference.original.length < indexLimit) (wrong : (layout model).representation.No reference) :
    terminalCheck model selection reference.original
      (SumcheckVerifierBodies.reduceReturnValues (encode model 0 reference).slots) = .done (some false) := by
  rw [terminal_check model selection reference count shape small finite]
  have unequal : reference.scalar ≠ reference.entries.sum := ((layout model).no_iff reference).mp wrong
  simp only [unequal, decide_false]

def rejectingHandler : PIR.Handler (Occurrence.signature model.toCarriers) Unit Unit :=
  fun _ _ => ⟨.stopped .reject, (), []⟩

theorem rejecting_reduction (selection : Selection) (ctx : ProtocolContext)
    (distinct : NormalForm.RosterDistinct ctx 1 2) (handle : Nat)
    (reference : PrefixState (model.Field field) Frame 1) (bounded : 1 ≤ maximum selection) :
    (reduction model (source selection).payload.definitions (Occurrence.table model (source selection).payload)
      ctx handle (maximum selection) 1 reference).run (rejectingHandler model) () =
      ⟨.stopped .reject, (), []⟩ := by
  rw [reduction_equation model _ (source selection).payload.linked (roundBodies selection)
    (Occurrence.table model (source selection).payload) ctx distinct handle
    (SumcheckReductionReference.actual_bodies model selection) (maximum selection) 1 bounded]
  rfl

theorem honest_reject_refused (selection : Selection) (ctx : ProtocolContext)
    (distinct : NormalForm.RosterDistinct ctx 1 2) (handle : Nat)
    (reference : PrefixState (model.Field field) Frame 1) (bounded : 1 ≤ maximum selection)
    (history : List Unit) :
    ¬ PIR.WeakestPrecondition.satisfies
      ((reduction model (source selection).payload.definitions (Occurrence.table model (source selection).payload)
        ctx handle (maximum selection) 1 reference).run (rejectingHandler model) ())
      (fun _ _ _ => True) (fun _ _ _ => False) history := by
  rw [rejecting_reduction model selection ctx distinct handle reference bounded]
  exact id

/-- Source selection and polynomial degrees do not supply the reached-history
collision law. The attempted actual-library contract must leave that goal open. -/
example (_selection : Selection) [∀ event, SampleableType (Raw event)]
    (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (_charge : List E → E → ENNReal) (ctx : ProtocolContext) (_distinct : NormalForm.RosterDistinct ctx 1 2)
    (handle : Nat) (_cuts : SourceRound.Cuts model absorb ctx handle) (_boundaries : Boundaries model absorb ctx)
    (_xs : List (model.Field field)) (_frame : Frame) : True := by
  fail_if_success
    have : RepeatedComponent.NoContract
        (component model (source _selection).payload.definitions (Occurrence.table model (source _selection).payload) ctx handle)
        absorb (ZkcSecurity.Obligations.boundedEscape _charge) (no model _xs _frame) := by
      apply sampled_contract model _ (source _selection).payload.linked (roundBodies _selection)
        (Occurrence.table model (source _selection).payload) ctx _distinct handle _xs _frame absorb _charge _cuts _boundaries
      assumption
  trivial

/-- The terminal source theorem cannot silently invent a missing finite bound. -/
example (_selection : Selection) (reference : PrefixState (model.Field field) Frame 0)
    (count : Nat) (_shape : reference.original.length = 2^count) (_small : count < 64) : True := by
  fail_if_success
    have : terminalCheck model _selection reference.original
        (SumcheckVerifierBodies.reduceReturnValues (encode model 0 reference).slots) =
        .done (some (decide (reference.scalar = reference.entries.sum))) := by
      apply terminal_check model _selection reference count _shape _small
      assumption
  trivial

#print axioms actual_sampled
#print axioms actual_honest
#print axioms false_initial
#print axioms bad_initial_shape
#print axioms lost_private_no
#print axioms lost_private_yes
#print axioms terminal_false
#print axioms rejecting_reduction
#print axioms honest_reject_refused
#print axioms SourceIteration.loop_equation
#print axioms SourceIteration.reduction_honest_preserving
#print axioms SourceRootReference.actual_reference
#print axioms SourceInstallations.small_no
#print axioms SourceInstallations.small_honest
#print axioms SourceInstallations.two_no
#print axioms SourceInstallations.two_honest
#print axioms SourceInstallations.two_cost
#print axioms SourceLossless.small_data
#print axioms SourceLossless.two_data
#print axioms SourceLossless.root_lossless
end TestsSecurity.SumcheckSourceProperties
