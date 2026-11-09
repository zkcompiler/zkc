import Zkc.Verification.Bindings.Sumcheck.SourcePairRound
import Zkc.Verification.Bindings.Sumcheck.SourceProducerReduction
import Zkc.Applications.IR.Structured.SumcheckSourceSelections

/-! Direct controls for nominal reconstruction and the actual selected round
consumers. Complete root controls remain in SumcheckSourceProperties. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
namespace TestsSecurity.SumcheckNominalAdoption
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured SumcheckReferenceInstallation
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck TableComponent
open Zkc.Protocols.Sumcheck.Multilinear

section Nominal
variable (model : DomainModel) (domain : String) (bindings : MultilinearBodies.Bindings)

/-- Both views retain precisely the original dependency predicates. -/
example (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (args : Values model.Value (ReferenceLibrary.Multilinear.triple domain)) :
    (ReferenceLibrary.Multilinear.sumsView model domain bindings).Requires table args ↔
      (ReferenceLibrary.Multilinear.sums model domain bindings).Requires table args := Iff.rfl

example (table : Evaluation.MeaningsOn model.toCarriers closedInterface)
    (args : Values model.Value (ReferenceLibrary.Multilinear.firstInputs domain)) :
    (ReferenceLibrary.Multilinear.firstView model domain bindings).Requires table args ↔
      (ReferenceLibrary.Multilinear.first model domain bindings).Requires table args := Iff.rfl

/-- Equality on all raw inputs retains every original nominal guard and stop. -/
example (args : Values model.Value (ReferenceLibrary.Multilinear.triple domain)) :
    (ReferenceLibrary.Multilinear.sumsView model domain bindings).reference args =
      (ReferenceLibrary.Multilinear.sums model domain bindings).reference args :=
  ReferenceLibrary.Multilinear.sumsView_reference model domain bindings args

/-- Raw sums still ignore column representability and the global table shape. -/
example (a b : model.Field domain) :
    (ReferenceLibrary.Multilinear.sumsView model domain bindings).reference
      (ReferenceLibrary.Multilinear.tableValues model domain [a, b] 3 indexLimit) =
        .returned (.cons a (.cons b .nil)) := by
  rw [ReferenceLibrary.Multilinear.sumsView_reference]
  simp [ReferenceLibrary.Multilinear.sums, ReferenceLibrary.Multilinear.halves,
    ReferenceLibrary.Multilinear.halvesOutcome, ReferenceLibrary.Multilinear.tableValues,
    show 3 < indexLimit by decide +kernel]

example (a : model.Field domain) :
    (ReferenceLibrary.Multilinear.sumsView model domain bindings).reference
      (ReferenceLibrary.Multilinear.tableValues model domain [a] 1 1) = .stopped .refused := by
  rw [ReferenceLibrary.Multilinear.sumsView_reference]
  simp [ReferenceLibrary.Multilinear.sums, ReferenceLibrary.Multilinear.halves,
    ReferenceLibrary.Multilinear.halvesOutcome, ReferenceLibrary.Multilinear.tableValues,
    show 1 < indexLimit by decide +kernel]

/-- Every challenge restores all three restriction outputs, including columns. -/
example (entries : List (model.Field domain)) (dimension columns : Nat)
    (challenge : model.Field domain) :
    (ReferenceLibrary.Multilinear.firstView model domain bindings).reference
      (.cons entries (.cons dimension (.cons columns (.cons challenge .nil)))) =
        ReferenceLibrary.Multilinear.firstOutcome model domain
          (.cons entries (.cons dimension (.cons columns (.cons challenge .nil)))) :=
  ReferenceLibrary.Multilinear.firstView_reference model domain bindings _

/-- A different nominal domain changes the exact helper signature. -/
example (other : String) (different : other ≠ domain) :
    (ReferenceLibrary.Multilinear.firstHelper other bindings).inputs ≠
      (ReferenceLibrary.Multilinear.firstHelper domain bindings).inputs := by
  intro same
  have head := List.cons.inj same
  exact different (Ty.vector.inj head.1)
end Nominal

variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {Frame : Type}

omit fieldLaw in
/-- Each actual library installs the same law in its own complete table. -/
theorem actual_sums (selection : SumcheckSourceSelections.Selection)
    (entries : List (model.Field field)) (dimension columns : Nat) :
    invoke (ReferenceLibrary.Multilinear.closed model
      (definitions := (SumcheckSourceSelections.source selection).payload.definitions))
      ⟨MultilinearSourceBindings.sumcheck.sums, .local,
        ReferenceLibrary.Multilinear.triple field, [.field field, .field field]⟩
      (ReferenceLibrary.Multilinear.tableValues model field entries dimension columns) =
        primitiveOutcome ((ReferenceLibrary.Multilinear.sumsView model field
          MultilinearSourceBindings.sumcheck).reference
            (ReferenceLibrary.Multilinear.tableValues model field entries dimension columns)) := by
  rw [ReferenceLibrary.Multilinear.sumsView_reference]
  exact ReferenceLibrary.Multilinear.sums_eq model
    (SumcheckSourceSelections.source selection).payload.linked
    (SumcheckSourceSelections.roundBodies selection).toBodies entries dimension columns

/-- The exact producer/validator pair still needs roles, delivery, shape,
bounds and scalar truth, and retains an arbitrary caller frame. -/
abbrev actual_pair {n : Nat} (selection : SumcheckSourceSelections.Selection) :=
  SourcePair.round (Frame := Frame) (n := n) model _
    (SumcheckSourceSelections.source selection).payload.linked
    (SumcheckSourceSelections.roundBodies selection)
    (Occurrence.table model (SumcheckSourceSelections.source selection).payload)

example {n : Nat} (state : PrefixState (model.Field field) Frame (n + 1))
    (message : model.Field field × model.Field field) (challenge : model.Field field) :
    RestrictionInvariant (SourceIteration.originalTable model state)
      (state.advance message challenge).point (state.advance message challenge).entries n 1 :=
  SourceIteration.advance_restriction model state message challenge

example {n : Nat} (state : PrefixState (model.Field field) Frame (n + 1))
    (challenge : model.Field field) :
    (state.advance (SourcePair.endpoints model state) challenge).scalar =
      (state.advance (SourcePair.endpoints model state) challenge).entries.sum :=
  SourcePair.advance_honest model state challenge

/-- Complete producer terminal row keeps the private point and every absence. -/
example (entries point : List (model.Field field)) (dimension columns : Nat) :
    SourceProducerReduction.terminal model (Prover.state model entries dimension columns point) =
      .cons (some point) (.cons (some entries) (.cons (some dimension) (.cons (some columns)
        (.cons none (.cons none (.cons none .nil)))))) := rfl

def stopHandler (reason : PIR.Stop) :
    PIR.Handler (Occurrence.signature model.toCarriers) Nat Nat :=
  fun _ state ↦ ⟨.stopped reason, state + 1, [state]⟩

/-- A stop at the first actual operation preserves its state and event prefix. -/
example (ctx : ProtocolContext) (entries point : List (model.Field field))
    (dimension columns : Nat) (reason : PIR.Stop) (state : Nat) :
    (Prover.reference model ctx entries dimension columns point).run
      (stopHandler model reason) state = ⟨.stopped reason, state + 1, [state]⟩ := rfl

example (ctx : ProtocolContext) (reason : PIR.Stop) (state : Nat) :
    (SumcheckReferenceInstallation.reference model ctx none none none).run
      (stopHandler model reason) state = ⟨.stopped reason, state + 1, [state]⟩ := rfl

#print axioms ReferenceLibrary.Multilinear.sumsView
#print axioms ReferenceLibrary.Multilinear.firstView
#print axioms actual_sums
#print axioms actual_pair
#print axioms SourceIteration.restriction
#print axioms SourceIteration.advance_table
#print axioms SourceIteration.no_contract
#print axioms SourcePair.advance_honest
#print axioms SourcePair.round
end TestsSecurity.SumcheckNominalAdoption
