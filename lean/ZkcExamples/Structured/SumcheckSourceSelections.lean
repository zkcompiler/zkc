module

public import Zkc.Source.Structured.SumReferenceInstallation
public import Zkc.Source.Structured.MultilinearAdmissionInstallation
public import ZkcExamples.Structured.SumcheckReferenceInstallation
public import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs
public import ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs
public meta import ZkcTools.StructuredSource.ReferenceInstallation
public meta import ZkcTools.StructuredSource.InferReferenceInstallation

@[expose] public section

/-! Data selections for two actual admitted sources. Names select complete
signatures and bodies; the mathematical formulas come from the shared laws.
No source/root receipt or constructed-artifact equation is asserted here. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace ZkcExamples.Structured.SumcheckSourceSelections
open Zkc.Source Zkc.Source.Structured ReferenceLibrary
open Generated.Bindings

inductive Selection | small | twoSums

noncomputable def source : Selection → Program
  | .small => SmallSumcheckInputs.imported.program
  | .twoSums => TwoSumsInputs.imported.program

def maximum : Selection → Nat | .small => 2 | .twoSums => 4

abbrev field := SumcheckReferenceInstallation.field

/-- The admitted scalar target anchors dependency discovery. The witness and
its exact body associations are checked together. -/
noncomputable def scalarInstallation : {bindings : Sum.Bindings // ∀ model,
    Sum.ScalarBodies model SmallSumcheckInputs.program.payload.definitions field
      SmallSumcheckInputs.helper4Helper.name bindings} := by
  infer_reference_installation

/-- TwoSums contains two sum chains. The pair target chooses the outer chain;
list order and the first matching sum helper are not its semantic identity. -/
noncomputable def pairInstallation : {bindings : Sum.Bindings // ∀ model,
    Sum.PairBodies model TwoSumsInputs.program.payload.definitions field
      TwoSumsInputs.helper4Helper.name bindings} := by
  infer_reference_installation

noncomputable def sumBindings : Sum.Bindings := scalarInstallation.val
noncomputable def outerSumBindings : Sum.Bindings := pairInstallation.val

/-- Infer the entire multilinear dependency chain from its checked typed
bodies. The library supplies the formulas; the source supplies their identities. -/
noncomputable def multilinearInstallation : {bindings : MultilinearBodies.Bindings //
    Multilinear.Admission.Bodies SmallSumcheckInputs.program.payload.definitions field bindings
      SmallSumcheckInputs.helper33Helper.name} := by
  infer_reference_installation

noncomputable abbrev bindings := multilinearInstallation.val
abbrev checker := SmallSumcheckInputs.helper33Helper.name

/-- Exact body checks are shared proofs, with each instance's checking charged. -/
theorem roundBodies (selection : Selection) :
    SumcheckReferenceInstallation.Bodies (source selection).payload.definitions bindings := by
  constructor
  · cases selection <;> select_reference_bodies
  · cases selection <;> bind_structured_bodies

theorem admissionBodies (selection : Selection) :
    Multilinear.Admission.Bodies (source selection).payload.definitions field bindings checker := by
  refine ⟨(roundBodies selection).toBodies, ?_, ?_, ?_, ?_, ?_⟩
  all_goals cases selection <;> bind_structured_bodies

theorem sumBodies (model : DomainModel) (selection : Selection) :
    Sum.Bodies model (source selection).payload.definitions field sumBindings := by
  cases selection with
  | small => exact (scalarInstallation.property model).toBodies
  | twoSums => select_reference_bodies

theorem outerSumBodies (model : DomainModel) :
    Sum.Bodies model (source .twoSums).payload.definitions field outerSumBindings :=
  (pairInstallation.property model).toBodies

structure Wrappers (model : DomainModel) (definitions : List CheckedDefinition) : Prop where
  initial : BodyIn definitions
    SmallSumcheckInputs.helper9Helper (Sum.initial model field "s0").body
  openClaim : BodyIn definitions
    SmallSumcheckInputs.helper16Helper (Sum.identity model field).body
  atPrefix : BodyIn definitions
    TwoSumsInputs.helper24Helper (Sum.identity model field).body
  empty : BodyIn definitions
    SmallSumcheckInputs.helper15Helper (emptyVector model field "s0").body
  tableShape : BodyIn definitions SmallSumcheckInputs.helper13Helper (Sum.tableShape model field bindings).body
  pending : BodyIn definitions
    SmallSumcheckInputs.helper14Helper (Sum.pendingRelation model field sumBindings bindings.values).body

/-- One nominal wrapper installation serves both actual Sumcheck components. -/
theorem wrappers (model : DomainModel) (selection : Selection) :
    Wrappers model (source selection).payload.definitions := by
  cases selection <;> select_reference_bodies

def shapeName : Selection → String
  | .small => SmallSumcheckInputs.helper0Helper.name
  | .twoSums => TwoSumsInputs.helper0Helper.name

theorem shapeBody (model : DomainModel) (selection : Selection) :
    BodyIn (source selection).payload.definitions
      ⟨shapeName selection, .math, [.vector field, .index], [.boolean]⟩
      (Sum.inputShape model field (maximum selection)).body := by
  cases selection <;> bind_structured_bodies

theorem scalarBody (model : DomainModel) :
    BodyIn (source .small).payload.definitions SmallSumcheckInputs.helper4Helper
      (Sum.scalarRelation model field sumBindings).body :=
  (scalarInstallation.property model).relation

theorem pairBody (model : DomainModel) :
    BodyIn (source .twoSums).payload.definitions TwoSumsInputs.helper4Helper
      (Sum.pairRelation model field outerSumBindings).body :=
  (pairInstallation.property model).relation

theorem bothBody (model : DomainModel) :
    BodyIn (source .twoSums).payload.definitions TwoSumsInputs.helper25Helper (Sum.both model).body := by
  bind_structured_bodies

/-- Selection of the actual admitted reduction body, charged per source. -/
noncomputable def reduction : Selection →
    Region protocolDialect SumcheckVerifierBodies.reduceInputs SumcheckVerifierBodies.reduceOutputs
  | .small => SmallSumcheckInputs.protocol0Body
  | .twoSums => TwoSumsInputs.protocol0Body

theorem reduction_selected (selection : Selection) :
    reduction selection = SumcheckVerifierBodies.reduceBody (maximum selection) := by
  cases selection <;> kernel_rfl

end ZkcExamples.Structured.SumcheckSourceSelections

namespace ZkcExamples.Structured.SumcheckReductionReference
open Zkc.Source Zkc.Source.Structured
theorem actual_bodies (model : DomainModel) (selection : SumcheckSourceSelections.Selection) :
    Bodies model (SumcheckSourceSelections.source selection).payload.definitions := by
  refine ⟨?_, ?_, (SumcheckSourceSelections.wrappers model selection).openClaim,
    (SumcheckSourceSelections.wrappers model selection).atPrefix⟩
  all_goals cases selection <;> bind_structured_bodies

end ZkcExamples.Structured.SumcheckReductionReference
