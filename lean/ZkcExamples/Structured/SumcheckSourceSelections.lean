module

public import Zkc.Source.Structured.SumReferenceInstallation
public import Zkc.Source.Structured.MultilinearAdmissionInstallation
public import ZkcExamples.Structured.SumcheckReferenceInstallation
public import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs
public import ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs
public meta import ZkcTools.StructuredSource.ReferenceInstallation

@[expose] public section

/-! Data selections for two actual admitted sources. Names select complete
signatures and bodies; the mathematical formulas come from the shared laws.
No source/root receipt or constructed-artifact equation is asserted here. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.SumcheckSourceSelections
open Zkc.Source Zkc.Source.Structured ReferenceLibrary
open Generated.Bindings

inductive Selection | small | twoSums

noncomputable def source : Selection → Program
  | .small => SmallSumcheckInputs.imported.program
  | .twoSums => TwoSumsInputs.imported.program

def maximum : Selection → Nat | .small => 2 | .twoSums => 4

def sumBindings : Sum.Bindings where
  add := SmallSumcheckInputs.helper1Helper.name
  step := SmallSumcheckInputs.helper2Helper.name
  total := SmallSumcheckInputs.helper3Helper.name
  domain := "finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_domain"

def outerSumBindings : Sum.Bindings where
  add := TwoSumsInputs.helper1Helper.name
  step := TwoSumsInputs.helper2Helper.name
  total := TwoSumsInputs.helper3Helper.name
  domain := "finite_zkl_9d89739f0825e451fe8a58993c7a5d6dc7767d148c154dbd13182e883a66e305_s1_domain"

abbrev field := SumcheckReferenceInstallation.field
abbrev bindings := MultilinearSourceBindings.sumcheck
abbrev checker := "zkl_0861cc269909e563bb5bba257221bc271da7a3c6e097d1e621b4924aa733d3cc"

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
  cases selection <;> select_reference_bodies

theorem outerSumBodies (model : DomainModel) :
    Sum.Bodies model (source .twoSums).payload.definitions field outerSumBindings := by
  select_reference_bodies

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
      (Sum.scalarRelation model field sumBindings).body := by
  bind_structured_bodies

theorem pairBody (model : DomainModel) :
    BodyIn (source .twoSums).payload.definitions TwoSumsInputs.helper4Helper
      (Sum.pairRelation model field outerSumBindings).body := by
  bind_structured_bodies

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
