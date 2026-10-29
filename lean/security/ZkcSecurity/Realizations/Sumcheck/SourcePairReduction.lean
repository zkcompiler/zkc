module

public import ZkcSecurity.Realizations.Sumcheck.SourcePairIteration
public import ZkcSecurity.Source.LoopContracts

@[expose] public section

/-! Successful pairing of both actual reduction bodies. This theorem has no
validator-handler or whole-program equality premise. Exact local body laws,
source shape, arithmetic bounds and the honest scalar are its obligations.
-/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourcePair
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent
open ZkcSecurity.Source

variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {Frame : Type}

def returned (original : List (model.Field field)) (callerFrame : Frame)
    (p v : Values (Component model.Value) SumcheckVerifierBodies.reduceOutputs) : Prop :=
  ∃ state : PrefixState (model.Field field) Frame 0,
    state.original = original ∧ state.frame = callerFrame ∧ state.scalar = state.entries.sum ∧
    p = SourceProducerReduction.terminal model (producerSlots model state) ∧
    v = SumcheckVerifierBodies.reduceReturnValues (validatorSlots model state)

theorem reduction (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (roundBodies : Bodies definitions MultilinearSourceBindings.sumcheck)
    (producerBodies : SourceProducerReduction.Bodies model definitions)
    (validatorBodies : SumcheckReductionReference.Bodies model definitions)
    (protocols : ProtocolTable model.Value (Occurrence.signature model.toCarriers))
    (ctx : ProtocolContext) (distinctP : NormalForm.RosterDistinct ctx 0 2)
    (distinctV : NormalForm.RosterDistinct ctx 1 2)
    (scope : PairScope)
    (roles : ctx.roles 0 = scope.producer ∧ ctx.roles 1 = scope.validator)
    (delivery : (SumcheckRoundNormalForms.challengeSite ctx,
      SumcheckRoundNormalForms.deliverySite ctx) ∈ scope.deliveries)
    (original : List (model.Field field)) (scalar : model.Field field) (callerFrame : Frame)
    (maximum count handle : Nat) (shape : original.length = 2^count)
    (bounded : count ≤ maximum) (small : count < 64) (finite : original.length < indexLimit)
    (honest : scalar = original.sum) :
    Pair scope (returned model original callerFrame)
      ((SumcheckVerifierBodies.reduceBody maximum).denote
        (participantMeaningWithOn model (.silent _) Occurrence.actions (tables model definitions)
          (ctx.roles 0) protocols ctx Occurrence.iterations)
        (SourceProducerReduction.pattern.environment model
          (SourceProducerReduction.inputs model original count count)).get)
      ((SumcheckVerifierBodies.reduceBody maximum).denote
        (participantMeaningWithOn model (.silent _) Occurrence.actions (tables model definitions)
          (ctx.roles 1) protocols ctx Occurrence.iterations)
        (SumcheckReductionReference.pattern.environment model
          (SumcheckReductionReference.inputs model (some []) (some scalar) (some count) (some handle))).get) := by
  have bound : count < indexLimit := lt_trans small (by decide +kernel)
  rw [SourceProducerReduction.body_reference model definitions linked producerBodies protocols
    maximum ctx distinctP original count count bound bound (le_refl count)]
  rw [SumcheckReductionReference.body_reference model definitions linked validatorBodies protocols
    maximum ctx distinctV]
  let initial := PrefixState.initial original count scalar callerFrame shape
  let contract : LoopContracts.Paired (scope := scope)
      (producerStep model definitions protocols ctx maximum)
      (validatorStep model definitions protocols ctx maximum handle) :=
    ⟨invariant model original callerFrame,
      fun n index p v related => step model definitions linked roundBodies protocols ctx distinctP distinctV
        scope roles delivery original callerFrame maximum handle n index p v related⟩
  have paired := LoopContracts.repeat_pair (SumcheckVerifierBodies.repeatSpec maximum) ctx 0 1
    (.cons none .nil) (.cons (some handle) .nil)
    (callback model definitions protocols ctx 0) (callback model definitions protocols ctx 1)
    SumcheckVerifierBodies.repeatSite contract count (producerSlots model initial) (validatorSlots model initial)
    (by simp) (by simp) bounded (by
      dsimp only [contract, producerSlots, validatorSlots]
      rw [mask_producer model ctx maximum, SourceIteration.mask_state model ctx maximum]
      exact ⟨initial, rfl, rfl, honest, finite, small, rfl, rfl⟩)
  unfold SourceProducerReduction.reference SumcheckReductionReference.reference
  exact paired.bind _ _ (by
    intro p v valid
    obtain ⟨state, same, retained, right, _, _, rfl, rfl⟩ := valid
    exact Pair.done ⟨state, same, retained, right, rfl, rfl⟩)

#print axioms reduction
end ZkcSecurity.Realizations.Sumcheck.SourcePair
